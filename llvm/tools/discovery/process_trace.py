#!/usr/bin/env python3

import sys
import networkx as nx
import argparse
import copy
import subprocess
import re
import io as sio
import os
import itertools
import html
import operator
from functools import cmp_to_key

import trace_utils as u

arg_plain = "plain"
arg_minizinc = "minizinc"
arg_graphviz = "graphviz"

arg_query = "query"
arg_simplify = "simplify"
arg_record = "record"
arg_decompose = "decompose"
arg_subtract = "subtract"
arg_compose = "compose"
arg_transform = "transform"
arg_fold = "fold"
arg_print = "print"
arg_visualize = "visualize"

# List of colors for visualization.
colors = [(141, 211, 199), (255, 255, 179), (190, 186, 218), (251, 128, 114),
          (128, 177, 211), (253, 180, 98),  (179, 222, 105), (252, 205, 229),
          (217, 217, 217), (188, 128, 189), (204, 235, 197), (255, 237, 111),
          (241, 150, 112), (204, 235, 197)]

# Cache of demangled function names.
demangled_cache = {}

# Input order of instruction properties.
property_input_order = {u.tk_iterator : 0,
                        u.tk_impure : 1,
                        u.tk_control : 2,
                        u.tk_noncommutative : 3,
                        u.tk_name : 4,
                        u.tk_location : 5,
                        u.tk_children : 6,
                        u.tk_region : 7,
                        u.tk_immediate : 8}

# Orders instruction properties according to input order.
def instruction_property_compare(i1, i2):
    (k1, _1) = i1
    (k2, _2) = i2
    return u.cmp(property_input_order[k1], property_input_order[k2])

# Orders instructions by name except for 'source' which goes first, for sanity.
def instruction_name_compare(n1, n2):
    if n1 == "source":
        return -1
    if n2 == "source":
        return 1
    else:
        return u.cmp(n1, n2)

# Removes instruction properties without any corresponding blocks.
def clean_instruction_properties(PI, PB):
    PIc = {}
    for inst in set([value[u.tk_instruction]
                     for key, value in PB.items()
                     if u.tk_instruction in value]):
        PIc[inst] = PI[inst]
    for inst, ips in list(PI.items()):
        for child in PI[inst].get(u.tk_children, []):
            PIc[child] = PI[child]
    return PIc

# Tells wether the given instruction corresponds to a LLVM conversion operation.
def is_conversion(i):
    # See https://llvm.org/docs/LangRef.html#conversion-operations.
    return i in {"trunc", "zext", "sext", "fptrunc", "fpext", "fptoui",
                 "fptosi", "uitofp", "sitofp", "ptrtoint", "inttoptr",
                 "bitcast", "addrspacecast"}

# Tells wether the given instruction corresponds to a LLVM getelementptr
# operation.
def is_gep(i):
    return i == "getelementptr"

# Tells whether the given instruction corresponds to a LLVM aggregate operation.
def is_aggregate(i):
    # See https://llvm.org/docs/LangRef.html#aggregate-operations
    return i in {"extractvalue", "insertvalue"}

# Tells whether the given block is effectful and cannot be pruned away. A block
# is effectful if:
# - it is impure, or
# - it is a control, non-iterator block
def is_effectful(b, PB, PI):
    return u.properties(b, PB, PI).get(u.tk_impure) == u.tk_true or \
           (u.properties(b, PB, PI).get(u.tk_control) == u.tk_true and \
            u.properties(b, PB, PI).get(u.tk_iterator) != u.tk_true)

# Tells whether the given block is dispensable for simplification purposes.
def is_dispensable(b, PB, PI):
    name = u.properties(b, PB, PI).get(u.tk_name)
    return name in ["dfsw$pthread_create"]

# Tells whether a list of tag-data pairs contains the given tag.
def is_tagged_with(tag, tags):
    return find_tag_data(tag, tags) != None

# Gives a tag-data string out of a tag tuple:
def tag_tuple_to_str(tagdata):
    # t can be a string or an int (if the tag has been normalized).
    (t, (g, i)) = tagdata
    return str(t) + u.tk_tag_sep + str(g) + u.tk_tag_sep + str(i)

# Gives the numeric tag id of the given tag string (which can also be an alias).
def get_tag_id(tag, G):
    (_, __, ___, PT) = G
    if tag in PT:
        # The tag is already an existent numeric tag id.
        return tag
    if tag.isdigit() and int(tag) in PT:
        return int(tag)
    else:
        for key, value in PT.items():
            if tag == value.get(u.tk_alias):
                return key
        sys.stderr.write("Error: could not find tag or tag alias '" + tag + "'\n")
        sys.exit(-1)

# Gives the data of a tag within a list of tag-data pairs.
def find_tag_data(tag, tags):
    if tags == None:
        return None
    for tag_data in tags:
        t = u.tag_name(tag_data)
        if t == tag:
            return u.tag_data(tag_data)
    return None

# Returns a map from a property of the given tag to nodes.
def tag_nodes_map(G, tag, f):
    (DDG, PB, _, __) = G
    tag_nodes = {}
    for block in [b for b in DDG.nodes()]:
        if is_tagged_with(tag, PB[block].get(u.tk_tags)):
            # p is either a tag group or a tag instance
            p = f(find_tag_data(tag, PB[block].get(u.tk_tags)))
            if not p in tag_nodes:
                tag_nodes[p] = set()
            tag_nodes[p].add(block)
    return tag_nodes

# Returns a map from groups of the given tag to nodes.
def group_nodes_map(G, tag):
    return tag_nodes_map(G, tag, lambda g_i : g_i[0])

# Returns a map from instances of the given tag to nodes.
def instance_nodes_map(G, tag):
    return tag_nodes_map(G, tag, lambda g_i1 : g_i1[1])

# Makes a set of given nodes darker in a color map.
def contrast_colors(color_map, darker_nodes):
    for k in list(color_map.keys()):
        if k in darker_nodes:
            factor = 0.2
        else:
            factor = -0.05
        color_map[k] = adjust_color(color_map[k], factor)

# Returns a legend and a color map to be applied to a match visualization.
def format_match(pattern, match):
    if pattern in u.pat_all_uni:
        if pattern in u.pat_all_map_like:
            unit = "runs"
        elif pattern in [u.pat_linear_reduction, u.pat_linear_scan,
                         u.pat_conditional_linear_scan]:
            unit = "steps"
        legend = "(" + str(len(match)) + " " + unit + ")"
        color_map = {node: colors[(step % len(colors))]
                     for node, step in list(u.index_map(match).items())}
    elif pattern == u.pat_pipeline:
        (stages, runs) = match
        node_stage = u.index_map(stages)
        node_run = u.index_map(runs)
        legend = "(" + str(len(stages)) + " stages, " + str(len(runs)) + \
                 " runs)"
        color_map = dict()
        for k in list(node_stage.keys()):
            run_completion = float(node_run[k]) / len(runs)
            factor = run_completion * 0.5
            original_color = colors[node_stage[k] % len(colors)]
            color_map[k] = adjust_color(original_color, factor)
    elif pattern == u.pat_linear_map_reduction:
        (runs, steps) = match
        legend = "(" + str(len(steps)) + " steps)"
        color_map = {node: colors[(step % len(colors))]
                     for node, step
                     in list(u.index_map(runs).items()) + list(u.index_map(steps).items())}
        contrast_colors(color_map, set(u.concat(runs)))
    elif pattern in [u.pat_tiled_reduction, u.pat_tiled_map_reduction]:
        if pattern == u.pat_tiled_reduction:
            unified_match = [([], f, p) for f, p in match]
        else:
            unified_match = match
        partial_steps = set([len(p) for _, __, p in unified_match])
        (min_step, max_step) = (min(partial_steps), max(partial_steps))
        if min_step == max_step:
            partial_steps_range = str(min_step)
        else:
            partial_steps_range = str(min_step) + "-" + str(max_step)
        legend = "(" + str(len(unified_match)) + " partial reductions of " + \
                 partial_steps_range + " steps each)"
        metasteps  = [u.concat(m) + f + u.concat(p)
                      for m, f, p in unified_match]
        color_map  = {node: colors[(metastep % len(colors))]
                      for node, metastep in list(u.index_map(metasteps).items())}
        darker = set(u.concat([f + u.concat(m) for m, f, __ in unified_match]))
        contrast_colors(color_map, darker)
    else:
        sys.stderr.write("Error: unknown pattern type\n")
        sys.exit(-1)
    return (legend, color_map)

# Returns a color map over tagged nodes with different colors for each property
# (group or instance).
def format_tags(G, tag, f):
    tag_nodes = tag_nodes_map(G, tag, f)
    color_map = {}
    for p, nodes in list(tag_nodes.items()):
        color = colors[(p - 1) % len(colors)]
        color_map.update(dict(list(zip(list(nodes), itertools.repeat(color)))))
    return color_map

# Gives a string with the hexadecimal representation of a color triple.
def hex_color(rgb):
    (r, g, b) = rgb
    return "#" + "{:02x}".format(r) + "{:02x}".format(g) + "{:02x}".format(b)

# Adjusts a color according to a factor.
def adjust_color(rgb, factor):
    (r, g, b) = rgb
    return (adjust_color_component(r, factor),
            adjust_color_component(g, factor),
            adjust_color_component(b, factor))

# Adjusts a color component according to a factor.
def adjust_color_component(c, factor):
    return min(255, int(((c / float(255.0)) * (1.0 - factor)) * 255.0))

# Returns a labeled DDG where instruction IDs are normalized (transformed into a
# sequence of integer IDs) across the entire trace.
def normalize_instructions(G):
    (DDG, PB, PI, PT) = G
    rename = dict(list(zip(sorted(list(PI.keys()), key=cmp_to_key(instruction_name_compare)),
                      list(range(0, len(list(PI.keys())))))))
    PBn = {}
    for (block, _) in PB.items():
        PBn[block] = {}
        for (key, value) in PB[block].items():
            new_value = value
            if key == u.tk_instruction:
                new_value = rename[value]
            PBn[block][key] = new_value
    PIn = {}
    for (key, value) in PI.items():
        PIn[rename[key]] = value
    return (DDG, PBn, PIn, PT)

# Returns a labeled DDG where block properties that belong to their instructions
# are lifted to these (for region instructions).
def lift_instruction_properties(G):
    (DDG, PB, PI, PT) = G
    PBl = copy.deepcopy(PB)
    PIl = copy.deepcopy(PI)
    for b in list(PBl.keys()):
        for p in [u.tk_impure, u.tk_noncommutative]:
            if PBl[b].get(p) == u.tk_true:
                del PBl[b][p]
                u.properties(b, PBl, PIl)[p] = u.tk_true
    return (DDG, PBl, PIl, PT)

# Returns a labeled DDG where tag IDs are normalized (transformed into a
# sequence of integer IDs) and all instances within each tag are normalized
# (transformed into a sequence of consecutive integers).
def normalize_tags(G):
    (DDG, PB, PI, PT) = G
    tags = u.tag_set((DDG, PB, PI, PT))
    if all([isinstance(tag, int) or (isinstance(tag, str) and tag.isdigit())
            for tag in tags]):
        # Tags are already normalized, skip
        return (DDG, PB, PI, PT)
    tag_rename = dict(list(zip(sorted(tags), list(range(len(tags))))))
    for tag in tags:
        new_tag_name = tag_rename[tag]
        PT[new_tag_name] = {u.tk_alias : tag}
        instances = sorted(instance_nodes_map((DDG, PB, PI, PT), tag).keys())
        instance_rename = dict(list(zip(sorted(instances), list(range(len(instances))))))
        tag_blocks = 0
        for block, value in PB.items():
            new_tags = []
            for (old_name, (old_group, old_instance)) in \
                PB[block].get(u.tk_tags, []):
                if old_name == tag:
                    new_instance = instance_rename[old_instance]
                    new_tags += [(new_tag_name, (old_group, new_instance))]
                    tag_blocks += 1
                else:
                    new_tags += [(old_name, (old_group, old_instance))]
            if new_tags:
                PB[block][u.tk_tags] = new_tags
        PT[new_tag_name][u.tk_original_blocks] = tag_blocks
    return (DDG, PB, PI, PT)

# Prints all different tags in the trace, one per line.
def print_tags(G):
    out = sio.StringIO()
    for tag in u.tag_set(G):
        print(tag, file=out)
    tags = out.getvalue()
    out.close()
    return tags

# Prints all different tag aliases, one per line.
def print_tag_aliases(G):
    (DDG, PB, PI, PT) = G
    out = sio.StringIO()
    for tag in u.tag_set((DDG, PB, PI, PT)):
        print(PT[tag].get(u.tk_alias), file=out)
    aliases = out.getvalue()
    out.close()
    return aliases

# Prints all groups in the given tag, one per line.
def print_tag_groups(G, tag):
    out = sio.StringIO()
    for group in list(group_nodes_map(G, tag).keys()):
        print(group, file=out)
    groups = out.getvalue()
    out.close()
    return groups

# Prints the component IDs in the trace, one per line.
def print_components(G, min_nodes, top_components):
    out = sio.StringIO()
    (DDGf, PBf, PIf, PTf) = filter_middle(G)
    for c in \
      range(len(weakly_connected_components(DDGf, min_nodes, top_components))):
        print(c, file=out)
    components = out.getvalue()
    out.close()
    return components

# Prints the size of the trace in number of nodes.
def print_size(G):
    (DDG, PB, PI, PT) = G
    out = sio.StringIO()
    print(len(DDG.nodes()), file=out)
    size = out.getvalue()
    out.close()
    return size

# Returns a labeled DDG where non-region, effectful blocks only connected to the
# source are removed.
def clean(G):
    (DDG, PB, PI, PT) = G
    DDGr = DDG.copy()
    PBr = copy.deepcopy(PB)
    for effectful in [b for b in DDG.nodes() if is_effectful(b, PB, PI) and \
                      not (u.properties(b, PB, PI).get(u.tk_region) == u.tk_true)]:
        if DDGr.degree(effectful) == 0 or \
           (DDGr.degree(effectful) == 1 and DDGr.has_edge(0, effectful)):
            DDGr.remove_node(effectful)
            PBr.pop(effectful, None)
    PIr = clean_instruction_properties(PI, PBr)
    return (DDGr, PBr, PIr, PT)

# Returns a labeled DDG where blocks whose name matches the given predicate are
# removed.
def remove_instructions(G, p):
    (DDG, PB, PI, PT) = G
    DDGr = DDG.copy()
    PBr = copy.deepcopy(PB)
    for block in [b for b in DDG.nodes() if \
                  p(u.properties(b, PB, PI).get(u.tk_name))]:
        for pred in DDGr.predecessors(block):
            for succ in DDGr.successors(block):
                DDGr.add_edge(pred, succ)
        DDGr.remove_node(block)
        PBr.pop(block, None)
    PIr = clean_instruction_properties(PI, PBr)
    return (DDGr, PBr, PIr, PT)

# Returns a labeled DDG where only data-flow leading to effectful and region
# blocks are preserved. This gets rid of data-flow related to address
# computations and data-structure traversals.
def prune(G):
    (DDG, PB, PI, PT) = G
    DDGr = DDG.reverse(copy=True)
    reachable = set()
    for effectful in [b for b in DDGr.nodes() if \
                      (is_effectful(b, PB, PI) and not is_dispensable(b, PB, PI)) \
                      or u.properties(b, PB, PI).get(u.tk_region) == u.tk_true]:
        reachable.add(effectful)
        reachable |= set(nx.descendants(DDGr, effectful))
    DDGrp = DDGr.subgraph(reachable)
    DDGp = DDGrp.reverse(copy=True)
    PBp = {k:PB[k] for k in PB if k in reachable}
    PIp = clean_instruction_properties(PI, PBp)
    return (DDGp, PBp, PIp, PT)

# Record original nodes for tracing back from future transformed traces.
def record_original_nodes(G):
    (DDG, PB, PI, PT) = G
    for b in DDG.nodes():
        PB[b][u.tk_original] = [b]
    return

# Filters nodes in the labeled DDG that satisfy p.
def filter_by(G, p, add_context = True):
    (DDG, PB, PI, PT) = G
    DDGf = DDG.copy()
    PBf = copy.deepcopy(PB)
    remove_nodes = [b for b in DDG.nodes() if not p(b)]
    for block in remove_nodes:
        DDGf.remove_node(block)
        PBf.pop(block, None)
    PIf = clean_instruction_properties(PI, PBf)
    if not add_context:
        return (DDGf, PBf, PIf, PT)
    # Add arcs into and from the filtered nodes, for context.
    entries = set()
    exits = set()
    for (source, target) in DDG.edges():
        keep_source = p(source)
        keep_target = p(target)
        if not keep_source and keep_target:
            entries.add(target)
        elif keep_source and not keep_target:
            exits.add(source)
    if entries:
        source = add_region_instruction("source", PIf)
        source_block = max(PBf.keys()) + 1
        PBf[source_block] = {u.tk_instruction : source}
        for ent in entries:
            DDGf.add_edge(source_block, ent)
    if exits:
        sink = add_region_instruction("sink", PIf)
        sink_block = max(PBf.keys()) + 1
        PBf[sink_block] = {u.tk_instruction : sink}
        for ex in exits:
            DDGf.add_edge(ex, sink_block)
    return (DDGf, PBf, PIf, PT)

# Filters nodes in the labeled DDG by location according to a regexp.
def filter_location(G, pattern):
    (DDG, PB, PI, PT) = G
    has_loc = lambda b: \
              re.match(pattern, u.properties(b, PB, PI).get(u.tk_location, ""))
    return filter_by(G, has_loc)

# Filters nodes in the labeled DDG by name according to a regexp.
def filter_name(G, pattern):
    (DDG, PB, PI, PT) = G
    has_name = lambda b: \
               re.match(pattern, u.properties(b, PB, PI).get(u.tk_name, ""))
    return filter_by(G, has_name)

# Filters out nodes in the labeled DDG with the exact location and name as one
# of the instructions in a list.
def filter_out_location_and_name(G, instructions):
    (DDG, PB, PI, PT) = G
    not_has_loc_name = \
        lambda b: \
        (not u.is_source(b, PB, PI)) and \
        (not u.is_sink(b, PB, PI)) and \
        all([(loc, name) != (u.properties(b, PB, PI).get(u.tk_location, ""),
                             u.properties(b, PB, PI).get(u.tk_name, ""))
             for (loc, name) in instructions])
    return filter_by(G, not_has_loc_name)

# Filters tagged nodes in the labeled DDG.
def filter_tag(G, tag, group):
    (DDG, PB, PI, PT) = G
    is_tag_group = lambda b: is_preserved(b, tag, group, PB)
    return filter_by(G, is_tag_group)

# Whether the given block is to be preserved when filtering.
def is_preserved(block, tag, group, PB):
    tag_data = find_tag_data(tag, PB[block].get(u.tk_tags))
    return (tag_data != None) and ((group == None) or tag_data[0] == int(group))

# Filters out the source and sink nodes.
def filter_middle(G):
    (DDG, PB, PI, PT) = G
    is_middle = lambda b: \
                not (u.properties(b, PB, PI).get(u.tk_name, "") in
                     ["source", "sink"])
    return filter_by(G, is_middle, False)

# Filters nodes with the given component ID.
def filter_component(G, component, min_nodes, top_components):
    (DDG, PB, PI, PT) = G
    (DDGf, PBf, PIf, PTf) = filter_middle(G)
    c = weakly_connected_components(DDGf, min_nodes,
                                    top_components)[int(component)]
    is_component = lambda b: b in c
    (DDGc, PBc, PIc, PTc) = filter_by(G, is_component)
    return (DDGc, PBc, PIc, PTc)

# Filters nodes with the given ID.
def filter_blocks(G, blocks):
    return filter_by(G, lambda b: b in blocks)

# Computes top weakly connected components of cardinality greater or equal than
# the given one. Returns the components ordered in decreasing size.
def weakly_connected_components(DDG, min_nodes, top_components):
    filtered = [c for c in nx.weakly_connected_components(DDG)
                if not min_nodes or len(c) >= int(min_nodes)]
    ordered =  sorted(filtered, key=len, reverse=True)
    if top_components:
        return ordered[0:int(top_components)]
    else:
        return ordered

# Decomposes the given DDG into a DDG per tag and group within the tag.
def decompose_loops(G):
    tags = u.tag_set(G)
    LGS = []
    # For each loop (tag), produce a temporary DDG.
    for tag in tags:
        Gt = filter_tag(G, tag, None)
        Gt = remove_tags(Gt, tags - set([tag]))
        # For each loop run (group within a tag), generate a DDG.
        for group in list(group_nodes_map(Gt, tag).keys()):
            loop_id = "l" + str(tag) + "r" + str(group)
            Gtg = filter_tag(Gt, tag, group)
            Gtg = normalize(Gtg)
            LGS.append((Gtg, loop_id))
    return LGS

# Decomposes the given DDG into a DDG per associative instruction and connected
# component within it.
def decompose_associative_components(G, min_nodes, top_components):
    tags = u.tag_set(G)
    CGS = []
    # For each associative instruction.
    for instr_name in u.associative_names:
        Gi = filter_name(G, instr_name)
        Gi = remove_tags(Gi, tags)
        Gi = normalize(Gi)
        DDGi = filter_middle(Gi)[0]
        c = 0
        for component in \
            weakly_connected_components(DDGi, min_nodes, top_components):
            component_id = "i" + instr_name + "c" + str(c)
            Gic = filter_by(Gi, lambda b: b in component)
            Gic = normalize(Gic)
            CGS.append((Gic, component_id))
            c += 1
    return CGS

# Subtracts the sub-DDG SG2 from the sub-DDG w.r.t. the original DDG. The
# resulting DDG is not compacted, even if the original sub-DDGs might be.
def subtract(SG1, SG2, G):
    return apply_operation(lambda n1, n2 : n1 - n2, SG1, SG2, G)

# Composes the two given sub-DDGs w.r.t. to their original DDG. The resulting
# DDG is not compacted, even if the original sub-DDGs might be.
def compose(SG1, SG2, G):
    return apply_operation(lambda n1, n2 : n1 | n2, SG1, SG2, G)

# Gives a DDG (subset of G) where 'op' is applied to SG1 and SG2.
def apply_operation(op, SG1, SG2, G):
    blocks = op(u.original_blocks(SG1), u.original_blocks(SG2))
    G = filter_blocks(G, blocks)
    # Preserve the tags in SG1 & blocks and SG2 & blocks, for future compaction.
    # Note that this is not equivalent to fetching the tags in DDG & blocks
    # (loop decomposition leaves only the tag of each decomposed loop, and
    # associative component decomposition removes all traces).
    G = remove_tags(G, u.tag_set(G))
    def add_tags(G1, offset):
        (DDG, PB, _, PT) = G1
        tags = set()
        for b in DDG.nodes():
            original = PB[b].get(u.tk_original, [])
            if not (set(original) & blocks):
                continue
            offset_tags = set()
            for (tag_name, tag_data) in PB[b].get(u.tk_tags, []):
                tags.add((tag_name, tag_data))
                offset_tags.add((tag_name + offset, tag_data))
            if offset_tags:
                for ob in original:
                    G[1][ob][u.tk_tags] = list(offset_tags)
        for tag in tags:
            G[3][u.tag_name(tag) + offset] = PT[u.tag_name(tag)]
        return tags
    sg1_tags = add_tags(SG1, 0)
    offset = max(list(map(u.tag_name, sg1_tags)) or [0]) + 1
    add_tags(SG2, offset)
    return G

# Adds a new region instruction with the given name.
def add_region_instruction(name, PI):
    instruction = max(PI.keys()) + 1
    PI[instruction] = \
        {u.tk_impure : u.tk_true,
         u.tk_noncommutative : u.tk_true,
         u.tk_name : name,
         u.tk_region : u.tk_true}
    return instruction

# Removes the given tags from the labeled DDG.
def remove_tags(G, tags):
    (DDG, PB, PI, PT) = G
    PTc = {}
    for block, value in PB.items():
        old_tags = PB[block].get(u.tk_tags, [])
        new_tags = [(t, i) for (t, i) in old_tags if t not in tags]
        if old_tags:
            PB[block][u.tk_tags] = new_tags
            if not new_tags:
                del PB[block][u.tk_tags]
    for tag in u.tag_set((DDG, PB, PI, PT)) - tags:
        PTc[tag] = PT[tag]
    return (DDG, PB, PI, PTc)

# Collapse all nodes belonging to the same instance of the given tag into nodes.
def collapse_tags(G, tag):
    (DDG, PB, PI, PT) = G
    DDGc = DDG.copy()
    PBc = copy.deepcopy(PB)
    PIc = copy.deepcopy(PI)
    # Create single instruction corresponding to the tag.
    group_instruction = max(PIc.keys()) + 1
    PIc[group_instruction] = {u.tk_name : PT[tag].get(u.tk_alias, tag)}
    # Map from instances of the given tag to nodes.
    instance_nodes = instance_nodes_map((DDG, PB, PI, PT), tag)
    # Create a new node for each instance.
    for instance, nodes in list(instance_nodes.items()):
        group_block = max(DDGc.nodes()) + 1
        DDGc.add_node(group_block)
        # The list() conversion is needed since we may add new edges to DDGc.
        for (source, target) in list(DDGc.edges()):
            # Add incoming arcs.
            if (not source in nodes) and (target in nodes):
                DDGc.add_edge(source, group_block)
            # Add outgoing arcs.
            if (source in nodes) and (not target in nodes):
                DDGc.add_edge(group_block, target)
        PBc[group_block] = {u.tk_instruction : group_instruction}
        group_tags = \
        list(set.intersection(*[set(PB[b].get(u.tk_tags, [])) for b in nodes]))
        if group_tags:
            PBc[group_block][u.tk_tags] = group_tags
        # Collect all original nodes.
        group_original = \
        list(set.union(*[set(PBc[b].get(u.tk_original, [])) for b in nodes]))
        if group_original:
            PBc[group_block][u.tk_original] = group_original
    collapsed_nodes = set()
    for nodes in list(instance_nodes.values()):
        collapsed_nodes |= nodes
    # If any of the collapsed instructions is impure and/or non-commutative, tag
    # as such.
    for block in collapsed_nodes:
        impure = u.properties(block, PB, PI).get(u.tk_impure)
        if impure:
            PIc[group_instruction][u.tk_impure] = impure
        non_commutative = u.properties(block, PB, PI).get(u.tk_noncommutative)
        if non_commutative:
            PIc[group_instruction][u.tk_noncommutative] = non_commutative
    # Add all children instructions of the collapsed instruction.
    children = set()
    for block in collapsed_nodes:
        children.add(PB[block].get(u.tk_instruction))
    PIc[group_instruction][u.tk_children] = list(map(int, children))
    # Mark the collapsed instruction as a region.
    PIc[group_instruction][u.tk_region] = u.tk_true
    # Remove all collapsed nodes.
    for nodes in list(instance_nodes.values()):
        for block in nodes:
            DDGc.remove_node(block)
            PBc.pop(block, None)
    PIs = clean_instruction_properties(PIc, PBc)
    return (DDGc, PBc, PIs, PT)

# Collapses all nodes of each instruction into a single node.
def fold(G):
    (DDG, PB, PI, PT) = G
    for i in list(PI.keys()):
        (DDG, PB, PI, PT) = \
          collapse_group_by((DDG, PB, PI, PT),
                            lambda b: PB[b].get(u.tk_instruction) == i,
                            PI[i])
    return (DDG, PB, PI, PT)

# Collapses all nodes that satisfy p into a single node.
def collapse_group_by(G, p, instruction_properties):
    (DDG, PB, PI, PT) = G
    DDGc = DDG.copy()
    PBc = copy.deepcopy(PB)
    PIc = copy.deepcopy(PI)
    # Collect group nodes.
    nodes = [b for b in DDG.nodes() if p(b)]
    # Create single instruction for the group.
    group_instruction = max(PIc.keys()) + 1
    # Pick the name from an arbitrary node.
    PIc[group_instruction] = instruction_properties
    group_block = max(DDGc.nodes()) + 1
    DDGc.add_node(group_block)
    for (source, target) in DDGc.edges():
        # Add incoming arcs.
        if (not source in nodes) and (target in nodes):
            DDGc.add_edge(source, group_block)
        # Add outgoing arcs.
        if (source in nodes) and (not target in nodes):
            DDGc.add_edge(group_block, target)
        # Add self arcs.
        if (source in nodes) and (target in nodes):
            DDGc.add_edge(group_block, group_block)
    PBc[group_block] = {u.tk_instruction : group_instruction}
    # If any of the collapsed instructions is impure, mark as impure.
    for block in nodes:
        impure = u.properties(block, PB, PI).get(u.tk_impure)
        if impure:
            PIc[group_instruction][u.tk_impure] = impure
    # Add all children instructions of the collapsed instruction.
    children = set()
    for block in nodes:
        children.add(PB[block].get(u.tk_instruction))
    PIc[group_instruction][u.tk_children] = list(map(int, children))
    # Mark the collapsed instruction as a region.
    PIc[group_instruction][u.tk_region] = u.tk_true
    # Remove all collapsed nodes.
    for block in nodes:
        DDGc.remove_node(block)
        PBc.pop(block, None)
    PIs = clean_instruction_properties(PIc, PBc)
    return (DDGc, PBc, PIs, PT)

# Remove instances of the given tag that only contain compare and branch nodes,
# where the compare has the branch as its only successor.
def untag_header_instances(G, tag):
    (DDG, PB, PI, PT) = G
    instance_nodes = instance_nodes_map(G, tag)
    for (instance, nodes) in instance_nodes.items():
        node_list = list(nodes)
        if len(node_list) != 2:
            continue
        if node_list[0] in DDG.predecessors(node_list[1]):
            p = node_list[0]
            s = node_list[1]
        elif node_list[1] in DDG.predecessors(node_list[0]):
            p = node_list[1]
            s = node_list[0]
        else:
            continue
        if u.properties(p, PB, PI).get(u.tk_name) != "icmp":
            continue
        if u.properties(s, PB, PI).get(u.tk_name) != "br":
            continue
        succ = list(DDG.successors(p))
        if succ != [s]:
            continue
        # If all the above conditions hold, untag the two nodes.
        for b in [p, s]:
            PB[b][u.tk_tags] = [(t, (g, i)) for (t, (g, i)) in PB[b][u.tk_tags]
                                if t != tag]
            if not PB[b][u.tk_tags]:
                PB[b].pop(u.tk_tags, None)
    return (DDG, PB, PI, PT)

# Remove the given tag from nodes identified as induction dataflow.
def untag_induction_nodes(G, tag):
    (DDG, PB, PI, PT) = G
    instance_nodes = instance_nodes_map(G, tag)
    tag_nodes = set().union(*list(map(set, list(instance_nodes.values()))))
    tag_inst_to_nodes = dict()
    for b in tag_nodes:
        inst = PB[b].get(u.tk_instruction)
        if not inst in tag_inst_to_nodes:
            tag_inst_to_nodes[inst] = []
        tag_inst_to_nodes[inst].append(b)
    for (inst, blocks) in tag_inst_to_nodes.items():
        # Assert that all nodes (blocks) belong to the same tag.
        for b in blocks:
            assert tag in list(map(u.tag_name, PB[b].get(u.tk_tags)))
        # Test if every node has a different tag instance.
        instances = set()
        node_instance = dict()
        for b in blocks:
            instance = next(u.tag_instance(t) for t in PB[b].get(u.tk_tags)
                            if u.tag_name(t) == tag)
            instances.add(instance)
            node_instance[b] = instance
        if len(instances) != len(blocks):
            continue
        # Test if, for all nodes, all input nodes come from outside the tag.
        all_outside = True
        for b in blocks:
            for p in DDG.predecessors(b):
                if p in blocks or not all_outside:
                    continue
                if PB[p].get(u.tk_tags) and \
                   tag in list(map(u.tag_name, PB[p].get(u.tk_tags))):
                    all_outside = False
                    continue
        if not all_outside:
            continue
        # Test if all nodes have a successor in another instance of the tag.
        all_other_instance = True
        for b in blocks:
            if not DDG.successors(b):
                all_other_instance = False
                break
            some_other_instance = False
            for s in DDG.successors(b):
                for (t, i) in PB[s].get(u.tk_tags, []):
                    if t == tag and i != node_instance[b]:
                        some_other_instance = True
                        break
                if not some_other_instance:
                    all_other_instance = False
                    break;
        if not all_other_instance:
            continue
        # If all the above conditions hold, untag all nodes of the instruction.
        for b in blocks:
            PB[b][u.tk_tags] = [(t, i) for (t, i) in PB[b][u.tk_tags]
                                if t != tag]
            if not PB[b][u.tk_tags]:
                PB[b].pop(u.tk_tags, None)
    return (DDG, PB, PI, PT)

# Normalizes ID numbers using consecutive integers starting from zero.
def normalize(G):
    (DDG, PB, PI, PT) = G
    DDGn = nx.DiGraph()
    PBn = {}
    PIn = {}
    PTn = {}
    block_rename = dict(list(zip(sorted(DDG.nodes()), list(range(DDG.number_of_nodes())))))
    inst_rename = dict(list(zip(sorted(PI.keys()), list(range(len(list(PI.keys())))))))
    tags = u.tag_set(G)
    tag_rename = dict(list(zip(sorted(tags), list(range(len(tags))))))
    for node in DDG.nodes():
        DDGn.add_node(block_rename[node])
    for (source, target) in DDG.edges():
        DDGn.add_edge(block_rename[source], block_rename[target])
    for block in DDG.nodes():
        value = PB[block]
        if u.tk_instruction in value:
            value[u.tk_instruction] = inst_rename[value[u.tk_instruction]]
        PBn[block_rename[block]] = value
    for inst in PI:
        PIn[inst_rename[inst]] = PI[inst]
    for inst in PIn:
        for (key, value) in PIn[inst].items():
            new_value = value
            if key == u.tk_children:
                new_value = sorted([inst_rename[v] for v in value])
            PIn[inst][key] = new_value
    for tag in tags:
        PTn[tag_rename[tag]] = PT[tag]
    for block, value in PBn.items():
        old_tags = PBn[block].get(u.tk_tags, [])
        new_tags = [(tag_rename[t], i) for (t, i) in old_tags]
        if old_tags:
            PBn[block][u.tk_tags] = new_tags
    # TODO: normalize tag instances here as well?
    return (DDGn, PBn, PIn, PTn)

# Returns a string with the labeled DDG in GraphViz format.
def print_graphviz(G, print_ids, simplify_loc, print_basefile_loc, print_source,
                   legend=None, color_map=None):
    (DDG, PB, PI, PT) = G
    out = sio.StringIO()
    print("digraph DataFlow {", file=out)
    for block in sorted(DDG.nodes()):
        if u.is_source(block, PB, PI) and not print_source:
            continue
        out.write(str(block) + " [")
        attributes = []
        region = u.properties(block, PB, PI).get(u.tk_region) == u.tk_true
        styles = []
        for key, value in u.properties(block, PB, PI).items():
            if key == u.tk_name:
                label = u.demangle(value, demangled_cache)
                loc_value = u.properties(block, PB, PI).get(u.tk_location, "")
                if simplify_loc and loc_value:
                    [loc_file, loc_line, loc_col] = loc_value.split(u.tk_loc_sep)
                    if print_basefile_loc:
                        loc_value = loc_file.split("/")[-1] + u.tk_loc_sep + loc_line
                    else:
                        loc_value = loc_line
                if print_ids:
                    label += "-" + str(block)
                if loc_value:
                    label += " (" + loc_value + ")"
                label = html.escape(label)
                if region:
                    label = "<B>" + label + "</B>"
                attributes += ["label=<" + label + ">"]
            if key == u.tk_iterator and value == u.tk_true:
                attributes += ["color=gray", "fontcolor=gray"]
            if key == u.tk_region and value == u.tk_true:
                styles += ["bold"]
            if key == u.tk_impure and value == u.tk_true:
                if u.properties(block, PB, PI).get(u.tk_noncommutative, ""):
                    attributes += ["shape=signature"]
                else:
                    attributes += ["shape=box"]
            if key == u.tk_control and value == u.tk_true:
                attributes += ["shape=diamond"]
        if color_map and block in color_map:
            styles += ["filled"]
            attributes += ["fillcolor=\"" + hex_color(color_map[block]) + "\""]
        attributes += ["style=\"" + ",".join(styles) + "\""]
        out.write(", ".join(attributes))
        print("];", file=out)
    for (source, target) in sorted(DDG.edges()):
        if u.is_source(source, PB, PI) and not print_source:
            continue
        out.write(str(source) + "->" + str(target) + " [");
        attributes = []
        if PB[source].get(u.tk_iterator) == u.tk_true or \
           PB[target].get(u.tk_iterator) == u.tk_true:
            attributes += ["color=gray"]
        out.write(", ".join(attributes))
        print("];", file=out)
    print("concentrate=true;", file=out)
    if legend:
        print("fontsize=16;", file=out)
        print("labelloc=\"b\";", file=out)
        print("label=\"\n" + legend + "\";", file=out)
    print("}", file=out)
    gv = out.getvalue()
    out.close()
    return gv

# Prints the labeled DDG in the same plain format as the input.
def print_plain(G):
    (DDG, PB, PI, PT) = G
    out = sio.StringIO()
    for instr in sorted(PI):
        for key, value in sorted(iter(PI[instr].items()),
                                 key=cmp_to_key(instruction_property_compare)):
            if key == u.tk_children:
               value = u.tk_list_sep.join(map(str, value))
            print(u.tk_ip, instr, key, value, file=out)
    for tag in sorted(PT):
        for key, value in PT[tag].items():
            print(u.tk_tp, tag, key, value, file=out)
    for block in sorted(DDG.nodes()):
       for key, value in PB[block].items():
           if key == u.tk_tags:
               value = u.tk_list_sep.join(map(tag_tuple_to_str, value))
           elif key == u.tk_original:
               value = u.tk_list_sep.join(map(str, value))
           print(u.tk_bp, block, key, value, file=out)
       for (source, _) in DDG.in_edges(block):
           print(u.tk_df, source, block, file=out)
    pl = out.getvalue()
    out.close()
    return pl

# Prints the labeled DDG as a MiniZinc data file.
def print_minizinc(G, match_regions_only):
    (DDG, PB, PI, PT) = G
    out = sio.StringIO()
    # Conserve only instructions that are referred directly by nodes (that is,
    # remove unreferenced instructions, typically children of regions).
    # TODO: sort instructions in PI such that unreferenced instructions appear
    # at the end.
    PIp = {}
    for block in DDG.nodes():
        inst = PB[block].get(u.tk_instruction)
        if inst != None:
            PIp[inst] = PI[inst]
    n = len(DDG.nodes());
    c = len(list(PIp.keys()));
    opr2blocks = {}
    for opr in sorted(list(set([v.get(u.tk_name) for v in list(PIp.values())]))):
        opr2blocks[opr] = [b for b in sorted(DDG.nodes())
                           if u.properties(b, PB, PIp).get(u.tk_name) == opr]
    o = len(opr2blocks)
    print("n", "=", str(n) + ";", file=out);
    print("c", "=", str(c) + ";", file=out);
    print("o", "=", str(o) + ";", file=out);
    # Candidate nodes are either pure or impure but commutative w.r.t. itself
    # (user-defined property).
    candidates = [b for b in DDG.nodes() if \
                  (not (u.properties(b, PB, PIp).get(u.tk_impure) == u.tk_true)) or
                  (u.properties(b, PB, PIp).get(u.tk_impure) == u.tk_true and
                   (not u.properties(b, PB, PIp).get(u.tk_noncommutative) == u.tk_true))]
    if match_regions_only:
        matchable = [b for b in candidates if \
                     u.properties(b, PB, PIp).get(u.tk_region) == u.tk_true]
    else:
        matchable = candidates
    print("matchable = {" + ", ".join(map(str, sorted(matchable))) + "};", file=out)
    print("arcs = array2d(0.." + str(len(DDG.edges()) - 1) + ", 0..1, [", file=out);
    for (source, target) in DDG.edges():
        print((str(source) + ","), (str(target) + ","), file=out)
    print("]);", file=out)
    print("static_classes = array1d(0.." + str(c - 1) + ", [", file=out);
    instr2blocks = {}
    for instr in list(PIp.keys()):
        instr_blocks = [b for b in sorted(DDG.nodes())
                        if PB[b].get(u.tk_instruction) == instr]
        instr2blocks[instr] = instr_blocks
        print("{" + ", ".join(map(str, instr_blocks)) + "},", file=out)
    print("]);", file=out)
    print("operation_classes = array1d(0.." + str(o - 1) + ", [", file=out);
    for opr in sorted(opr2blocks):
        print("{" + ", ".join(map(str, opr2blocks[opr])) + "},", file=out)
    print("]);", file=out)
    print("reachable = array1d(0.." + str(n - 1) + ", [", file=out);
    for b in sorted(DDG.nodes()):
        print("{" + ", ".join(map(str, nx.descendants(DDG, b))) + "},", file=out)
    print("]);", file=out)
    branches = [instr for instr in list(PIp.keys())
                if PIp[instr].get(u.tk_name, "") == "br"]
    print("branches = {" + ", ".join(map(str, branches)) + "};", file=out)
    i = 0
    associative = set()
    for instr in list(PIp.keys()):
        if u.is_associative(instr, PI):
            associative.add(i)
        i += 1
    print("associative = {" + ", ".join(map(str, sorted(associative))) + "};", file=out)
    max_count = []
    for instr in list(PIp.keys()):
        mc = len(instr2blocks[instr]) // 2
        # We only allow a single execution of each region per component.
        # FIXME: generalize: allow as many executions per component as the size
        # of the smallest connected component of the instr-induced subgraph.
        # See case with partial map in examples/streamcluster.c.
        if PIp[instr].get(u.tk_region) == u.tk_true:
            mc = min(mc, 1)
        max_count.append(mc)
    print("max_count = array1d(0.." + str(c - 1) + ", [" \
        + ", ".join(map(str, max_count)) + "]);", file=out)
    dzn = out.getvalue()
    out.close()
    return dzn

# Outputs the given DDG acording to command-line options.
def output(G, args):
    if args.output_format == arg_graphviz:
        select_tag = lambda t : list(u.tag_set(G))[0] if t == "all" else t
        if args.color_tag_groups:
            tag = select_tag(args.color_tag_groups)
            color_map = format_tags(G, get_tag_id(tag, G), lambda g__ : g__[0])
        elif args.color_tag_instances:
            tag = select_tag(args.color_tag_instances)
            color_map = format_tags(G, get_tag_id(tag, G), lambda __i : __i[1])
        else:
            color_map = None
        out = print_graphviz(G, args.print_ids, args.simplify_loc,
                             args.print_basefile_loc, args.print_source,
                             None, color_map)
    elif args.output_format == arg_plain:
        out = print_plain(G)
    elif args.output_format == arg_minizinc:
        out = print_minizinc(G, args.match_regions_only)
    if args.output_file:
        outfile = open(args.output_file ,"w+")
        outfile.write(out)
        outfile.close()
    else:
        print(out, end=' ')

# Loads and pre-processes a trace file.
def load_trace(trace_file):
    G = u.read_trace(trace_file)
    G = normalize_instructions(G)
    G = lift_instruction_properties(G)
    G = normalize_tags(G)
    return G

def main(args):

    parser = argparse.ArgumentParser(description='Process, simplify, and visualize traces and matches.')
    subparsers = parser.add_subparsers(help='sub-command help', dest="subparser")
    parser.add_argument('TRACE_FILE')
    parser.add_argument('-o', "--output-file", help='output file')
    parser.add_argument('--output-format', dest='output_format', action='store', type=str, choices=[arg_plain, arg_minizinc, arg_graphviz], default=arg_plain, help='format to output the processed trace')
    parser.add_argument('--simplify-loc', dest='simplify_loc', action='store_true', help='show a simplied form of the location')
    parser.add_argument('--print-basefile-loc', dest='print_basefile_loc', action='store_true', help='print the base file name in the simplified location')
    parser.add_argument('--print-source', dest='print_source', action='store_true', help='print source node and all its outgoing data flow')
    parser.add_argument('--no-print-source', dest='print_source', action='store_false')
    parser.set_defaults(print_source=True)
    parser.add_argument('--print-ids', dest='print_ids', action='store_true', help='print block identifiers in Graphviz format')
    parser.add_argument('--no-print-ids', dest='print_ids', action='store_false')
    parser.set_defaults(print_ids=False)
    parser.add_argument('--color-tag-groups', help='color the different groups of all tagged nodes')
    parser.add_argument('--color-tag-instances', help='color the different instances of all tagged nodes')
    parser.add_argument('--match-regions-only', dest='match_regions_only', action='store_true', help='define region nodes as the only matchable nodes in the MiniZinc format')
    parser.add_argument('--min-nodes', help='minimum amount of nodes required in a component', default=3)
    parser.add_argument('--top-components', help='filter only the largest number of given components', default=50)

    parser_query = subparsers.add_parser(arg_query, help='query about properties of the trace')
    parser_query.add_argument('--print-tags', dest='print_tags', action='store_true', help='print all different tags in the trace, one per line')
    parser_query.add_argument('--print-tag-aliases', dest='print_tag_aliases', action='store_true', help='print all different tag aliases in the trace, one per line')
    parser_query.add_argument('--print-tag-groups', help='print the groups of the given tag, one per line')
    parser_query.add_argument('--print-components', dest='print_components', action='store_true', help='print the component IDs in the trace, one per line')
    parser_query.add_argument('--print-size', dest='print_size', action='store_true', help='print the number of nodes in the trace')

    parser_simplify = subparsers.add_parser(arg_simplify, help='simplify the trace')
    parser_simplify.add_argument('--prune', dest='prune', action='store_true', help='remove data-flow that does not lead to impure or control blocks')
    parser_simplify.add_argument('--no-prune', dest='prune', action='store_false')
    parser_simplify.set_defaults(prune=True)
    parser_simplify.add_argument('--clean', dest='clean', action='store_true', help='remove isolated impure blocks')
    parser_simplify.add_argument('--no-clean', dest='clean', action='store_false')
    parser_simplify.set_defaults(clean=True)
    parser_simplify.add_argument('--remove-conversions', dest='remove_conversions', action='store_true', help='remove LLVM IR conversion operations')
    parser_simplify.add_argument('--no-remove-conversions', dest='remove_conversions', action='store_false')
    parser_simplify.set_defaults(remove_conversions=True)
    parser_simplify.add_argument('--remove-geps', dest='remove_geps', action='store_true', help='remove LLVM IR getelementptr operations')
    parser_simplify.add_argument('--no-remove-geps', dest='remove_geps', action='store_false')
    parser_simplify.set_defaults(remove_geps=True)
    parser_simplify.add_argument('--remove-aggregates', dest='remove_aggregates', action='store_true', help='remove LLVM IR aggregate operations')
    parser_simplify.add_argument('--no-remove-aggregates', dest='remove_aggregates', action='store_false')
    parser_simplify.set_defaults(remove_aggregates=True)
    parser_simplify.add_argument('--untag-header-instances', dest='untag_header_instances', action='store_true', help='remove tag instances that only contain compare and branch nodes')
    parser_simplify.add_argument('--no-untag-header-instances', dest='untag_header_instances', action='store_false')
    parser_simplify.set_defaults(untag_header_instances=True)
    parser_simplify.add_argument('--untag-inductions', dest='untag_inductions', action='store_true', help='remove tags from induction nodes')
    parser_simplify.set_defaults(untag_inductions=False)

    parser_record = subparsers.add_parser(arg_record, help='save node identifiers for backtracing.')

    parser_decompose = subparsers.add_parser(arg_decompose, help='decompose a trace into multiple subtraces')
    parser_decompose.add_argument('--loops',    dest='loops', action='store_true', help='extract loop subtraces')
    parser_decompose.add_argument('--no-loops', dest='loops', action='store_false')
    parser_decompose.set_defaults(loops=True)
    parser_decompose.add_argument('--associative-components',    dest='associative_components', action='store_true', help='extract associative component subtraces')
    parser_decompose.add_argument('--no-associative-components', dest='associative_components', action='store_false')
    parser_decompose.set_defaults(associative_components=True)
    parser_decompose.add_argument('--output-dir', help='output directory')

    parser_subtract = subparsers.add_parser(arg_subtract, help='subtract one subtrace from another')
    parser_subtract.add_argument('SUBTRACE_FILE_1')
    parser_subtract.add_argument('SUBTRACE_FILE_2')

    parser_compose = subparsers.add_parser(arg_compose, help='compose two subtraces into a single one')
    parser_compose.add_argument('SUBTRACE_FILE_1')
    parser_compose.add_argument('SUBTRACE_FILE_2')

    parser_transform = subparsers.add_parser(arg_transform, help='apply filter and collapse operations to the trace')
    parser_transform.add_argument('--filter-location', help='filters blocks by location according to a regexp')
    parser_transform.add_argument('--filter-name', help='filters blocks by name according to a regexp')
    parser_transform.add_argument('--filter-blocks', help='filters blocks specified in a file')
    parser_transform.add_argument('--filter-out-instructions', help='filters out blocks from instructions specified in a file')
    parser_transform.add_argument('--filter-tags', nargs="*", help='filters tagged blocks')
    parser_transform.add_argument('--filter-group', help='filters a specific group (used together with --filter-tags)')
    parser_transform.add_argument('--filter-component', help='filters blocks with the given component ID')
    parser_transform.add_argument('--clean-tags', dest='clean_tags', action='store_true', help='filter out non-specified tags (works only together with --filter-tags)')
    parser_transform.add_argument('--no-clean-tags', dest='clean_tags', action='store_false')
    parser_transform.set_defaults(clean_tags=True)
    parser_transform.add_argument('--collapse-tags', nargs="*", help='collapse all nodes belonging to the same instance of each of the given tags into single nodes')

    parser_print = subparsers.add_parser(arg_print, help='simply print the trace')

    parser_visualize = subparsers.add_parser(arg_visualize, help='visualize a set of matches on the trace')
    parser_visualize.add_argument('SZN_FILE', help='matches given by the MiniZinc finder')
    parser_visualize.add_argument('--clean-intermediate', dest='clean_intermediate', action='store_true', help='clean intermediate files')
    parser_visualize.add_argument('--no-clean-intermediate', dest='clean_intermediate', action='store_false')
    parser_visualize.add_argument('--discard-subsumed', dest='discard_subsumed', action='store_true', help='discard subsumed matches')
    parser_visualize.add_argument('--no-discard-subsumed', dest='discard_subsumed', action='store_false')
    parser_visualize.set_defaults(clean_intermediate=True)
    parser_visualize.set_defaults(discard_subsumed=True)

    parser_fold = subparsers.add_parser(arg_fold, help='fold the trace')

    args = parser.parse_args(args)

    G = load_trace(args.TRACE_FILE)

    if args.subparser == arg_query:
        if args.print_tags:
            out = print_tags(G)
        elif args.print_tag_aliases:
            out = print_tag_aliases(G)
        elif args.print_tag_groups:
            out = print_tag_groups(G, get_tag_id(args.print_tag_groups, G))
        elif args.print_components:
            out = print_components(G, args.min_nodes, args.top_components)
        elif args.print_size:
            out = print_size(G)
        if args.output_file:
            outfile = open(args.output_file ,"w+")
            outfile.write(out)
            outfile.close()
        else:
            print(out, end=' ')
    elif args.subparser == arg_simplify:
        if args.clean:
            G = clean(G)
        if args.prune:
            G = prune(G)
        if args.remove_conversions:
            G = remove_instructions(G, is_conversion)
        if args.remove_geps:
            G = remove_instructions(G, is_gep)
        if args.remove_aggregates:
            G = remove_instructions(G, is_aggregate)
        if args.untag_header_instances:
            for tag in u.tag_set(G):
                G = untag_header_instances(G, (get_tag_id(tag, G)))
        if args.untag_inductions:
            for tag in u.tag_set(G):
                G = untag_induction_nodes(G, (get_tag_id(tag, G)))
        G = normalize(G)
        output(G, args)
    elif args.subparser == arg_record:
        record_original_nodes(G)
        G = normalize(G)
        output(G, args)
    elif args.subparser == arg_decompose:
        GS = []
        if args.loops:
            GS.extend(decompose_loops(G))
        if args.associative_components:
            GS.extend(decompose_associative_components(G, args.min_nodes,
                                                       args.top_components))
        input_dir    = os.path.dirname(args.TRACE_FILE)
        input_file   = os.path.basename(args.TRACE_FILE)
        input_prefix, input_ext = os.path.splitext(input_file)
        if args.output_dir:
            output_dir = args.output_dir
        else:
            output_dir = input_dir
        for (G, subtrace_id) in GS:
            output_file = input_prefix + "." + subtrace_id + input_ext
            args.output_file = os.path.join(output_dir, output_file)
            output(G, args)
    elif args.subparser == arg_subtract:
        SG1 = load_trace(args.SUBTRACE_FILE_1)
        SG2 = load_trace(args.SUBTRACE_FILE_2)
        SG = subtract(SG1, SG2, G)
        SG = normalize(SG)
        output(SG, args)
    elif args.subparser == arg_compose:
        SG1 = load_trace(args.SUBTRACE_FILE_1)
        SG2 = load_trace(args.SUBTRACE_FILE_2)
        CG = compose(SG1, SG2, G)
        CG = normalize(CG)
        output(CG, args)
    elif args.subparser == arg_transform:
        if args.filter_location:
            G = filter_location(G, args.filter_location)
        if args.filter_name:
            G = filter_name(G, args.filter_name)
        if args.filter_blocks:
            blocks = set([])
            with open(args.filter_blocks, "r") as blocks_file:
                for line in blocks_file:
                    blocks.add(int(line))
            G = filter_blocks(G, blocks)
            G = remove_tags(G, u.tag_set(G))
        if args.filter_out_instructions:
            instructions = []
            with open(args.filter_out_instructions, "r") as instructions_file:
                for line in instructions_file:
                    [location, name_end] = line.rsplit(u.tk_loc_sep, 1)
                    name = name_end.rstrip("\n\r")
                    instructions.append((location, name))
            G = filter_out_location_and_name(G, instructions)
        if args.filter_tags:
            for tag in args.filter_tags:
                G = filter_tag(G, (get_tag_id(tag, G)), args.filter_group)
            if args.clean_tags:
                rem_tags = u.tag_set(G) - \
                           set([get_tag_id(tag, G) for tag in args.filter_tags])
                G = remove_tags(G, rem_tags)
        if args.filter_component:
            G = filter_component(G, args.filter_component, args.min_nodes,
                                 args.top_components)
        if args.collapse_tags:
            for tag in (u.tag_set(G) if args.collapse_tags == ["all"]
                        else args.collapse_tags):
                G = collapse_tags(G, (get_tag_id(tag, G)))
        G = normalize(G)
        output(G, args)
    elif args.subparser == arg_fold:
        G = fold(G)
        output(G, args)
    elif args.subparser == arg_print:
        output(G, args)

    if args.subparser == arg_visualize:
        (pattern, S, _) = u.read_matches(args.SZN_FILE)
        i = 0
        pdffilenames = []
        gvfilenames = []
        rootfilename = os.path.splitext(args.SZN_FILE)[0]
        if args.discard_subsumed:
            S = u.discard_subsumed_matches(S)
        for match in S:
            (legend, color_map) = format_match(pattern, match)
            gv = print_graphviz(G, args.print_ids, args.simplify_loc,
                                args.print_basefile_loc, args.print_source,
                                legend, color_map)
            basefilename = rootfilename + ".match" + str(i)
            gvfilename = basefilename + ".gv"
            pdffilename = basefilename + ".pdf"
            gvfile = open(gvfilename ,"w+")
            gvfile.write(gv)
            gvfile.close()
            gvfilenames.append(gvfilename)
            try:
                process = subprocess.Popen(["dot", "-Tpdf", gvfilename, "-o",
                                            pdffilename], stdout=subprocess.PIPE,
                                           text=True)
                process.wait()
            except OSError:
                sys.stderr.write("Error: could not find 'dot' executable\n")
                sys.exit(-1)
            pdffilenames.append(pdffilename)
            i += 1
        if len(S) == 1:
            dim = "1x1"
        elif len(S) == 2:
            dim = "2x1"
        else:
            dim = "2x2"
        try:
            process = subprocess.Popen(["pdfjam"] + pdffilenames +
                                       ["--nup", dim, "--landscape",
                                        "--outfile", args.output_file],
                                       stdout=subprocess.PIPE, text=True)
            process.wait()
        except OSError:
            sys.stderr.write("Error: could not find 'pdfjam' executable\n")
            sys.exit(-1)
        if args.clean_intermediate:
            for f in pdffilenames + gvfilenames:
                os.remove(f)

if __name__ == '__main__':
    main(sys.argv[1:])
