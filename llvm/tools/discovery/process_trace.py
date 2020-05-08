#!/usr/bin/python

import sys
import networkx as nx
from sets import Set
import argparse
import copy
import subprocess
import re
import StringIO as sio
import os
import itertools
import cgi

import trace_utils as u

arg_plain = "plain"
arg_minizinc = "minizinc"
arg_graphviz = "graphviz"

arg_query = "query"
arg_simplify = "simplify"
arg_decompose = "decompose"
arg_compose = "compose"
arg_transform = "transform"
arg_fold = "fold"
arg_print = "print"
arg_visualize = "visualize"
arg_report = "report"

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
                        u.tk_region : 7}

# Orders instruction properties according to input order.
def instruction_property_compare((k1, _1), (k2, _2)):
    return cmp(property_input_order[k1], property_input_order[k2])

# Orders instructions by name except for 'source' which goes first, for sanity.
def instruction_name_compare(n1, n2):
    if n1 == "source":
        return -1
    if n2 == "source":
        return 1
    else:
        return cmp(n1, n2)

# Gives the instruction's column.
def col(PI, inst):
    [_, _, loc_col] = PI[inst].get(u.tk_location, "").split(u.tk_loc_sep)
    return int(loc_col)

# Removes instruction properties without any corresponding blocks.
def clean_instruction_properties(PI, PB):
    PIc = {}
    for inst in Set([value[u.tk_instruction]
                     for key, value in PB.iteritems()
                     if u.tk_instruction in value]):
        PIc[inst] = PI[inst]
    for inst, ips in PI.items():
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
def tag_tuple_to_str((t, (g, i))):
    # t can be a string or an int (if the tag has been normalized).
    return str(t) + u.tk_tag_sep + str(g) + u.tk_tag_sep + str(i)

# Gives the numeric tag id of the given tag string (which can also be an alias).
def get_tag_id(tag, (_, __, ___, PT)):
    if tag in PT:
        # The tag is already an existent numeric tag id.
        return tag
    if tag.isdigit() and int(tag) in PT:
        return int(tag)
    else:
        for key, value in PT.iteritems():
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
def tag_nodes_map((DDG, PB, _, __), tag, f):
    tag_nodes = {}
    for block in [b for b in DDG.nodes()]:
        if is_tagged_with(tag, PB[block].get(u.tk_tags)):
            # p is either a tag group or a tag instance
            p = f(find_tag_data(tag, PB[block].get(u.tk_tags)))
            if not p in tag_nodes:
                tag_nodes[p] = Set()
            tag_nodes[p].add(block)
    return tag_nodes

# Returns a map from groups of the given tag to nodes.
def group_nodes_map(G, tag):
    return tag_nodes_map(G, tag, lambda (g, i) : g)

# Returns a map from instances of the given tag to nodes.
def instance_nodes_map(G, tag):
    return tag_nodes_map(G, tag, lambda (g, i) : i)

# Returns a legend and a color map to be applied to a match visualization.
def format_match(pattern, match):
    if pattern in u.pat_all_uni:
        if pattern in [u.pat_doall, u.pat_map, u.pat_mapfilter]:
            unit = "runs"
        elif pattern in [u.pat_reduction, u.pat_scan]:
            unit = "steps"
        legend = "(" + str(len(match)) + " " + unit + ")"
        color_map = {node: colors[(step % len(colors))]
                     for node, step in u.index_map(match).items()}
    elif pattern == u.pat_pipeline:
        (stages, runs) = match
        node_stage = u.index_map(stages)
        node_run = u.index_map(runs)
        legend = "(" + str(len(stages)) + " stages, " + str(len(runs)) + \
                 " runs)"
        color_map = dict()
        for k in node_stage.keys():
            run_completion = float(node_run[k]) / len(runs)
            factor = run_completion * 0.5
            original_color = colors[node_stage[k] % len(colors)]
            color_map[k] = adjust_color(original_color, factor)
    elif pattern == u.pat_twophasereduction:
        partial_steps = set([len(p) for _, p in match])
        (min_step, max_step) = (min(partial_steps), max(partial_steps))
        if min_step == max_step:
            partial_steps_range = str(min_step)
        else:
            partial_steps_range = str(min_step) + "-" + str(max_step)
        legend = "(" + str(len(match)) + " partial reductions of " + \
                 partial_steps_range + " steps each)"
        metasteps  = [f + u.concat(p) for f, p in match]
        color_map  = {node: colors[(metastep % len(colors))]
                      for node, metastep in u.index_map(metasteps).items()}
        # Make final step nodes darker and partial step nodes lighter.
        finalsteps = set(u.concat([f for f, _ in match]))
        for k in color_map.keys():
            if k in finalsteps:
                factor = 0.2
            else:
                factor = -0.05
            color_map[k] = adjust_color(color_map[k], factor)
    else:
        sys.stderr.write("Error: unknown pattern type\n")
        sys.exit(-1)
    return (legend, color_map)

# Returns a color map over tagged nodes with different colors for each property
# (group or instance).
def format_tags(G, tag, f):
    tag_nodes = tag_nodes_map(G, tag, f)
    color_map = {}
    for p, nodes in tag_nodes.items():
        color = colors[(p - 1) % len(colors)]
        color_map.update(dict(zip(list(nodes), itertools.repeat(color))))
    return color_map

# Gives a string with the hexadecimal representation of a color triple.
def hex_color((r, g, b)):
    return "#" + "{:02x}".format(r) + "{:02x}".format(g) + "{:02x}".format(b)

# Adjusts a color according to a factor.
def adjust_color((r, g, b), factor):
    return (adjust_color_component(r, factor),
            adjust_color_component(g, factor),
            adjust_color_component(b, factor))

# Adjusts a color component according to a factor.
def adjust_color_component(c, factor):
    return min(255, int(((c / float(255.0)) * (1.0 - factor)) * 255.0))

# Returns a labeled DDG where instruction IDs are normalized (transformed into a
# sequence of integer IDs) across the entire trace.
def normalize_instructions((DDG, PB, PI, PT)):
    rename = dict(zip(sorted(PI.keys(), cmp=instruction_name_compare),
                      range(0, len(PI.keys()))))
    PBn = {}
    for (block, _) in PB.iteritems():
        PBn[block] = {}
        for (key, value) in PB[block].iteritems():
            new_value = value
            if key == u.tk_instruction:
                new_value = rename[value]
            PBn[block][key] = new_value
    PIn = {}
    for (key, value) in PI.iteritems():
        PIn[rename[key]] = value
    return (DDG, PBn, PIn, PT)

# Returns a labeled DDG where block properties that belong to their instructions
# are lifted to these (for region instructions).
def lift_instruction_properties((DDG, PB, PI, PT)):
    PBl = copy.deepcopy(PB)
    PIl = copy.deepcopy(PI)
    for b in PBl.keys():
        for p in [u.tk_impure, u.tk_noncommutative]:
            if PBl[b].get(p) == u.tk_true:
                del PBl[b][p]
                u.properties(b, PBl, PIl)[p] = u.tk_true
    return (DDG, PBl, PIl, PT)

# Returns a labeled DDG where tag IDs are normalized (transformed into a
# sequence of integer IDs) and all instances within each tag are normalized
# (transformed into a sequence of consecutive integers).
def normalize_tags((DDG, PB, PI, PT)):
    tags = u.tag_set((DDG, PB, PI, PT))
    if all([isinstance(tag, int) or (isinstance(tag, str) and tag.isdigit())
            for tag in tags]):
        # Tags are already normalized, skip
        return (DDG, PB, PI, PT)
    tag_rename = dict(zip(sorted(tags), range(len(tags))))
    for tag in tags:
        new_tag_name = tag_rename[tag]
        PT[new_tag_name] = {u.tk_alias : tag}
        instances = sorted(instance_nodes_map((DDG, PB, PI, PT), tag).keys())
        instance_rename = dict(zip(sorted(instances), range(len(instances))))
        tag_blocks = 0
        for block, value in PB.iteritems():
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
        print >>out, tag
    tags = out.getvalue()
    out.close()
    return tags

# Prints all different tag aliases, one per line.
def print_tag_aliases((DDG, PB, PI, PT)):
    out = sio.StringIO()
    for tag in u.tag_set((DDG, PB, PI, PT)):
        print >>out, PT[tag].get(u.tk_alias)
    aliases = out.getvalue()
    out.close()
    return aliases

# Prints all groups in the given tag, one per line.
def print_tag_groups(G, tag):
    out = sio.StringIO()
    for group in group_nodes_map(G, tag).keys():
        print >>out, group
    groups = out.getvalue()
    out.close()
    return groups

# Prints the component IDs in the trace, one per line.
def print_components(G, min_nodes, top_components):
    out = sio.StringIO()
    (DDGf, PBf, PIf, PTf) = filter_middle(G)
    for c in \
      range(len(weakly_connected_components(DDGf, min_nodes, top_components))):
        print >>out, c
    components = out.getvalue()
    out.close()
    return components

# Prints the size of the trace in number of nodes.
def print_size((DDG, PB, PI, PT)):
    out = sio.StringIO()
    print >>out, len(DDG.nodes())
    size = out.getvalue()
    out.close()
    return size

# Returns a labeled DDG where non-region, effectful blocks only connected to the
# source are removed.
def clean((DDG, PB, PI, PT)):
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
def remove_instructions((DDG, PB, PI, PT), p):
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
def prune((DDG, PB, PI, PT)):
    DDGr = DDG.reverse(copy=True)
    reachable = Set()
    for effectful in [b for b in DDGr.nodes() if \
                      (is_effectful(b, PB, PI) and not is_dispensable(b, PB, PI)) \
                      or u.properties(b, PB, PI).get(u.tk_region) == u.tk_true]:
        reachable.add(effectful)
        reachable |= Set(nx.descendants(DDGr, effectful))
    DDGrp = DDGr.subgraph(reachable)
    DDGp = DDGrp.reverse(copy=True)
    PBp = {k:PB[k] for k in PB if k in reachable}
    PIp = clean_instruction_properties(PI, PBp)
    return (DDGp, PBp, PIp, PT)

# Filters nodes in the labeled DDG that satisfy p.
def filter_by((DDG, PB, PI, PT), p, add_context = True):
    DDGf = DDG.copy()
    PBf = copy.deepcopy(PB)
    remove_nodes = [b for b in DDG.nodes() if not p(b)]
    for block in remove_nodes:
        DDGf.remove_node(block)
        PBf.pop(block, None)
    PIf = clean_instruction_properties(PI, PBf)
    for b in DDGf.nodes():
        PBf[b][u.tk_original] = [b]
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
def filter_location((DDG, PB, PI, PT), pattern):
    has_loc = lambda b: \
              re.match(pattern, u.properties(b, PB, PI).get(u.tk_location, ""))
    return filter_by((DDG, PB, PI, PT), has_loc)

# Filters nodes in the labeled DDG by name according to a regexp.
def filter_name((DDG, PB, PI, PT), pattern):
    has_name = lambda b: \
               re.match(pattern, u.properties(b, PB, PI).get(u.tk_name, ""))
    return filter_by((DDG, PB, PI, PT), has_name)

# Filters out nodes in the labeled DDG with the exact location and name as one
# of the instructions in a list.
def filter_out_location_and_name((DDG, PB, PI, PT), instructions):
    not_has_loc_name = \
        lambda b: \
        (not u.is_source(b, PB, PI)) and \
        (not u.is_sink(b, PB, PI)) and \
        all([(loc, name) != (u.properties(b, PB, PI).get(u.tk_location, ""),
                             u.properties(b, PB, PI).get(u.tk_name, ""))
             for (loc, name) in instructions])
    return filter_by((DDG, PB, PI, PT), not_has_loc_name)

# Filters tagged nodes in the labeled DDG.
def filter_tag((DDG, PB, PI, PT), tag, group):
    is_tag_group = lambda b: is_preserved(b, tag, group, PB)
    return filter_by((DDG, PB, PI, PT), is_tag_group)

# Whether the given block is to be preserved when filtering.
def is_preserved(block, tag, group, PB):
    tag_data = find_tag_data(tag, PB[block].get(u.tk_tags))
    return (tag_data != None) and ((group == None) or tag_data[0] == int(group))

# Filters out the source and sink nodes.
def filter_middle((DDG, PB, PI, PT)):
    is_middle = lambda b: \
                not (u.properties(b, PB, PI).get(u.tk_name, "") in
                     ["source", "sink"])
    return filter_by((DDG, PB, PI, PT), is_middle, False)

# Filters nodes with the given component ID.
def filter_component((DDG, PB, PI, PT), component, min_nodes, top_components):
    (DDGf, PBf, PIf, PTf) = filter_middle((DDG, PB, PI, PT))
    c = weakly_connected_components(DDGf, min_nodes,
                                    top_components)[int(component)]
    is_component = lambda b: b in c
    (DDGc, PBc, PIc, PTc) = filter_by((DDG, PB, PI, PT), is_component)
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
def decompose_loops(G, clean_tags):
    tags = u.tag_set(G)
    LGS = []
    # For each loop (tag), produce a temporary DDG.
    for tag in tags:
        Gt = filter_tag(G, tag, None)
        if clean_tags:
            Gt = remove_tags(Gt, tags - set([tag]))
        # For each loop run (group within a tag), generate a DDG.
        for group in group_nodes_map(Gt, tag).keys():
            loop_id = str(tag) + "." + str(group)
            Gtg = filter_tag(Gt, tag, group)
            Gtg = normalize(Gtg)
            LGS.append((Gtg, loop_id))
    return LGS

# Decomposes the given DDG into a DDG per associative instruction and connected
# component within it.
def decompose_associative_components(G, min_nodes, top_components):
    # For each associative instruction.
    # FIXME: We added 'sub' to simulate algebraic transformation: a statement
    # "foo -= bar" can always be rewritten as "foo += (-bar)" and matched as a
    # map+reduction. See case in streamcluster.c:171 (seq) and
    # streamcluster.c:316 (pthread) within the StarBench suite. This should
    # rather be implemented as a transformation, e.g. within the simplification
    # step or perhaps even at instrumentation phase.
    CGS = []
    for instr_name in \
        ["add", "fadd", "mul", "fmul", "and", "or", "xor", "sub", "fsub"]:
        Gi = filter_name(G, instr_name)
        Gi = normalize(Gi)
        DDGi = filter_middle(Gi)[0]
        c = 0
        for component in \
            weakly_connected_components(DDGi, min_nodes, top_components):
            component_id = instr_name + "." + str(c)
            Gic = filter_by(Gi, lambda b: b in component)
            Gic = normalize(Gic)
            CGS.append((Gic, component_id))
            c += 1
    return CGS

# Composes the two given sub-DDGs w.r.t. to their original DDG. The resulting
# composition is not compacted, even if the original sub-DDGs might be.
def compose(SG1, SG2, G):
    def original_blocks((DDG, PB, _, __)):
        return set.union(*[set(PB[b].get(u.tk_original, []))
                           for b in DDG.nodes()])
    blocks = set.union(*(map(original_blocks, [SG1, SG2])))
    G = filter_blocks(G, blocks)
    # TODO: preserve only the tags present in SG1 and SG2 (for compaction).
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
def remove_tags((DDG, PB, PI, PT), tags):
    PTc = {}
    for block, value in PB.iteritems():
        old_tags = PB[block].get(u.tk_tags, [])
        new_tags = [(t, i) for (t, i) in old_tags if t not in tags]
        if old_tags:
            PB[block][u.tk_tags] = new_tags
    for tag in u.tag_set((DDG, PB, PI, PT)) - tags:
        PTc[tag] = PT[tag]
    return (DDG, PB, PI, PTc)

# Collapse all nodes belonging to the same instance of the given tag into nodes.
def collapse_tags((DDG, PB, PI, PT), tag):
    DDGc = DDG.copy()
    PBc = copy.deepcopy(PB)
    PIc = copy.deepcopy(PI)
    # Create single instruction corresponding to the tag.
    group_instruction = max(PIc.keys()) + 1
    PIc[group_instruction] = {u.tk_name : PT[tag].get(u.tk_alias, tag)}
    # Map from instances of the given tag to nodes.
    instance_nodes = instance_nodes_map((DDG, PB, PI, PT), tag)
    # Create a new node for each instance.
    for instance, nodes in instance_nodes.items():
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
        PBc[group_block][u.tk_original] = group_original
    collapsed_nodes = Set()
    for nodes in instance_nodes.values():
        collapsed_nodes |= nodes
    # If any of the collapsed instructions is impure, tag as impure.
    for block in collapsed_nodes:
        impure = u.properties(block, PB, PI).get(u.tk_impure)
        if impure:
            PIc[group_instruction][u.tk_impure] = impure
    # Add all children instructions of the collapsed instruction.
    children = Set()
    for block in collapsed_nodes:
        children.add(PB[block].get(u.tk_instruction))
    PIc[group_instruction][u.tk_children] = list(map(int, children))
    # Mark the collapsed instruction as a region.
    PIc[group_instruction][u.tk_region] = u.tk_true
    # Remove all collapsed nodes.
    for nodes in instance_nodes.values():
        for block in nodes:
            DDGc.remove_node(block)
            PBc.pop(block, None)
    PIs = clean_instruction_properties(PIc, PBc)
    return (DDGc, PBc, PIs, PT)

# Collapses all nodes of each instruction into a single node.
def fold((DDG, PB, PI, PT)):
    for i in PI.keys():
        (DDG, PB, PI, PT) = \
          collapse_group_by((DDG, PB, PI, PT),
                            lambda b: PB[b].get(u.tk_instruction) == i,
                            PI[i])
    return (DDG, PB, PI, PT)

# Collapses all nodes that satisfy p into a single node.
def collapse_group_by((DDG, PB, PI, PT), p, instruction_properties):
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
    children = Set()
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
def untag_header_instances((DDG, PB, PI, PT), tag):
    instance_nodes = instance_nodes_map((DDG, PB, PI, PT), tag)
    for (instance, nodes) in instance_nodes.iteritems():
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
def untag_induction_nodes((DDG, PB, PI, PT), tag):
    instance_nodes = instance_nodes_map((DDG, PB, PI, PT), tag)
    tag_nodes = set().union(*map(set, instance_nodes.values()))
    tag_inst_to_nodes = dict()
    for b in tag_nodes:
        inst = PB[b].get(u.tk_instruction)
        if not inst in tag_inst_to_nodes:
            tag_inst_to_nodes[inst] = []
        tag_inst_to_nodes[inst].append(b)
    for (inst, blocks) in tag_inst_to_nodes.iteritems():
        # Assert that all nodes (blocks) belong to the same tag.
        for b in blocks:
            assert tag in map(u.tag_name, PB[b].get(u.tk_tags))
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
                   tag in map(u.tag_name, PB[p].get(u.tk_tags)):
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
def normalize((DDG, PB, PI, PT)):
    DDGn = nx.DiGraph()
    PBn = {}
    PIn = {}
    PTn = {}
    block_rename = dict(zip(sorted(DDG.nodes()), range(DDG.number_of_nodes())))
    inst_rename = dict(zip(sorted(PI.keys()), range(len(PI.keys()))))
    tags = u.tag_set((DDG, PB, PI, PT))
    tag_rename = dict(zip(sorted(tags), range(len(tags))))
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
        for (key, value) in PIn[inst].iteritems():
            new_value = value
            if key == u.tk_children:
                new_value = sorted([inst_rename[v] for v in value])
            PIn[inst][key] = new_value
    for tag in tags:
        PTn[tag_rename[tag]] = PT[tag]
    for block, value in PBn.iteritems():
        old_tags = PBn[block].get(u.tk_tags, [])
        new_tags = [(tag_rename[t], i) for (t, i) in old_tags]
        if old_tags:
            PBn[block][u.tk_tags] = new_tags
    # TODO: normalize tag instances here as well?
    return (DDGn, PBn, PIn, PTn)

# Returns a string with the labeled DDG in GraphViz format.
def print_graphviz((DDG, PB, PI, PT), print_ids, simplify_loc, print_basefile_loc,
                   print_source, legend=None, color_map=None):
    out = sio.StringIO()
    print >>out, "digraph DataFlow {"
    for block in sorted(DDG.nodes()):
        if u.is_source(block, PB, PI) and not print_source:
            continue
        out.write(str(block) + " [")
        attributes = []
        region = u.properties(block, PB, PI).get(u.tk_region) == u.tk_true
        styles = []
        for key, value in u.properties(block, PB, PI).iteritems():
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
                label = cgi.escape(label)
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
        print >>out, "];"
    for (source, target) in sorted(DDG.edges()):
        if u.is_source(source, PB, PI) and not print_source:
            continue
        out.write(str(source) + "->" + str(target) + " [");
        attributes = []
        if PB[source].get(u.tk_iterator) == u.tk_true or \
           PB[target].get(u.tk_iterator) == u.tk_true:
            attributes += ["color=gray"]
        out.write(", ".join(attributes))
        print >>out, "];"
    print >>out, "concentrate=true;"
    if legend:
        print >>out, "fontsize=16;"
        print >>out, "labelloc=\"b\";"
        print >>out, "label=\"\n" + legend + "\";"
    print >>out, "}"
    gv = out.getvalue()
    out.close()
    return gv

# Prints the labeled DDG in the same plain format as the input.
def print_plain((DDG, PB, PI, PT)):
    out = sio.StringIO()
    for instr in sorted(PI):
        for key, value in sorted(PI[instr].iteritems(),
                                 cmp=instruction_property_compare):
            if key == u.tk_children:
               value = u.tk_list_sep.join(map(str, value))
            print >>out, u.tk_ip, instr, key, value
    for tag in sorted(PT):
        for key, value in PT[tag].iteritems():
            print >>out, u.tk_tp, tag, key, value
    for block in sorted(DDG.nodes()):
       for key, value in PB[block].iteritems():
           if key == u.tk_tags:
               value = u.tk_list_sep.join(map(tag_tuple_to_str, value))
           elif key == u.tk_original:
               value = u.tk_list_sep.join(map(str, value))
           print >>out, u.tk_bp, block, key, value
       for (source, _) in DDG.in_edges(block):
           print >>out, u.tk_df, source, block
    pl = out.getvalue()
    out.close()
    return pl

# Prints the labeled DDG as a MiniZinc data file.
def print_minizinc((DDG, PB, PI, PT), match_regions_only):
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
    c = len(PIp.keys());
    print >>out, "n", "=", str(n) + ";";
    print >>out, "c", "=", str(c) + ";";
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
    print >>out, "matchable = {" + ", ".join(map(str, sorted(matchable))) + "};"
    print >>out, "arcs = array2d(0.." + str(len(DDG.edges()) - 1) + ", 0..1, [";
    for (source, target) in DDG.edges():
        print >>out, (str(source) + ","), (str(target) + ",")
    print >>out, "]);"
    print >>out, "static_classes = array1d(0.." + str(c - 1) + ", [";
    instr2blocks = {}
    for instr in PIp.keys():
        instr_blocks = [b for b in sorted(DDG.nodes())
                        if PB[b].get(u.tk_instruction) == instr]
        instr2blocks[instr] = instr_blocks
        print >>out, "{" + ", ".join(map(str, instr_blocks)) + "},"
    print >>out, "]);"
    print >>out, "reachable = array1d(0.." + str(n - 1) + ", [";
    for b in sorted(DDG.nodes()):
        print >>out, "{" + ", ".join(map(str, nx.descendants(DDG, b))) + "},"
    print >>out, "]);"
    branches = [instr for instr in PIp.keys()
                if PIp[instr].get(u.tk_name, "") == "br"]
    print >>out, "branches = {" + ", ".join(map(str, branches)) + "};"
    max_count = []
    for instr in PIp.keys():
        mc = len(instr2blocks[instr]) / 2
        if match_regions_only:
            mc = min(mc, 1)
        max_count.append(mc)
    print >>out, "max_count = array1d(0.." + str(c - 1) + ", [" \
        + ", ".join(map(str, max_count)) + "]);"
    dzn = out.getvalue()
    out.close()
    return dzn

# Outputs the given DDG acording to command-line options.
def output(G, args):
    if args.output_format == arg_graphviz:
        select_tag = lambda t : list(u.tag_set(G))[0] if t == "all" else t
        if args.color_tag_groups:
            tag = select_tag(args.color_tag_groups)
            color_map = format_tags(G, get_tag_id(tag, G), lambda (g, _) : g)
        elif args.color_tag_instances:
            tag = select_tag(args.color_tag_instances)
            color_map = format_tags(G, get_tag_id(tag, G), lambda (_, i) : i)
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
        print out,

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

    parser_decompose = subparsers.add_parser(arg_decompose, help='decompose a trace into multiple subtraces')
    parser_decompose.add_argument('--loops',    dest='loops', action='store_true', help='extract loop subtraces')
    parser_decompose.add_argument('--no-loops', dest='loops', action='store_false')
    parser_decompose.set_defaults(loops=True)
    parser_decompose.add_argument('--associative-components',    dest='associative_components', action='store_true', help='extract associative component subtraces')
    parser_decompose.add_argument('--no-associative-components', dest='associative_components', action='store_false')
    parser_decompose.set_defaults(associative_components=True)
    parser_decompose.add_argument('--clean-tags',    dest='clean_tags', action='store_true', help='remove non-specified loop tags in loop subtraces')
    parser_decompose.add_argument('--no-clean-tags', dest='clean_tags', action='store_false')
    parser_decompose.set_defaults(clean_tags=True)

    parser_compose = subparsers.add_parser(arg_compose, help='compose two subtraces into a single one')
    parser_compose.add_argument('SUBTRACE_FILE_1')
    parser_compose.add_argument('SUBTRACE_FILE_2')

    parser_transform = subparsers.add_parser(arg_transform, help='apply filter and collapse operations to the trace')
    parser_transform.add_argument('--filter-location', help='filters blocks by location according to a regexp')
    parser_transform.add_argument('--filter-name', help='filters blocks by name according to a regexp')
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

    parser_report = subparsers.add_parser(arg_report, help='generate a YAML file with LLVM optimization remarks')
    parser_report.add_argument('SZN_FILE', help='matches given by the MiniZinc finder')

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
            print out,
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
    elif args.subparser == arg_decompose:
        GS = []
        if args.loops:
            GS.extend(decompose_loops(G, args.clean_tags))
        if args.associative_components:
            GS.extend(decompose_associative_components(G, args.min_nodes,
                                                       args.top_components))
        [root, ext] = os.path.splitext(args.TRACE_FILE)
        for (G, subtrace_id) in GS:
            args.output_file = root + "." + subtrace_id + ext
            output(G, args)
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
                                            pdffilename], stdout=subprocess.PIPE)
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
                                       stdout=subprocess.PIPE)
            process.wait()
        except OSError:
            sys.stderr.write("Error: could not find 'pdfjam' executable\n")
            sys.exit(-1)
        if args.clean_intermediate:
            for f in pdffilenames + gvfilenames:
                os.remove(f)

    if args.subparser == arg_report:
        (_, PB, PI, PT) = G
        (pattern, S, _) = u.read_matches(args.SZN_FILE)
        m = 0
        for insts in u.insts_to_steps(G, pattern, S).keys():
            for inst in sorted(list(insts),
                               cmp=lambda i1, i2: cmp(col(PI, i1), col(PI, i2))):
                print "--- !Analysis"
                print "Pass: " + pattern + " " + str(m)
                print "Name: " + pattern
                [loc_file, loc_line, loc_col] = PI[inst].get(u.tk_location).split(u.tk_loc_sep)
                print "DebugLoc: { File: " + loc_file + ", Line: " + loc_line + \
                      ", Column: " + loc_col + "}"
                # TODO: trace the mangled function name of each instruction
                print "Function: main"
                print "Args:"
                if len(insts) == 1:
                    match_type = "a potential " + pattern
                else:
                    match_type = "part of a potential " + pattern
                print "  - String:      '<b>" + PI[inst].get(u.tk_name) + \
                      "</b> is " + match_type + "'"
                print "..."
            m += 1

if __name__ == '__main__':
    main(sys.argv[1:])
