# Common definitions and functions to process traces and matches.

import networkx as nx
import itertools
import subprocess
import collections
import re
from sets import Set

tk_df = "DF"
tk_bp = "BP"
tk_ip = "IP"
tk_tp = "TP"
tk_hl = "HL"

tk_name = "NAME"
tk_iterator = "ITERATOR"
tk_impure = "IMPURE"
tk_control = "CONTROL"
tk_noncommutative = "NONCOMMUTATIVE"
tk_location = "LOCATION"
tk_true = "TRUE"
tk_instruction = "INSTRUCTION"
tk_children = "CHILDREN"
tk_region = "REGION"
tk_tag = "TAG"
tk_tags = "TAGS"
tk_alias = "ALIAS"
tk_original_blocks = "ORIGINALBLOCKS"
tk_original = "ORIGINAL"

tk_list_sep = ";"
tk_tag_sep = "-"
tk_loc_sep = ":"

tk_sol_sep = "----------"
tk_sol_end = "=========="
tk_sol_unsat = "=====UNSATISFIABLE====="
tk_sol_error = "=====ERROR====="
tk_sol_unknown = "=====UNKNOWN====="
tk_sol_com = "%"

tk_sol_status_normal = "normal"
tk_sol_status_error = "error"
tk_sol_status_unknown = "unknown"
tk_sol_status_empty = "empty"

pat_doall = "doall"
pat_map = "map"
pat_mapfilter = "mapfilter"
pat_reduction = "reduction"
pat_scan = "scan"
pat_pipeline = "pipeline"
pat_twophasereduction = "twophasereduction"
pat_mapreduction = "mapreduction"
pat_twophasemapreduction = "twophasemapreduction"

arg_nodes = "nodes"
arg_location = "location"
arg_heuristic = "heuristic"
arg_eager = "eager"
arg_complete = "complete"

match_unknown = "?"
match_partial = "~"
match_full    = "1"
match_none    = "0"

match    = "yes"
no_match = "no"

loop_subtrace                  = "loop"
associative_component_subtrace = "associative-component"

# List with all supported unidimensional patterns.
pat_all_uni = [pat_doall, pat_map, pat_mapfilter, pat_reduction, pat_scan]

# List with all supported patterns.
pat_all = pat_all_uni + [pat_twophasereduction, pat_pipeline]

# List with all patterns that require asociativity.
pat_all_associative = [pat_reduction, pat_scan, pat_twophasereduction]

# Returns a labeled DDG from a trace loaded from the given file.
def read_trace(trace_file):
    # Read the traces
    df_lines = []
    bp_lines = []
    ip_lines = []
    tp_lines = []
    hl_lines = []
    with open(trace_file, "r") as trace:
        array = []
        lines_seen = set()
        for line in trace:
            if line in lines_seen:
                continue
            lines_seen.add(line)
            tokens = line.split()
            if not tokens:
                continue
            if tokens[0] == tk_df:
                df_lines.append(tokens[1:])
            elif tokens[0] == tk_bp:
                bp_lines.append(tokens[1:])
            elif tokens[0] == tk_ip:
                ip_lines.append(tokens[1:])
            elif tokens[0] == tk_tp:
                tp_lines.append(tokens[1:])
            elif tokens[0] == tk_hl:
                hl_lines.append(tokens[1:])
    # Build the labeled graph.
    DDG = nx.DiGraph()
    for tokens in df_lines:
        DDG.add_edge(int(tokens[0]), int(tokens[1]))
    # Complete the graph with isolated, impure or control nodes.
    for tokens in bp_lines:
        DDG.add_node(int(tokens[0]))
    PB = {}
    for block in DDG.nodes():
        PB[block] = {}
    for tokens in bp_lines:
        block = int(tokens[0])
        key = tokens[1]
        value = tokens[2]
        if key == tk_tag:
            # Compress multiple values of tk_tag into a tk_tags list.
            tags = PB[block].get(tk_tags, [])
            tag = tag_str_to_tuple(value)
            if not tag in tags:
                tags.append(tag)
            PB[block][tk_tags] = tags
        elif key == tk_tags:
            PB[block][key] = map(tag_str_to_tuple, value.split(tk_list_sep))
        elif key == tk_original:
            PB[block][key] = map(int, value.split(tk_list_sep))
        elif key == tk_instruction:
            try:
                instruction = int(value)
            except ValueError:
                instruction = value
            PB[block][key] = instruction
        else:
            assert not (key in PB[block])
            PB[block][key] = value
    PI = {}
    for tokens in ip_lines:
        try:
            instruction = int(tokens[0])
        except ValueError:
            instruction = tokens[0]
        if not instruction in PI:
            PI[instruction] = {}
        key = tokens[1]
        value = tokens[2]
        if key == tk_children:
            PI[instruction][key] = map(int, value.split(tk_list_sep))
        else:
            PI[instruction][key] = value
    PT = {}
    for tokens in tp_lines:
        tag = int(tokens[0])
        if not tag in PT:
            PT[tag] = {}
        key = tokens[1]
        value = tokens[2]
        PT[tag][key] = value
    return (DDG, PB, PI, PT)

# Gives a map from nodes in a solution array to their indices.
def index_map(array):
    return dict(itertools.chain.from_iterable(
        [[(n, idx) for n in step] for (idx, step) in
         zip(range(len(array)), array)]))

# Takes a DDG, a pattern name and a set of matches and gives a map from sets of
# instructions to sets of number of pattern steps.
# TODO: simplify, the number of pattern steps is unused.
def insts_to_steps(G, pattern, matches):
    i_to_s = dict()
    for match in matches:
        if pattern in pat_all_uni:
            steps = len(match)
        elif pattern == pat_pipeline:
            (stages, runs) = match
            steps = len(stages) * len(runs)
        elif pattern == pat_twophasereduction:
            partial_steps = [len(p) for (f, p) in match]
            steps = sum(partial_steps) + len(partial_steps)
        sol_insts = Set()
        for n in match_nodes(pattern, match):
                sol_insts.update(node_instructions(G, n))
        si = frozenset(sol_insts)
        if si in i_to_s:
            i_to_s[si].add(steps)
        else:
            i_to_s[si] = set([steps])
    return i_to_s

# Takes a pattern name and a match and gives the set of nodes.
def match_nodes(pattern, match):
    if pattern in pat_all_uni:
        nodes = index_map(match).keys()
    elif pattern == pat_pipeline:
        (stages, runs) = match
        nodes = index_map(stages).keys()
    elif pattern == pat_twophasereduction:
        nodes = flatten(match)
    return nodes

# Gives the instruction(s) corresponding to a node.
def node_instructions((_, PB, PI, __), node):
    inst = PB[node].get(tk_instruction)
    if tk_children in PI[inst]:
        return PI[inst].get(tk_children)
    return [inst]

# Gives a tag tuple out of a tag-data string.
def tag_str_to_tuple(tag_data):
    [t,g,i] = tag_data.rsplit(tk_tag_sep, 2)
    try:
        tag = int(t)
    except ValueError:
        tag = t
    return (tag, (int(g), int(i)))

# Gives the tag in a tag-data pair.
def tag_name((t, _)):
    return t

# Gives the tag data a tag-data pair.
def tag_data((_, d)):
    return d

# Gives the group in a tag-data pair.
def tag_group((_, (g, _i))):
    return g

# Gives the instance in a tag-data pair.
def tag_instance((_, (_g, i))):
    return i

# Returns a set with all different tags in the trace.
def tag_set((_, PB, __, ___)):
    return set(itertools.chain.from_iterable(
        [[tag_name(tag_data) for tag_data in PB[block].get(tk_tags, [])]
         for block in PB]))

# Transforms a MiniZinc set of ints into a Python one.
def int_set(e):
    if e[0] == "{":
        iset = sorted(map(int, e[1:-1].split(",")))
    else:
        [first, last] = map(int, e.split(".."))
        iset = range(first, last + 1)
    return iset

# Concats a list of lists.
def concat(l):
    return list(itertools.chain.from_iterable(l))

# Deep-flattens a list.
def flatten(x):
    if isinstance(x, collections.Iterable):
        return [a for i in x for a in flatten(i)]
    else:
        return [x]

# Reads the given .szn file and returns a tuple (pattern, matches, status) where
# 'pattern' is the name of the potentially matched pattern, 'matches' is the
# list of matches, and 'status' tells the solver status (unknown, error, etc.).
def read_matches(match_file):
    # Read the traces
    matches = []
    stages = None
    runs = None
    pattern = None
    partials = []
    status = tk_sol_status_normal
    with open(match_file, "r") as match:
        for line in match:
            if line and line.lstrip()[0] == tk_sol_com:
                continue
            tokens = line.split()
            if not tokens \
                 or tokens == [tk_sol_sep] \
                 or tokens == [tk_sol_end] \
                 or tokens == [tk_sol_unsat]:
                continue
            elif tokens == [tk_sol_unknown]:
                status = tk_sol_status_unknown
                continue
            elif tokens == [tk_sol_error]:
                status = tk_sol_status_error
                continue
            pattern = tokens[0][:-1]
            if pattern in [pat_pipeline, pat_mapreduction,
                           pat_twophasereduction, pat_twophasemapreduction]:
                typ  = tokens[1]
                rest = tokens[2:]
            else:
                rest = tokens[1:]
            array = [int_set(e) for e in rest if not e == "{}"]
            if pattern == pat_pipeline:
                if stages:
                    match = (stages, array)
                    stages = None
                else:
                    # Partial solution, rest of the solution is in next line.
                    stages = array
                    continue
            elif pattern == pat_mapreduction:
                if runs:
                    match = (runs, array)
                    runs = None
                else:
                    # Partial solution, rest of the solution is in next line.
                    runs = array
                    continue
            elif pattern in [pat_twophasereduction, pat_twophasemapreduction]:
                # Map in a map-reduction.
                if typ == "map:":
                    map_runs = array
                    continue
                # New final reduction step.
                if typ == "final:":
                    if array:
                        final = array[0]
                        continue # Partial solution, keep reading.
                    else: # End of two-phase reduction
                        if partials:
                            match = partials
                            partials = []
                        else:
                            continue # Partial solution, keep reading.
                elif typ == "partial:":
                    if array:
                        if pattern == pat_twophasereduction:
                            partial = (final, array)
                        elif pattern == pat_twophasemapreduction:
                            runs = map_runs[0:len(array)]
                            map_runs = map_runs[len(array):]
                            partial = (runs, final, array)
                        partials.append(partial)
                    continue # Partial solution, keep reading.
                else:
                    assert False
            else:
                match = array
            matches.append(match)
    if status in [tk_sol_status_unknown]:
        assert not matches, \
        "unexpected matches when solver terminates with unknown status"
    return (pattern, matches, status)

# Discards subsumed matches based on the pattern node subset relation.  Note
# that this is a naive, quadratic-time implementation.
def discard_subsumed_matches(matches):
    nodeset = lambda match : set(flatten(match))
    nodesets = map(nodeset, matches)
    filtered_matches = []
    for match in matches:
        subsumed = False
        for ns in nodesets:
            if nodeset(match) < ns:
                subsumed = True
                continue
        if not subsumed:
            filtered_matches.append(match)
    return filtered_matches

# Demangles a function name if the external tool 'c++filt' is available.
def demangle(name, cache):
    if cache.get(name) == None:
        try:
            process = subprocess.Popen(["c++filt", "--no-params",
                                        "--no-verbose", name],
                                       stdout=subprocess.PIPE)
        except OSError:
            cache[name] = name
            return name
        (output, err) = process.communicate()
        exit_code = process.wait()
        demangled = output.rstrip("\n\r")
        simplified = demangled \
                     .replace("std::", "") \
                     .replace("operator<<", "<<")
        cache[name] = simplified
    return cache[name]

# Gives the minimal set of tags that covers all blocks in the instructions.
def min_tag_cover((DDG, PB, PI, PT), insts):
    min_tags = set([])
    # Find, for each instruction, the most specific tag.
    for inst in insts:
        tags = set([])
        for block in DDG.nodes():
            if PB[block].get(tk_instruction) == inst:
                tags |= set([tag_name(t) for t in PB[block].get(tk_tags, [])])
        if tags:
            min_tag = sorted(tags, cmp=lambda t1, t2:
                             cmp(int(PT[t1][tk_original_blocks]),
                                 int(PT[t2][tk_original_blocks])))[0]
            min_tags.add(min_tag)
    return min_tags

# Note: this is taken from https://stackoverflow.com/a/16090640.
def natural_sort_key(s, _nsre=re.compile('([0-9]+)')):
    return [int(text) if text.isdigit() else text.lower()
            for text in _nsre.split(s)]

# Gives the static instruction properties of the given block.
def properties(b, PB, PI):
    return PI[PB[b][tk_instruction]]

# Tells whether the given block is the source.
def is_source(b, PB, PI):
    return properties(b, PB, PI).get(tk_region) == tk_true and \
           properties(b, PB, PI).get(tk_name) == "source"

# Tells whether the given block is the sink.
def is_sink(b, PB, PI):
    return properties(b, PB, PI).get(tk_region) == tk_true and \
           properties(b, PB, PI).get(tk_name) == "sink"

# Tells whether the given instruction is associative.
def is_associative(i, PI):
    props = PI[i]
    if props.get(tk_region) == tk_true:
        children = props.get(tk_children)
        if not children or len(children) != 1:
            return False
        return (PI[children[0]].get(tk_name) in associative_names)
    else:
        return props.get(tk_name) in associative_names

# Gives a set of instruction names that are known to be associative.
# FIXME: We added 'sub' and 'fsub' to simulate an algebraic transformation: a
# statement "foo -= bar" can always be rewritten as "foo += (-bar)" and matched
# as a map+reduction. See case in streamcluster.c:171 (seq) and
# streamcluster.c:316 (pthread) within the StarBench suite. This should rather
# be implemented as a transformation, e.g. within the simplification step or
# perhaps even at instrumentation phase.
associative_names = \
    set(["add", "fadd", "mul", "fmul", "and", "or", "xor", "sub", "fsub"])
