# Common definitions and functions to process traces and matches.

import networkx as nx
import itertools
import subprocess
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

pat_doall = "doall"
pat_map = "map"
pat_reduction = "reduction"
pat_scan = "scan"
pat_pipeline = "pipeline"

arg_loop = "loop"
arg_instruction = "instruction"

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
            (t, i) = tag_str_to_tuple(value)
            if not (t,i) in tags:
                tags.append((t,i))
            PB[block][tk_tags] = tags
        elif key == tk_tags:
            PB[block][key] = map(tag_str_to_tuple, value.split(tk_list_sep))
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
def insts_to_steps((_, PB, PI, __), pattern, matches):
    i_to_s = dict()
    for match in matches:
        if pattern in [pat_doall, pat_map, pat_reduction, pat_scan]:
            steps = len(match)
            nodes = index_map(match).keys()
        elif pattern == pat_pipeline:
            (stages, runs) = match
            steps = len(stages) * len(runs)
            nodes = index_map(stages).keys()
        sol_insts = Set()
        for n in nodes:
            inst = PB[n].get(tk_instruction)
            if tk_children in PI[inst]:
                sol_insts.add(PI[inst].get(tk_children))
            else:
                sol_insts.add(inst)
        si = frozenset(sol_insts)
        if si in i_to_s:
            i_to_s[si].add(steps)
        else:
            i_to_s[si] = set([steps])
    return i_to_s

# Gives a tag tuple out of a tag-instance string.
def tag_str_to_tuple(tag_instance):
    [t,i] = tag_instance.rsplit(tk_tag_sep, 1)
    try:
        tag = int(t)
    except ValueError:
        tag = t
    return (tag, int(i))

# Gives the tag in a tag-instance pair.
def tag_name((t, _)):
    return t

# Gives the instance in a tag-instance pair.
def tag_instance((_, i)):
    return i

# Returns a set with all different tags in the trace.
def tag_set((_, PB, __, ___)):
    return set(itertools.chain.from_iterable(
        [[tag_name(tag_ins) for tag_ins in PB[block].get(tk_tags, [])]
         for block in PB]))

# Transforms a MiniZinc set of ints into a Python one.
def int_set(e):
    if e[0] == "{":
        iset = sorted(map(int, e[1:-1].split(",")))
    else:
        [first, last] = map(int, e.split(".."))
        iset = range(first, last + 1)
    return iset

# Reads the given .szn file and returns a tuple (pattern, matches, status) where
# 'pattern' is the name of the potentially matched pattern, 'matches' is the
# list of matches, and 'status' tells the solver status (unknown, error, etc.).
def read_matches(match_file):
    # Read the traces
    matches = []
    stages = None
    pattern = None
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
            if pattern == pat_pipeline:
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
            else:
                match = array
            matches.append(match)
    if status in [tk_sol_status_unknown]:
        assert not matches, \
        "unexpected matches when solver terminates with unknown status"
    return (pattern, matches, status)

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

