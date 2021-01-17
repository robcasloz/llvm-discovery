#!/usr/bin/env python3

import argparse
import tempfile
import os
import subprocess
import sys
from concurrent import futures
import multiprocessing
import shutil
import glob
import filecmp
import time
import csv
import enum
import copy

import trace_utils as u
import process_trace as pt
import process_matches as pm

eol = "\n"

sub = "-"
add = "+"

class Level(enum.Enum):
    top       = 1
    iteration = 2
    candidate = 3

class Phase(enum.Enum):
    subtraction = 1
    composition = 2

class Context:
    itr     = None
    base    = None
    basedir = None

    def iterdir(self):
        assert self.basedir
        assert self.itr
        return os.path.join(self.basedir, str(self.itr))

    def canddir(self):
        return os.path.join(self.iterdir(), "candidates")

rank = {
    u.pat_doall : 1,
    u.pat_map : 1,
    u.pat_conditional_map : 1,
    u.pat_linear_reduction : 1,
    u.pat_linear_scan : 1,
    u.pat_conditional_linear_scan : 1,
    u.pat_tiled_reduction : 2,
    u.pat_linear_map_reduction : 2,
    u.pat_tiled_map_reduction : 3
}

parser = argparse.ArgumentParser(description='Find parallel patterns in the given trace.')
parser.add_argument('TRACE_FILE')
parser.add_argument('-l,', '--level', dest='level', action='store', type=str, choices=[u.arg_complete, u.arg_eager, u.arg_lazy], default=u.arg_lazy)
parser.add_argument('-v', '--verbose', action='store_true')
parser.add_argument('-j', '--jobs', metavar='N', type=int)
parser.add_argument('--clean', dest='clean', action='store_true')
parser.add_argument('--no-clean', dest='clean', action='store_false')
parser.add_argument('--detailed', dest='detailed', action='store_true')
parser.add_argument('--deep', dest='deep', action='store_true')
parser.add_argument('--max-iterations', type=int)
parser.add_argument('--stats')
parser.add_argument('--html')
parser.add_argument('--html-source-dir')
parser.set_defaults(jobs=multiprocessing.cpu_count())
parser.set_defaults(clean=True)
parser.set_defaults(detailed=False)
parser.set_defaults(stats=False)
parser.set_defaults(deep=False)

args = parser.parse_args()

if args.stats:
    stats = {}
    start = {}

def start_measurement(measurement):
    if not args.stats:
        return
    if not measurement in stats:
        stats[measurement] = 0.0
    start[measurement] = time.time()

def end_measurement(measurement):
    if not args.stats:
        return
    end = time.time()
    stats[measurement] += (end - start[measurement])

def print_debug(message, level = 1):
    if args.verbose:
        sys.stderr.write(("    " * level) + message + eol)

def run_command(cmd):
    print_debug(" ".join(cmd))
    subprocess.check_output(cmd)

def run_process_trace(arguments):
    print_debug(indir("process_trace.py") + " " + " ".join(arguments))
    pt.main(arguments)

def run_process_matches(arguments):
    print_debug(indir("process_matches.py") + " " + " ".join(arguments))
    pm.main(arguments)

def run_minizinc(outfile, arguments):
    print_debug("minizinc " + " ".join(arguments) + " > " + outfile)
    try:
        p = subprocess.Popen(["minizinc"] + arguments, stdout=subprocess.PIPE,
                             stderr=subprocess.PIPE, text=True)
        out, _ = p.communicate()
        with open(outfile, 'w') as of:
            of.writelines(out)
    except OSError:
        sys.stderr.write("Error: could not find 'minizinc' executable\n")
        sys.exit(-1)

def temp(ctx, extension, level):
    if   level == Level.top:
        rootdir = ctx.basedir
    elif level == Level.iteration:
        rootdir = ctx.iterdir()
    elif level == Level.candidate:
        rootdir = ctx.canddir()
    assert(rootdir)
    return os.path.join(rootdir, ".".join([ctx.base] + extension))

def original_trace(ctx):
    return temp(ctx, ["original", "trace"], Level.top)

def indir(filename):
    return os.path.join(sys.path[0], filename)

def mzn(pattern):
    return indir(pattern + ".mzn")

def subtrace_id(ctx, st):
    reserved = set([ctx.base, "trace"])
    for name_component in os.path.basename(st).split("."):
        if not name_component in reserved:
            return name_component

def subtrace_type(ctx, st):
    st_id = subtrace_id(ctx, st)
    if sub in st_id or add in st_id:
        return u.unknown_subtrace
    else:
        if st_id[0] == 'l': # Loop sub-trace
            return u.loop_subtrace
        elif st_id[0] == 'i': # Associative component sub-trace
            return u.associative_component_subtrace
    assert(False)

def applicable_patterns(ctx, st, loops):
    st_type = subtrace_type(ctx, st)
    if   (st_type == u.loop_subtrace):
        # Basic loop trace, do not bother looking for reductions and scans
        # (these are findable by associative components).
        return u.pat_all_map_like
    elif (st_type == u.unknown_subtrace and loops):
        # The trace is derived from a loop, do not bother looking for reductions
        # and scans, but add map-reductions.
        return u.pat_all_map_like + u.pat_all_map_reductions
    elif (st_type == u.associative_component_subtrace) or \
         (st_type == u.unknown_subtrace and not loops):
        # The trace is derived from an associative component, do not bother
        # looking for disconnected patterns (these are findable by loops).
        return u.pat_all_associative
    assert(False)

def applicable_match_trivial(pattern):
    if pattern == u.pat_tiled_reduction:
        return [False, True]
    else:
        return [False]

def candidate_traces(ctx):
    sts = set()
    for itr in range(1, ctx.itr + 1):
        itr_ctx = copy.deepcopy(ctx)
        itr_ctx.itr = itr
        sts |= candidate_traces_iter(itr_ctx)
    return sts

def candidate_traces_iter(ctx):
    return set(glob.glob(os.path.join(ctx.canddir(), "*.trace")))

def subtrace_nodes_loops(st):
    G = u.read_trace(st)
    st_nodes = u.original_blocks(G)
    tags = set()
    for tag in u.tag_set(G):
        tags.add(G[3][tag].get(u.tk_alias))
    st_loops = tags
    return (st_nodes, st_loops)

def update(ex, ctx, nodes, loops, succ):
    start_measurement("update-time")
    (ODDG, _, __, ___) = u.read_trace(original_trace(ctx))
    update_traces = [st for st in candidate_traces(ctx)
                     if not ((st in nodes) and (st in loops) and (st in succ))]
    for (st, (st_nodes, st_loops)) in \
        zip(update_traces, ex.map(subtrace_nodes_loops, update_traces)):
        nodes[st] = st_nodes
        loops[st] = st_loops
        st_succ = set()
        for n in st_nodes:
            st_succ |= (set(ODDG.successors(n)) - st_nodes)
        succ[st] = st_succ
    end_measurement("update-time")

def remove_new_duplicates(nodes, loops, new):
    def get_key(st):
        return (frozenset(nodes[st]), frozenset(loops[st]))
    subtraces = {}
    for st in list(nodes.keys()):
        key = get_key(st)
        if not key in subtraces:
            subtraces[key] = set()
        subtraces[key].add(st)
    for st in new:
        key = get_key(st)
        if len(subtraces[key]) > 1:
            os.remove(st)
            del nodes[st]
            del loops[st]
            subtraces[key].remove(st)

def maybe_paren(string):
    if sub in string or add in string:
        return "[" + string + "]"
    else:
        return string

def operation_id(op, left, right):
    return maybe_paren(left) + op + maybe_paren(right)

def is_subtrahend(st1, st2, nodes, match):
    if st1 == st2:
        return False
    if not (match[st2] in u.pat_all_associative):
        return False
    n1 = nodes[st1]
    n2 = nodes[st2]
    if (n1 - n2 == set()) or (n1 & n2 == set()):
        return False
    return True

def make_subtraction_or_composition(sub_comp_args):
    (phase, phase_args) = sub_comp_args
    if phase == Phase.subtraction:
        make_subtraction(phase_args)
    elif phase == Phase.composition:
        make_composition(phase_args)
    else:
        assert(False)

def make_subtraction(sub_args):
    # Check that there is something to subtract.
    (ctx, (st1, n1, p1), st2s) = sub_args
    if not st2s:
        return
    # Check that we are in first re-iteration. Subtraction only leads to more
    # pattern finding early.
    if ctx.itr > 2:
        return
    # Check that the result is matchable.
    if subtrace_type(ctx, st1) != u.loop_subtrace:
        return
    # Check that st1 has not yet been found as a map-like pattern.
    if p1 in u.pat_all_map_like:
        return
    n2s = set()
    for st2, n2 in st2s:
        n2s |= n2
    st1_id  = subtrace_id(ctx, st1)
    if len(st2s) == 1:
        st2s_id = subtrace_id(ctx, st2s[0][0])
    else:
        st2s_id = "a" + str(ctx.itr - 1)
    # TODO: embed this into a single "subtract-nodes" command.
    subtrahend_id = st1_id + "." + st2s_id
    subtrahend_nodes = temp(ctx, [subtrahend_id, "nodes"], Level.iteration)
    with open(subtrahend_nodes, 'w+') as outfile:
        for n in n2s:
            outfile.write(str(n) + "\n")
    subtrahend_st = temp(ctx, [subtrahend_id, "trace"], Level.iteration)
    run_process_trace(["-o", subtrahend_st, "transform", "--filter-blocks",
                       subtrahend_nodes, original_trace(ctx)])
    subtract_id = operation_id(sub, st1_id, st2s_id)
    subtract_st = temp(ctx, [subtract_id, "trace"], Level.candidate)
    run_process_trace(["-o", subtract_st, "subtract", st1, subtrahend_st,
                       original_trace(ctx)])

def make_composition(comp_args):
    # Check that the result is matchable.
    (ctx, (st1, n1, l1, s1, p1), (st2, n2, l2, s2, p2)) = comp_args
    if None in [p1, p2]:
        return
    # Check that the node sets do not overlap.
    if not n1.isdisjoint(n2):
        return
    # Check that the loop sets do not overlap.
    if not l1.isdisjoint(l2):
        return
    # Check that the subtraces are adjacent, and record pred and succ patterns.
    if s1.issubset(n2):
        (p_fst, p_snd) = (p1, p2)
    elif s2.issubset(n1):
        (p_fst, p_snd) = (p2, p1)
    else:
        return
    # Check that the patterns are compatible.
    if not (p_fst, p_snd) in \
       [(u.pat_map, u.pat_map),
        (u.pat_map, u.pat_conditional_map),
        (u.pat_conditional_map, u.pat_map),
        (u.pat_map, u.pat_linear_reduction),
        (u.pat_map, u.pat_tiled_reduction),
        (u.pat_map, u.pat_linear_map_reduction),
        (u.pat_map, u.pat_tiled_map_reduction)]:
        return
    # Check that the result is different to st1 and st2.
    (ns, ls) = (n1 | n2, l1 | l2)
    if ((ns, ls) == (n1, l1)) or ((ns, ls) == (n2, l2)):
        return
    compose_id = operation_id(add, subtrace_id(ctx, st1), subtrace_id(ctx, st2))
    compose_st = temp(ctx, [compose_id, "trace"], Level.candidate)
    run_process_trace(["-o", compose_st, "compose", st1, st2,
                       original_trace(ctx)])

def make_dzn(dzn_args):
    (ctx, st) = dzn_args
    compact_st = temp(ctx, [subtrace_id(ctx, st), "collapsed", "trace"],
                      Level.iteration)
    run_process_trace(["-o", compact_st, "transform", "--collapse-tags", "all",
                       st])
    compact_st_dzn = temp(ctx, [subtrace_id(ctx, st), "collapsed", "dzn"],
                          Level.iteration)
    run_process_trace(["-o", compact_st_dzn, "--output-format=minizinc",
                       "print", compact_st])

def make_szn(szn_args):
    (ctx, st, pattern, match_trivial) = szn_args
    compact_subtrace_dzn = temp(ctx, [subtrace_id(ctx, st), "collapsed", "dzn"],
                                Level.iteration)
    trivial_extension = []
    if match_trivial:
        trivial_extension.append("trivial")
    compact_subtrace_pattern_szn = \
        temp(ctx, [subtrace_id(ctx, st), "collapsed", pattern + "s"] + \
             trivial_extension + ["szn"],
             Level.iteration)
    run_minizinc(compact_subtrace_pattern_szn,
                 ["-D", "match_trivial=" + str(match_trivial).lower(),
                  "--time-limit", "60000", "-a", "--solver", "chuffed",
                  mzn(pattern), compact_subtrace_dzn])

def make_complete_szn(complete_szn_args):
    (ctx, pattern) = complete_szn_args
    simple_pattern_szn = temp(ctx, ["original", pattern + "s", "szn"],
                              Level.top)
    run_minizinc(simple_pattern_szn, ["-D", "match_trivial=false", "-a",
                                      "--solver", "chuffed", mzn(pattern),
                                      simple_dzn])


ctx = Context()
ctx.basedir = tempfile.mkdtemp(prefix = "discovery-")
ctx.base = os.path.splitext(os.path.basename(args.TRACE_FILE))[0]

try:

    if args.stats:
        finding_start = time.time()

    simplified_trace = temp(ctx, ["simple", "trace"], Level.top)
    start_measurement("simplification-time")
    run_process_trace(["-o", simplified_trace, "simplify", args.TRACE_FILE])
    end_measurement("simplification-time")

    if args.stats:
        for (ext, trace) in [("trace-size", args.TRACE_FILE),
                             ("simplified-trace-size", simplified_trace)]:
            size = temp(ctx, [ext], Level.top)
            run_process_trace(["-o", size, "query", "--print-size", trace])
            with open(size, "r") as size_file:
                stats[ext] = int(size_file.readline())

    run_process_trace(["-o", original_trace(ctx), "record", simplified_trace])

    ex = futures.ProcessPoolExecutor(max_workers=int(args.jobs))

    if args.detailed:
        process_matches_options = []
    else:
        process_matches_options = ["--simple"]
    if args.html:
        process_matches_options += ["--html", args.html]
    if args.html_source_dir:
        process_matches_options += ["--html-source-dir", args.html_source_dir]

    if args.level in [u.arg_eager, u.arg_lazy]:

        # Traces to be subtracted and composed in the current iteration.
        iteration_traces = set()
        # Map from candidate sub-DDG to maximum-rank pattern found.
        match = dict()
        ctx.itr = 1
        patterns_csv = temp(ctx, ["patterns", "csv"], Level.top)

        while True:

            os.mkdir(ctx.iterdir())
            os.mkdir(ctx.canddir())

            if ctx.itr == 1:
                decompose_options = ["--output-dir", ctx.canddir()]
                if ctx.itr > 1:
                    decompose_options += ["--no-associative-components"]
                iter_original_trace = temp(ctx, ["trace"], Level.iteration)
                run_command(["cp", original_trace(ctx), iter_original_trace])
                start_measurement("decomposition-time")
                run_process_trace(["decompose"] + decompose_options + \
                                  [iter_original_trace])
                end_measurement("decomposition-time")

            # Maps from candidate sub-DDG to original node and loop set, and set
            # of external successors. Allows to quickly examine the content and
            # properties of each candidate sub-trace (only used in eager mode).
            nodes = {}
            loops = {}
            succ  = {}

            # Generate candidate subtraces (resulting from applying 'subtract'
            # and 'compose' operations to pairs of sub-traces).

            print_debug("iteration " + str(ctx.itr), level = 0)
            print_debug(str(len(iteration_traces)) + \
                        " iteration traces: " + \
                        str(iteration_traces), level = 0)

            # In eager mode, consider all pairs of candidate traces. In lazy
            # mode, consider (candidate trace, iteration trace) pairs.
            if   args.level == u.arg_eager:
                def active_traces(ctx):
                    return candidate_traces(ctx)
            elif args.level == u.arg_lazy:
                def active_traces(ctx):
                    return iteration_traces
            else:
                assert(False)

            update(ex, ctx, nodes, loops, succ)

            # The list conversion is just to force evaluation.
            start_measurement("expansion-time")
            subtraces_before = set()
            subtraces_after  = candidate_traces(ctx)
            while subtraces_after != subtraces_before:
                subtraces_before = subtraces_after
                start_measurement("subtraction-composition-time")
                pool = candidate_traces(ctx)
                active = active_traces(ctx)
                subtraction_args = \
                    [(Phase.subtraction,
                      (ctx,
                       (st1, nodes[st1], match.get(st1)),
                       [(st2, nodes[st2]) for st2 in active
                        if is_subtrahend(st1, st2, nodes, match)]))
                     for st1 in pool]
                composition_args = \
                    [(Phase.composition,
                      (ctx,
                       (st1, nodes[st1], loops[st1], succ[st1], match.get(st1)),
                       (st2, nodes[st2], loops[st2], succ[st2], match.get(st2))
                      )) for st1 in pool for st2 in active if st1 < st2]
                list(ex.map(make_subtraction_or_composition,
                            subtraction_args + composition_args))
                end_measurement("subtraction-composition-time")
                update(ex, ctx, nodes, loops, succ)
                new = candidate_traces(ctx) - subtraces_before
                remove_new_duplicates(nodes, loops, new)
                subtraces_after = candidate_traces(ctx)
                if not args.deep:
                    break
            end_measurement("expansion-time")

            # The list conversion is just to force evaluation.
            start_measurement("compaction-time")
            list(ex.map(make_dzn,
                        [(ctx, st) for st in candidate_traces_iter(ctx)]))
            end_measurement("compaction-time")

            # The list conversion is just to force evaluation.
            start_measurement("matching-time")
            list(ex.map(make_szn,
                        [(ctx, st, p, mt)
                         for st in candidate_traces_iter(ctx)
                         for p  in applicable_patterns(ctx, st,
                                                       loops.get(st, {}))
                         for mt in applicable_match_trivial(p)]))
            end_measurement("matching-time")

            # Compute traces where a pattern was found in the iteration.
            # TODO: refine by including only traces where a *new* pattern
            # has been found.
            iter_szn_files = [temp(ctx, [subtrace_id(ctx, st), "collapsed",
                                         p + "s", "szn"], Level.iteration)
                             for st in candidate_traces_iter(ctx)
                             for p  in applicable_patterns(ctx, st,
                                                           loops.get(st, {}))]
            patterns_iter_csv = temp(ctx, ["patterns", "csv"], Level.iteration)
            run_process_matches(iter_szn_files + \
                                ["-o", patterns_iter_csv, "--show-doall",
                                 "--show-linear-scan", "--show-subsumed",
                                 "--show-constant-reductions"])
            iteration_traces = set()
            with open(patterns_iter_csv) as csv_file:
                r = csv.reader(csv_file, delimiter=",")
                legend = next(r)
                traces_index = legend.index("traces")
                location_index = legend.index("location")
                loops_index = legend.index("loops")
                new_traces = set()
                for line in r:
                    key = (line[location_index], line[loops_index])
                    for cst in line[traces_index].split(";"):
                        st = temp(ctx, [subtrace_id(ctx, cst), "trace"],
                                  Level.candidate)
                        pattern = None
                        for p in u.pat_all:
                            if line[legend.index(p)] == u.match_full:
                                pattern = p
                                break
                        if not pattern:
                            # Can happen if there are only partial matches.
                            continue
                        if st in match:
                            match[st] = max([match[st], pattern],
                                            key=lambda p : rank[p])
                        else:
                            match[st] = pattern
                        new_traces.add(st)

            # Select all new traces where a useful pattern has been
            # found for the new iteration.
            for st in new_traces:
                if match[st] in [u.pat_map, u.pat_conditional_map] + \
                   u.pat_all_associative:
                    iteration_traces.add(st)

            # If we are in eager mode or in lazy mode but not more patterns
            # are found, terminate.
            if args.level == u.arg_eager or not iteration_traces or \
               (args.max_iterations and ctx.itr == args.max_iterations):
                def candidate_to_szn(ctx, st, p):
                    # FIXME: do this properly.
                    return st.replace("/candidates", "")\
                             .replace(".trace", ".collapsed." + p + "s.szn")
                szn_files = [candidate_to_szn(ctx, st, p)
                             for st in candidate_traces(ctx)
                             for p  in applicable_patterns(
                                     ctx, st, loops.get(st, {}))]
                run_process_matches(szn_files + ["-o", patterns_csv] + \
                                    process_matches_options)
                break

            # Otherwise, re-iterate.
            ctx.itr += 1

        # Done with eager or lazy pattern finding, print final results.
        for line in open(patterns_csv, "r"):
            print(line, end="")

    elif args.level == u.arg_complete:

        simple_dzn = temp(ctx, ["original", "dzn"], Level.top)
        run_process_trace(["-o", simple_dzn, "--output-format=minizinc", "print",
                           original_trace(ctx)])

        # The list conversion is just to force evaluation.
        start_measurement("matching-time")
        list(ex.map(make_complete_szn, [(ctx, p) for p in u.pat_all]))
        end_measurement("matching-time")

        szn_files = \
            [temp(ctx, ["original", p + "s", "szn"], Level.top)
             for p in u.pat_all]
        run_process_matches(szn_files + process_matches_options)

finally:
    if args.clean:
        shutil.rmtree(ctx.basedir)
    if args.stats:
        finding_end = time.time()
        with open(args.stats ,"w+") as stats_out:
            stats["finding-time"] = finding_end - finding_start
            st_writer = csv.writer(stats_out, delimiter=",",
                                   quoting=csv.QUOTE_MINIMAL)
            st_writer.writerow(["measurement", "value"])
            for (measurement, value) in stats.items():
                st_writer.writerow([measurement, value])
