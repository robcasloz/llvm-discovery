#!/usr/bin/python

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
import merge_matches as mm

eol = "\n"

sub = "-"
add = "+"

class Level(enum.Enum):
    top       = 1
    iteration = 2
    candidate = 3

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

parser = argparse.ArgumentParser(description='Find parallel patterns in the given trace.')
parser.add_argument('TRACE_FILE')
parser.add_argument('-l,', '--level', dest='level', action='store', type=str, choices=[u.arg_heuristic, u.arg_eager, u.arg_lazy, u.arg_complete], default=u.arg_heuristic)
parser.add_argument('-v', '--verbose', action='store_true')
parser.add_argument('-j', '--jobs', metavar='N', type=int)
parser.add_argument('--clean', dest='clean', action='store_true')
parser.add_argument('--no-clean', dest='clean', action='store_false')
parser.add_argument('--detailed', dest='detailed', action='store_true')
parser.add_argument('--deep', dest='deep', action='store_true')
parser.add_argument('--max-iterations', type=int)
parser.add_argument('--stats')
parser.set_defaults(jobs=multiprocessing.cpu_count())
parser.set_defaults(clean=True)
parser.set_defaults(detailed=False)
parser.set_defaults(stats=False)
parser.set_defaults(deep=False)

args = parser.parse_args()

if args.stats:
    stats = {}
    start = 0.0

def start_measurement(measurement):
    global start
    if not args.stats:
        return
    if not measurement in stats:
        stats[measurement] = 0.0
    start = time.time()

def end_measurement(measurement):
    global start
    if not args.stats:
        return
    end = time.time()
    stats[measurement] += (end - start)

def run_command(cmd):
    if args.verbose:
        sys.stderr.write(" ".join(cmd) + eol)
    subprocess.check_output(cmd)

def run_process_trace(arguments):
    if args.verbose:
        sys.stderr.write(indir("process_trace.py") + " " + " ".join(arguments) + eol)
    pt.main(arguments)

def run_process_matches(arguments):
    if args.verbose:
        sys.stderr.write(indir("process_matches.py") + " " + " ".join(arguments) + eol)
    pm.main(arguments)

def run_merge_matches(arguments):
    if args.verbose:
        sys.stderr.write(indir("merge_matches.py") + " " + " ".join(arguments) + eol)
    mm.main(arguments)

def run_minizinc(outfile, arguments):
    if args.verbose:
        sys.stderr.write("minizinc " + " ".join(arguments) + " > " + outfile +
                         eol)
    try:
        p = subprocess.Popen(["minizinc"] + arguments, stdout=subprocess.PIPE,
                             stderr=subprocess.PIPE)
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
        return u.pat_all_disconnected
    elif (st_type == u.unknown_subtrace and loops):
        # The trace is derived from a loop, do not bother looking for reductions
        # and scans, but add map-reductions.
        return u.pat_all_disconnected + u.pat_all_map_reductions
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
    sts = []
    for itr in range(1, ctx.itr + 1):
        itr_ctx = copy.deepcopy(ctx)
        itr_ctx.itr = itr
        sts += candidate_traces_iter(itr_ctx)
    return sts

def candidate_traces_iter(ctx):
    return glob.glob(os.path.join(ctx.canddir(), "*.trace"))

def update(ctx, nodes, loops, succ):
    # TODO: do this in parallel.
    for st in candidate_traces(ctx):
        G = u.read_trace(st)
        nodes[st] = u.original_blocks(G)
        tags = set()
        for tag in u.tag_set(G):
            tags.add(G[3][tag].get(u.tk_alias))
        loops[st] = tags
        s = set()
        (ODDG, _, __, ___) = u.read_trace(original_trace(ctx))
        for n in nodes[st]:
            s |= (set(ODDG.successors(n)) - nodes[st])
        succ[st] = s

def remove_new_duplicates(nodes, loops, new):
    def get_key(st):
        return (frozenset(nodes[st]), frozenset(loops[st]))
    subtraces = {}
    for st in nodes.keys():
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

def make_subtraction((ctx, st1, st2, n1, n2)):
    # This operation only leads to finding more patterns up to the second
    # iteration. In later iterations, do not bother.
    if ctx.itr > 2:
        return
    # If the result would not be a new sub-trace (because it
    # would be empty or equal to st1), do not bother.
    if (n1 - n2 == set()) or (n1 & n2 == set()):
        return
    # If the result would not be matchable, do not bother. This is the case for
    # subtractions of loops from associative components.
    if subtrace_type(ctx, st1) == u.associative_component_subtrace and \
       subtrace_type(ctx, st2) == u.loop_subtrace:
        return
    subtract_id = \
        operation_id(sub, subtrace_id(ctx, st1), subtrace_id(ctx, st2))
    subtract_st = temp(ctx, [subtract_id, "trace"], Level.candidate)
    run_process_trace(["-o", subtract_st, "subtract", st1, st2,
                       original_trace(ctx)])

def make_composition((ctx, st1, st2, n1, l1, s1, n2, l2, s2)):
    # Check that the node sets do not overlap.
    if not n1.isdisjoint(n2):
        return
    # If the result would be equal to st1 or st2, do not bother.
    (ns, ls) = (n1 | n2, l1 | l2)
    if ((ns, ls) == (n1, l1)) or ((ns, ls) == (n2, l2)):
        return
    # If the result would not be matchable for fused map or map-reduction
    # patterns, do not bother. This is the case if none of the subtraces is
    # loop-based or the subtraces are not adjacent.
    if not l1 and not l2:
        return
    if not (s1.issubset(n2) or s2.issubset(n1)):
        return
    compose_id = operation_id(add, subtrace_id(ctx, st1), subtrace_id(ctx, st2))
    compose_st = temp(ctx, [compose_id, "trace"], Level.candidate)
    run_process_trace(["-o", compose_st, "compose", st1, st2,
                       original_trace(ctx)])

def make_dzn((ctx, st)):
    compact_st = temp(ctx, [subtrace_id(ctx, st), "collapsed", "trace"],
                      Level.iteration)
    run_process_trace(["-o", compact_st, "transform", "--collapse-tags", "all",
                       st])
    compact_st_dzn = temp(ctx, [subtrace_id(ctx, st), "collapsed", "dzn"],
                          Level.iteration)
    run_process_trace(["-o", compact_st_dzn, "--output-format=minizinc",
                       "print", compact_st])

def make_szn((ctx, st, pattern, match_trivial)):
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

def make_complete_szn((ctx, pattern)):
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
        simple_options = []
    else:
        simple_options = ["--simple"]

    if args.level in [u.arg_heuristic, u.arg_eager, u.arg_lazy]:

        # Traces where a pattern was found in the previous iteration.
        last_matched = []
        ctx.itr = 1
        patterns_csv = temp(ctx, ["patterns", "csv"], Level.top)
        run_process_matches(["-o", patterns_csv] + simple_options)

        while True:

            os.mkdir(ctx.iterdir())
            os.mkdir(ctx.canddir())

            if ctx.itr == 1 or args.level == u.arg_heuristic:
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
            if args.level == u.arg_eager or args.level == u.arg_lazy:

                # In early mode, consider all pairs of candidate traces. In lazy
                # mode, consider pairs of candidate traces and last-matched
                # traces.
                if   args.level == u.arg_eager:
                    def active_traces(ctx):
                        return candidate_traces(ctx)
                elif args.level == u.arg_lazy:
                    def active_traces(ctx):
                        return last_matched
                else:
                    assert(False)

                update(ctx, nodes, loops, succ)

                # The list conversion is just to force evaluation.
                start_measurement("eager-generation-time")
                subtraces_before = set()
                subtraces_after  = set(candidate_traces(ctx))
                while subtraces_after != subtraces_before:
                    subtraces_before = subtraces_after
                    list(ex.map(make_subtraction,
                                [(ctx, st1, st2, nodes[st1], nodes[st2])
                                 for st1 in candidate_traces(ctx)
                                 for st2 in active_traces(ctx)
                                 if st1 != st2]))
                    update(ctx, nodes, loops, succ)
                    new = set(candidate_traces(ctx)) - subtraces_before
                    remove_new_duplicates(nodes, loops, new)
                    subtraces_between = set(candidate_traces(ctx))
                    list(ex.map(make_composition,
                                [(ctx, st1, st2,
                                  nodes[st1], loops[st1], succ[st1],
                                  nodes[st2], loops[st2], succ[st2])
                                 for st1 in candidate_traces(ctx)
                                 for st2 in active_traces(ctx)
                                 if st1 < st2]))
                    update(ctx, nodes, loops, succ)
                    subtraces_after = set(candidate_traces(ctx))
                    if not args.deep:
                        break
                end_measurement("eager-generation-time")

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

            if args.level == u.arg_eager or args.level == u.arg_lazy:

                # Compute traces where a pattern was found in the iteration.
                # TODO: refine by including only traces where a *new* pattern
                # has been found.
                iter_szn_files = [temp(ctx, [subtrace_id(ctx, st), "collapsed",
                                             p + "s", "szn"], Level.iteration)
                                 for st in candidate_traces_iter(ctx)
                                 for p  in applicable_patterns(ctx, st,
                                                               loops.get(st, {}))]
                patterns_iter_csv = temp(ctx, ["patterns", "csv"], Level.iteration)
                matched_csv = temp(ctx, ["matched", "csv"], Level.iteration)
                run_process_matches(iter_szn_files + \
                                    ["-o", patterns_iter_csv,
                                     "--matched-traces-file", matched_csv] + \
                                    simple_options)
                last_matched = []
                with open(matched_csv) as csv_file:
                    for line in csv.reader(csv_file, delimiter=","):
                        st = temp(ctx, [subtrace_id(ctx, line[0]), "trace"],
                                  Level.candidate)
                        last_matched.append(st)

                # If we are in eager mode or in lazy mode but not more patterns
                # are found, terminate.
                if args.level == u.arg_eager or not last_matched or \
                   (args.max_iterations and ctx.itr == args.max_iterations):
                    def candidate_to_szn(ctx, st, p):
                        # FIXME: do this properly.
                        return st.replace("/candidates", "")\
                                 .replace(".trace", ".collapsed." + p + "s.szn")
                    szn_files = [candidate_to_szn(ctx, st, p)
                                 for st in candidate_traces(ctx)
                                 for p  in applicable_patterns(ctx, st,
                                                               loops.get(st, {}))]
                    run_process_matches(szn_files + ["-o", patterns_csv] + \
                                        simple_options)
                    break

                ctx.itr += 1
                continue

            def subtrace_szn_files(st_type):
                return [temp(ctx, [subtrace_id(ctx, st), "collapsed", p + "s",
                                   "szn"], Level.iteration)
                        for st in candidate_traces(ctx)
                        for p in  applicable_patterns(ctx, st,
                                                      loops.get(st, {}))
                        if subtrace_type(ctx, st) == st_type]

            def update_patterns_csv(new):
                tmp_csv = temp(ctx, ["tmp", "csv"], Level.iteration)
                run_merge_matches([patterns_csv, new, "-o", tmp_csv] + \
                                  simple_options)
                run_command(["mv", tmp_csv, patterns_csv])

            loop_szn_files = subtrace_szn_files(u.loop_subtrace)
            loop_csv = temp(ctx, ["loops", "csv"], Level.iteration)
            run_process_matches(loop_szn_files + \
                                ["-o", loop_csv] + \
                                simple_options)
            update_patterns_csv(loop_csv)
            associative_component_szn_files = \
                subtrace_szn_files(u.associative_component_subtrace)
            associative_component_csv = \
                temp(ctx, ["associative_components", "csv"], Level.iteration)
            instructions = temp(ctx, ["instructions"], Level.iteration)
            run_process_matches(associative_component_szn_files +
                                ["-o", associative_component_csv,
                                 "--matched-instructions-prefix",
                                 ctx.iterdir()] + simple_options)
            update_patterns_csv(associative_component_csv)
            if not os.path.isfile(instructions):
                break

            subtracted_trace = \
                temp(ctx, ["original", "subtracted", "trace"], Level.iteration)
            start_measurement("subtraction-time")
            run_process_trace(["-o", subtracted_trace, "transform",
                               "--filter-out-instructions", instructions,
                               original_trace(ctx)])
            end_measurement("subtraction-time")

            if filecmp.cmp(original_trace(ctx), subtracted_trace):
                break
            # TODO: move directly to next iteration's directory.
            run_command(["mv", subtracted_trace, original_trace(ctx)])
            ctx.itr += 1

        for line in open(patterns_csv, "r"):
            print line,

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
        run_process_matches(szn_files + simple_options)

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
            for (measurement, value) in stats.iteritems():
                st_writer.writerow([measurement, value])
