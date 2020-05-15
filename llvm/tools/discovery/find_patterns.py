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

import trace_utils as u
import process_trace as pt
import process_matches as pm
import merge_matches as mm

eol = "\n"

class Level(enum.Enum):
    top       = 1
    iteration = 2
    candidate = 3

parser = argparse.ArgumentParser(description='Find parallel patterns in the given trace.')
parser.add_argument('TRACE_FILE')
parser.add_argument('-l,', '--level', dest='level', action='store', type=str, choices=[u.arg_heuristic, u.arg_eager, u.arg_complete], default=u.arg_heuristic)
parser.add_argument('-v', '--verbose', action='store_true')
parser.add_argument('-j', '--jobs', metavar='N', type=int)
parser.add_argument('--clean', dest='clean', action='store_true')
parser.add_argument('--no-clean', dest='clean', action='store_false')
parser.add_argument('--detailed', dest='detailed', action='store_true')
parser.add_argument('--stats')
parser.set_defaults(jobs=multiprocessing.cpu_count())
parser.set_defaults(clean=True)
parser.set_defaults(detailed=False)
parser.set_defaults(stats=False)

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

basedir = tempfile.mkdtemp(prefix = "discovery-")
base = os.path.splitext(os.path.basename(args.TRACE_FILE))[0]
iterdir = None
canddir = None

try:

    def temp(extension, level):
        if   level == Level.top:
            rootdir = basedir
        elif level == Level.iteration:
            rootdir = iterdir
        elif level == Level.candidate:
            rootdir = canddir
        assert(rootdir)
        return os.path.join(rootdir, ".".join([base] + extension))

    def indir(filename):
        return os.path.join(sys.path[0], filename)

    def mzn(pattern):
        return indir(pattern + ".mzn")

    def subtrace_id(subtrace):
        base_subtrace = os.path.basename(os.path.splitext(subtrace)[0])
        [_, _, subtrace_id] = base_subtrace.split(".", 2)
        return subtrace_id

    def subtrace_type((st_type, _)):
        return st_type

    def subtrace_prefix((st_type, (first, second))):
        if st_type == u.loop_subtrace:
            suffix = [str(first), str(second)]
        else:
            suffix = [first, str(second)]
        return ["original"] + suffix

    def applicable_patterns(st_type):
        if st_type == u.loop_subtrace:
            return u.pat_all_uni
        elif st_type == u.associative_component_subtrace:
            return u.pat_all_associative

    if args.stats:
        finding_start = time.time()

    simplified_trace = temp(["simple", "trace"], Level.top)
    start_measurement("simplification-time")
    run_process_trace(["-o", simplified_trace, "simplify", args.TRACE_FILE])
    end_measurement("simplification-time")

    if args.stats:
        for (ext, trace) in [("trace-size", args.TRACE_FILE),
                             ("simplified-trace-size", simplified_trace)]:
            size = temp([ext], Level.top)
            run_process_trace(["-o", size, "query", "--print-size", trace])
            with open(size, "r") as size_file:
                stats[ext] = int(size_file.readline())

    original_trace = temp(["original", "trace"], Level.top)
    run_process_trace(["-o", original_trace, "record", simplified_trace])

    ex = futures.ThreadPoolExecutor(max_workers=int(args.jobs))

    if args.detailed:
        simple_options = []
    else:
        simple_options = ["--simple"]

    if args.level in [u.arg_heuristic, u.arg_eager]:

        iteration = 1
        patterns_csv = temp(["patterns", "csv"], Level.top)
        run_process_matches(["-o", patterns_csv] + simple_options)

        while True:

            iterdir = os.path.join(basedir, str(iteration))
            os.mkdir(iterdir)
            canddir = os.path.join(iterdir, "candidates")
            os.mkdir(canddir)

            decompose_options = ["--output-dir", canddir]
            if iteration > 1:
                decompose_options += ["--no-associative-components"]
            iter_original_trace = temp(["original", "trace"], Level.iteration)
            run_command(["cp", original_trace, iter_original_trace])
            start_measurement("decomposition-time")
            run_process_trace(["decompose"] + \
                              decompose_options + \
                              [iter_original_trace])
            end_measurement("decomposition-time")
            subtrace_ids = set()
            def candidate_traces():
                return glob.glob(os.path.join(canddir, "*.trace"))
            for subtrace in candidate_traces():
                base_subtrace = os.path.basename(os.path.splitext(subtrace)[0])
                [_, first, second] = base_subtrace.rsplit(".", 2)
                if first.isdigit(): # Loop sub-trace
                    subtrace_ids.add((u.loop_subtrace,
                                      (int(first), int(second))))
                else: # Associative component sub-trace
                    subtrace_ids.add((u.associative_component_subtrace,
                                      (first, int(second))))

            # Generate all candidate subtraces eagerly (resulting from applying
            # 'subtract' and 'compose' operations to each pair of sub-traces
            # until a fixpoint is reached).
            if args.level == u.arg_eager:
                def make_subtraction((st1, st2)):
                    def paren(string):
                        return "[" + string + "]"
                    subtract_id = paren(subtrace_id(st1)) + "-" + \
                                  paren(subtrace_id(st2))
                    subtract_subtrace = \
                        temp(["original", subtract_id, "trace"],
                             Level.candidate)
                    run_process_trace(["-o", subtract_subtrace, "subtract",
                                       st1, st2, original_trace])

                # The list conversion is just to force evaluation.
                start_measurement("subtract-time")
                list(ex.map(make_subtraction, [(st1, st2)
                                       for st1 in candidate_traces()
                                       for st2 in candidate_traces()
                                       if st1 != st2]))
                end_measurement("subtract-time")
                exit(0)

            def make_dzn(st):
                compact_st = \
                    temp(["original", subtrace_id(st), "collapsed", "trace"],
                         Level.iteration)
                run_process_trace(["-o", compact_st, "transform",
                                   "--collapse-tags", "all", st])
                compact_st_dzn = \
                    temp(["original", subtrace_id(st), "collapsed", "dzn"],
                         Level.iteration)
                run_process_trace(["-o", compact_st_dzn,
                                   "--output-format=minizinc", "print",
                                   compact_st])

            # The list conversion is just to force evaluation.
            start_measurement("compaction-time")
            list(ex.map(make_dzn, candidate_traces()))
            end_measurement("compaction-time")

            def make_szn((subtrace_id, pattern)):
                pre = subtrace_prefix(subtrace_id)
                compact_subtrace_dzn = \
                    temp(pre + ["collapsed", "dzn"], Level.iteration)
                compact_subtrace_pattern_szn = \
                    temp(pre + ["collapsed", pattern + "s", "szn"],
                         Level.iteration)
                run_minizinc(compact_subtrace_pattern_szn,
                             ["--time-limit", "60000", "-a", "--solver",
                              "chuffed", mzn(pattern), compact_subtrace_dzn])

            # The list conversion is just to force evaluation.
            start_measurement("matching-time")
            list(ex.map(make_szn,
                        [(st, p)
                         for st in subtrace_ids
                         for p  in applicable_patterns(subtrace_type(st))]))
            end_measurement("matching-time")

            def subtrace_szn_files(st_type):
                return [temp(subtrace_prefix(st) + \
                             ["collapsed", p + "s", "szn"], Level.iteration)
                        for st in subtrace_ids
                        for p in  applicable_patterns(st_type)
                        if subtrace_type(st) == st_type]

            def update_patterns_csv(new):
                tmp_csv = temp(["tmp", "csv"], Level.iteration)
                run_merge_matches([patterns_csv, new, "-o", tmp_csv] + \
                                  simple_options)
                run_command(["mv", tmp_csv, patterns_csv])

            loop_szn_files = subtrace_szn_files(u.loop_subtrace)
            loop_csv = temp(["loops", "csv"], Level.iteration)
            run_process_matches(loop_szn_files + \
                                ["-o", loop_csv] + \
                                simple_options)
            update_patterns_csv(loop_csv)
            associative_component_szn_files = \
                subtrace_szn_files(u.associative_component_subtrace)
            associative_component_csv = \
                temp(["associative_components", "csv"], Level.iteration)
            instructions = temp(["instructions"], Level.iteration)
            run_process_matches(associative_component_szn_files +
                                ["-o", associative_component_csv,
                                 "--matched-instructions-prefix", iterdir] + \
                                simple_options)
            update_patterns_csv(associative_component_csv)
            if not os.path.isfile(instructions):
                break

            subtracted_trace = \
                temp(["original", "subtracted", "trace"], Level.iteration)
            start_measurement("subtraction-time")
            run_process_trace(["-o", subtracted_trace, "transform",
                               "--filter-out-instructions", instructions,
                               original_trace])
            end_measurement("subtraction-time")

            if filecmp.cmp(original_trace, subtracted_trace):
                break
            # TODO: move directly to next iteration's directory.
            run_command(["mv", subtracted_trace, original_trace])
            iteration += 1

        for line in open(patterns_csv, "r"):
            print line,

    elif args.level == u.arg_complete:

        simple_dzn = temp(["original", "dzn"], Level.top)
        run_process_trace(["-o", simple_dzn, "--output-format=minizinc", "print",
                           original_trace])

        def make_szn(pattern):
            simple_pattern_szn = \
                temp(["original", pattern + "s", "szn"], Level.top)
            run_minizinc(simple_pattern_szn,
                         ["-a", "--solver", "chuffed", mzn(pattern),
                          simple_dzn])

        # The list conversion is just to force evaluation.
        start_measurement("matching-time")
        list(ex.map(make_szn, u.pat_all))
        end_measurement("matching-time")

        szn_files = \
            [temp(["original", p + "s", "szn"], Level.top) for p in u.pat_all]
        run_process_matches(szn_files + simple_options)

finally:
    if args.clean:
        shutil.rmtree(basedir)
    if args.stats:
        finding_end = time.time()
        with open(args.stats ,"w+") as stats_out:
            stats["finding-time"] = finding_end - finding_start
            st_writer = csv.writer(stats_out, delimiter=",",
                                   quoting=csv.QUOTE_MINIMAL)
            st_writer.writerow(["measurement", "value"])
            for (measurement, value) in stats.iteritems():
                st_writer.writerow([measurement, value])
