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

import trace_utils as u
import process_trace as pt
import process_matches as pm
import merge_matches as mm

eol = "\n"

parser = argparse.ArgumentParser(description='Find parallel patterns in the given trace.')
parser.add_argument('TRACE_FILE')
parser.add_argument('-l,', '--level', dest='level', action='store', type=str, choices=[u.arg_heuristic, u.arg_complete], default=u.arg_heuristic)
parser.add_argument('-v', '--verbose', action='store_true')
parser.add_argument('-j', '--jobs', metavar='N', type=int)
parser.add_argument('--clean', dest='clean', action='store_true')
parser.add_argument('--no-clean', dest='clean', action='store_false')
parser.set_defaults(jobs=multiprocessing.cpu_count())
parser.set_defaults(clean=True)

args = parser.parse_args()

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

try:

    def temp(extension):
        return os.path.join(basedir, ".".join([base] + extension))

    def indir(filename):
        return os.path.join(sys.path[0], filename)

    def mzn(pattern):
        return indir(pattern + ".mzn")

    def subtrace_type((st_type, _)):
        return st_type

    def subtrace_prefix((st_type, (first, second))):
        if st_type == u.loop_subtrace:
            suffix = [str(first), str(second)]
        else:
            suffix = [first, str(second)]
        return ["simple"] + suffix

    def applicable_patterns(st_type):
        if st_type == u.loop_subtrace:
            return u.pat_all_uni
        elif st_type == u.associative_component_subtrace:
            return u.pat_all_associative

    simplified_trace = temp(["simple", "trace"])
    run_process_trace(["-o", simplified_trace, "--output-format=plain",
                       "simplify", args.TRACE_FILE])

    ex = futures.ThreadPoolExecutor(max_workers=int(args.jobs))

    if args.level == u.arg_heuristic:

        run_process_trace(["decompose", simplified_trace])
        subtrace_ids = set()
        for subtrace in (set(glob.glob(os.path.join(basedir, "*.trace"))) \
                         - set([simplified_trace])):
            base_subtrace = os.path.basename(os.path.splitext(subtrace)[0])
            [_, first, second] = base_subtrace.rsplit(".", 2)
            if first.isdigit(): # Loop sub-trace
                subtrace_ids.add((u.loop_subtrace,
                                  (int(first), int(second))))
            else: # Associative component sub-trace
                subtrace_ids.add((u.associative_component_subtrace,
                                  (first, int(second))))

        def make_dzn(subtrace_id):
            pre = subtrace_prefix(subtrace_id)
            subtrace = temp(pre + ["trace"])
            compact_subtrace = temp(pre + ["collapsed", "trace"])
            if subtrace_type(subtrace_id) == u.loop_subtrace:
                run_process_trace(["-o", compact_subtrace,
                                   "--output-format=plain", "transform",
                                   "--collapse-tags", "all", subtrace])
            else:
                run_command(["cp", subtrace, compact_subtrace])
            compact_subtrace_dzn = temp(pre + ["collapsed", "dzn"])
            if subtrace_type(subtrace_id) == u.loop_subtrace:
                minizinc_dzn_options = ["--match-regions-only"]
            else:
                minizinc_dzn_options = []
            run_process_trace(["-o", compact_subtrace_dzn,
                               "--output-format=minizinc"] + \
                              minizinc_dzn_options + \
                              ["print", compact_subtrace])

        # The list conversion is just to force evaluation.
        list(ex.map(make_dzn, subtrace_ids))

        def make_szn((subtrace_id, pattern)):
            pre = subtrace_prefix(subtrace_id)
            compact_subtrace_dzn = temp(pre + ["collapsed", "dzn"])
            compact_subtrace_pattern_szn = \
                temp(pre + ["collapsed", pattern + "s", "szn"])
            run_minizinc(compact_subtrace_pattern_szn,
                         ["--time-limit", "60000", "-a", "--solver", "chuffed",
                          mzn(pattern), compact_subtrace_dzn])

        # The list conversion is just to force evaluation.
        list(ex.map(make_szn,
                    [(st, p)
                     for st in subtrace_ids
                     for p  in applicable_patterns(subtrace_type(st))]))

        def subtrace_szn_files(st_type):
            return [temp(subtrace_prefix(st) + ["collapsed", p + "s", "szn"])
                    for st in subtrace_ids
                    for p in  applicable_patterns(st_type)
                    if subtrace_type(st) == st_type]

        loop_szn_files = subtrace_szn_files(u.loop_subtrace)
        loop_csv = temp(["loops", "csv"])
        run_process_matches(loop_szn_files + \
                            ["-o", loop_csv, "-l", u.arg_loop, "--simple"])
        associative_component_szn_files = \
            subtrace_szn_files(u.associative_component_subtrace)
        associative_component_csv = temp(["associative_components", "csv"])
        run_process_matches(associative_component_szn_files +
                            ["-o", associative_component_csv, "-l",
                             u.arg_instruction, "--simple"])
        run_merge_matches([loop_csv, associative_component_csv, "--simple"])

    elif args.level == u.arg_complete:

        simple_dzn = temp(["simple", "dzn"])
        run_process_trace(["-o", simple_dzn, "--output-format=minizinc", "print",
                           simplified_trace])

        def make_szn(pattern):
            simple_pattern_szn = temp(["simple", pattern + "s", "szn"])
            run_minizinc(simple_pattern_szn,
                         ["-a", "--solver", "chuffed", mzn(pattern),
                          simple_dzn])

        # The list conversion is just to force evaluation.
        list(ex.map(make_szn, u.pat_all))

        szn_files = [temp(["simple", p + "s", "szn"]) for p in u.pat_all]
        run_process_matches(szn_files + ["-l", u.arg_instruction, "--simple"])

finally:

    if args.clean:
        shutil.rmtree(basedir)
