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

def run_process_trace(arguments):
    if args.verbose:
        sys.stderr.write(indir("process_trace.py") + " " + " ".join(arguments) + eol)
    pt.main(arguments)

def run_process_matches(arguments):
    if args.verbose:
        sys.stderr.write(indir("process_matches.py") + " " + " ".join(arguments) + eol)
    pm.main(arguments)

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

    def subtrace_prefix((loop, run)):
        return ["simple", str(loop), str(run)]

    simplified_trace = temp(["simple", "trace"])
    run_process_trace(["-o", simplified_trace, "--output-format=plain",
                       "simplify", args.TRACE_FILE])

    ex = futures.ThreadPoolExecutor(max_workers=int(args.jobs))

    if args.level == u.arg_heuristic:

        run_process_trace(["decompose", "--no-associative-components",
                           simplified_trace])
        subtrace_ids = set()
        for subtrace in (set(glob.glob(os.path.join(basedir, "*.trace"))) \
                         - set([simplified_trace])):
            base_subtrace = os.path.basename(os.path.splitext(subtrace)[0])
            [_, l, r] = base_subtrace.rsplit(".", 2)
            subtrace_ids.add((int(l), int(r)))

        def make_dzn(subtrace_id):
            pre = subtrace_prefix(subtrace_id)
            subtrace = temp(pre + ["trace"])
            compact_subtrace = temp(pre + ["collapsed", "trace"])
            run_process_trace(["-o", compact_subtrace, "--output-format=plain",
                               "transform", "--collapse-tags", "all", subtrace])
            compact_subtrace_dzn = temp(pre + ["collapsed", "dzn"])
            run_process_trace(["-o", compact_subtrace_dzn,
                               "--output-format=minizinc",
                               "--match-regions-only", "print",
                               compact_subtrace])

        # The list conversion is just to force evaluation.
        list(ex.map(make_dzn, subtrace_ids))
        #exit(0)
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
                    [(st, p) for st in subtrace_ids for p in u.pat_all_uni]))

        szn_files = [temp(subtrace_prefix(st) + ["collapsed", p + "s", "szn"])
                     for st in subtrace_ids for p in u.pat_all_uni]
        run_process_matches(szn_files + ["-l", u.arg_loop, "--simple"])

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
