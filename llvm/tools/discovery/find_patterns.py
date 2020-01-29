#!/usr/bin/python

import argparse
import tempfile
import os
import subprocess
import sys
from concurrent import futures
import multiprocessing
import shutil

import trace_utils as u
import process_trace as pt
import process_matches as pm

eol = "\n"

parser = argparse.ArgumentParser(description='Find parallel patterns in the given trace.')
parser.add_argument('TRACE_FILE')
parser.add_argument('-l,', '--level', dest='level', action='store', type=str, choices=[u.arg_loop, u.arg_instruction], default=u.arg_loop)
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

def run_minizinc(arguments):
    if args.verbose:
        sys.stderr.write("minizinc " + " ".join(arguments) + eol)
    try:
        p = subprocess.Popen(["minizinc"] + arguments, stdout=subprocess.PIPE)
        p.wait()
    except OSError:
        sys.stderr.write("Error: could not find 'dot' executable\n")
        sys.exit(-1)

basedir = tempfile.mkdtemp(prefix = "discovery-")
base = os.path.splitext(os.path.basename(args.TRACE_FILE))[0]

def temp(extension):
    return os.path.join(basedir, ".".join([base] + extension))

def indir(filename):
    return os.path.join(sys.path[0], filename)

def mzn(pattern):
    return indir(pattern + ".mzn")

simple_trace = temp(["simple", "trace"])
run_process_trace(["-o", simple_trace, "--output-format=plain", "simplify",
                   args.TRACE_FILE])

ex = futures.ThreadPoolExecutor(max_workers=int(args.jobs))

if args.level == u.arg_loop:

    simple_tags = temp(["simple", "tags"])
    run_process_trace(["-o", simple_tags, "query", "--print-tags",
                       simple_trace])

    tags = set()
    with open(simple_tags, "r") as st:
        for line in st:
            tags.add(int(line))

    def make_dzn(tag):
        t = str(tag)
        pre = ["simple", t]
        simple_tag_trace = temp(pre + ["trace"])
        run_process_trace(["-o", simple_tag_trace, "--output-format=plain",
                           "transform", "--filter-tags", t, simple_trace])
        simple_tag_collapsed_trace = temp(pre + ["collapsed", "trace"])
        run_process_trace(["-o", simple_tag_collapsed_trace,
                           "--output-format=plain", "transform",
                           "--collapse-tags", "all", simple_tag_trace])
        simple_tag_collapsed_dzn = temp(pre + ["collapsed", "dzn"])
        run_process_trace(["-o", simple_tag_collapsed_dzn,
                           "--output-format=minizinc", "print",
                           simple_tag_collapsed_trace])

    # The list conversion is just to force evaluation.
    list(ex.map(make_dzn, tags))

    def make_szn((tag, pattern)):
        t = str(tag)
        pre = ["simple", t]
        simple_tag_collapsed_dzn = temp(pre + ["collapsed", "dzn"])
        simple_tag_collapsed_pattern_szn = \
            temp(pre + ["collapsed", pattern + "s", "szn"])
        run_minizinc(["-o", simple_tag_collapsed_pattern_szn, "-a", "--solver",
                      "chuffed", mzn(pattern), simple_tag_collapsed_dzn])

    # The list conversion is just to force evaluation.
    list(ex.map(make_szn, [(t, p) for t in tags for p in u.pat_all_uni]))

    szn_files = [temp(["simple", str(t), "collapsed", p + "s", "szn"])
                 for t in tags for p in u.pat_all_uni]
    run_process_matches(szn_files + ["-l", u.arg_loop, "--simple"])

elif args.level == u.arg_instruction:

    simple_dzn = temp(["simple", "dzn"])
    run_process_trace(["-o", simple_dzn, "--output-format=minizinc", "print",
                       simple_trace])

    def make_szn(pattern):
        simple_pattern_szn = temp(["simple", pattern + "s", "szn"])
        run_minizinc(["-o", simple_pattern_szn, "-a", "--solver", "chuffed",
                      mzn(pattern), simple_dzn])

    # The list conversion is just to force evaluation.
    list(ex.map(make_szn, u.pat_all))

    szn_files = [temp(["simple", p + "s", "szn"]) for p in u.pat_all]
    run_process_matches(szn_files + ["-l", u.arg_instruction, "--simple"])

if args.clean:
    shutil.rmtree(basedir)
