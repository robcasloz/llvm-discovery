#!/usr/bin/env python3

import sys
import os
import argparse
import subprocess
import filecmp
import glob
from concurrent import futures
import multiprocessing

patterns = ["map", "linear_reduction", "linear_scan", "conditional_linear_scan",
            "pipeline", "tiled_reduction", "linear_map_reduction",
            "tiled_map_reduction"]

test_cases = {
    "map" : [
        "map",
        "list-map",
        "map-reduction",
        "complex-map",
        "map-reduction-list",
        "map-reduction-parallel",
        "fused-map"
    ],
    "linear_reduction" : [
        "complex-reduction",
        "list-reduction",
        "map-reduce-nodata",
        "reduction-branch",
        "reduction",
        "reduction-max",
        "double-reduction",
        "reduction-coarse"
    ],
    "linear_scan" : [
        "scan"
    ],
    "conditional_linear_scan" : [
        "conditional-scan"
    ],
    "pipeline" : [
        "sequential-pipe",
        "complex-pipe"
    ],
    "tiled_reduction" : [
        "reduction-parallel"
    ],
    "linear_map_reduction" : [
        "linear-mapreduce"
    ],
    "tiled_map_reduction" : [
        "mapreduce"
    ]

}

test_input_dir = os.path.join("test", "input")
test_output_dir = os.path.join("test", "output")

parser = argparse.ArgumentParser(description='Tests the pattern finder through its Makefile interface.')
parser.add_argument('--no-clean', dest='clean', action='store_false', help='do not clean temporary files')
parser.add_argument('--verbose', dest='verbose', action='store_true', help='print stdout of executed commands')
parser.add_argument('--update', dest='update', action='store_true', help='update expected results with the actual results of the test run', default=False)
parser.add_argument('-j', '--jobs', metavar='N', type=int)
parser.set_defaults(clean=True,
                    verbose=False,
                    update=False,
                    jobs=multiprocessing.cpu_count())

args = parser.parse_args(sys.argv[1:])

def run_and_print(cmd, check = True):
    if args.verbose:
        print(" ".join(cmd))
    if check:
        out = subprocess.check_output(cmd)
    else:
        p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                             text=True)
        out, _ = p.communicate()
    if args.verbose:
        print(out)
    return out

def read_normalize_write(source, pattern, destination):
    lines = set()
    with open(source) as s:
        for line in s:
            if pattern in line:
                lines.add(line)
    with open(destination, 'w') as d:
        d.writelines(sorted(lines))

def run_test(instance):
    (p, t) = instance
    szn = os.path.join(test_input_dir, t + ".simple." + p + "s.szn")
    run_and_print(["make", szn])
    short_szn = t + "." + p + "s.szn"
    actual = os.path.join(test_output_dir, short_szn + ".actual")
    read_normalize_write(szn, p, actual)
    expected = os.path.join(test_output_dir, short_szn + ".expected")
    if args.update:
        read_normalize_write(szn, p, expected)
    if filecmp.cmp(actual, expected):
        passed = True
    else:
        passed = False
    return ((p, t), passed)

def clean_files():
    files = []
    for file_pattern in ["trace", "*.bin", "*.trace", "*.dzn", "*.szn"]:
        files += glob.glob(os.path.join(test_input_dir, file_pattern))
    for file_pattern in ["*.actual"]:
        files += glob.glob(os.path.join(test_output_dir, file_pattern))
    if files:
        run_and_print(["rm", "-rf"] + files)

try:

    clean_files()

    for p in patterns:
        for t in test_cases[p]:
            trace = t + ".trace"
            run_and_print(["make", os.path.join(test_input_dir, trace)])

    ex = futures.ThreadPoolExecutor(max_workers=int(args.jobs))
    passed = dict(ex.map(run_test,
                         [(p, t) for p in patterns for t in test_cases[p]]))

    max_len = 0
    for p in patterns:
        for t in test_cases[p]:
            if len(t) > max_len:
                max_len = len(t)

    total_tests = 0
    total_pass = 0
    for p in patterns:
        for t in test_cases[p]:
            print((t + ":").ljust(max_len + 1), end=' ')
            if passed[(p, t)]:
                print("pass")
                total_pass += 1
            else:
                print("fail")
            total_tests += 1
    print("---")
    print((str(total_tests) + " tests: " + \
           str(total_pass) + " pass, " + \
           str(total_tests - total_pass) + " fail"))

finally:
    if args.clean:
        clean_files()
