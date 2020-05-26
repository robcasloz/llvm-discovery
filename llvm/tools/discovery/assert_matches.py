#!/usr/bin/python

import argparse
import csv
import sys

import trace_utils as u

def match_name(p, m):
    if m == "1":
        return p
    else:
        assert m == "~"
        return p + " (partial)"

parser = argparse.ArgumentParser(description='Asserts that an expected pattern is found.')
parser.add_argument('RESULTS_FILE')
parser.add_argument('BENCHMARK_MODE')
parser.add_argument('LOCATION')
parser.add_argument('--matches', nargs="*", help='patterns expected to be matched')
parser.add_argument('--loop', help='whether the location specifies a loop', dest='loop', action='store_true', default=False)
parser.add_argument('--iteration', help='iteration expected to be matched')
args = parser.parse_args()

expected_matches = set(args.matches if args.matches else [])

r = csv.reader(open(args.RESULTS_FILE), delimiter=",")
legend = r.next()
benchmark_index = legend.index("benchmark")
mode_index = legend.index("mode")
location_index = legend.index("location")
loops_index = legend.index("loops")
iteration_index = legend.index("iteration")
map_index = legend.index(u.pat_map)
conditional_map_index = legend.index(u.pat_conditional_map)
linear_reduction_index = legend.index(u.pat_linear_reduction)
tiled_reduction_index = legend.index(u.pat_tiled_reduction)
linear_map_reduction_index = legend.index(u.pat_linear_map_reduction)
tiled_map_reduction_index = legend.index(u.pat_tiled_map_reduction)
found = False
occurrence = 0

def matches(line):
    if args.loop and line[loops_index] != args.LOCATION:
        return False
    if not args.loop and line[location_index] != args.LOCATION:
        return False
    if args.iteration and int(line[iteration_index]) != int(args.iteration):
        return False
    return True

for line in r:
    benchmark = line[benchmark_index]
    mode = line[mode_index]
    if "-".join([benchmark, mode]) == args.BENCHMARK_MODE and \
       matches(line):
        actual_results = [(u.pat_map, line[map_index]),
                          (u.pat_conditional_map, line[conditional_map_index]),
                          (u.pat_linear_reduction, line[linear_reduction_index]),
                          (u.pat_tiled_reduction, line[tiled_reduction_index]),
                          (u.pat_linear_map_reduction, line[linear_map_reduction_index]),
                          (u.pat_tiled_map_reduction, line[tiled_map_reduction_index])]
        actual_matches = set([match_name(p, m) for (p, m) in actual_results
                              if m in [u.match_full, u.match_partial]])
        if actual_matches == expected_matches:
            exit(0)
sys.stderr.write("The specified pattern was not found\n")
exit(1)
