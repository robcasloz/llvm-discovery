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
parser.add_argument('FUNCTION')
parser.add_argument('--matches', nargs="*", help='patterns (doall, map, reduction, scan) expected to be matched')
args = parser.parse_args()

expected_matches = set(args.matches if args.matches else [])

r = csv.reader(open(args.RESULTS_FILE), delimiter=",")
legend = r.next()
benchmark_index = legend.index("benchmark")
mode_index = legend.index("mode")
location_index = legend.index("location")
function_index = legend.index("function")
doall_index = legend.index(u.pat_doall)
map_index = legend.index(u.pat_map)
mapfilter_index = legend.index(u.pat_mapfilter)
reduction_index = legend.index(u.pat_reduction)
scan_index = legend.index(u.pat_scan)
found = False
for line in r:
    benchmark = line[benchmark_index]
    mode = line[mode_index]
    location = line[location_index]
    function = line[function_index]
    if "-".join([benchmark, mode]) == args.BENCHMARK_MODE and \
       location == args.LOCATION and \
       function == args.FUNCTION:
        found = True
        actual_results = [(u.pat_doall, line[doall_index]),
                          (u.pat_map, line[map_index]),
                          (u.pat_mapfilter, line[mapfilter_index]),
                          (u.pat_reduction, line[reduction_index]),
                          (u.pat_scan, line[scan_index])]
        actual_matches = set([match_name(p, m) for (p, m) in actual_results
                              if m in [u.match_full, u.match_partial]])
        assert actual_matches == expected_matches, \
            "the matched patterns " + str(list(actual_matches)) + \
            " differ from the expected ones " + str(list(expected_matches))
        break
if not found:
    assert False, "could not find the given tag"
