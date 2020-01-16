#!/usr/bin/python

import argparse
import csv
import sys

import trace_utils as u

def char2int(c):
    if c == '?':
        return 0
    else:
        return int(c)

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
        map_matched = bool(char2int(line[map_index]))
        doall_matched = bool(char2int(line[doall_index]))
        reduction_matched = bool(char2int(line[reduction_index]))
        scan_matched = bool(char2int(line[scan_index]))
        actual_results = [(u.pat_doall, doall_matched),
                          (u.pat_map, map_matched),
                          (u.pat_reduction, reduction_matched),
                          (u.pat_scan, scan_matched)]
        actual_matches = set(p for (p, m) in actual_results if m)
        assert actual_matches == expected_matches, \
            "the matched patterns " + str(list(actual_matches)) + \
            " differ from the expected ones " + str(list(expected_matches))
        break
if not found:
    assert False, "could not find the given tag"
