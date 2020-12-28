#!/usr/bin/env python3

import argparse
import csv
import sys

parser = argparse.ArgumentParser(description='Checks that the expected entries match a results file.')
parser.add_argument('RESULTS_FILE')
parser.add_argument('EXPECTATIONS_FILE')
parser.add_argument('--benchmarks', nargs="*", help='benchmarks that should be checked in the results file')
parser.add_argument('--source', help='source of the expectations to be checked')
args = parser.parse_args()

def match_fields(r0, e0):
    if e0 == "*":
        return True
    return r0 == e0

def match_entries(r, e):
    for (r0, e0) in zip(r, e):
        if not match_fields(r0, e0):
            return False
    return True

def match(results, e, ex):
    found = False
    for r in results:
        if match_entries(r, e):
            found = True
            break
    if ex == "match":
        return found
    elif ex == "no-match":
        return not found
    else:
        assert(False)

def load(f, benchmarks, source, expected):
    r = csv.reader(open(f), delimiter=",")
    legend = next(r)
    benchmark_index = legend.index("benchmark")
    mode_index = legend.index("mode")
    location_index = legend.index("location")
    loops_index = legend.index("loops")
    iteration_index = legend.index("iteration")
    patterns_index = legend.index("patterns")
    if expected:
        expected_index = legend.index("expected")
        action_index   = legend.index("action")
        source_index   = legend.index("source")
    out = []
    for line in r:
        benchmark_mode = line[benchmark_index] + "-" + line[mode_index]
        if not benchmark_mode in benchmarks:
            continue
        if expected and source and (not line[source_index] == source):
            continue
        if expected and (not line[expected_index] or not line[action_index]):
            continue
        entry = (line[benchmark_index],
                 line[mode_index],
                 line[location_index],
                 line[loops_index],
                 line[iteration_index],
                 line[patterns_index])
        if expected:
            out.append((entry, line[expected_index], line[source_index], line[action_index]))
        else:
            out.append(entry)
    return (out, legend)

results, _       = load(args.RESULTS_FILE,      args.benchmarks, args.source, False)
expected, legend = load(args.EXPECTATIONS_FILE, args.benchmarks, args.source, True)

total = len(expected)
mismatches = []
ignored    = 0

for (e, ex, s, a) in expected:
    if a == "ignore":
        ignored += 1
        continue
    match_result = match(results, e, ex)
    if not match_result:
        mismatches.append(e + (ex, s, a, ""))

mism    = len(mismatches)
matches = total - (mism + ignored)

print((str(total)   + " total: " + \
       str(matches) + " matches, " + \
       str(mism) + " mismatches, " + \
       str(ignored) + " ignored"))

if mismatches:
    print("mismatches:")
    csvw = csv.writer(sys.stdout, delimiter=",", quoting=csv.QUOTE_MINIMAL)
    csvw.writerow(legend)
    for e in mismatches:
        csvw.writerow(e)
    exit(1)

exit(0)
