#!/usr/bin/python

import argparse
import os
import glob
import csv
import sys
import re
from sets import Set
import trace_utils as u

def load_legend(file):
    r = csv.reader(open(file), delimiter=",")
    return r.next()

def load_data(file):
    r = csv.reader(open(file), delimiter=",")
    # Skip legend.
    r.next()
    data = []
    for line in r:
        data.append(line)
    return data

def merge_data(legend, data1, data2, sort, simple):
    location_index = legend.index("location")
    if not simple:
        benchmark_index = legend.index("benchmark")
        mode_index = legend.index("mode")
        nodes_index = legend.index("nodes")
    merged = data1 + data2
    if simple: # Ignore sorting criteria, sort solely by location.
        k = (lambda r: u.natural_sort_key(r[location_index]))
    else:
        if sort == u.arg_nodes:
            k = (lambda r: (r[benchmark_index], r[mode_index],
                            -int(r[nodes_index])))
        elif sort == u.arg_location:
            k = (lambda r: (r[benchmark_index], r[mode_index],
                            u.natural_sort_key(r[location_index])))
    merged.sort(key = k)
    return merged

def main(args):

    parser = argparse.ArgumentParser(description='Merge and sort CSV pattern match tables.')
    parser.add_argument('RESULTS_FILES', nargs="*")
    parser.add_argument('--simple', dest='simple', action='store_true', default=False)
    parser.add_argument('-s,', '--sort', dest='sort', action='store', type=str, choices=[u.arg_nodes, u.arg_location], default=u.arg_nodes)
    args = parser.parse_args(args)

    assert(len(args.RESULTS_FILES) >= 2)

    legend = load_legend(args.RESULTS_FILES[0])
    merged = load_data(args.RESULTS_FILES[0])
    for file in args.RESULTS_FILES[1:]:
        data = load_data(file)
        merged = merge_data(legend, merged, data, args.sort, args.simple)

    csvwriter = csv.writer(sys.stdout, delimiter=",", quoting=csv.QUOTE_MINIMAL)
    csvwriter.writerow(legend)
    for line in merged:
        csvwriter.writerow(line)

if __name__ == '__main__':
    main(sys.argv[1:])
