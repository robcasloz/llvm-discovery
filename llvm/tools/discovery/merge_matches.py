#!/usr/bin/env python3

import argparse
import os
import glob
import csv
import sys
import re
import trace_utils as u

def load_legend(file):
    r = csv.reader(open(file), delimiter=",")
    return tuple(next(r))

def load_data(file):
    r = csv.reader(open(file), delimiter=",")
    # Skip legend.
    next(r)
    data = []
    for line in r:
        data.append(tuple(line))
    return data

def merge_data(legend, data1, data2, sort, simple):
    id_index = legend.index("id")
    location_index = legend.index("location")
    if not simple:
        benchmark_index = legend.index("benchmark")
        mode_index = legend.index("mode")
        nodes_index = legend.index("nodes")
        iteration_index = legend.index("iteration")
        traces_index = legend.index("traces")

    # Remove duplicates: two lines are duplicated if they are all equal except
    # possibly for the 'nodes' and 'trace' columns.
    # TODO: merge similar lines with different patterns matched in different
    # iterations.
    duplicates = set()
    merged = []
    for line in data1 + data2:
        key = list(line)
        if not simple:
            key.pop(iteration_index)
            key.pop(traces_index)
            key.pop(nodes_index)
        if tuple(key) not in duplicates:
            merged.append(line)
            duplicates.add(tuple(key))

    # Sort results according to given criterion.
    if simple:
        k = (lambda r: r[id_index])
    elif sort == u.arg_id:
        k = (lambda r: (r[benchmark_index], r[mode_index], r[id_index]))
    elif sort == u.arg_nodes:
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
    parser.add_argument('-o', "--output-file", help='output file')
    parser.add_argument('--simple', dest='simple', action='store_true', default=False)
    parser.add_argument('-s,', '--sort', dest='sort', action='store', type=str, choices=[u.arg_id, u.arg_nodes, u.arg_location], default=u.arg_id)
    args = parser.parse_args(args)

    assert(len(args.RESULTS_FILES) >= 2)

    legend = load_legend(args.RESULTS_FILES[0])
    merged = load_data(args.RESULTS_FILES[0])
    for file in args.RESULTS_FILES[1:]:
        data = load_data(file)
        merged = merge_data(legend, merged, data, args.sort, args.simple)

    if args.output_file:
        out = open(args.output_file ,"w+")
    else:
        out = sys.stdout
    csvwriter = csv.writer(out, delimiter=",", quoting=csv.QUOTE_MINIMAL)
    csvwriter.writerow(legend)
    for line in merged:
        csvwriter.writerow(line)
    if args.output_file:
        out.close()

if __name__ == '__main__':
    main(sys.argv[1:])
