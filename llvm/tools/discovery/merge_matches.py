#!/usr/bin/python

import argparse
import os
import glob
import csv
import sys
import re
from sets import Set

# Note: this is taken from https://stackoverflow.com/a/16090640.
def natural_sort_key(s, _nsre=re.compile('([0-9]+)')):
    return [int(text) if text.isdigit() else text.lower()
            for text in _nsre.split(s)]

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

def merge_data(legend, data1, data2):
    benchmark_index = legend.index("benchmark")
    mode_index = legend.index("mode")
    location_index = legend.index("location")
    merged = data1 + data2
    ordered = sorted(merged, key = lambda line:
                     (line[benchmark_index],
                      line[mode_index],
                      natural_sort_key(line[location_index])))
    return ordered

def main(args):

    parser = argparse.ArgumentParser(description='Merge and sort CSV pattern match tables.')
    parser.add_argument('RESULTS_FILES', nargs="*")
    args = parser.parse_args(args)

    assert(len(args.RESULTS_FILES) >= 2)

    legend = load_legend(args.RESULTS_FILES[0])
    merged = load_data(args.RESULTS_FILES[0])
    for file in args.RESULTS_FILES[1:]:
        data = load_data(file)
        merged = merge_data(legend, merged, data)

    csvwriter = csv.writer(sys.stdout, delimiter=",", quoting=csv.QUOTE_MINIMAL)
    csvwriter.writerow(legend)
    for line in merged:
        csvwriter.writerow(line)

if __name__ == '__main__':
    main(sys.argv[1:])
