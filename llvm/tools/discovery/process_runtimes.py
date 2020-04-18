#!/usr/bin/python

import argparse
import os
import glob
import csv
import sys
from sets import Set
from numpy import median

def unique(items):
    found = set([])
    keep = []
    for item in items:
        if item not in found:
            found.add(item)
            keep.append(item)
    return keep

def data_range(x):
    return max(x) - min(x)

def process_runtimes(results_file):

    # Multi-level map: input -> nproc -> key -> measurements.
    data = {}

    r = csv.reader(open(sys.argv[1]), delimiter=",")
    legend = r.next()
    input_index = 0
    nproc_index = 1
    repetition_index = 2
    first_measurement_index = 3
    measurement_keys = legend[first_measurement_index:]
    inputs = []
    nprocs = []
    for line in r:
        input  = line[input_index]
        nproc = int(line[nproc_index])
        repetition = line[repetition_index]
        measurements = line[first_measurement_index:]
        inputs.append(input)
        nprocs.append(nproc)
        # Create keys at all levels first if not present.
        if not input in data:
            data[input] = dict()
        if not nproc in data[input]:
            data[input][nproc] = dict()
        for key, measurement in zip(measurement_keys, measurements):
            if not key in data[input][nproc]:
                data[input][nproc][key] = set()
            # Finally populate.
            data[input][nproc][key].add(float(measurement))

    results = []
    for input in unique(inputs):
        input_data = data[input]
        for nproc in sorted(unique(nprocs)):
            nproc_data = input_data[nproc]
            ag_results = []
            for key in measurement_keys:
                measurements = nproc_data[key]
                key_median        = median(list(measurements))
                key_range         = data_range(measurements)
                key_range_percent = key_range / key_median
                ag_results.append((key, {"median" : key_median,
                                         "range" : key_range,
                                         "range_percent" : key_range_percent}))
            row = {"input" : input,
                   "nproc" : nproc,
                   "data"  : ag_results}
            results.append(row)
    return results

def main(args):

    parser = argparse.ArgumentParser(description='Aggregate runtimes from multiple repetitions into a CSV table.')
    parser.add_argument('FILE')
    args = parser.parse_args(args)

    # Gather results.
    results = process_runtimes(args.FILE)
    measures = ["median", "range", "range_percent"]

    legend = ["input", "nproc"]
    line = list(results)[0]
    keys = []
    for (key, _) in line["data"]:
        keys.append(key)
    for suffix in ["", "-range", "-range-percent"]:
        for (key, _) in line["data"]:
            legend.append(key + suffix)

    # Print results in a level-independent manner.
    csvwriter = csv.writer(sys.stdout, delimiter=",", quoting=csv.QUOTE_MINIMAL)
    csvwriter.writerow(legend)

    for r in results:
        row = [r["input"], r["nproc"]]
        for measure in measures:
            for (key, data) in r["data"]:
                row.append(data[measure])
        csvwriter.writerow(row)

if __name__ == '__main__':
    main(sys.argv[1:])
