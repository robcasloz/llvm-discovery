#!/usr/bin/env python3

import argparse
import os
import glob
import csv
import sys
from sets import Set
from numpy import percentile

def unique(items):
    found = set([])
    keep = []
    for item in items:
        if item not in found:
            found.add(item)
            keep.append(item)
    return keep

def process_runtimes(results_file):

    # Multi-level map: input -> nproc -> key -> measurements.
    data = {}

    r = csv.reader(open(sys.argv[1]), delimiter=",")
    legend = next(r)
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
                [q1, median, q3] = percentile(list(measurements), [25, 50, 75])
                iqr = q3 - q1
                # Robust CV as introduced by Shapiro, 2003.
                robustcv = 0.75 * (iqr / median)
                ag_results.append((key, {"median"   : median,
                                         "iqr"      : iqr,
                                         "robustcv" : robustcv}))
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
    measures = ["median", "iqr", "robustcv"]

    legend = ["input", "nproc"]
    line = list(results)[0]
    keys = []
    for (key, _) in line["data"]:
        keys.append(key)
    for suffix in ["", "-iqr", "-robustcv"]:
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
