#!/usr/bin/python

import argparse
import os
import glob
import csv
import sys
from sets import Set
from numpy import median, percentile

def file_info(stats_filename):
    [base, suffix] = os.path.basename(stats_filename).split(".", 1)
    [benchmark, mode, repetition] = base.rsplit("-", 2)
    return (benchmark, mode, int(repetition), suffix)

def process_stats(stats_files):
    # Multi-level map: benchmark -> mode -> repetition -> stats entries.
    data = {}

    # Populate the map loading each stats file. A stats file is expected to be
    # called [BENCHMARK]-[MODE]-[REPETITION].[SUFFIX], where:
    #
    # BENCHMARK is the benchmark name (e.g. c-ray)
    # MODE is the benchmark mode (e.g. pthread)
    # REPETITION is the repetition number (e.g. 2)
    # SUFFIX is the file suffix (e.g. tracing.time or simple.size)
    for filename in stats_files:
        if os.path.isfile(filename) and \
           (filename.endswith(".size") or filename.endswith(".time")):
            # Gather all data.
            (benchmark, mode, repetition, suffix) = file_info(filename)
            with open(filename, "r") as datafile:
                for line in datafile:
                    if suffix.endswith("time"):
                        point = float(line)
                    elif suffix.endswith("size"):
                        point = int(line)
                    else:
                        assert(False)
                    break
            # Create keys at all levels first if not present.
            if not benchmark in data:
                data[benchmark] = dict()
            if not mode in data[benchmark]:
                data[benchmark][mode] = dict()
            if not repetition in data[benchmark][mode]:
                data[benchmark][mode][repetition] = dict()
            # Finally populate.
            data[benchmark][mode][repetition][suffix] = point

    # Aggregate data across repetitions.
    # Multi-level map: benchmark -> mode -> aggregated stats entries.
    ag_data = {}
    for (benchmark, benchmark_data) in data.iteritems():
        ag_data[benchmark] = dict()
        for (mode, mode_data) in benchmark_data.iteritems():
            ag_data[benchmark][mode] = dict()
            for (repetition, repetition_data) in sorted(mode_data.iteritems()):
                for (suffix, point) in repetition_data.iteritems():
                    if not suffix in ag_data[benchmark][mode]:
                        ag_data[benchmark][mode][suffix] = []
                    ag_data[benchmark][mode][suffix].append(point)

    results = []
    for (benchmark, benchmark_data) in sorted(ag_data.iteritems()):
        for (mode, mode_data) in sorted(benchmark_data.iteritems()):
            ddg_size = median(mode_data["size"])
            simple_ddg_size = median(mode_data["simple.size"])
            [total_time_q1, total_time, total_time_q3] = \
                percentile(mode_data["total.time"], [25, 50, 75])
            total_time_iqr = total_time_q3 - total_time_q1
            total_time_robustcv = 0.75 * (total_time_iqr / total_time)
            tracing_time = median(mode_data["tracing.time"])
            matching_time = median(mode_data["matching.time"])
            row = {"benchmark" : benchmark,
                   "mode" : mode,
                   "ddg-size" : ddg_size,
                   "simple-ddg-size" : simple_ddg_size,
                   "total-time" : total_time,
                   "total-time-iqr" : total_time_iqr,
                   "total-time-robustcv" : total_time_robustcv,
                   "tracing-time" : tracing_time,
                   "matching-time" : matching_time}
            results.append(row)
    return results

def main(args):

    parser = argparse.ArgumentParser(description='Aggregate benchmark-iteration level stats into a CSV table.')
    parser.add_argument('FILES', nargs="*")
    args = parser.parse_args(args)

    # Gather results.
    results = process_stats(args.FILES)

    # Print results in a level-independent manner.
    csvwriter = csv.writer(sys.stdout, delimiter=",", quoting=csv.QUOTE_MINIMAL)
    legend = ["benchmark", "mode", "ddg-size", "simple-ddg-size", "total-time",
              "total-time-iqr", "total-time-robustcv", "tracing-time",
              "matching-time"]
    csvwriter.writerow(legend)

    # Sort results.
    k = (lambda r: (r["benchmark"], r["mode"]))
    results.sort(key = k)

    for r in results:
        csvwriter.writerow([r[k] for k in legend])

if __name__ == '__main__':
    main(sys.argv[1:])
