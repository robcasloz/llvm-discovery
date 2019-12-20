#!/usr/bin/python

import argparse
import os
import glob
import csv
import sys
from sets import Set

import trace_utils as u

def match_to_digit((matches, status)):
    if status == u.tk_sol_status_unknown:
        return "?"
    elif status == u.tk_sol_status_error and not matches:
        return "?"
    return str(int(matches))

def file_info(szn_filename):
    file_components = szn_filename.split(".")
    base_file_components = os.path.basename(szn_filename).split(".")
    if "-seq" in base_file_components[0] or \
       "-pthread" in base_file_components[0]:
        [benchmark, mode] = base_file_components[0].rsplit("-", 1)
    else:
        benchmark = base_file_components[0]
        mode = "unknown"
    pattern = base_file_components[-2][0:-1]
    maybe_tag = map(int, [component for component in base_file_components
                          if component.isdigit()])
    if maybe_tag:
        tag = maybe_tag[0]
    else:
        tag = None
    trace_filename = ".".join(file_components[0:-2]) + ".trace"
    return (benchmark, mode, tag, pattern, trace_filename)

def process_loop_matches(szn_files, simple):

    # Cache of demangled function names.
    demangled_cache = {}

    # Multi-level map: benchmark -> mode -> tag -> pattern match entries.
    data = {}

    # Populate the map loading each solution file. A solution file is expected
    # to be called [BENCHMARK]-[MODE] ... [TAG_ID] ... [PATTERN].szn, where:
    #
    # BENCHMARK is the benchmark name (e.g. c-ray)
    # MODE is the benchmark mode (e.g. pthread)
    # TAG_ID is the loop tag id (e.g. 5)
    # PATTERN is the pattern that is matched (e.g. reductions)
    #
    # For each solution file, a corresponding trace called
    # [BENCHMARK]-[MODE] ... [TAG_ID] ... .trace is expected.
    for filename in szn_files:
        if os.path.isfile(filename) and filename.endswith(".szn"):
            # Gather all data.
            (benchmark, mode, tag, pattern, trace_filename) = \
                file_info(filename)
            G = u.read_trace(trace_filename)
            [internal_tag_id] = list(u.tag_set(G))
            (_, __, ___, PT) = G
            tag_alias = PT[internal_tag_id].get(u.tk_alias)
            [src_file, src_function, src_line, src_col] = tag_alias.split(":")
            location = ":".join([os.path.basename(src_file), src_line] + \
                                ([] if simple else [src_col]))
            function = u.demangle(src_function, demangled_cache)
            nodes = int(PT[internal_tag_id].get(u.tk_original_blocks))
            (_, matches, status) = u.read_matches(filename)
            match = (len(matches) > 0, status)
            # Create keys at all levels first if not present.
            if not benchmark in data:
                data[benchmark] = dict()
            if not mode in data[benchmark]:
                data[benchmark][mode] = dict()
            if not tag in data[benchmark][mode]:
                data[benchmark][mode][tag] = (location, function, nodes, dict())
            # Finally populate.
            data[benchmark][mode][tag][3][pattern] = match

    # Print the CSV table.
    csvwriter = csv.writer(sys.stdout, delimiter=",", quoting=csv.QUOTE_MINIMAL)
    csvwriter.writerow(([] if simple else ["benchmark", "mode", "loop", "nodes"]) + \
                       ["location"] + \
                       ([] if simple else ["function"]) + \
                       [u.pat_map, u.pat_reduction, u.pat_scan])
    for (benchmark, benchmark_data) in sorted(data.iteritems()):
        for (mode, mode_data) in sorted(benchmark_data.iteritems()):
            nodes_inv = lambda x: -x[1][2]
            for (tag, (location, function, nodes, matches)) in \
                sorted(mode_data.iteritems(),
                       cmp=lambda t1, t2: cmp(nodes_inv(t1), nodes_inv(t2))):
                row = ([] if simple else [benchmark, mode, tag, nodes]) + \
                      [location] + \
                       ([] if simple else [function]) + \
                      [match_to_digit(matches[u.pat_map]),
                       match_to_digit(matches[u.pat_reduction]),
                       match_to_digit(matches[u.pat_scan])]
                csvwriter.writerow(row)

def process_instruction_matches(szn_files, simple):

    # Multi-level map: benchmark -> mode -> location -> pattern match entries.
    data = {}

    # Populate the map loading each solution file. A solution file is expected
    # to be called [BENCHMARK]-[MODE] ... [PATTERN].szn, where:
    #
    # BENCHMARK is the benchmark name (e.g. c-ray)
    # MODE is the benchmark mode (e.g. pthread)
    # PATTERN is the pattern that is matched (e.g. reductions)
    #
    # For each solution file, a corresponding trace called
    # [BENCHMARK]-[MODE] ... .trace is expected.
    for filename in szn_files:
        if os.path.isfile(filename) and filename.endswith(".szn"):
            # Gather all data.
            (benchmark, mode, tag, pattern, trace_filename) = \
                file_info(filename)
            G = u.read_trace(trace_filename)
            (_, matches, status) = u.read_matches(filename)
            (_, PB, PI, PT) = G
            for insts in u.insts_to_steps(G, pattern, matches).keys():
                # Map from file names to sets of lines
                lines = dict()
                for inst in insts:
                    [loc_file, loc_line, _] = \
                        PI[inst].get(u.tk_location).split(u.tk_loc_sep)
                    loc_basefile = os.path.basename(loc_file)
                    if not loc_basefile in lines:
                        lines[loc_basefile] = set()
                    lines[loc_basefile].add(int(loc_line))
                loc = ";".join([loc_basefile + ":" +
                                ",".join(map(str, sorted(loc_lines)))
                                for (loc_basefile, loc_lines)
                                in lines.iteritems()])
                # Create keys at all levels first if not present.
                if not benchmark in data:
                    data[benchmark] = dict()
                if not mode in data[benchmark]:
                    data[benchmark][mode] = dict()
                if not loc in data[benchmark][mode]:
                    data[benchmark][mode][loc] = set()
                # Finally populate.
                data[benchmark][mode][loc].add(pattern)

    # Print the CSV table.
    csvwriter = csv.writer(sys.stdout, delimiter=",", quoting=csv.QUOTE_MINIMAL)
    csvwriter.writerow(([] if simple else ["benchmark", "mode", "pattern"]) + \
                       ["location",
                        u.pat_map, u.pat_reduction, u.pat_scan, u.pat_pipeline])
    m = 0
    for (benchmark, benchmark_data) in sorted(data.iteritems()):
        for (mode, mode_data) in sorted(benchmark_data.iteritems()):
            for (loc, matches) in sorted(mode_data.iteritems(),
                                         cmp=lambda t1, t2: cmp(t1[0], t2[0])):
                def match_digit(p):
                    return match_to_digit((p in matches,
                                           u.tk_sol_status_normal))
                row = ([] if simple else [benchmark, mode, m]) + \
                      [loc,
                       match_digit(u.pat_map),
                       match_digit(u.pat_reduction),
                       match_digit(u.pat_scan),
                       match_digit(u.pat_pipeline)]
                csvwriter.writerow(row)
                m += 1

def main(args):

    parser = argparse.ArgumentParser(description='Aggregate matches into a CSV table.')
    parser.add_argument('FILES', nargs="*")
    parser.add_argument('-l,', '--level', dest='level', action='store', type=str, choices=[u.arg_loop, u.arg_instruction], default=u.arg_loop)
    parser.add_argument('--simple', dest='simple', action='store_true', default=False)
    args = parser.parse_args(args)

    if args.level == u.arg_loop:
        process_loop_matches(args.FILES, args.simple)
    elif args.level == u.arg_instruction:
        process_instruction_matches(args.FILES, args.simple)

if __name__ == '__main__':
    main(sys.argv[1:])
