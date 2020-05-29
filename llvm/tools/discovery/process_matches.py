#!/usr/bin/python

import argparse
import os
import glob
import csv
import sys
from sets import Set
import copy
import StringIO as sio
import shutil
import hashlib

import trace_utils as u
import view_patterns as vp

def entry_id(r):
    key = r["benchmark"] + r["mode"] + r["location"] + r["loops"]
    return hashlib.md5(key).hexdigest()[:4]

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
    trace_filename = ".".join(file_components[0:-2]) + ".trace"
    return (benchmark, mode, pattern, trace_filename)

def maybe_iteration(trace):
    for component in os.path.normpath(trace).split(os.sep):
        if component.isdigit():
            return int(component)
    return -1

def print_location(iset):
    # Map from file names to sets of lines
    lines = dict()
    for (inst_name, inst_loc) in iset:
        [loc_file, loc_line, _] = inst_loc.split(u.tk_loc_sep)
        loc_basefile = os.path.basename(loc_file)
        if not loc_basefile in lines:
            lines[loc_basefile] = set()
        lines[loc_basefile].add(int(loc_line))
    return ";".join([loc_basefile + ":" +
                     ",".join(map(str, sorted(loc_lines)))
                     for (loc_basefile, loc_lines)
                     in lines.iteritems()])

def print_loops(loops, simple):
    # Set of loops
    loop_lines = set()
    for loop in loops:
        [src_file, src_function, src_line, src_col] = loop.split(":")
        loop_lines.add(":".join([os.path.basename(src_file), src_line] + \
                                ([] if simple else [src_col])))
    return ";".join(loop_lines)

def match_consensus(pattern, pattern_data):
    if not pattern in pattern_data:
        return u.match_none
    match_data = pattern_data[pattern]
    if len(match_data) == 1:
        if u.match in match_data:
            return u.match_full
        elif u.no_match in match_data:
            return u.match_none
    elif len(match_data) >= 1:
        if u.match in match_data and u.no_match in match_data:
            return u.match_partial
    assert(False)

def generalize_partial_maps(pattern_data):
    maplike_patterns = u.pat_all_map_like
    # If the trace is matched as something else, nothing to do.
    for pattern in set(u.pat_all) - set(maplike_patterns):
        if pattern in pattern_data and u.match in pattern_data[pattern]:
            return
    # If the trace does not contain at least two matches of different map-like
    # patterns, nothing to do.
    maplike = 0
    for pattern in set(maplike_patterns):
        if pattern in pattern_data and u.match in pattern_data[pattern]:
            maplike += 1
    if maplike < 2:
        return
    # If the trace is not matched as a map-like pattern by all matches, nothing
    # to do.
    all_traces = set()
    yes_traces = set()
    common_result_data = set()
    for pattern in maplike_patterns:
        if pattern in pattern_data:
            for (match_result, result_data) in pattern_data[pattern].iteritems():
                traces = [trace for (trace, _) in result_data]
                all_traces.update(traces)
                if match_result == u.match:
                    yes_traces.update(traces)
                    common_result_data.update(result_data)
    if yes_traces != all_traces:
        return
    # The trace can be generalized as a conditional map, now do it.
    pattern_data[u.pat_doall]     = {u.no_match  : common_result_data}
    pattern_data[u.pat_map]       = {u.no_match  : common_result_data}
    pattern_data[u.pat_conditional_map] = {u.match : common_result_data}
    return

def discard_subsumed_linear_reductions(pattern_data):
    if not u.pat_linear_reduction in pattern_data:
        return
    reductions = pattern_data[u.pat_linear_reduction]
    if not u.pat_tiled_reduction in pattern_data:
        return
    tiled_reductions = pattern_data[u.pat_tiled_reduction]
    if tiled_reductions.keys() == [u.match] and \
       reductions.keys() == [u.match]:
        reductions[u.no_match] = reductions[u.match]
        del reductions[u.match]
    return

generalizes = {
    (u.pat_linear_map_reduction, u.pat_map) : True,
    (u.pat_linear_map_reduction, u.pat_linear_reduction) : True,
    (u.pat_tiled_map_reduction, u.pat_map) : True,
    (u.pat_tiled_map_reduction, u.pat_tiled_reduction) : True,
}

def process_matches(szn_files, simple, show_constant_reductions):

    # Multi-level map: benchmark -> mode -> (instruction set, loop set) ->
    # pattern -> match result -> (trace, number of matched nodes) tuples.
    data = {}

    def register_match(benchmark, mode, instructions, loops, pattern,
                       match_result, trace, nodes):
        iset = frozenset(instructions)
        lset = frozenset(loops)
        identifier = (iset, lset)
        # Create keys at all levels first if not present.
        if not benchmark in data:
            data[benchmark] = dict()
        if not mode in data[benchmark]:
            data[benchmark][mode] = dict()
        if not identifier in data[benchmark][mode]:
            data[benchmark][mode][identifier] = dict()
        if not pattern in data[benchmark][mode][identifier]:
            data[benchmark][mode][identifier][pattern] = dict()
        if not match_result in data[benchmark][mode][identifier][pattern]:
            data[benchmark][mode][identifier][pattern][match_result] = set()
        # Finally populate.
        data[benchmark][mode][identifier][pattern][match_result].add(
            (trace, nodes))

    # Populate the map loading each solution file. A solution file is expected
    # to be called [BENCHMARK]-[MODE] ... [PATTERN].szn, where:
    #
    # BENCHMARK is the benchmark name (e.g. c-ray)
    # MODE is the benchmark mode (e.g. pthread)
    # PATTERN is the pattern that is matched (e.g. reductions)
    #
    # If the solution file does not contain a MODE, this is set as 'unknown'.
    #
    # For each solution file, a corresponding trace called
    # [BENCHMARK]-[MODE] ... .trace is expected.
    for filename in szn_files:
        if os.path.isfile(filename) and filename.endswith(".szn") and \
           not filename.endswith(".trivial.szn"):
            # Gather all data.
            (benchmark, mode, pattern, trace_filename) = file_info(filename)
            G = u.read_trace(trace_filename)
            (_, matches, status) = u.read_matches(filename)
            (DDG, PB, PI, PT) = G
            # Skip traces with only one node (besides possibly a source and a
            # sink). Pattern-finding on those is fundamentally inconclusive.
            # TODO: skip also inconclusive traces due to timeouts and errors.
            inner_nodes = len(filter(lambda b: (not u.is_source(b, PB, PI)) and \
                                     (not u.is_sink(b, PB, PI)), DDG.nodes()))
            if inner_nodes <= 1:
                continue
            # If there are no matches but the trivial version does contain
            # matches, the trace is inconclusive and should be skipped.
            # TODO: This could generalize the single-node check above.
            trivial_filename = os.path.splitext(filename)[0] + ".trivial.szn"
            if not matches and os.path.isfile(trivial_filename):
                (_, trivial_matches, __) = u.read_matches(trivial_filename)
                if trivial_matches:
                    continue

            # For all matches of 'pattern' in the file (possibly different
            # subsets of DDG):
            for match in matches:
                nodes = u.match_nodes(match)
                total_nodes = 0
                loops = set()
                # Collect precise instruction information.
                instructions = []
                has_constant = False
                for node in nodes:
                    tags = PB[node].get(u.tk_tags)
                    if tags != None:
                        loops.update([PT[u.tag_name(t)][u.tk_alias]
                                      for t in tags])
                    for inst in u.node_instructions(G, node):
                        instructions.append((PI[inst].get(u.tk_name),
                                             PI[inst].get(u.tk_location)))
                        if (PI[inst].get(u.tk_immediate) == u.tk_true):
                            has_constant = True
                        total_nodes += 1
                if not show_constant_reductions \
                   and pattern in u.pat_all_associative \
                   and has_constant:
                    continue
                register_match(benchmark, mode, instructions, loops, pattern,
                               u.match, trace_filename, total_nodes)
            # If there are no matches, register that as well (for identifying
            # partial patterns):
            if not matches and status == u.tk_sol_status_normal:
                all_insts = Set()
                loops = set()
                for node in DDG.nodes():
                    if u.is_source(node, PB, PI) or u.is_sink(node, PB, PI):
                        continue
                    all_insts.update(u.node_instructions(G, node))
                    tags = PB[node].get(u.tk_tags)
                    if tags != None:
                        loops.update([PT[u.tag_name(t)][u.tk_alias]
                                      for t in tags])
                instructions = []
                for inst in all_insts:
                    instructions.append((PI[inst].get(u.tk_name),
                                         PI[inst].get(u.tk_location)))
                register_match(benchmark, mode, instructions, loops, pattern,
                               u.no_match, trace_filename, -1)
    results = []
    for (benchmark, benchmark_data) in sorted(data.iteritems()):
        for (mode, mode_data) in sorted(benchmark_data.iteritems()):
            for ((iset, lset), pattern_data) in sorted(mode_data.iteritems()):
                # Possibly generalize partial matches of map-like patterns into
                # full conditional map matches.
                generalize_partial_maps(pattern_data)
                # If there are both linear and tiled reductions, discard the
                # former.
                discard_subsumed_linear_reductions(pattern_data)
                match_columns = {p : match_consensus(p, pattern_data)
                                 for p in u.pat_all}
                # If there is no match in this instruction set, discard.
                if all([m == u.match_none for m in match_columns.values()]):
                    continue
                # Compute positive traces corresponding to this instruction set.
                traces = set()
                # Compute total nodes.
                nodes = 0
                for (pattern, match_data) in pattern_data.iteritems():
                    for (match_result, result_data) in match_data.iteritems():
                        if match_result == u.match:
                            traces.update([trace for (trace, _) in result_data])
                            nodes += sum([match_nodes for (_, match_nodes)
                                          in result_data])
                loops = print_loops(lset, True)
                # Pretty-print location.
                location = print_location(iset)
                # "Repetitions" is just the number of traces.
                repetitions = len(traces)
                trace = ";".join(traces)
                instructions = list(iset)
                iteration = min(map(maybe_iteration, traces) or [-1])
                row = {"benchmark" : benchmark,
                       "mode" : mode,
                       "location" : location,
                       "loops" : loops,
                       "repetitions" : repetitions,
                       "nodes" : nodes,
                       "iteration" : iteration,
                       "traces" : trace,
                       "instructions" : instructions}
                row.update(match_columns)
                results.append(row)
    return results

def main(args):

    parser = argparse.ArgumentParser(description='Aggregate matches into a CSV table.')
    parser.add_argument('FILES', nargs="*")
    parser.add_argument('-o', "--output-file", help='output file')
    parser.add_argument('--simple', dest='simple', action='store_true', default=False)
    parser.add_argument('-s,', '--sort', dest='sort', action='store', type=str, choices=[u.arg_nodes, u.arg_location], default=u.arg_nodes)
    parser.add_argument('--extract-matched-instructions', dest='extract_matched_instructions', action='store_true', default=True)
    parser.add_argument('--matched-instructions-prefix')
    parser.add_argument('--show-doall', dest='show_doall', action='store_true', default=False)
    parser.add_argument('--show-linear-scan', dest='show_linear_scan', action='store_true', default=False)
    parser.add_argument('--show-subsumed', dest='show_subsumed', action='store_true', default=False)
    parser.add_argument('--show-constant-reductions', dest='show_constant_reductions', action='store_true', default=False)
    parser.add_argument('--html', help='HTML output directory')
    parser.add_argument('--html-source-dir', help='HTML source code directory')
    args = parser.parse_args(args)

    # Gather results.
    results = process_matches(args.FILES, args.simple,
                              args.show_constant_reductions)

    patterns_to_show = copy.deepcopy(u.pat_all)
    if not args.show_doall:
        patterns_to_show.remove(u.pat_doall)
    if not args.show_linear_scan:
        patterns_to_show.remove(u.pat_linear_scan)

    def result_summary(r):
        insts = set(r["instructions"])
        pattern = None
        for p in patterns_to_show:
            if r[p] == u.match_full:
                pattern = p
                break
        return (insts, pattern)

    # Remove subsumed patterns.
    if not args.show_subsumed:
        final_results = []
        for r in results:
            (insts, pattern) = result_summary(r)
            if not pattern:
                continue
            subsumed = False
            for r2 in results:
                (insts2, pattern2) = result_summary(r2)
                if not pattern2:
                    continue
                if insts.issubset(insts2) and \
                   generalizes.get((pattern2, pattern), False):
                    subsumed = True
                    break
            if not subsumed:
                final_results.append(r)
        results = final_results

    # Print results.
    if args.output_file:
        out = open(args.output_file ,"w+")
    else:
        out = sys.stdout
    csvwriter = csv.writer(out, delimiter=",", quoting=csv.QUOTE_MINIMAL)

    if args.simple:
        legend = ["id", "location", "loops", "patterns"]
    else:
        legend = ["benchmark", "mode", "id", "location", "loops", "repetitions",
                  "nodes", "iteration", "traces"] + patterns_to_show + \
                  ["patterns"]
    csvwriter.writerow(legend)

    # Sort results according to given criterion.
    if args.sort == u.arg_nodes:
        k = (lambda r: (r["benchmark"], r["mode"], -r["nodes"]))
    elif args.sort == u.arg_location:
        k = (lambda r: (r["benchmark"], r["mode"],
                        u.natural_sort_key(r["location"])))
    results.sort(key = k)

    # Assign a (hopefully) unique ID to each entry.
    for r in results:
        r["id"] = entry_id(r)

    for r in results:
        matches = []
        patterns = []
        some_match = False
        for p in patterns_to_show:
            matches.append(r[p])
            if r[p] == u.match_full:
                patterns.append(p)
            if r[p] != u.match_none:
                some_match = True
        if not some_match:
            continue
        if args.simple:
            row = [r["id"],
                   r["location"],
                   r["loops"]]
        else:
            row = [r["benchmark"],
                   r["mode"],
                   r["id"],
                   r["location"],
                   r["loops"],
                   r["repetitions"],
                   r["nodes"],
                   r["iteration"],
                   r["traces"]]
            row += matches
        row += [";".join(patterns)]
        csvwriter.writerow(row)

    if args.output_file:
        out.close()

    # Generate a HTML report.
    if args.html:
        out = sio.StringIO()
        for r in results:
            (insts, pattern) = result_summary(r)
            if not pattern:
                # Can happen if there are only partial matches.
                continue
            eid = r["id"]
            line_insts = {}
            for (name, location) in insts:
                [loc_file, loc_line, loc_col] = location.split(u.tk_loc_sep)
                key = (loc_file, int(loc_line))
                if not key in line_insts:
                    line_insts[key] = set()
                line_insts[key].add((name, int(loc_col)))
            for ((loc_file, loc_line), line_insts) in line_insts.iteritems():
                sorted_insts = sorted(list(line_insts),
                                      cmp=lambda (_, c1), (__, c2): cmp(c1, c2))
                assert(sorted_insts)
                loc_col = sorted_insts[0][1]
                names = ["<b>" + n + "</b>" for (n, _) in sorted_insts]
                name = ",".join(names)
                if len(sorted_insts) > 1:
                    name = "IR instructions: {" + name + "}"
                else:
                    name = "IR instruction: " + name
                print >>out, "--- !Analysis"
                print >>out, "Pass: " + pattern + " " + eid
                print >>out, "Name: " + pattern
                print >>out, "DebugLoc: { File: " + loc_file + ", Line: " + \
                    str(loc_line) + ", Column: " + str(loc_col) + "}"
                # TODO: trace the mangled function name of each instruction.
                print >>out, "Function: N/A"
                print >>out, "Args:"
                print >>out, "  - String:      '" + name + "'"
                print >>out, "..."
        yaml = out.getvalue()
        out.close()
        yaml_outfilename = args.html + ".yaml"
        with open(yaml_outfilename, 'w+') as yaml_outfile:
            yaml_outfile.write(yaml)
        vp_args = [yaml_outfilename, "-o", args.html]
        if args.html_source_dir:
            vp_args += ["--source-dir", args.html_source_dir]
        vp.main(vp_args)
        os.remove(yaml_outfilename)

    # Generate a file for each benchmark and mode with all instructions matched.
    if args.extract_matched_instructions:
        matched = dict()
        for r in results:
            benchmark_mode = (r["benchmark"], r["mode"])
            if not benchmark_mode in matched:
                matched[benchmark_mode] = set([])
            matched[benchmark_mode] |= set(r["instructions"])
        for ((benchmark, mode), matched_instructions) in matched.iteritems():
            if mode == "unknown":
                filename = benchmark + ".instructions"
            else:
                filename = benchmark + "-" + mode + ".instructions"
            if args.matched_instructions_prefix:
                filename = \
                    os.path.join(args.matched_instructions_prefix, filename)
            matched_instructions_list = list(matched_instructions)
            matched_instructions_list.sort(
                key = (lambda (name, loc): (u.natural_sort_key(loc), name)))
            with open(filename, 'w+') as outfile:
                for (name, location) in matched_instructions_list:
                    line = location + ":" + name + "\n"
                    outfile.write(line)

if __name__ == '__main__':
    main(sys.argv[1:])
