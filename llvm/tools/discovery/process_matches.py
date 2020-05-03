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
        return u.match_unknown
    elif status == u.tk_sol_status_error and not matches:
        return u.match_unknown
    return str(int(matches))

def matches_to_digit(matches_list):
    unknown = 0
    for (matches, status) in matches_list:
        if status in [u.tk_sol_status_unknown, u.tk_sol_status_error]:
            unknown += 1
    total_groups   = len(matches_list)
    matched_groups = sum(1 for (matches, status) in matches_list if matches)
    if matched_groups == 0:
        if unknown > 0:
            return (u.match_unknown, 0)
        else:
            return (u.match_none, 0)
    elif matched_groups == total_groups:
        return (u.match_full, total_groups)
    else:
        return (u.match_partial, matched_groups)

# Generalizes matches of map-like patterns across groups (loop runs). If
# different map-like patterns are found in all non-empty runs of the same loop,
# they generalize as a map-filter pattern. TODO: an alternative would be to
# filter out empty run traces upfront, already during decomposition. This would
# allow generalization to work for other patterns than maps.
def generalize_maps_across_groups(sum_matches_list, groups, empty_groups):
    maplike_patterns = [u.pat_doall, u.pat_map, u.pat_mapfilter]
    maplike_count = sum(sum_matches_list[p][1] for p in maplike_patterns)
    # Require that a map-like pattern is matched in every group (loop run) that
    # is not empty (that is, where the trace has multiple non-boundary nodes).
    if maplike_count < (groups - empty_groups):
        return
    # Require that at least two different map-like patterns are matched.
    if any([sum_matches_list[p][1] == maplike_count for p in maplike_patterns]):
        return
    # Generalize: move all matches to the map-filter pattern.
    sum_matches_list[u.pat_doall] = (u.match_none, 0)
    sum_matches_list[u.pat_map] = (u.match_none, 0)
    sum_matches_list[u.pat_mapfilter] = (u.match_full, groups)

# Discards linear reductions if two-phase reductions have also been found.
def discard_subsumed_reductions(matches):
    if u.pat_twophasereduction in matches:
        return filter(lambda m: m != u.pat_reduction, matches)
    return matches

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
    maybe_tag_group = map(int, [component for component in base_file_components
                                if component.isdigit()])
    if len(maybe_tag_group) > 0:
        tag = maybe_tag_group[0]
    else:
        tag = None
    if len(maybe_tag_group) > 1:
        group = maybe_tag_group[1]
    else:
        group = None
    trace_filename = ".".join(file_components[0:-2]) + ".trace"
    return (benchmark, mode, tag, group, pattern, trace_filename)

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


def match_consensus(pattern, pattern_data):
    if not pattern in pattern_data:
        return u.match_none
    match_data = pattern_data[pattern]
    if len(match_data) == 1:
        if "yes" in match_data:
            return u.match_full
        elif "no" in match_data:
            return u.match_none
    elif len(match_data) >= 1:
        if "yes" in match_data and "no" in match_data:
            return u.match_partial
    assert(False)

def generalize_partial_maps(pattern_data):
    maplike_patterns = [u.pat_doall, u.pat_map, u.pat_mapfilter]
    # If the trace is matched as something else, nothing to do.
    for pattern in set(u.pat_all) - set(maplike_patterns):
        if pattern in pattern_data and "yes" in pattern_data[pattern]:
            return
    # If the trace does not contain at least two matches of different map-like
    # patterns, nothing to do.
    maplike = 0
    for pattern in set(maplike_patterns):
        if pattern in pattern_data and "yes" in pattern_data[pattern]:
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
                if match_result == "yes":
                    yes_traces.update(traces)
                    common_result_data.update(result_data)
    if yes_traces != all_traces:
        return
    # The trace can be generalized as a mapfilter, now do it.
    pattern_data[u.pat_doall]     = {"no"  : common_result_data}
    pattern_data[u.pat_map]       = {"no"  : common_result_data}
    pattern_data[u.pat_mapfilter] = {"yes" : common_result_data}
    return

def process_unified_matches(szn_files, simple, generalize_maps,
                            discard_subsumed,
                            discard_no_matches):

    # Multi-level map: benchmark -> mode -> instruction set -> pattern ->
    #                  match result -> (trace, number of matched nodes) pairs.
    data = {}

    def register_match(benchmark, mode, instructions, pattern, match_result,
                       trace, nodes):
        iset = frozenset(instructions)
        # Create keys at all levels first if not present.
        if not benchmark in data:
            data[benchmark] = dict()
        if not mode in data[benchmark]:
            data[benchmark][mode] = dict()
        if not iset in data[benchmark][mode]:
            data[benchmark][mode][iset] = dict()
        if not pattern in data[benchmark][mode][iset]:
            data[benchmark][mode][iset][pattern] = dict()
        if not match_result in data[benchmark][mode][iset][pattern]:
            data[benchmark][mode][iset][pattern][match_result] = set()
        # Finally populate.
        data[benchmark][mode][iset][pattern][match_result].add((trace, nodes))

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
        if os.path.isfile(filename) and filename.endswith(".szn"):
            # Gather all data.
            (benchmark, mode, _tag, _group, pattern, trace_filename) = \
                file_info(filename)
            G = u.read_trace(trace_filename)
            (_, matches, status) = u.read_matches(filename)
            (DDG, PB, PI, PT) = G
            # TODO: disard inconclusive solutions files: because of timeouts,
            # errors, or just one non-boundary node.

            # For all matches of 'pattern' in the file (possibly different
            # subsets of DDG):
            for match in matches:
                nodes = u.match_nodes(pattern, match)
                total_nodes = 0
                # Collect precise instruction information.
                instructions = []
                for node in nodes:
                    for inst in u.node_instructions(G, node):
                        instructions.append((PI[inst].get(u.tk_name),
                                             PI[inst].get(u.tk_location)))
                        total_nodes += 1
                register_match(benchmark, mode, instructions, pattern, "yes",
                               trace_filename, total_nodes)
            # If there are no matches, register that as well (for identifying
            # partial patterns):
            if not matches and status == u.tk_sol_status_normal:
                all_insts = Set()
                for n in DDG.nodes():
                    if u.is_source(n, PB, PI) or u.is_sink(n, PB, PI):
                        continue
                    all_insts.update(u.node_instructions(G, n))
                instructions = []
                for inst in all_insts:
                    instructions.append((PI[inst].get(u.tk_name),
                                         PI[inst].get(u.tk_location)))
                register_match(benchmark, mode, instructions, pattern, "no",
                               trace_filename, -1)
    results = []
    for (benchmark, benchmark_data) in sorted(data.iteritems()):
        for (mode, mode_data) in sorted(benchmark_data.iteritems()):
            for (iset, pattern_data) in sorted(mode_data.iteritems()):
                # Possibly generalize partial matches of map-like patterns into
                # full 'mapfilter' matches.
                generalize_partial_maps(pattern_data)
                match_columns = {p : match_consensus(p, pattern_data)
                                 for p in u.pat_all}
                # If there is no match in this instruction set, discard.
                if discard_no_matches and \
                   all([m == u.match_none for m in match_columns]):
                    continue
                # Compute traces corresponding to this instruction set.
                traces = set()
                # Compute total nodes.
                nodes = 0
                for (pattern, match_data) in pattern_data.iteritems():
                    for (match_result, result_data) in match_data.iteritems():
                        traces.update([trace for (trace, _) in result_data])
                        if match_result == "yes":
                            nodes += sum([match_nodes for (_, match_nodes)
                                          in result_data])
                # Pretty-print location.
                location = print_location(iset)
                # "Repetitions" is just the number of traces.
                repetitions = len(traces)
                trace = ";".join(traces)
                instructions = list(iset)
                row = {"benchmark" : benchmark,
                       "mode" : mode,
                       "location" : location,
                       "repetitions" : repetitions,
                       "nodes" : nodes,
                       "trace" : trace,
                       "instructions" : instructions}
                row.update(match_columns)
                results.append(row)
    return results

def process_loop_matches(szn_files, simple, generalize_maps,
                         discard_no_matches):

    # Cache of demangled function names.
    demangled_cache = {}

    # Multi-level map: benchmark -> mode -> tag -> group -> pattern match entries.
    data = {}

    # Populate the map loading each solution file. A solution file is expected
    # to be called [BENCHMARK]-[MODE] ... [TAG_ID].[GROUP_ID] ... [PATTERN].szn, where:
    #
    # BENCHMARK is the benchmark name (e.g. c-ray)
    # MODE is the benchmark mode (e.g. pthread)
    # TAG_ID is the loop tag id (e.g. 5)
    # GROUP_ID is the loop group id (e.g. 2)
    # PATTERN is the pattern that is matched (e.g. reductions)
    #
    # For each solution file, a corresponding trace called
    # [BENCHMARK]-[MODE] ... [TAG_ID].[GROUP_ID] ... .trace is expected.
    for filename in szn_files:
        if os.path.isfile(filename) and filename.endswith(".szn"):
            # Gather all data.
            (benchmark, mode, tag, group, pattern, trace_filename) = \
                file_info(filename)
            G = u.read_trace(trace_filename)
            [internal_tag_id] = list(u.tag_set(G))
            (DDG, PB, PI, PT) = G
            tag_alias = PT[internal_tag_id].get(u.tk_alias)
            [src_file, src_function, src_line, src_col] = tag_alias.split(":")
            location = ":".join([os.path.basename(src_file), src_line] + \
                                ([] if simple else [src_col]))
            function = u.demangle(src_function, demangled_cache)
            nodes = int(PT[internal_tag_id].get(u.tk_original_blocks))
            (_, matches, status) = u.read_matches(filename)
            inner_nodes = len(filter(lambda b: (not u.is_source(b, PB, PI)) and \
                                     (not u.is_sink(b, PB, PI)), DDG.nodes()))
            if inner_nodes <= 1:
                status = u.tk_sol_status_empty
            match = (len(matches) > 0, status)
            # Create keys at all levels first if not present.
            if not benchmark in data:
                data[benchmark] = dict()
            if not mode in data[benchmark]:
                data[benchmark][mode] = dict()
            if not tag in data[benchmark][mode]:
                data[benchmark][mode][tag] = \
                    (location, function, nodes, trace_filename, dict())
            if not group in data[benchmark][mode][tag][4]:
                data[benchmark][mode][tag][4][group] = dict()
            # Finally populate.
            data[benchmark][mode][tag][4][group][pattern] = match

    results = []
    for (benchmark, benchmark_data) in sorted(data.iteritems()):
        for (mode, mode_data) in sorted(benchmark_data.iteritems()):
            for (tag, (location, function, nodes, trace, groups)) in \
                sorted(mode_data.iteritems()):
                all_matches = dict()
                for (group, matches) in sorted(groups.iteritems()):
                    for p in u.pat_all:
                        if not p in all_matches:
                            all_matches[p] = []
                        if p in matches:
                            match = matches[p]
                        else:
                            # If minizinc fails with a 'model inconsistency
                            # warning', it does not honor the -o flag and
                            # does not create a .szn file. In that case,
                            # assume there is no match (equivalent to
                            # MiniZinc's =====UNSATISFIABLE=====).
                            match = (False, u.tk_sol_status_normal)
                        all_matches[p].append(match)
                runs = len(groups)
                # Compute number of runs where there is only one node (besides
                # possibly a source and a sink). Pattern-finding on those is
                # fundamentally inconclusive, and should not prevent
                # generalizing maps.
                all_empty = lambda g: [status == u.tk_sol_status_empty
                                       for (p, (_, status)) in g.iteritems()]
                empty_runs = len([g for (g, m) in groups.iteritems()
                                  if all(all_empty(m))])
                all_summarized_matches = \
                    {p : matches_to_digit(m) for p, m in all_matches.items()}
                if generalize_maps:
                    generalize_maps_across_groups(all_summarized_matches,
                                                  runs, empty_runs)
                row = {"benchmark" : benchmark,
                       "mode" : mode,
                       "location" : location,
                       "repetitions" : runs,
                       "nodes" : nodes,
                       "trace" : trace,
                       "instructions" : []}
                row.update({p : all_summarized_matches[p][0]
                            for p in u.pat_all})
                match_digits = [all_summarized_matches[p][0] for p in u.pat_all]
                if discard_no_matches and \
                   all([m == u.match_none for m in match_digits]):
                    continue
                results.append(row)
    return results

def process_instruction_matches(szn_files, simple, discard_subsumed,
                                discard_no_matches):

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
            (benchmark, mode, _tag, _group, pattern, trace_filename) = \
                file_info(filename)
            G = u.read_trace(trace_filename)
            (_, matches, status) = u.read_matches(filename)
            (DDG, PB, PI, PT) = G
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
                # Collect precise instruction information in case we want to
                # extract a list of matched instructions later.
                instructions = []
                for inst in insts:
                    instructions.append((PI[inst].get(u.tk_name),
                                         PI[inst].get(u.tk_location)))
                cover = u.min_tag_cover(G, insts)
                if cover:
                    nodes = sum([int(PT[t][u.tk_original_blocks])
                                 for t in cover])
                else:
                    nodes = len(DDG.nodes())
                # Create keys at all levels first if not present.
                if not benchmark in data:
                    data[benchmark] = dict()
                if not mode in data[benchmark]:
                    data[benchmark][mode] = dict()
                if not loc in data[benchmark][mode]:
                    data[benchmark][mode][loc] = []
                # Finally populate.
                data[benchmark][mode][loc].append((pattern, trace_filename,
                                                   nodes, instructions))

    results = []
    for (benchmark, benchmark_data) in sorted(data.iteritems()):
        for (mode, mode_data) in sorted(benchmark_data.iteritems()):
            for (location, matches_traces) in sorted(mode_data.iteritems(),
                cmp=lambda t1, t2: cmp(t1[0], t2[0])):
                [matches, traces, nodes_list, instructions_list] = \
                    map(list, zip(*matches_traces))
                # Pick the first trace for simplicity, in general there will be
                # as many traces as repetitions.
                trace = traces[0]
                nodes = nodes_list[0]
                instructions = instructions_list[0]
                if discard_subsumed:
                    matches = discard_subsumed_reductions(matches)
                repetitions = max([matches.count(p) for p in u.pat_all])
                def match_digit(p):
                    return match_to_digit((p in matches,
                                           u.tk_sol_status_normal))
                row = {"benchmark" : benchmark,
                       "mode" : mode,
                       "location" : location,
                       "repetitions" : repetitions,
                       "nodes" : nodes,
                       "trace" : trace,
                       "instructions" : instructions}
                row.update({p : match_digit(p) for p in u.pat_all})
                match_digits = [match_digit(p) for p in u.pat_all]
                if discard_no_matches and \
                   all([m == u.match_none for m in match_digits]):
                    continue
                results.append(row)
    return results

def main(args):

    parser = argparse.ArgumentParser(description='Aggregate matches into a CSV table.')
    parser.add_argument('FILES', nargs="*")
    parser.add_argument('-o', "--output-file", help='output file')
    parser.add_argument('-l,', '--level', dest='level', action='store', type=str, choices=[u.arg_unified, u.arg_loop, u.arg_instruction], default=u.arg_unified)
    parser.add_argument('--simple', dest='simple', action='store_true', default=False)
    parser.add_argument('--generalize-maps', dest='generalize_maps', action='store_true', default=True)
    parser.add_argument('--discard-subsumed-patterns', dest='discard_subsumed', action='store_true', default=True)
    parser.add_argument('--discard-no-matches', dest='discard_no_matches', action='store_true', default=True)
    parser.add_argument('-s,', '--sort', dest='sort', action='store', type=str, choices=[u.arg_nodes, u.arg_location], default=u.arg_nodes)
    parser.add_argument('--extract-matched-instructions', dest='extract_matched_instructions', action='store_true', default=True)
    parser.add_argument('--matched-instructions-prefix')
    args = parser.parse_args(args)

    # Gather results.
    if args.level == u.arg_unified:
        results = process_unified_matches(args.FILES, args.simple,
                                          args.generalize_maps,
                                          args.discard_subsumed,
                                          args.discard_no_matches)
    elif args.level == u.arg_loop:
        results = process_loop_matches(args.FILES, args.simple,
                                       args.generalize_maps,
                                       args.discard_no_matches)
    elif args.level == u.arg_instruction:
        results = process_instruction_matches(args.FILES, args.simple,
                                              args.discard_subsumed,
                                              args.discard_no_matches)

    # Print results in a level-independent manner.
    if args.output_file:
        out = open(args.output_file ,"w+")
    else:
        out = sys.stdout
    csvwriter = csv.writer(out, delimiter=",", quoting=csv.QUOTE_MINIMAL)

    if args.simple:
        legend = ["location"] + u.pat_all
    else:
        legend = ["benchmark", "mode", "location", "repetitions", "nodes",
                  "trace"] + u.pat_all
    csvwriter.writerow(legend)

    # Sort results according to given criterion.
    if args.sort == u.arg_nodes:
        k = (lambda r: (r["benchmark"], r["mode"], -r["nodes"]))
    elif args.sort == u.arg_location:
        k = (lambda r: (r["benchmark"], r["mode"],
                        u.natural_sort_key(r["location"])))
    results.sort(key = k)

    for r in results:
        if args.simple:
            row = [r["location"]]
        else:
            row = [r["benchmark"],
                   r["mode"],
                   r["location"],
                   r["repetitions"],
                   r["nodes"],
                   r["trace"]]
        row += [r[p] for p in u.pat_all]
        csvwriter.writerow(row)

    if args.output_file:
        out.close()

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
