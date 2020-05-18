set (files
  "Makefile"
  "assert_matches.py"
  "merge_matches.py"
  "process_runtimes.py"
  "process_trace.py"
  "trace_utils.py"
  "find_patterns.py"
  "process_matches.py"
  "process_stats.py"
  "test.py"
  "common.mzn"
  "linear_map_reduction.mzn"
  "mapfilter.mzn"
  "pipeline.mzn"
  "tiled_map_reduction.mzn"
  "doall.mzn"
  "linear_reduction.mzn"
  "map.mzn"
  "scan.mzn"
  "commutative.txt")

foreach (file ${files})
  install(PROGRAMS ${file}
    DESTINATION share/discovery
    COMPONENT discovery)
endforeach (file)
