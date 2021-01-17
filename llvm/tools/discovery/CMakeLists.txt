set (files
  "Makefile"
  "check_patterns.py"
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
  "conditional_map.mzn"
  "pipeline.mzn"
  "tiled_map_reduction.mzn"
  "doall.mzn"
  "linear_reduction.mzn"
  "map.mzn"
  "linear_scan.mzn"
  "conditional_linear_scan.mzn"
  "commutative.txt")

foreach (file ${files})
  install(PROGRAMS ${file}
    DESTINATION share/discovery
    COMPONENT discovery)
endforeach (file)
