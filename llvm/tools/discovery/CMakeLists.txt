set (files
  "Makefile"
  "process_trace.py"
  "process_matches.py"
  "assert_matches.py"
  "trace_utils.py"
  "find_patterns.py"
  "common.mzn"
  "map.mzn"
  "pipeline.mzn"
  "reduction.mzn"
  "commutative.txt")

foreach (file ${files})
  install(PROGRAMS ${file}
    DESTINATION share/discovery
    COMPONENT discovery)
endforeach (file)
