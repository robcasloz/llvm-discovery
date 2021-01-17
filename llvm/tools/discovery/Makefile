# Basic clang flags to compile and instrument C and C++ files with Discovery.
CBASEFLAGS = -pthread -fno-vectorize -fno-slp-vectorize -fno-unroll-loops	\
-Xclang -disable-lifetime-markers
CDFSANFLAGS = -g -fno-discard-value-names -fsanitize=dataflow -mllvm		\
-dfsan-discovery -mllvm -dfsan-discovery-commutativity-list=commutative.txt
CFLAGS += $(CBASEFLAGS) $(CDFSANFLAGS)
CXXFLAGS += $(CBASEFLAGS) $(CDFSANFLAGS)

# Directory and argument configuration.
DISCOVERY_DIR ?= .
PROCESS_TRACE = $(DISCOVERY_DIR)/process_trace.py
PROCESS_MATCHES = $(DISCOVERY_DIR)/process_matches.py
PROCESS_STATS = $(DISCOVERY_DIR)/process_stats.py
PROCESS_RUNTIMES = $(DISCOVERY_DIR)/process_runtimes.py
GRAPHVIZ_FLAGS = --simplify-loc
MINIZINC_FLAGS ?= -D match_trivial=false -a --solver chuffed
MINIZINC_DZN_FLAGS ?=
OPT_VIEWER = $(DISCOVERY_DIR)/../opt-viewer/opt-viewer.py
TAG ?= 0
GROUP ?= 0
NAME ?= ".*"
NAMES ?= add fadd mul fmul and or xor
COMPONENT ?= 0
MIN_COMPONENT_NODES ?= 3
TOP_COMPONENTS ?= 50

# Do not remove intermediate files.
.SECONDARY:

# Instrumented binary for single C++ source file.
%.bin: %.cpp
	$(CXX) $< -o $@ $(CXXFLAGS)

# Instrumented binary for single C source file.
%.bin: %.c
	$(CC) $< -o $@ $(CFLAGS)

# Raw trace.
%.trace: %.bin
	PATH=$$PATH:$(dir $<) $< | true
	mv $(PWD)/trace $@

# Simplified trace.
%.simple.trace: %.trace
	$(PROCESS_TRACE) --output-format=plain simplify $< > $@

# Filtered trace for a given tag.
%.tag-filtered.trace: %.trace
	$(PROCESS_TRACE) --output-format=plain transform --filter-tags $(TAG) $< > $@

# Filtered trace for a given tag and group.
%.group-filtered.trace: %.trace
	$(PROCESS_TRACE) --output-format=plain transform --filter-tags $(TAG) --filter-group $(GROUP) $< > $@

# Filtered trace for a given instruction name.
%.name-filtered.trace: %.trace
	$(PROCESS_TRACE) --output-format=plain transform --filter-name $(NAME) $< > $@

# Filtered trace for a given weakly connected component.
%.component-filtered.trace: %.trace
	$(PROCESS_TRACE) --output-format=plain \
	--min-nodes $(MIN_COMPONENT_NODES) \
	--top-components $(TOP_COMPONENTS) \
	transform --filter-component $(COMPONENT) $< > $@

# Filtered trace for a given instruction file.
%.instruction-filtered.trace: %.trace %.instructions
	$(PROCESS_TRACE) --output-format=plain transform --filter-out-instructions $*.instructions $< > $@

# Collapsed trace for a given tag.
%.collapsed.trace: %.trace
	$(PROCESS_TRACE) --output-format=plain transform --collapse-tags $(TAG) $< > $@

# Trace as input to the MiniZinc pattern finder.
%.dzn: %.trace
	$(PROCESS_TRACE) --output-format=minizinc $(MINIZINC_DZN_FLAGS) print $< > $@

# List of tags in a trace.
%.tags: %.trace
	$(PROCESS_TRACE) query --print-tags $< > $@

# List of tag aliases in a trace.
%.aliases: %.trace
	$(PROCESS_TRACE) query --print-tag-aliases $< > $@

# List of tag groups in a trace.
%.groups: %.trace
	$(PROCESS_TRACE) query --print-tag-groups $(TAG) $< > $@

# List of weakly connected components in a trace, excluding source and sink.
%.components: %.trace
	$(PROCESS_TRACE) \
	--min-nodes $(MIN_COMPONENT_NODES) \
	--top-components $(TOP_COMPONENTS) \
	query --print-components $< > $@

# Size of the trace.
%.size: %.trace
	$(PROCESS_TRACE) query --print-size $< > $@

# One trace file for each loop and associative component.
%.subtraces: %.trace
	$(PROCESS_TRACE) decompose $<

# One trace file for each loop.
%.loop-subtraces: %.trace
	$(PROCESS_TRACE) decompose --no-associative-components $<

# One trace file for each associative component.
%.associative-component-subtraces: %.trace
	$(PROCESS_TRACE) decompose --no-loops $<

# One trace file for each tag in the %.tags file.
%.tag-traces: %.trace %.tags
	while read TAG; do \
		$(MAKE) $*.tag-filtered.trace TAG=$$TAG; \
		mv $*.tag-filtered.trace $*.$$TAG.trace; \
	done < $*.tags

# One trace file for each group in the %.groups file.
%.group-traces: %.trace %.groups
	while read GROUP; do \
		$(MAKE) $*.group-filtered.trace GROUP=$$GROUP; \
		mv $*.group-filtered.trace $*.$$GROUP.trace; \
	done < $*.groups

# One trace file for each instruction name in $(NAMES).
%.name-traces: %.trace
	for NAME in $(NAMES); do \
		$(MAKE) $*.name-filtered.trace NAME=$$NAME; \
		mv $*.name-filtered.trace $*.$$NAME.trace; \
	done

# One trace file for each weakly connected component in the %.components file.
%.component-traces: %.trace %.components
	while read COMPONENT; do \
		if [ -n "$$COMPONENT" ]; \
		then \
			$(MAKE) $*.component-filtered.trace COMPONENT=$$COMPONENT; \
			mv $*.component-filtered.trace $*.$$COMPONENT.trace; \
		fi; \
	done < $*.components

# DOALL pattern matches in MiniZinc solution format.
%.doalls.szn: %.dzn $(DISCOVERY_DIR)/doall.mzn $(DISCOVERY_DIR)/common.mzn
	-minizinc $(MINIZINC_FLAGS) $(DISCOVERY_DIR)/doall.mzn $< > $@

# DOALL pattern matches in PDF format.
%.doalls.pdf: %.doalls.szn %.trace
	$(PROCESS_TRACE) -o $@ visualize $^ $(GRAPHVIZ_FLAGS)

# Map pattern matches in MiniZinc solution format.
%.maps.szn: %.dzn $(DISCOVERY_DIR)/map.mzn $(DISCOVERY_DIR)/common.mzn
	-minizinc $(MINIZINC_FLAGS) $(DISCOVERY_DIR)/map.mzn $< > $@

# Map pattern matches in PDF format.
%.maps.pdf: %.maps.szn %.trace
	$(PROCESS_TRACE) -o $@ visualize $^ $(GRAPHVIZ_FLAGS)

# Conditional map pattern matches in MiniZinc solution format.
%.conditional_maps.szn: %.dzn $(DISCOVERY_DIR)/conditional_map.mzn $(DISCOVERY_DIR)/common.mzn
	-minizinc $(MINIZINC_FLAGS) $(DISCOVERY_DIR)/conditional_map.mzn $< > $@

# Conditional map pattern matches in PDF format.
%.conditional_maps.pdf: %.conditional_maps.szn %.trace
	$(PROCESS_TRACE) -o $@ visualize $^ $(GRAPHVIZ_FLAGS)

# Linear reduction pattern matches in MiniZinc solution format.
%.linear_reductions.szn: %.dzn $(DISCOVERY_DIR)/linear_reduction.mzn $(DISCOVERY_DIR)/common.mzn
	-minizinc $(MINIZINC_FLAGS) $(DISCOVERY_DIR)/linear_reduction.mzn $< > $@

# Linear reduction pattern matches in PDF format.
%.linear_reductions.pdf: %.linear_reductions.szn %.trace
	$(PROCESS_TRACE) -o $@ visualize $^ $(GRAPHVIZ_FLAGS)

# Tiled reduction pattern matches in MiniZinc solution format.
%.tiled_reductions.szn: %.dzn $(DISCOVERY_DIR)/tiled_reduction.mzn $(DISCOVERY_DIR)/common.mzn
	-minizinc $(MINIZINC_FLAGS) $(DISCOVERY_DIR)/tiled_reduction.mzn $< > $@

# Tiled reduction pattern matches in PDF format.
%.tiled_reductions.pdf: %.tiled_reductions.szn %.trace
	$(PROCESS_TRACE) -o $@ visualize $^ $(GRAPHVIZ_FLAGS)

# Linear map-reduction pattern matches in MiniZinc solution format.
%.linear_map_reductions.szn: %.dzn $(DISCOVERY_DIR)/linear_map_reduction.mzn $(DISCOVERY_DIR)/common.mzn
	-minizinc $(MINIZINC_FLAGS) $(DISCOVERY_DIR)/linear_map_reduction.mzn $< > $@

# Map-reduction pattern matches in PDF format.
%.linear_map_reductions.pdf: %.linear_map_reductions.szn %.trace
	$(PROCESS_TRACE) -o $@ visualize $^ $(GRAPHVIZ_FLAGS)

# Tiled map-reduction pattern matches in MiniZinc solution format.
%.tiled_map_reductions.szn: %.dzn $(DISCOVERY_DIR)/tiled_map_reduction.mzn $(DISCOVERY_DIR)/common.mzn
	-minizinc $(MINIZINC_FLAGS) $(DISCOVERY_DIR)/tiled_map_reduction.mzn $< > $@

# Tiled map-reduction pattern matches in PDF format.
%.tiled_map_reductions.pdf: %.tiled_map_reductions.szn %.trace
	$(PROCESS_TRACE) -o $@ visualize $^ $(GRAPHVIZ_FLAGS)

# Linear scan pattern matches in MiniZinc solution format.
%.linear_scans.szn: %.dzn $(DISCOVERY_DIR)/linear_scan.mzn $(DISCOVERY_DIR)/common.mzn
	-minizinc $(MINIZINC_FLAGS) $(DISCOVERY_DIR)/linear_scan.mzn $< > $@

# Conditional linear scan pattern matches in PDF format.
%.linear_scans.pdf: %.linear_scans.szn %.trace
	$(PROCESS_TRACE) -o $@ visualize $^ $(GRAPHVIZ_FLAGS)

# Conditional linear scan pattern matches in MiniZinc solution format.
%.conditional_linear_scans.szn: %.dzn $(DISCOVERY_DIR)/conditional_linear_scan.mzn $(DISCOVERY_DIR)/common.mzn
	-minizinc $(MINIZINC_FLAGS) $(DISCOVERY_DIR)/conditional_linear_scan.mzn $< > $@

# Conditional linear scan pattern matches in PDF format.
%.conditional_linear_scans.pdf: %.conditional_linear_scans.szn %.trace
	$(PROCESS_TRACE) -o $@ visualize $^ $(GRAPHVIZ_FLAGS)

# Pipeline pattern matches in MiniZinc solution format.
%.pipelines.szn: %.dzn $(DISCOVERY_DIR)/pipeline.mzn $(DISCOVERY_DIR)/common.mzn
	minizinc $(MINIZINC_FLAGS) $(DISCOVERY_DIR)/pipeline.mzn $< > $@

# Pipeline pattern matches in PDF format.
%.pipelines.pdf: %.pipelines.szn %.trace
	$(PROCESS_TRACE) -o $@ visualize $^ $(GRAPHVIZ_FLAGS)

# Instrumented LLVM IR for single C++ source file.
%.ll: %.cpp
	$(CXX) $< -o $@ $(CXXFLAGS) -emit-llvm -S

# Instrumented LLVM IR for single C source file.
%.ll: %.c
	$(CC) $< -o $@ $(CFLAGS) -emit-llvm -S

# Pattern matches in HTML LLVM remarks format.
%.html: %.szn
	$(PROCESS_MATCHES) $< -o /dev/null --html $@

# Trace in GraphViz format where tag instances get different colors.
%.instances.trace.gv: %.trace
	$(PROCESS_TRACE) $(GRAPHVIZ_FLAGS) --output-format=graphviz --color-tag-instances $(TAG) print $< > $@

# Trace in GraphViz format where tag groups get different colors.
%.groups.trace.gv: %.trace
	$(PROCESS_TRACE) $(GRAPHVIZ_FLAGS) --output-format=graphviz --color-tag-groups $(TAG) print $< > $@

# Trace in GraphViz format.
%.trace.gv: %.trace
	$(PROCESS_TRACE) $(GRAPHVIZ_FLAGS) --output-format=graphviz print $< > $@

# Trace in PDF format.
%.pdf: %.trace.gv
	dot -Tpdf $< -o $@

# PDF of a given GraphViz trace.
%.pdf : %.gv
	dot -Tpdf $< > $@

# Clean all intermediate files.
clean:
	rm -rf trace *.bin *.trace *.gv *.pdf *.ll *.html *.yaml *.dzn *.szn *.tags *.aliases *.components *.groups *.instructions *~
