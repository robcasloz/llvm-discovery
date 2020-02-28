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
GRAPHVIZ_FLAGS = --simplify-loc
MINIZINC_FLAGS ?= -a --solver chuffed
MINIZINC_DZN_FLAGS ?=
OPT_VIEWER = $(DISCOVERY_DIR)/../opt-viewer/opt-viewer.py
TAG ?= 0
GROUP ?= 0
NAME ?= ".*"
NAMES ?= add fadd mul fmul and or xor
COMPONENT ?= 0
MIN_COMPONENT_NODES ?= 3

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
	$(PROCESS_TRACE) --output-format=plain --min-nodes $(MIN_COMPONENT_NODES) transform --filter-component $(COMPONENT) $< > $@

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
	$(PROCESS_TRACE) --min-nodes $(MIN_COMPONENT_NODES) query --print-components $< > $@

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

# DOALL pattern matches in YAML LLVM remarks format.
%.doalls.yaml: %.doalls.szn %.trace
	$(PROCESS_TRACE) report $^ > $@

# Map pattern matches in MiniZinc solution format.
%.maps.szn: %.dzn $(DISCOVERY_DIR)/map.mzn $(DISCOVERY_DIR)/common.mzn
	-minizinc $(MINIZINC_FLAGS) $(DISCOVERY_DIR)/map.mzn $< > $@

# Map pattern matches in PDF format.
%.maps.pdf: %.maps.szn %.trace
	$(PROCESS_TRACE) -o $@ visualize $^ $(GRAPHVIZ_FLAGS)

# Map pattern matches in YAML LLVM remarks format.
%.maps.yaml: %.maps.szn %.trace
	$(PROCESS_TRACE) report $^ > $@

# Map-filter pattern matches in MiniZinc solution format.
%.mapfilters.szn: %.dzn $(DISCOVERY_DIR)/mapfilter.mzn $(DISCOVERY_DIR)/common.mzn
	-minizinc $(MINIZINC_FLAGS) $(DISCOVERY_DIR)/mapfilter.mzn $< > $@

# Map-filter pattern matches in PDF format.
%.mapfilters.pdf: %.mapfilters.szn %.trace
	$(PROCESS_TRACE) -o $@ visualize $^ $(GRAPHVIZ_FLAGS)

# Map-filter pattern matches in YAML LLVM remarks format.
%.mapfilters.yaml: %.mapfilters.szn %.trace
	$(PROCESS_TRACE) report $^ > $@

# Reduction pattern matches in MiniZinc solution format.
%.reductions.szn: %.dzn $(DISCOVERY_DIR)/reduction.mzn $(DISCOVERY_DIR)/common.mzn
	-minizinc $(MINIZINC_FLAGS) $(DISCOVERY_DIR)/reduction.mzn $< > $@

# Reduction pattern matches in PDF format.
%.reductions.pdf: %.reductions.szn %.trace
	$(PROCESS_TRACE) -o $@ visualize $^ $(GRAPHVIZ_FLAGS)

# Reduction pattern matches in YAML LLVM remarks format.
%.reductions.yaml: %.reductions.szn %.trace
	$(PROCESS_TRACE) report $^ > $@

# Two-phase reduction pattern matches in MiniZinc solution format.
%.twophasereductions.szn: %.dzn $(DISCOVERY_DIR)/twophasereduction.mzn $(DISCOVERY_DIR)/common.mzn
	-minizinc $(MINIZINC_FLAGS) $(DISCOVERY_DIR)/twophasereduction.mzn $< > $@

# Two-phase reduction pattern matches in PDF format.
%.twophasereductions.pdf: %.twophasereductions.szn %.trace
	$(PROCESS_TRACE) -o $@ visualize $^ $(GRAPHVIZ_FLAGS)

# Two-phase reduction pattern matches in YAML LLVM remarks format.
%.twophasereductions.yaml: %.twophasereductions.szn %.trace
	$(PROCESS_TRACE) report $^ > $@

# Scan pattern matches in MiniZinc solution format.
%.scans.szn: %.dzn $(DISCOVERY_DIR)/scan.mzn $(DISCOVERY_DIR)/common.mzn
	-minizinc $(MINIZINC_FLAGS) $(DISCOVERY_DIR)/scan.mzn $< > $@

# Scan pattern matches in PDF format.
%.scans.pdf: %.scans.szn %.trace
	$(PROCESS_TRACE) -o $@ visualize $^ $(GRAPHVIZ_FLAGS)

# Scan pattern matches in YAML LLVM remarks format.
%.scans.yaml: %.scans.szn %.trace
	$(PROCESS_TRACE) report $^ > $@

# Pipeline pattern matches in MiniZinc solution format.
%.pipelines.szn: %.dzn $(DISCOVERY_DIR)/pipeline.mzn $(DISCOVERY_DIR)/common.mzn
	minizinc $(MINIZINC_FLAGS) $(DISCOVERY_DIR)/pipeline.mzn $< > $@

# Pipeline pattern matches in PDF format.
%.pipelines.pdf: %.pipelines.szn %.trace
	$(PROCESS_TRACE) -o $@ visualize $^ $(GRAPHVIZ_FLAGS)

# Pipeline pattern matches in YAML LLVM remarks format.
%.pipelines.yaml: %.pipelines.szn %.trace
	$(PROCESS_TRACE) report $^ > $@

# Combined pattern matches in YAML LLVM remarks format.
%.patterns.yaml: %.doalls.yaml %.maps.yaml %.mapfilters.yaml %.reductions.yaml %.scans.yaml %.pipelines.yaml
	cat $^ > $@

# Instrumented LLVM IR for single C++ source file.
%.ll: %.cpp
	$(CXX) $< -o $@ $(CXXFLAGS) -emit-llvm -S

# Instrumented LLVM IR for single C source file.
%.ll: %.c
	$(CC) $< -o $@ $(CFLAGS) -emit-llvm -S

# Pattern matches in HTML LLVM remarks format.
%.html: %.yaml
	rm -rf $@
	$(OPT_VIEWER) $<
	mv html $@

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

# Prefix of all .trace files under BASENAME.
ALL_TRACES = $(basename $(wildcard $(BASENAME)*.trace))

# DO-ALL patterns found by collapsing the nodes in each trace.
all-collapsed-doalls-szn: TAG=all
all-collapsed-doalls-szn: $(addsuffix .collapsed.doalls.szn, $(ALL_TRACES))

# Map patterns found by collapsing the nodes in each trace.
all-collapsed-maps-szn: TAG=all
all-collapsed-maps-szn: $(addsuffix .collapsed.maps.szn, $(ALL_TRACES))

# Map-filter patterns found by collapsing the nodes in each trace.
all-collapsed-mapfilters-szn: TAG=all
all-collapsed-mapfilters-szn: $(addsuffix .collapsed.mapfilters.szn, $(ALL_TRACES))

# Reduction patterns found by collapsing the nodes in each trace.
all-collapsed-reductions-szn: TAG=all
all-collapsed-reductions-szn: $(addsuffix .collapsed.reductions.szn, $(ALL_TRACES))

# Scan patterns found by collapsing the nodes in each trace.
all-collapsed-scans-szn: TAG=all
all-collapsed-scans-szn: $(addsuffix .collapsed.scans.szn, $(ALL_TRACES))

# Clean all intermediate files.
clean:
	rm -rf trace *.bin *.trace *.gv *.pdf *.ll *.html *.yaml *.dzn *.szn *.tags *.aliases *.components *.groups *~
