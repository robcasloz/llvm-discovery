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
OPT_VIEWER = $(DISCOVERY_DIR)/../opt-viewer/opt-viewer.py

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
%.filtered.trace: %.trace
	$(PROCESS_TRACE) --output-format=plain transform --filter-tags $(TAG) $< > $@

# Collapsed trace for a given tag.
%.collapsed.trace: %.trace
	$(PROCESS_TRACE) --output-format=plain transform --collapse-tags $(TAG) $< > $@

# Trace as input to the MiniZinc pattern finder.
%.dzn: %.trace
	$(PROCESS_TRACE) --output-format=minizinc print $< > $@

# List of tags in a trace.
%.tags: %.trace
	$(PROCESS_TRACE) query --print-tags $< > $@

# List of tag aliases in a trace.
%.aliases: %.trace
	$(PROCESS_TRACE) query --print-tag-aliases $< > $@

# One trace file for each tag in the %.tags file.
%.traces: %.trace %.tags
	while read TAG; do \
		$(MAKE) $*.filtered.trace TAG=$$TAG; \
		mv $*.filtered.trace $*.$$TAG.trace; \
	done < $*.tags

# Map pattern matches in MiniZinc solution format.
%.maps.szn: %.dzn $(DISCOVERY_DIR)/map.mzn $(DISCOVERY_DIR)/common.mzn
	-minizinc $(MINIZINC_FLAGS) $(DISCOVERY_DIR)/map.mzn $< > $@

# Map pattern matches in PDF format.
%.maps.pdf: %.maps.szn %.trace
	$(PROCESS_TRACE) -o $@ visualize $^ $(GRAPHVIZ_FLAGS)

# Map pattern matches in YAML LLVM remarks format.
%.maps.yaml: %.maps.szn %.trace
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
%.patterns.yaml: %.maps.yaml %.reductions.yaml %.scans.yaml %.pipelines.yaml
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

# Trace in GraphViz format where instances of the tag get different colors.
%.colored.trace.gv: %.trace
	$(PROCESS_TRACE) $(GRAPHVIZ_FLAGS) --output-format=graphviz --color-tag $(TAG) print $< > $@

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

# Map patterns found by collapsing the nodes in each trace.
all-collapsed-maps-szn: TAG=all
all-collapsed-maps-szn: $(addsuffix .collapsed.maps.szn, $(ALL_TRACES))

# Reduction patterns found by collapsing the nodes in each trace.
all-collapsed-reductions-szn: TAG=all
all-collapsed-reductions-szn: $(addsuffix .collapsed.reductions.szn, $(ALL_TRACES))

# Scan patterns found by collapsing the nodes in each trace.
all-collapsed-scans-szn: TAG=all
all-collapsed-scans-szn: $(addsuffix .collapsed.scans.szn, $(ALL_TRACES))

# Clean all intermediate files.
clean:
	rm -rf trace *.bin *.trace *.gv *.pdf *.ll *.html *.yaml *.dzn *.szn *.tags *.aliases *~
