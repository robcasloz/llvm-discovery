# Discovery of Structured Parallelism In Sequential and Parallel Code

This repository contains a tool for finding parallel patterns in the execution of sequential and multi-threaded C and C++ code. The tool instruments the code and generates execution traces using an extended version of LLVM, and finds parallel patterns on the traces using a combination of high-level exploration and constraint-based graph matching techniques.

## Trace generation

The code instrumentation and trace generation component is implemented on top of LLVM's DataFlowSanitizer. Most of the additions can be found in the files `llvm/lib/Transforms/Instrumentation/DataFlowSanitizer.cpp` and `compiler-rt/lib/dfsan/dfsan.cc`.

### Dependencies

- Clang 7 or later (to compile the project)

- Boost 1.68

### Compiling

Take the following steps (beware that compiling LLVM consumes a significant amount of resources):

```
git clone --recursive https://github.com/robcasloz/llvm-discovery.git
cd llvm-project
mkdir build
cd build
cmake -DLLVM_CCACHE_BUILD=1 -DCMAKE_C_COMPILER=clang -DCMAKE_CXX_COMPILER=clang++ -DBUILD_SHARED_LIBS=1 -DLLVM_ENABLE_PROJECTS="clang;compiler-rt" -DLLVM_TARGETS_TO_BUILD="X86" -DCMAKE_CXX_STANDARD=14 -DCMAKE_BUILD_TYPE=Release -G "Ninja" ../llvm
ninja compiler-rt clang
```

### Instrumenting a source file

The directory `llvm/tools/discovery/examples` contains a simple `hello-world.c` example source file. To instrument it, run the compiled `clang` with the following arguments:

```
clang -g -fno-discard-value-names -Xclang -disable-lifetime-markers -fsanitize=dataflow -mllvm -dfsan-discovery llvm/tools/discovery/examples/hello-world.c
```

The optional argument `-mllvm -dfsan-discovery-commutativity-list=FILE` can be used to provide a [Sanitizer special case list](https://releases.llvm.org/7.0.0/tools/clang/docs/SanitizerSpecialCaseList.html) that lists external functions (for example from the standard C library) that can be part of parallel patterns. An example file can be found in `llvm/tools/discovery/commutative.txt`.

### Generating a trace

Running the instrumented binary generated by `clang` using the above command generates as a side effect a `trace` file in the working directory. This file is used as input to the parallel pattern discovery phase. It is important to run the instrumented binary with as small input data as possible, since the traces grow very quickly as the instrumented program executes.

The directory `llvm/tools/discovery/examples` contains the trace `hello-world.trace` generated by running the instrumented example.

## Discovery of parallel patterns

The parallel pattern discovery finding component is implemented as a collection of Python scripts and [MiniZinc](https://www.minizinc.org) graph matching models. Both can be found in the `llvm/tools/discovery` directory.

### Dependencies

- Python 2.7 or later

- MiniZinc 2.3.2 or later

### Finding parallel patterns in a trace

To find do-all, map, reduction, and scan patterns in each loop of the example trace, run:

```
llvm/tools/discovery/find_patterns.py llvm/tools/discovery/examples/hello-world.trace
```

The script outputs a table in CSV format where each row corresponds to a loop in the instrumented source code, and the `doall`, `map`, `reduction`, and `scan` columns indicate whether a pattern has been found.

To find do-all, map, reduction, scan, and pipeline patterns within all possible combinations of instructions in the example trace, add the option `--level=instruction` to the same command:

```
llvm/tools/discovery/find_patterns.py --level=instruction llvm/tools/discovery/examples/hello-world.trace
```

Beware that finding patterns at instruction level is computationally very costly and does not currently scale beyond small examples.

The file `llvm/tools/discovery/Makefile` provides further support for processing, transforming, and visualizing traces; invoking the constraint-based pattern finder, and visualizing and exporting the found patterns as [LLVM remark diagnostics](https://llvm.org/docs/Remarks.html). See the file documentation for more information.

## Contact

If you have questions or suggestions, please do not hesitate to contact us:

- [Roberto Castañeda Lozano](https://robcasloz.github.io/) [<roberto.castaneda@ed.ac.uk>]
- [Murray Cole](https://homepages.inf.ed.ac.uk/mic/) [<mic@inf.ed.ac.uk>]
- [Björn Franke](https://blog.inf.ed.ac.uk/bfranke/) [<bfranke@inf.ed.ac.uk>]
