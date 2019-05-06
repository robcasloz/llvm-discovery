# Generation of dynamic data-flow graphs with LLVM

This project is extended to generate dynamic data-flow graphs with the help of
LLVM's DataFlowSanitizer. Most of the extensions are implemented in the files
`llvm/lib/Transforms/Instrumentation/DataFlowSanitizer.cpp` and
`compiler-rt/lib/dfsan/dfsan.cc`.

## Compiling the extended LLVM project

```
git clone https://github.com/robcasloz/llvm-discovery.git
cd llvm-project
mkdir build
cd build
cmake -DLLVM_ENABLE_PROJECTS="clang;compiler-rt" -DLLVM_PARALLEL_LINK_JOBS=1 -DLLVM_TARGETS_TO_BUILD="X86" ../llvm
make compiler-rt clang
```

## Compiling a source file `foo.c` with data-flow tracing enabled

```
clang foo.c -fsanitize=dataflow -mllvm -dfsan-discovery [-mllvm -dfsan-discovery-debug]
```

The optional argument `-mllvm -dfsan-discovery-debug` labels the data-flow graph
nodes with the name of their operations.
