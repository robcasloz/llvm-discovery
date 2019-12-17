# Generation of dynamic data-flow graphs with LLVM

This project is extended to generate dynamic data-flow graphs with the help of LLVM's DataFlowSanitizer. Most of the extensions are implemented in the files `llvm/lib/Transforms/Instrumentation/DataFlowSanitizer.cpp` and `compiler-rt/lib/dfsan/dfsan.cc`.

## Additional dependencies

- Clang 7 or later (to compile the project)

- Boost 1.68

## Compiling the extended LLVM project

```
git clone --recursive https://github.com/robcasloz/llvm-discovery.git
cd llvm-project
mkdir build
cd build
cmake -DLLVM_CCACHE_BUILD=1 -DCMAKE_C_COMPILER=clang -DCMAKE_CXX_COMPILER=clang++ -DBUILD_SHARED_LIBS=1 -DLLVM_ENABLE_PROJECTS="clang;compiler-rt" -DLLVM_TARGETS_TO_BUILD="X86" -DCMAKE_CXX_STANDARD=14 -DCMAKE_BUILD_TYPE=Release -G "Ninja" ../llvm
ninja compiler-rt clang
```

## Compiling a source file `foo.c` with data-flow tracing enabled

```
clang -g -fno-discard-value-names -Xclang -disable-lifetime-markers -fsanitize=dataflow -mllvm -dfsan-discovery [-mllvm -dfsan-discovery-commutativity-list=FILE] foo.c
```

where `FILE` is a [Sanitizer special case list](https://releases.llvm.org/7.0.0/tools/clang/docs/SanitizerSpecialCaseList.html) that lists external functions (for example from the standard C library) that can be part of parallel patterns. To accept patterns that include calls to a function `bar`, add the following line to `FILE`:

```
fun:bar=commutative
```
