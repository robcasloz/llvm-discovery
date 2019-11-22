//===- SimplifyMinMax.h - Min/Max Simplification Pass -----------*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
/// \file
/// This file provides the interface for LLVM's Min/Max Simplification Pass.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_TRANSFORMS_UTILS_SIMPLIFYMINMAX_H
#define LLVM_TRANSFORMS_UTILS_SIMPLIFYMINMAX_H

#include "llvm/IR/PassManager.h"

namespace llvm {

class Function;

class SimplifyMinMaxPass : public FunctionPass {
public:
  static char ID;
  SimplifyMinMaxPass();
  void getAnalysisUsage(AnalysisUsage &AU) const override;
  bool maybeSimplifyMax(BasicBlock &BB);
  bool runOnFunction(Function &F) override;
};

} // end namespace llvm

#endif // LLVM_TRANSFORMS_UTILS_SIMPLIFYMINMAX_H

