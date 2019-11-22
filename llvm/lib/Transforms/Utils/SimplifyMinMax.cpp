//===- SimplifyMinMax.cpp - Min/Max Simplification Pass -------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This pass simplifies specific min/max control-flow regions using select
// instructions. The pass is arranged as a peephole, and does not assume any
// previous IR simplification. The pass is useful to explicate computation that
// just moves data without transforming it so that it can be recognized by the
// Discovery trace-and-match tool.
//
//===----------------------------------------------------------------------===//

#include "llvm/Pass.h"
#include "llvm/Transforms/Utils.h"
#include "llvm/Transforms/Utils/SimplifyMinMax.h"

using namespace llvm;

#define DEBUG_TYPE "simplifyminmax"

INITIALIZE_PASS_BEGIN(SimplifyMinMaxPass, "simplifyminmax",
                      "Simplify min/max CFG regions", false, false)
INITIALIZE_PASS_END(SimplifyMinMaxPass, "simplifyminmax",
                    "Simplify min/max CFG regions", false, false)

char SimplifyMinMaxPass::ID = 0;

SimplifyMinMaxPass::SimplifyMinMaxPass() : FunctionPass(ID) {
  initializeSimplifyMinMaxPassPass(*PassRegistry::getPassRegistry());
}

void SimplifyMinMaxPass::getAnalysisUsage(AnalysisUsage &AU) const {}

bool SimplifyMinMaxPass::maybeSimplifyMax(BasicBlock &BB) {
  // TODO: grep for 'triangle' in SimplifyCFG.cpp
  return false;
}

bool SimplifyMinMaxPass::runOnFunction(Function &F) {
  bool Changed = false;
  for (auto & BB : F) {
    if (maybeSimplifyMax(BB))
      Changed = true;
  }
  errs() << "function: " << F.getName() << "\n";
  return Changed;
}

// Public interface to the SimplifyMinMax pass.
FunctionPass * llvm::createSimplifyMinMaxPass() {
  return new SimplifyMinMaxPass();
}
