//===-- Utils.cpp - TransformUtils Infrastructure -------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file defines the common initialization infrastructure for the
// TransformUtils library.
//
//===----------------------------------------------------------------------===//

#include "llvm/Transforms/Utils.h"
#include "llvm-c/Initialization.h"
#include "llvm-c/Transforms/Utils.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/InitializePasses.h"
#include "llvm/PassRegistry.h"

using namespace llvm;

/// initializeTransformUtils - Initialize all passes in the TransformUtils
/// library.
void llvm::initializeTransformUtils(PassRegistry &Registry) {
  initializeAddDiscriminatorsLegacyPassPass(Registry);
  initializeBreakCriticalEdgesPass(Registry);
  initializeInstNamerPass(Registry);
  initializeLCSSAWrapperPassPass(Registry);
  initializeLibCallsShrinkWrapLegacyPassPass(Registry);
  initializeLoopSimplifyPass(Registry);
  initializeLowerInvokeLegacyPassPass(Registry);
  initializeLowerSwitchPass(Registry);
  initializeNameAnonGlobalLegacyPassPass(Registry);
  initializePromoteLegacyPassPass(Registry);
  initializeStripNonLineTableDebugInfoPass(Registry);
  initializeUnifyFunctionExitNodesPass(Registry);
  initializeMetaRenamerPass(Registry);
  initializeStripGCRelocatesPass(Registry);
  initializePredicateInfoPrinterLegacyPassPass(Registry);
  // Iterator recognition passes
  initializeIteratorRecognitionWrapperPassPass(Registry);
  // Pedigree passes
  initializePDGraphWrapperPassPass(Registry);
  initializeCDGraphWrapperPassPass(Registry);
  initializeDDGraphWrapperPassPass(Registry);
  initializeMDGraphWrapperPassPass(Registry);

}

/// LLVMInitializeTransformUtils - C binding for initializeTransformUtilsPasses.
void LLVMInitializeTransformUtils(LLVMPassRegistryRef R) {
  initializeTransformUtils(*unwrap(R));
}

void LLVMAddLowerSwitchPass(LLVMPassManagerRef PM) {
  unwrap(PM)->add(createLowerSwitchPass());
}

void LLVMAddPromoteMemoryToRegisterPass(LLVMPassManagerRef PM) {
  unwrap(PM)->add(createPromoteMemoryToRegisterPass());
}

