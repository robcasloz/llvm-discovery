//===- DataFlowSanitizer.cpp - dynamic data flow analysis -----------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
/// \file
/// This file is a part of DataFlowSanitizer, a generalised dynamic data flow
/// analysis.
///
/// Unlike other Sanitizer tools, this tool is not designed to detect a specific
/// class of bugs on its own.  Instead, it provides a generic dynamic data flow
/// analysis framework to be used by clients to help detect application-specific
/// issues within their own code.
///
/// The analysis is based on automatic propagation of data flow labels (also
/// known as taint labels) through a program as it performs computation.  Each
/// byte of application memory is backed by four bytes of shadow memory which
/// hold the label.  On Linux/x86_64, memory is laid out as follows:
///
/// +--------------------+ 0x800000000000 (top of memory)
/// | application memory |
/// +--------------------+ 0x700000008000 (kAppAddr)
/// |                    |
/// |       unused       |
/// |                    |
/// +--------------------+ 0x400200000000 (kUnusedAddr)
/// |    union table     |
/// +--------------------+ 0x400000000000 (kUnionTableAddr)
/// |   shadow memory    |
/// +--------------------+ 0x000000010000 (kShadowAddr)
/// | reserved by kernel |
/// +--------------------+ 0x000000000000
///
/// To derive a shadow memory address from an application memory address,
/// bits 44-46 are cleared to bring the address into the range
/// [0x000000008000,0x100000000000).  Then the address is shifted left by 2 to
/// account for the four-byte representation of shadow labels and move the
/// address into the shadow memory range.  See the function
/// DataFlowSanitizer::getShadowAddress below.
///
/// For more information, please refer to the design document:
/// http://clang.llvm.org/docs/DataFlowSanitizerDesign.html
//
//===----------------------------------------------------------------------===//

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/DepthFirstIterator.h"
#include "llvm/ADT/None.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/ADT/Triple.h"
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/Argument.h"
#include "llvm/IR/Attributes.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/Constant.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalAlias.h"
#include "llvm/IR/GlobalValue.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/MDBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/User.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/Pass.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/SpecialCaseList.h"
#include "llvm/Transforms/Instrumentation.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils.h"
#include "llvm/Transforms/Utils/SimplifyMinMax.h"
#include "IteratorRecognition/Analysis/Passes/IteratorRecognitionPass.hpp"

#include <algorithm>
#include <cassert>
#include <cstddef>
#include <cstdint>
#include <iterator>
#include <memory>
#include <set>
#include <string>
#include <utility>
#include <vector>

using namespace llvm;
using namespace iteratorrecognition;
using InstRefSet = DenseSet<const Instruction *>;

// External symbol to be used when generating the shadow address for
// architectures with multiple VMAs. Instead of using a constant integer
// the runtime will set the external mask based on the VMA range.
static const char *const kDFSanExternShadowPtrMask = "__dfsan_shadow_ptr_mask";

// The -dfsan-preserve-alignment flag controls whether this pass assumes that
// alignment requirements provided by the input IR are correct.  For example,
// if the input IR contains a load with alignment 8, this flag will cause
// the shadow load to have alignment 16.  This flag is disabled by default as
// we have unfortunately encountered too much code (including Clang itself;
// see PR14291) which performs misaligned access.
static cl::opt<bool> ClPreserveAlignment(
    "dfsan-preserve-alignment",
    cl::desc("respect alignment requirements provided by input IR"), cl::Hidden,
    cl::init(false));

// The ABI list files control how shadow parameters are passed. The pass treats
// every function labelled "uninstrumented" in the ABI list file as conforming
// to the "native" (i.e. unsanitized) ABI.  Unless the ABI list contains
// additional annotations for those functions, a call to one of those functions
// will produce a warning message, as the labelling behaviour of the function is
// unknown.  The other supported annotations are "functional" and "discard",
// which are described below under DataFlowSanitizer::WrapperKind.
static cl::list<std::string> ClABIListFiles(
    "dfsan-abilist",
    cl::desc("File listing native ABI functions and how the pass treats them"),
    cl::Hidden);

// Controls whether the pass uses IA_Args or IA_TLS as the ABI for instrumented
// functions (see DataFlowSanitizer::InstrumentedABI below).
static cl::opt<bool> ClArgsABI(
    "dfsan-args-abi",
    cl::desc("Use the argument ABI rather than the TLS ABI"),
    cl::Hidden);

// Controls whether the pass includes or ignores the labels of pointers in load
// instructions.
static cl::opt<bool> ClCombinePointerLabelsOnLoad(
    "dfsan-combine-pointer-labels-on-load",
    cl::desc("Combine the label of the pointer with the label of the data when "
             "loading from memory."),
    cl::Hidden, cl::init(false));

// Controls whether the pass includes or ignores the labels of pointers in
// stores instructions.
static cl::opt<bool> ClCombinePointerLabelsOnStore(
    "dfsan-combine-pointer-labels-on-store",
    cl::desc("Combine the label of the pointer with the label of the data when "
             "storing in memory."),
    cl::Hidden, cl::init(false));

static cl::opt<bool> ClDebugNonzeroLabels(
    "dfsan-debug-nonzero-labels",
    cl::desc("Insert calls to __dfsan_nonzero_label on observing a parameter, "
             "load or return with a nonzero label"),
    cl::Hidden);

static cl::opt<bool> ClDiscovery(
    "dfsan-discovery",
    cl::desc("Use DataFlowSanitizer to build the dynamic data-flow graph"),
    cl::Hidden, cl::init(false));

static cl::opt<bool> ClDiscoveryDebug(
    "dfsan-discovery-debug",
    cl::desc("Refine the dynamic data-flow graph with debug information"),
    cl::Hidden, cl::init(true));

cl::opt<bool> ClDiscoveryMarkIterators(
    "dfsan-discovery-mark-iterators",
    cl::desc("Mark iterator code in the dynamic data-flow graph"),
    cl::Hidden, cl::init(true));

cl::opt<bool> ClDiscoverySimplifyMinMax(
    "dfsan-discovery-simplify-minmax",
    cl::desc("Make min/max control-flow regions explicit using select instructions"),
    cl::Hidden, cl::init(false));

static cl::opt<bool> ClDiscoveryTagLoops(
    "dfsan-discovery-tag-loops",
    cl::desc("Tag data-flow with corresponding loop information"),
    cl::Hidden, cl::init(true));

static cl::opt<bool> ClDiscoveryTagIterationExpressions(
    "dfsan-discovery-tag-iteration-expressions",
    cl::desc("Tag data-flow corresponding to iteration expressions in for loops, requires setting -fno-discard-value-names to true"),
    cl::Hidden, cl::init(false));

static cl::opt<bool> ClDiscoveryTagSTL(
    "dfsan-discovery-tag-stl",
    cl::desc("Tag loops from STL header files"),
    cl::Hidden, cl::init(false));

static cl::list<std::string> ClDiscoveryCommutativityListFiles(
    "dfsan-discovery-commutativity-list",
    cl::desc("File listing commutative functions"),
    cl::Hidden);

static StringRef GetGlobalTypeString(const GlobalValue &G) {
  // Types of GlobalVariables are always pointer types.
  Type *GType = G.getValueType();
  // For now we support blacklisting struct types only.
  if (StructType *SGType = dyn_cast<StructType>(GType)) {
    if (!SGType->isLiteral())
      return SGType->getName();
  }
  return "<unknown type>";
}

static StringRef getCalleeName(CallInst &CI) {
  if (InlineAsm * IA = dyn_cast<InlineAsm>(CI.getCalledValue()))
    return IA->getAsmString();
  return CI.getCalledFunction()->getName();
}

namespace {


class DFSanCommutativityList {
  std::unique_ptr<SpecialCaseList> SCL;

  std::vector<StringRef> Always =
    {"dfsan_trace_region",
     "dfsan_trace_instructions"};

 public:
  DFSanCommutativityList() = default;

  void set(std::unique_ptr<SpecialCaseList> List) { SCL = std::move(List); }

  /// Returns whether this function is listed as commutative.
  bool isIn(StringRef FunctionName) const {
    if (std::find(Always.begin(), Always.end(), FunctionName) != Always.end())
      return true;
    return SCL->inSection("commutative", "fun", FunctionName, "commutative");
  }
};

class DFSanABIList {
  std::unique_ptr<SpecialCaseList> SCL;

 public:
  DFSanABIList() = default;

  void set(std::unique_ptr<SpecialCaseList> List) { SCL = std::move(List); }

  /// Returns whether either this function or its source file are listed in the
  /// given category.
  bool isIn(const Function &F, StringRef Category) const {
    return isIn(*F.getParent(), Category) ||
           SCL->inSection("dataflow", "fun", F.getName(), Category);
  }

  /// Returns whether this global alias is listed in the given category.
  ///
  /// If GA aliases a function, the alias's name is matched as a function name
  /// would be.  Similarly, aliases of globals are matched like globals.
  bool isIn(const GlobalAlias &GA, StringRef Category) const {
    if (isIn(*GA.getParent(), Category))
      return true;

    if (isa<FunctionType>(GA.getValueType()))
      return SCL->inSection("dataflow", "fun", GA.getName(), Category);

    return SCL->inSection("dataflow", "global", GA.getName(), Category) ||
           SCL->inSection("dataflow", "type", GetGlobalTypeString(GA),
                          Category);
  }

  /// Returns whether this module is listed in the given category.
  bool isIn(const Module &M, StringRef Category) const {
    return SCL->inSection("dataflow", "src", M.getModuleIdentifier(), Category);
  }
};

/// TransformedFunction is used to express the result of transforming one
/// function type into another.  This struct is immutable.  It holds metadata
/// useful for updating calls of the old function to the new type.
struct TransformedFunction {
  TransformedFunction(FunctionType* OriginalType,
                      FunctionType* TransformedType,
                      std::vector<unsigned> ArgumentIndexMapping)
      : OriginalType(OriginalType),
        TransformedType(TransformedType),
        ArgumentIndexMapping(ArgumentIndexMapping) {}

  // Disallow copies.
  TransformedFunction(const TransformedFunction&) = delete;
  TransformedFunction& operator=(const TransformedFunction&) = delete;

  // Allow moves.
  TransformedFunction(TransformedFunction&&) = default;
  TransformedFunction& operator=(TransformedFunction&&) = default;

  /// Type of the function before the transformation.
  FunctionType *OriginalType;

  /// Type of the function after the transformation.
  FunctionType *TransformedType;

  /// Transforming a function may change the position of arguments.  This
  /// member records the mapping from each argument's old position to its new
  /// position.  Argument positions are zero-indexed.  If the transformation
  /// from F to F' made the first argument of F into the third argument of F',
  /// then ArgumentIndexMapping[0] will equal 2.
  std::vector<unsigned> ArgumentIndexMapping;
};

/// Given function attributes from a call site for the original function,
/// return function attributes appropriate for a call to the transformed
/// function.
AttributeList TransformFunctionAttributes(
    const TransformedFunction& TransformedFunction,
    LLVMContext& Ctx, AttributeList CallSiteAttrs) {

  // Construct a vector of AttributeSet for each function argument.
  std::vector<llvm::AttributeSet> ArgumentAttributes(
      TransformedFunction.TransformedType->getNumParams());

  // Copy attributes from the parameter of the original function to the
  // transformed version.  'ArgumentIndexMapping' holds the mapping from
  // old argument position to new.
  for (unsigned i=0, ie = TransformedFunction.ArgumentIndexMapping.size();
       i < ie; ++i) {
    unsigned TransformedIndex = TransformedFunction.ArgumentIndexMapping[i];
    ArgumentAttributes[TransformedIndex] = CallSiteAttrs.getParamAttributes(i);
  }

  // Copy annotations on varargs arguments.
  for (unsigned i = TransformedFunction.OriginalType->getNumParams(),
       ie = CallSiteAttrs.getNumAttrSets(); i<ie; ++i) {
    ArgumentAttributes.push_back(CallSiteAttrs.getParamAttributes(i));
  }

  return AttributeList::get(
      Ctx,
      CallSiteAttrs.getFnAttributes(),
      CallSiteAttrs.getRetAttributes(),
      llvm::makeArrayRef(ArgumentAttributes));
}

class DataFlowSanitizer : public ModulePass {
  friend struct DFSanFunction;
  friend class DFSanVisitor;

  enum {
    ShadowWidth = 32
  };

  enum {
    BlockIdWidth = 64
  };

  /// Which ABI should be used for instrumented functions?
  enum InstrumentedABI {
    /// Argument and return value labels are passed through additional
    /// arguments and by modifying the return type.
    IA_Args,

    /// Argument and return value labels are passed through TLS variables
    /// __dfsan_arg_tls and __dfsan_retval_tls.
    IA_TLS
  };

  /// How should calls to uninstrumented functions be handled?
  enum WrapperKind {
    /// This function is present in an uninstrumented form but we don't know
    /// how it should be handled.  Print a warning and call the function anyway.
    /// Don't label the return value.
    WK_Warning,

    /// This function does not write to (user-accessible) memory, and its return
    /// value is unlabelled.
    WK_Discard,

    /// This function does not write to (user-accessible) memory, and the label
    /// of its return value is the union of the label of its arguments.
    WK_Functional,

    /// Instead of calling the function, a custom wrapper __dfsw_F is called,
    /// where F is the name of the function.  This function may wrap the
    /// original function or provide its own implementation.  This is similar to
    /// the IA_Args ABI, except that IA_Args uses a struct return type to
    /// pass the return value shadow in a register, while WK_Custom uses an
    /// extra pointer argument to return the shadow.  This allows the wrapped
    /// form of the function type to be expressed in C.
    WK_Custom
  };

  Module *Mod;
  LLVMContext *Ctx;
  IntegerType *ShadowTy;
  PointerType *ShadowPtrTy;
  IntegerType *IntptrTy;
  IntegerType *BlockIdTy;
  PointerType *StaticInstIdTy;
  ConstantInt *ZeroShadow;
  ConstantInt *ShadowPtrMask;
  ConstantInt *ShadowPtrMul;
  Constant *ArgTLS;
  Constant *RetvalTLS;
  void *(*GetArgTLSPtr)();
  void *(*GetRetvalTLSPtr)();
  Constant *GetArgTLS;
  Constant *GetRetvalTLS;
  Constant *ExternalShadowMask;
  FunctionType *DFSanUnionFnTy;
  FunctionType *DFSanUnionLoadFnTy;
  FunctionType *DFSanUnimplementedFnTy;
  FunctionType *DFSanSetLabelFnTy;
  FunctionType *DFSanNonzeroLabelFnTy;
  FunctionType *DFSanVarargWrapperFnTy;
  FunctionType *DFSanEnterAssignmentFnTy;
  FunctionType *DFSanPrintDataFlowFnTy;
  FunctionType *DFSanCreateLabelWithDefinerFnTy;
  FunctionType *DFSanPrintBlockPropertyFnTy;
  FunctionType *DFSanPrintInstructionPropertyFnTy;
  FunctionType *DFSanPrintRegionPropertyFnTy;
  FunctionType *DFSanOpenTraceFnTy;
  FunctionType *DFSanCloseTraceFnTy;
  FunctionType *DFSanReportFnTy;
  FunctionType *DFSanBeginTaggingFnTy;
  FunctionType *DFSanEndTaggingFnTy;
  FunctionType *DFSanNewGroupFnTy;
  Constant *DFSanUnionFn;
  Constant *DFSanCheckedUnionFn;
  Constant *DFSanUnionLoadFn;
  Constant *DFSanUnimplementedFn;
  Constant *DFSanSetLabelFn;
  Constant *DFSanNonzeroLabelFn;
  Constant *DFSanVarargWrapperFn;
  Constant *DFSanEnterAssignmentFn;
  Constant *DFSanPrintDataFlowFn;
  Constant *DFSanCreateLabelWithDefinerFn;
  Constant *DFSanPrintBlockPropertyFn;
  Constant *DFSanPrintInstructionPropertyFn;
  Constant *DFSanPrintRegionPropertyFn;
  Constant *DFSanOpenTraceFn;
  Constant *DFSanCloseTraceFn;
  Constant *DFSanReportFn;
  Constant *DFSanBeginTaggingFn;
  Constant *DFSanEndTaggingFn;
  Constant *DFSanNewGroupFn;
  MDNode *ColdCallWeights;
  DFSanABIList ABIList;
  DFSanCommutativityList CommutativityList;
  DenseMap<Value *, Function *> UnwrappedFnMap;
  AttrBuilder ReadOnlyNoneAttrs;
  bool DFSanRuntimeShadowMask = false;
  // Static instruction ID counter that is unique within the module.
  unsigned int StaticInstID = 0;

  Value *getShadowAddress(Value *Addr, Instruction *Pos);
  bool isInstrumented(const Function *F);
  bool isInstrumented(const GlobalAlias *GA);
  FunctionType *getArgsFunctionType(FunctionType *T);
  FunctionType *getTrampolineFunctionType(FunctionType *T);
  TransformedFunction getCustomFunctionType(FunctionType *T);
  InstrumentedABI getInstrumentedABI();
  WrapperKind getWrapperKind(Function *F);
  void addGlobalNamePrefix(GlobalValue *GV);
  Function *buildWrapperFunction(Function *F, StringRef NewFName,
                                 GlobalValue::LinkageTypes NewFLink,
                                 FunctionType *NewFT);
  Constant *getOrBuildTrampolineFunction(FunctionType *FT, StringRef FName);
  bool isImpureFunctional(StringRef FunctionName) const;
  bool isCommutative(CallInst *CI);

public:
  static char ID;

  DataFlowSanitizer(
      const std::vector<std::string> &ABIListFiles = std::vector<std::string>(),
      void *(*getArgTLS)() = nullptr, void *(*getRetValTLS)() = nullptr);

  void getAnalysisUsage(AnalysisUsage &AU) const override;
  bool doInitialization(Module &M) override;
  bool runOnModule(Module &M) override;
};

struct DFSanFunction {
  DataFlowSanitizer &DFS;
  Function *F;
  DominatorTree DT;
  DataFlowSanitizer::InstrumentedABI IA;
  bool IsNativeABI;
  Value *ArgTLSPtr = nullptr;
  Value *RetvalTLSPtr = nullptr;
  AllocaInst *LabelReturnAlloca = nullptr;
  DenseMap<Value *, Value *> ValShadowMap;
  DenseMap<AllocaInst *, AllocaInst *> AllocaShadowMap;
  std::vector<std::pair<PHINode *, PHINode *>> PHIFixups;
  DenseSet<Instruction *> SkipInsts;
  std::vector<Value *> NonZeroChecks;
  bool AvoidNewBlocks;
  // Set of instructions marked as belonging to an iterator.
  InstRefSet IRInsts;

  struct CachedCombinedShadow {
    BasicBlock *Block;
    Value *Shadow;
  };
  DenseMap<std::pair<Value *, Value *>, CachedCombinedShadow>
      CachedCombinedShadows;
  DenseMap<Value *, std::set<Value *>> ShadowElements;

  DFSanFunction(DataFlowSanitizer &DFS, Function *F, bool IsNativeABI,
                InstRefSet IRInsts)
    : DFS(DFS), F(F), IA(DFS.getInstrumentedABI()), IsNativeABI(IsNativeABI),
      IRInsts(IRInsts) {
    DT.recalculate(*F);
    // FIXME: Need to track down the register allocator issue which causes poor
    // performance in pathological cases with large numbers of basic blocks.
    AvoidNewBlocks = ClDiscovery ? true : F->size() > 1000; // FIXME: temp, just to simplify!
  }

  Value *getArgTLSPtr();
  Value *getArgTLS(unsigned Index, Instruction *Pos);
  Value *getRetvalTLS();
  Value *getShadow(Value *V);
  void setShadow(Instruction *I, Value *Shadow);
  Value *combineShadows(Value *V1, Value *V2, Instruction *Pos);
  Value *combineOperandShadows(Instruction *Inst);
  Value *loadShadow(Value *ShadowAddr, uint64_t Size, uint64_t Align,
                    Instruction *Pos);
  void storeShadow(Value *Addr, uint64_t Size, uint64_t Align, Value *Shadow,
                   Instruction *Pos);
};

class DFSanVisitor : public InstVisitor<DFSanVisitor> {
public:
  DFSanFunction &DFSF;

  DFSanVisitor(DFSanFunction &DFSF) : DFSF(DFSF) {}

  const DataLayout &getDataLayout() const {
    return DFSF.F->getParent()->getDataLayout();
  }

  void visitOperandShadowInst(Instruction &I);
  void visitBinaryOperator(BinaryOperator &BO);
  void visitCastInst(CastInst &CI);
  void visitCmpInst(CmpInst &CI);
  void visitGetElementPtrInst(GetElementPtrInst &GEPI);
  void visitLoadInst(LoadInst &LI);
  void visitStoreInst(StoreInst &SI);
  void visitReturnInst(ReturnInst &RI);
  void visitCallSite(CallSite CS);
  void visitPHINode(PHINode &PN);
  void visitExtractElementInst(ExtractElementInst &I);
  void visitInsertElementInst(InsertElementInst &I);
  void visitShuffleVectorInst(ShuffleVectorInst &I);
  void visitExtractValueInst(ExtractValueInst &I);
  void visitInsertValueInst(InsertValueInst &I);
  void visitAllocaInst(AllocaInst &I);
  void visitSelectInst(SelectInst &I);
  void visitMemSetInst(MemSetInst &I);
  void visitMemTransferInst(MemTransferInst &I);
  void visitBranchInst(BranchInst &I);
};

} // end anonymous namespace

char DataFlowSanitizer::ID;

INITIALIZE_PASS_BEGIN(DataFlowSanitizer, "dfsan",
                     "DataFlowSanitizer: dynamic data flow analysis.", false, false)
INITIALIZE_PASS_DEPENDENCY(IteratorRecognitionWrapperPass)
INITIALIZE_PASS_END(DataFlowSanitizer, "dfsan",
                     "DataFlowSanitizer: dynamic data flow analysis.", false, false)

ModulePass *
llvm::createDataFlowSanitizerPass(const std::vector<std::string> &ABIListFiles,
                                  void *(*getArgTLS)(),
                                  void *(*getRetValTLS)()) {
  return new DataFlowSanitizer(ABIListFiles, getArgTLS, getRetValTLS);
}

DataFlowSanitizer::DataFlowSanitizer(
    const std::vector<std::string> &ABIListFiles, void *(*getArgTLS)(),
    void *(*getRetValTLS)())
    : ModulePass(ID), GetArgTLSPtr(getArgTLS), GetRetvalTLSPtr(getRetValTLS) {
  std::vector<std::string> AllABIListFiles(std::move(ABIListFiles));
  AllABIListFiles.insert(AllABIListFiles.end(), ClABIListFiles.begin(),
                         ClABIListFiles.end());
  ABIList.set(SpecialCaseList::createOrDie(AllABIListFiles));
  std::vector<std::string> AllCommutativityListFiles;
  AllCommutativityListFiles.insert(AllCommutativityListFiles.end(),
                                   ClDiscoveryCommutativityListFiles.begin(),
                                   ClDiscoveryCommutativityListFiles.end());
  CommutativityList.set(
      SpecialCaseList::createOrDie(AllCommutativityListFiles));
}

FunctionType *DataFlowSanitizer::getArgsFunctionType(FunctionType *T) {
  SmallVector<Type *, 4> ArgTypes(T->param_begin(), T->param_end());
  ArgTypes.append(T->getNumParams(), ShadowTy);
  if (T->isVarArg())
    ArgTypes.push_back(ShadowPtrTy);
  Type *RetType = T->getReturnType();
  if (!RetType->isVoidTy())
    RetType = StructType::get(RetType, ShadowTy);
  return FunctionType::get(RetType, ArgTypes, T->isVarArg());
}

FunctionType *DataFlowSanitizer::getTrampolineFunctionType(FunctionType *T) {
  assert(!T->isVarArg());
  SmallVector<Type *, 4> ArgTypes;
  ArgTypes.push_back(T->getPointerTo());
  ArgTypes.append(T->param_begin(), T->param_end());
  ArgTypes.append(T->getNumParams(), ShadowTy);
  Type *RetType = T->getReturnType();
  if (!RetType->isVoidTy())
    ArgTypes.push_back(ShadowPtrTy);
  return FunctionType::get(T->getReturnType(), ArgTypes, false);
}

TransformedFunction DataFlowSanitizer::getCustomFunctionType(FunctionType *T) {
  SmallVector<Type *, 4> ArgTypes;

  // Some parameters of the custom function being constructed are
  // parameters of T.  Record the mapping from parameters of T to
  // parameters of the custom function, so that parameter attributes
  // at call sites can be updated.
  std::vector<unsigned> ArgumentIndexMapping;
  for (unsigned i = 0, ie = T->getNumParams(); i != ie; ++i) {
    Type* param_type = T->getParamType(i);
    FunctionType *FT;
    if (isa<PointerType>(param_type) && (FT = dyn_cast<FunctionType>(
            cast<PointerType>(param_type)->getElementType()))) {
      ArgumentIndexMapping.push_back(ArgTypes.size());
      ArgTypes.push_back(getTrampolineFunctionType(FT)->getPointerTo());
      ArgTypes.push_back(Type::getInt8PtrTy(*Ctx));
    } else {
      ArgumentIndexMapping.push_back(ArgTypes.size());
      ArgTypes.push_back(param_type);
    }
  }
  for (unsigned i = 0, e = T->getNumParams(); i != e; ++i)
    ArgTypes.push_back(ShadowTy);
  if (T->isVarArg())
    ArgTypes.push_back(ShadowPtrTy);
  Type *RetType = T->getReturnType();
  if (!RetType->isVoidTy())
    ArgTypes.push_back(ShadowPtrTy);
  return TransformedFunction(
      T, FunctionType::get(T->getReturnType(), ArgTypes, T->isVarArg()),
      ArgumentIndexMapping);
}

void DataFlowSanitizer::getAnalysisUsage(AnalysisUsage &AU) const {
  if (ClDiscoveryMarkIterators) {
    AU.addRequiredTransitiveID(IteratorRecognitionID);
  }
  if (ClDiscoverySimplifyMinMax) {
    AU.addRequiredID(SimplifyMinMaxPass::ID);
  }
}

bool DataFlowSanitizer::doInitialization(Module &M) {
  Triple TargetTriple(M.getTargetTriple());
  bool IsX86_64 = TargetTriple.getArch() == Triple::x86_64;
  bool IsMIPS64 = TargetTriple.isMIPS64();
  bool IsAArch64 = TargetTriple.getArch() == Triple::aarch64 ||
                   TargetTriple.getArch() == Triple::aarch64_be;

  const DataLayout &DL = M.getDataLayout();

  Mod = &M;
  Ctx = &M.getContext();
  ShadowTy = IntegerType::get(*Ctx, ShadowWidth);
  ShadowPtrTy = PointerType::getUnqual(ShadowTy);
  IntptrTy = DL.getIntPtrType(*Ctx);
  BlockIdTy = IntegerType::get(*Ctx, BlockIdWidth);
  StaticInstIdTy = Type::getInt8PtrTy(*Ctx);
  ZeroShadow = ConstantInt::getSigned(ShadowTy, 0);
  ShadowPtrMul = ConstantInt::getSigned(IntptrTy, ShadowWidth / 8);
  if (IsX86_64)
    ShadowPtrMask = ConstantInt::getSigned(IntptrTy, ~0x700000000000LL);
  else if (IsMIPS64)
    ShadowPtrMask = ConstantInt::getSigned(IntptrTy, ~0xF000000000LL);
  // AArch64 supports multiple VMAs and the shadow mask is set at runtime.
  else if (IsAArch64)
    DFSanRuntimeShadowMask = true;
  else
    report_fatal_error("unsupported triple");

  Type *DFSanUnionArgs[2] = { ShadowTy, ShadowTy };
  DFSanUnionFnTy =
      FunctionType::get(ShadowTy, DFSanUnionArgs, /*isVarArg=*/ false);
  Type *DFSanUnionLoadArgs[2] = { ShadowPtrTy, IntptrTy };
  DFSanUnionLoadFnTy =
      FunctionType::get(ShadowTy, DFSanUnionLoadArgs, /*isVarArg=*/ false);
  DFSanUnimplementedFnTy = FunctionType::get(
      Type::getVoidTy(*Ctx), Type::getInt8PtrTy(*Ctx), /*isVarArg=*/false);
  Type *DFSanSetLabelArgs[3] = { ShadowTy, Type::getInt8PtrTy(*Ctx), IntptrTy };
  DFSanSetLabelFnTy = FunctionType::get(Type::getVoidTy(*Ctx),
                                        DFSanSetLabelArgs, /*isVarArg=*/false);
  DFSanNonzeroLabelFnTy = FunctionType::get(
      Type::getVoidTy(*Ctx), None, /*isVarArg=*/false);
  DFSanVarargWrapperFnTy = FunctionType::get(
      Type::getVoidTy(*Ctx), Type::getInt8PtrTy(*Ctx), /*isVarArg=*/false);
  if (ClDiscovery) {
    DFSanEnterAssignmentFnTy = FunctionType::get(BlockIdTy, {},
                                                 /*isVarArg=*/false);
    Type *DFSanPrintDataFlowArgs[2] = { ShadowTy, BlockIdTy };
    DFSanPrintDataFlowFnTy = FunctionType::get(
        Type::getVoidTy(*Ctx), DFSanPrintDataFlowArgs, /*isVarArg=*/false);
    Type *DFSanCreateLabelWithDefinerArgs[1] = { BlockIdTy };
    DFSanCreateLabelWithDefinerFnTy = FunctionType::get(
        ShadowTy, DFSanCreateLabelWithDefinerArgs, /*isVarArg=*/false);
    Type *DFSanPrintBlockPropertyArgs[3] =
      { BlockIdTy, Type::getInt8PtrTy(*Ctx), Type::getInt8PtrTy(*Ctx) };
    DFSanPrintBlockPropertyFnTy = FunctionType::get(
        Type::getVoidTy(*Ctx), DFSanPrintBlockPropertyArgs, /*isVarArg=*/false);
    Type *DFSanPrintInstructionPropertyArgs[3] =
      { StaticInstIdTy, Type::getInt8PtrTy(*Ctx), Type::getInt8PtrTy(*Ctx) };
    DFSanPrintInstructionPropertyFnTy = FunctionType::get(
        Type::getVoidTy(*Ctx), DFSanPrintInstructionPropertyArgs, /*isVarArg=*/false);
    DFSanPrintRegionPropertyFnTy = FunctionType::get(
        Type::getVoidTy(*Ctx), DFSanPrintBlockPropertyArgs, /*isVarArg=*/false);
    DFSanOpenTraceFnTy = FunctionType::get(
        Type::getVoidTy(*Ctx), {}, /*isVarArg=*/false);
    DFSanCloseTraceFnTy = FunctionType::get(
        Type::getVoidTy(*Ctx), {}, /*isVarArg=*/false);
    DFSanReportFnTy = FunctionType::get(
        Type::getVoidTy(*Ctx), {Type::getInt8PtrTy(*Ctx)}, /*isVarArg=*/false);
    DFSanBeginTaggingFnTy = FunctionType::get(
        Type::getVoidTy(*Ctx), {Type::getInt8PtrTy(*Ctx)}, /*isVarArg=*/false);
    DFSanEndTaggingFnTy = FunctionType::get(
        Type::getVoidTy(*Ctx), {Type::getInt8PtrTy(*Ctx)}, /*isVarArg=*/false);
    DFSanNewGroupFnTy = FunctionType::get(
        Type::getVoidTy(*Ctx), {Type::getInt8PtrTy(*Ctx)}, /*isVarArg=*/false);
  }

  if (GetArgTLSPtr) {
    Type *ArgTLSTy = ArrayType::get(ShadowTy, 64);
    ArgTLS = nullptr;
    GetArgTLS = ConstantExpr::getIntToPtr(
        ConstantInt::get(IntptrTy, uintptr_t(GetArgTLSPtr)),
        PointerType::getUnqual(
            FunctionType::get(PointerType::getUnqual(ArgTLSTy), false)));
  }
  if (GetRetvalTLSPtr) {
    RetvalTLS = nullptr;
    GetRetvalTLS = ConstantExpr::getIntToPtr(
        ConstantInt::get(IntptrTy, uintptr_t(GetRetvalTLSPtr)),
        PointerType::getUnqual(
            FunctionType::get(PointerType::getUnqual(ShadowTy), false)));
  }

  ColdCallWeights = MDBuilder(*Ctx).createBranchWeights(1, 1000);
  return true;
}

bool DataFlowSanitizer::isInstrumented(const Function *F) {
  return !ABIList.isIn(*F, "uninstrumented");
}

bool DataFlowSanitizer::isInstrumented(const GlobalAlias *GA) {
  return !ABIList.isIn(*GA, "uninstrumented");
}

DataFlowSanitizer::InstrumentedABI DataFlowSanitizer::getInstrumentedABI() {
  return ClArgsABI ? IA_Args : IA_TLS;
}

DataFlowSanitizer::WrapperKind DataFlowSanitizer::getWrapperKind(Function *F) {
  if (ABIList.isIn(*F, "functional"))
    return WK_Functional;
  if (ABIList.isIn(*F, "discard"))
    return WK_Discard;
  if (ABIList.isIn(*F, "custom"))
    return WK_Custom;

  return WK_Warning;
}

void DataFlowSanitizer::addGlobalNamePrefix(GlobalValue *GV) {
  std::string GVName = GV->getName(), Prefix = "dfs$";
  GV->setName(Prefix + GVName);

  // Try to change the name of the function in module inline asm.  We only do
  // this for specific asm directives, currently only ".symver", to try to avoid
  // corrupting asm which happens to contain the symbol name as a substring.
  // Note that the substitution for .symver assumes that the versioned symbol
  // also has an instrumented name.
  std::string Asm = GV->getParent()->getModuleInlineAsm();
  std::string SearchStr = ".symver " + GVName + ",";
  size_t Pos = Asm.find(SearchStr);
  if (Pos != std::string::npos) {
    Asm.replace(Pos, SearchStr.size(),
                ".symver " + Prefix + GVName + "," + Prefix);
    GV->getParent()->setModuleInlineAsm(Asm);
  }
}

Function *
DataFlowSanitizer::buildWrapperFunction(Function *F, StringRef NewFName,
                                        GlobalValue::LinkageTypes NewFLink,
                                        FunctionType *NewFT) {
  FunctionType *FT = F->getFunctionType();
  Function *NewF = Function::Create(NewFT, NewFLink, NewFName,
                                    F->getParent());
  NewF->copyAttributesFrom(F);
  NewF->removeAttributes(
      AttributeList::ReturnIndex,
      AttributeFuncs::typeIncompatible(NewFT->getReturnType()));

  BasicBlock *BB = BasicBlock::Create(*Ctx, "entry", NewF);
  if (F->isVarArg()) {
    NewF->removeAttributes(AttributeList::FunctionIndex,
                           AttrBuilder().addAttribute("split-stack"));
    CallInst::Create(DFSanVarargWrapperFn,
                     IRBuilder<>(BB).CreateGlobalStringPtr(F->getName()), "",
                     BB);
    new UnreachableInst(*Ctx, BB);
  } else {
    std::vector<Value *> Args;
    unsigned n = FT->getNumParams();
    for (Function::arg_iterator ai = NewF->arg_begin(); n != 0; ++ai, --n)
      Args.push_back(&*ai);
    CallInst *CI = CallInst::Create(F, Args, "", BB);
    if (FT->getReturnType()->isVoidTy())
      ReturnInst::Create(*Ctx, BB);
    else
      ReturnInst::Create(*Ctx, CI, BB);
  }

  return NewF;
}

Constant *DataFlowSanitizer::getOrBuildTrampolineFunction(FunctionType *FT,
                                                          StringRef FName) {
  FunctionType *FTT = getTrampolineFunctionType(FT);
  Constant *C = Mod->getOrInsertFunction(FName, FTT);
  Function *F = dyn_cast<Function>(C);
  if (F && F->isDeclaration()) {
    F->setLinkage(GlobalValue::LinkOnceODRLinkage);
    BasicBlock *BB = BasicBlock::Create(*Ctx, "entry", F);
    std::vector<Value *> Args;
    Function::arg_iterator AI = F->arg_begin(); ++AI;
    for (unsigned N = FT->getNumParams(); N != 0; ++AI, --N)
      Args.push_back(&*AI);
    CallInst *CI = CallInst::Create(&*F->arg_begin(), Args, "", BB);
    ReturnInst *RI;
    if (FT->getReturnType()->isVoidTy())
      RI = ReturnInst::Create(*Ctx, BB);
    else
      RI = ReturnInst::Create(*Ctx, CI, BB);

    InstRefSet IRInsts;
    DFSanFunction DFSF(*this, F, /*IsNativeABI=*/true, IRInsts);
    Function::arg_iterator ValAI = F->arg_begin(), ShadowAI = AI; ++ValAI;
    for (unsigned N = FT->getNumParams(); N != 0; ++ValAI, ++ShadowAI, --N)
      DFSF.ValShadowMap[&*ValAI] = &*ShadowAI;
    DFSanVisitor(DFSF).visitCallInst(*CI);
    if (!FT->getReturnType()->isVoidTy())
      new StoreInst(DFSF.getShadow(RI->getReturnValue()),
                    &*std::prev(F->arg_end()), RI);
  }

  return C;
}

// FIXME: create new annotation for functions that we want to model as if they
// were functional but are not necessarily commutative, such as the ones below.
bool DataFlowSanitizer::isImpureFunctional(StringRef FunctionName) const {
  return (FunctionName == "rand" ||
          FunctionName == "lrand48");
}

bool DataFlowSanitizer::isCommutative(CallInst *CI) {
  if (isa<InlineAsm>(CI->getCalledValue())) return false;
  Function * F = CI->getCalledFunction();
  return ((getWrapperKind(F) == WK_Functional &&
           !isImpureFunctional(F->getName())) ||
          CommutativityList.isIn(F->getName()));
}

bool DataFlowSanitizer::runOnModule(Module &M) {
  DenseMap<Function *, InstRefSet> IRIMap;
  for (Function &i : M) {
    if (!ClDiscoveryMarkIterators)
      continue;
    if (i.isDeclaration())
      continue;
    auto& IRI = getAnalysis<IteratorRecognitionWrapperPass>(i)
                  .getIteratorRecognitionInfo();
    InstRefSet IRInsts;
    for (auto & Iterator : IRI.getIteratorsInfo()) {
      IRInsts.insert(Iterator.begin(), Iterator.end());
    }
    IRIMap[&i] = IRInsts;
  }

  if (ABIList.isIn(M, "skip"))
    return false;

  if (!GetArgTLSPtr) {
    Type *ArgTLSTy = ArrayType::get(ShadowTy, 64);
    ArgTLS = Mod->getOrInsertGlobal("__dfsan_arg_tls", ArgTLSTy);
    if (GlobalVariable *G = dyn_cast<GlobalVariable>(ArgTLS))
      G->setThreadLocalMode(GlobalVariable::InitialExecTLSModel);
  }
  if (!GetRetvalTLSPtr) {
    RetvalTLS = Mod->getOrInsertGlobal("__dfsan_retval_tls", ShadowTy);
    if (GlobalVariable *G = dyn_cast<GlobalVariable>(RetvalTLS))
      G->setThreadLocalMode(GlobalVariable::InitialExecTLSModel);
  }

  ExternalShadowMask =
      Mod->getOrInsertGlobal(kDFSanExternShadowPtrMask, IntptrTy);

  DFSanUnionFn = Mod->getOrInsertFunction("__dfsan_union", DFSanUnionFnTy);
  if (Function *F = dyn_cast<Function>(DFSanUnionFn)) {
    F->addAttribute(AttributeList::FunctionIndex, Attribute::NoUnwind);
    F->addAttribute(AttributeList::FunctionIndex, Attribute::ReadNone);
    F->addAttribute(AttributeList::ReturnIndex, Attribute::ZExt);
    F->addParamAttr(0, Attribute::ZExt);
    F->addParamAttr(1, Attribute::ZExt);
  }
  DFSanCheckedUnionFn = Mod->getOrInsertFunction("dfsan_union", DFSanUnionFnTy);
  if (Function *F = dyn_cast<Function>(DFSanCheckedUnionFn)) {
    F->addAttribute(AttributeList::FunctionIndex, Attribute::NoUnwind);
    F->addAttribute(AttributeList::FunctionIndex, Attribute::ReadNone);
    F->addAttribute(AttributeList::ReturnIndex, Attribute::ZExt);
    F->addParamAttr(0, Attribute::ZExt);
    F->addParamAttr(1, Attribute::ZExt);
  }
  DFSanUnionLoadFn =
      Mod->getOrInsertFunction("__dfsan_union_load", DFSanUnionLoadFnTy);
  if (Function *F = dyn_cast<Function>(DFSanUnionLoadFn)) {
    F->addAttribute(AttributeList::FunctionIndex, Attribute::NoUnwind);
    F->addAttribute(AttributeList::FunctionIndex, Attribute::ReadOnly);
    F->addAttribute(AttributeList::ReturnIndex, Attribute::ZExt);
  }
  DFSanUnimplementedFn =
      Mod->getOrInsertFunction("__dfsan_unimplemented", DFSanUnimplementedFnTy);
  DFSanSetLabelFn =
      Mod->getOrInsertFunction("__dfsan_set_label", DFSanSetLabelFnTy);
  if (Function *F = dyn_cast<Function>(DFSanSetLabelFn)) {
    F->addParamAttr(0, Attribute::ZExt);
  }
  DFSanNonzeroLabelFn =
      Mod->getOrInsertFunction("__dfsan_nonzero_label", DFSanNonzeroLabelFnTy);
  DFSanVarargWrapperFn = Mod->getOrInsertFunction("__dfsan_vararg_wrapper",
                                                  DFSanVarargWrapperFnTy);
  if (ClDiscovery) {
    DFSanEnterAssignmentFn =
      Mod->getOrInsertFunction("__dfsan_enter_assignment",
                               DFSanEnterAssignmentFnTy);
    {
      AttributeList AL;
      AL = AL.addParamAttribute(M.getContext(), 0, Attribute::ZExt);
      DFSanPrintDataFlowFn =
        Mod->getOrInsertFunction("__dfsan_print_data_flow",
                                 DFSanPrintDataFlowFnTy, AL);
    }
    {
      AttributeList AL;
      AL = AL.addParamAttribute(M.getContext(), 0, Attribute::ZExt);
      DFSanCreateLabelWithDefinerFn =
        Mod->getOrInsertFunction("__dfsan_create_label_with_definer",
                                 DFSanCreateLabelWithDefinerFnTy, AL);
    }
    DFSanPrintBlockPropertyFn =
        Mod->getOrInsertFunction("__dfsan_print_block_property",
                                 DFSanPrintBlockPropertyFnTy);
    DFSanPrintInstructionPropertyFn =
        Mod->getOrInsertFunction("__dfsan_print_instruction_property",
                                 DFSanPrintInstructionPropertyFnTy);
    DFSanPrintRegionPropertyFn =
        Mod->getOrInsertFunction("__dfsan_print_region_property",
                                 DFSanPrintRegionPropertyFnTy);
    DFSanOpenTraceFn =
        Mod->getOrInsertFunction("__dfsan_open_trace",
                                 DFSanOpenTraceFnTy);
    DFSanCloseTraceFn =
        Mod->getOrInsertFunction("__dfsan_close_trace",
                                 DFSanCloseTraceFnTy);
    DFSanReportFn =
        Mod->getOrInsertFunction("__dfsan_report",
                                 DFSanReportFnTy);
    DFSanBeginTaggingFn =
        Mod->getOrInsertFunction("dfsan_begin_tagging",
                                 DFSanBeginTaggingFnTy);
    DFSanEndTaggingFn =
        Mod->getOrInsertFunction("dfsan_end_tagging",
                                 DFSanEndTaggingFnTy);
    DFSanNewGroupFn =
        Mod->getOrInsertFunction("dfsan_new_group",
                                 DFSanNewGroupFnTy);
  }
  std::vector<Function *> FnsToInstrument;
  SmallPtrSet<Function *, 2> FnsWithNativeABI;
  for (Function &i : M) {
    if (!i.isIntrinsic() &&
        &i != DFSanUnionFn &&
        &i != DFSanCheckedUnionFn &&
        &i != DFSanUnionLoadFn &&
        &i != DFSanUnimplementedFn &&
        &i != DFSanSetLabelFn &&
        &i != DFSanNonzeroLabelFn &&
        &i != DFSanVarargWrapperFn) {
      if (!ClDiscovery ||
          (&i != DFSanEnterAssignmentFn &&
           &i != DFSanPrintDataFlowFn &&
           &i != DFSanCreateLabelWithDefinerFn &&
           &i != DFSanPrintBlockPropertyFn &&
           &i != DFSanPrintInstructionPropertyFn &&
           &i != DFSanPrintRegionPropertyFn &&
           &i != DFSanOpenTraceFn &&
           &i != DFSanCloseTraceFn &&
           &i != DFSanReportFn &&
           &i != DFSanBeginTaggingFn &&
           &i != DFSanEndTaggingFn &&
           &i != DFSanNewGroupFn)) {
        FnsToInstrument.push_back(&i);
      }
    }
  }

  // Give function aliases prefixes when necessary, and build wrappers where the
  // instrumentedness is inconsistent.
  for (Module::alias_iterator i = M.alias_begin(), e = M.alias_end(); i != e;) {
    GlobalAlias *GA = &*i;
    ++i;
    // Don't stop on weak.  We assume people aren't playing games with the
    // instrumentedness of overridden weak aliases.
    if (auto F = dyn_cast<Function>(GA->getBaseObject())) {
      bool GAInst = isInstrumented(GA), FInst = isInstrumented(F);
      if (GAInst && FInst) {
        addGlobalNamePrefix(GA);
      } else if (GAInst != FInst) {
        // Non-instrumented alias of an instrumented function, or vice versa.
        // Replace the alias with a native-ABI wrapper of the aliasee.  The pass
        // below will take care of instrumenting it.
        Function *NewF =
            buildWrapperFunction(F, "", GA->getLinkage(), F->getFunctionType());
        GA->replaceAllUsesWith(ConstantExpr::getBitCast(NewF, GA->getType()));
        NewF->takeName(GA);
        GA->eraseFromParent();
        FnsToInstrument.push_back(NewF);
      }
    }
  }

  ReadOnlyNoneAttrs.addAttribute(Attribute::ReadOnly)
      .addAttribute(Attribute::ReadNone);

  // First, change the ABI of every function in the module.  ABI-listed
  // functions keep their original ABI and get a wrapper function.
  for (std::vector<Function *>::iterator i = FnsToInstrument.begin(),
                                         e = FnsToInstrument.end();
       i != e; ++i) {
    Function &F = **i;
    FunctionType *FT = F.getFunctionType();

    bool IsZeroArgsVoidRet = (FT->getNumParams() == 0 && !FT->isVarArg() &&
                              FT->getReturnType()->isVoidTy());

    if (isInstrumented(&F)) {
      // Instrumented functions get a 'dfs$' prefix.  This allows us to more
      // easily identify cases of mismatching ABIs.
      if (getInstrumentedABI() == IA_Args && !IsZeroArgsVoidRet) {
        FunctionType *NewFT = getArgsFunctionType(FT);
        Function *NewF = Function::Create(NewFT, F.getLinkage(), "", &M);
        NewF->copyAttributesFrom(&F);
        NewF->removeAttributes(
            AttributeList::ReturnIndex,
            AttributeFuncs::typeIncompatible(NewFT->getReturnType()));
        for (Function::arg_iterator FArg = F.arg_begin(),
                                    NewFArg = NewF->arg_begin(),
                                    FArgEnd = F.arg_end();
             FArg != FArgEnd; ++FArg, ++NewFArg) {
          FArg->replaceAllUsesWith(&*NewFArg);
        }
        NewF->getBasicBlockList().splice(NewF->begin(), F.getBasicBlockList());

        for (Function::user_iterator UI = F.user_begin(), UE = F.user_end();
             UI != UE;) {
          BlockAddress *BA = dyn_cast<BlockAddress>(*UI);
          ++UI;
          if (BA) {
            BA->replaceAllUsesWith(
                BlockAddress::get(NewF, BA->getBasicBlock()));
            delete BA;
          }
        }
        F.replaceAllUsesWith(
            ConstantExpr::getBitCast(NewF, PointerType::getUnqual(FT)));
        NewF->takeName(&F);
        F.eraseFromParent();
        *i = NewF;
        addGlobalNamePrefix(NewF);
      } else {
        addGlobalNamePrefix(&F);
      }
    } else if (!IsZeroArgsVoidRet || getWrapperKind(&F) == WK_Custom) {
      // Build a wrapper function for F.  The wrapper simply calls F, and is
      // added to FnsToInstrument so that any instrumentation according to its
      // WrapperKind is done in the second pass below.
      FunctionType *NewFT = getInstrumentedABI() == IA_Args
                                ? getArgsFunctionType(FT)
                                : FT;

      // If the function being wrapped has local linkage, then preserve the
      // function's linkage in the wrapper function.
      GlobalValue::LinkageTypes wrapperLinkage =
          F.hasLocalLinkage()
              ? F.getLinkage()
              : GlobalValue::LinkOnceODRLinkage;

      Function *NewF = buildWrapperFunction(
          &F, std::string("dfsw$") + std::string(F.getName()),
          wrapperLinkage, NewFT);
      if (getInstrumentedABI() == IA_TLS)
        NewF->removeAttributes(AttributeList::FunctionIndex, ReadOnlyNoneAttrs);

      Value *WrappedFnCst =
          ConstantExpr::getBitCast(NewF, PointerType::getUnqual(FT));
      F.replaceAllUsesWith(WrappedFnCst);

      UnwrappedFnMap[WrappedFnCst] = &F;
      *i = NewF;

      if (!F.isDeclaration()) {
        // This function is probably defining an interposition of an
        // uninstrumented function and hence needs to keep the original ABI.
        // But any functions it may call need to use the instrumented ABI, so
        // we instrument it in a mode which preserves the original ABI.
        FnsWithNativeABI.insert(&F);

        // This code needs to rebuild the iterators, as they may be invalidated
        // by the push_back, taking care that the new range does not include
        // any functions added by this code.
        size_t N = i - FnsToInstrument.begin(),
               Count = e - FnsToInstrument.begin();
        FnsToInstrument.push_back(&F);
        i = FnsToInstrument.begin() + N;
        e = FnsToInstrument.begin() + Count;
      }
               // Hopefully, nobody will try to indirectly call a vararg
               // function... yet.
    } else if (FT->isVarArg()) {
      UnwrappedFnMap[&F] = &F;
      *i = nullptr;
    }
  }

  // Whether the module has global static initializations (for trace opening).
  bool StaticInits = false;
  for (Function *i : FnsToInstrument) {
    if (!i || i->isDeclaration())
      continue;
    if (i->getName().contains("_GLOBAL__sub_I_")) {
      StaticInits = true;
      break;
    }
  }

  for (Function *i : FnsToInstrument) {
    if (!i || i->isDeclaration())
      continue;

    removeUnreachableBlocks(*i);

    DFSanFunction DFSF(*this, i, FnsWithNativeABI.count(i), IRIMap[i]);

    // DFSanVisitor may create new basic blocks, which confuses df_iterator.
    // Build a copy of the list before iterating over it.
    SmallVector<BasicBlock *, 4> BBList(depth_first(&i->getEntryBlock()));

    for (BasicBlock *i : BBList) {
      Instruction *Inst = &i->front();
      while (true) {
        // DFSanVisitor may split the current basic block, changing the current
        // instruction's next pointer and moving the next instruction to the
        // tail block from which we should continue.
        Instruction *Next = Inst->getNextNode();
        // DFSanVisitor may delete Inst, so keep track of whether it was a
        // terminator.
        bool IsTerminator = isa<TerminatorInst>(Inst);
        if (!DFSF.SkipInsts.count(Inst))
          DFSanVisitor(DFSF).visit(Inst);
        if (IsTerminator)
          break;
        Inst = Next;
      }
    }

    // We will not necessarily be able to compute the shadow for every phi node
    // until we have visited every block.  Therefore, the code that handles phi
    // nodes adds them to the PHIFixups list so that they can be properly
    // handled here.
    for (std::vector<std::pair<PHINode *, PHINode *>>::iterator
             i = DFSF.PHIFixups.begin(),
             e = DFSF.PHIFixups.end();
         i != e; ++i) {
      for (unsigned val = 0, n = i->first->getNumIncomingValues(); val != n;
           ++val) {
        i->second->setIncomingValue(
            val, DFSF.getShadow(i->first->getIncomingValue(val)));
      }
    }

    // -dfsan-debug-nonzero-labels will split the CFG in all kinds of crazy
    // places (i.e. instructions in basic blocks we haven't even begun visiting
    // yet).  To make our life easier, do this work in a pass after the main
    // instrumentation.
    if (ClDebugNonzeroLabels) {
      for (Value *V : DFSF.NonZeroChecks) {
        Instruction *Pos;
        if (Instruction *I = dyn_cast<Instruction>(V))
          Pos = I->getNextNode();
        else
          Pos = &DFSF.F->getEntryBlock().front();
        while (isa<PHINode>(Pos) || isa<AllocaInst>(Pos))
          Pos = Pos->getNextNode();
        IRBuilder<> IRB(Pos);
        Value *Ne = IRB.CreateICmpNE(V, DFSF.DFS.ZeroShadow);
        BranchInst *BI = cast<BranchInst>(SplitBlockAndInsertIfThen(
            Ne, Pos, /*Unreachable=*/false, ColdCallWeights));
        IRBuilder<> ThenIRB(BI);
        ThenIRB.CreateCall(DFSF.DFS.DFSanNonzeroLabelFn, {});
      }
    }

    // In ClDiscovery mode, insert calls to open and close the trace file on
    // entry to main() (or alternative on entry to _GLOBAL__sub_I_ if present),
    // return from main(), or any call to exit().
    if (ClDiscovery) {
      if (( StaticInits && DFSF.F->getName().contains("_GLOBAL__sub_I_")) ||
          (!StaticInits && DFSF.F->getName() == "main")) {
        IRBuilder<> IRB(&*DFSF.F->getEntryBlock().getFirstInsertionPt());
        // Insert call to open the trace file.
        IRB.CreateCall(DFSF.DFS.DFSanOpenTraceFn, {});
      }
      if (DFSF.F->getName() == "main") {
        // Insert call to close the trace file on return from main().
        for (BasicBlock &B : *DFSF.F) {
          Instruction *Term = B.getTerminator();
          if (isa<ReturnInst>(Term)) {
            IRBuilder<> IRT(Term);
            IRT.CreateCall(DFSF.DFS.DFSanCloseTraceFn, {});
          }
        }
      }
      // Insert call to close the trace file on any call to exit().
      for (BasicBlock &B : *DFSF.F) {
        for (Instruction &Inst : B) {
          if (isa<CallInst>(Inst)) {
            Function *CF = (cast<CallInst>(&Inst))->getCalledFunction();
            if (CF && CF->getName() == "exit") {
              IRBuilder<> IRC(&Inst);
              IRC.CreateCall(DFSF.DFS.DFSanCloseTraceFn, {});
            }
          }
        }
      }
    }

    // Insert calls to tag each block with loop information.
    if (ClDiscovery && ClDiscoveryTagLoops) {
      auto & LI = getAnalysis<LoopInfoWrapperPass>(*i).getLoopInfo();
      for (auto *L : LI.getLoopsInPreorder()) {
        DebugLoc Loc = L->getStartLoc();
        // Possibly skip loop if it belongs to a STL header.
        if (!ClDiscoveryTagSTL && Loc->getFilename().contains("include/c++"))
          continue;
        // The (template-specialized) function name needs to be part of the tag
        // to distinguish loops in different specializations of the same
        // original function.
        StringRef FunName;
        if (i->getName().startswith("dfs$")) {
          FunName = i->getName().substr(4);
        } else {
          FunName = i->getName();
        }
        std::stringstream LoopTag;
        LoopTag << Loc->getFilename().str()  << ":"
                << FunName.str() << ":"
                << Loc->getLine() << ":"
                << Loc->getColumn();
        // Begin tagging at the beginning of the header. Since the header
        // dominates all basic blocks in the loop, a new tag instance will be
        // created for each loop iteration.
        BasicBlock * H = L->getHeader();
        IRBuilder<> IRB(&*H->getFirstInsertionPt());
        IRB.CreateCall(DFSF.DFS.DFSanBeginTaggingFn,
                       {IRB.CreateGlobalStringPtr(LoopTag.str())});
        // End tagging at the beginning or end of each latch (depending on
        // ClDiscoveryTagIterationExpressions and the loop type).
        SmallVector<BasicBlock*, 16> LoopLatches;
        L->getLoopLatches(LoopLatches);
        for (BasicBlock *Latch : LoopLatches) {
          Instruction *InsertionPt;
          // FIXME: This test relies on basic block names (preserved with the
          // flag '-fno-discard-value-names'), which is not very robust. A
          // better way would be to mark latch basic blocks in for loops using
          // metadata in Clang at LLVM IR emission.
          bool IsForLoop = L->getName().startswith("for.");
          if (!ClDiscoveryTagIterationExpressions && IsForLoop) {
            // Do not tag the data-flow of iteration expressions (which in for
            // loops are placed in latch basic blocks). This is useful for the
            // collapsing heuristic, whenever iterator recognition cannot detect
            // and simplify away the header code (e.g. the inner loop in the
            // "rotate" benchmark, method 'run').
            InsertionPt = &*Latch->getFirstInsertionPt();
          } else {
            // This will tag iteration expressions in for loops (e.g. "i++")
            // which introduce loop-carried dependencies. We rely on iteration
            // recognition and the trace simplification phase to eliminate them.
            InsertionPt = Latch->getTerminator();
          }
          IRBuilder<> IRB(InsertionPt);
          IRB.CreateCall(DFSF.DFS.DFSanEndTaggingFn,
                         {IRB.CreateGlobalStringPtr(LoopTag.str())});
        }
        // End tagging at the beginning of each exit. There might be some
        // overlap with end tagging instructions in latches or other exit
        // blocks. This might lead to repeated calls to end the same tag, which
        // is allowed (the second end tagging calls will just be ignored). The
        // important thing is to prevent two consecutive begin tagging calls
        // with the same tag.
        // Examples of loops where double-ending might happen are do-while loops
        // (where the "condition" block is both latch and exiting) and loops
        // with break statements (where the "break" exit block is a predecessor
        // of the "regular" exit block).
        //
        // Also, increment the group counter at the beginning of each exit as
        // well. The next time the loop is entered, it is thus tagged with a new
        // group identifier. As discussed above, double-group-increments may
        // happen in loops where one exit block is a predecessor of another exit
        // block.
        // FIXME: ignore subsequent calls to 'dfsan_new_group' without
        // interleaved 'dfsan_beging_tagging' calls (e.g. by adding a guard to
        // the tag structure).
        SmallVector<BasicBlock*, 16> LoopExits;
        // Cannot use 'getExitEdges' because it is const-qualified, tough luck.
        L->getExitBlocks(LoopExits);
        for (BasicBlock *LEB : LoopExits) {
          IRBuilder<> IRB(&*LEB->getFirstInsertionPt());
          IRB.CreateCall(DFSF.DFS.DFSanEndTaggingFn,
                         {IRB.CreateGlobalStringPtr(LoopTag.str())});
          IRB.CreateCall(DFSF.DFS.DFSanNewGroupFn,
                         {IRB.CreateGlobalStringPtr(LoopTag.str())});
        }
      }
    }
  }

  return false;
}

Value *DFSanFunction::getArgTLSPtr() {
  if (ArgTLSPtr)
    return ArgTLSPtr;
  if (DFS.ArgTLS)
    return ArgTLSPtr = DFS.ArgTLS;

  IRBuilder<> IRB(&F->getEntryBlock().front());
  return ArgTLSPtr = IRB.CreateCall(DFS.GetArgTLS, {});
}

Value *DFSanFunction::getRetvalTLS() {
  if (RetvalTLSPtr)
    return RetvalTLSPtr;
  if (DFS.RetvalTLS)
    return RetvalTLSPtr = DFS.RetvalTLS;

  IRBuilder<> IRB(&F->getEntryBlock().front());
  return RetvalTLSPtr = IRB.CreateCall(DFS.GetRetvalTLS, {});
}

Value *DFSanFunction::getArgTLS(unsigned Idx, Instruction *Pos) {
  IRBuilder<> IRB(Pos);
  return IRB.CreateConstGEP2_64(getArgTLSPtr(), 0, Idx);
}

Value *DFSanFunction::getShadow(Value *V) {
  if (!isa<Argument>(V) && !isa<Instruction>(V))
    return DFS.ZeroShadow;
  Value *&Shadow = ValShadowMap[V];
  if (!Shadow) {
    if (Argument *A = dyn_cast<Argument>(V)) {
      if (IsNativeABI)
        return DFS.ZeroShadow;
      switch (IA) {
      case DataFlowSanitizer::IA_TLS: {
        Value *ArgTLSPtr = getArgTLSPtr();
        Instruction *ArgTLSPos =
            DFS.ArgTLS ? &*F->getEntryBlock().begin()
                       : cast<Instruction>(ArgTLSPtr)->getNextNode();
        IRBuilder<> IRB(ArgTLSPos);
        Shadow = IRB.CreateLoad(getArgTLS(A->getArgNo(), ArgTLSPos));
        break;
      }
      case DataFlowSanitizer::IA_Args: {
        unsigned ArgIdx = A->getArgNo() + F->arg_size() / 2;
        Function::arg_iterator i = F->arg_begin();
        while (ArgIdx--)
          ++i;
        Shadow = &*i;
        assert(Shadow->getType() == DFS.ShadowTy);
        break;
      }
      }
      NonZeroChecks.push_back(Shadow);
    } else {
      Shadow = DFS.ZeroShadow;
    }
  }
  return Shadow;
}

void DFSanFunction::setShadow(Instruction *I, Value *Shadow) {
  assert(!ValShadowMap.count(I));
  assert(Shadow->getType() == DFS.ShadowTy);
  ValShadowMap[I] = Shadow;
}

Value *DataFlowSanitizer::getShadowAddress(Value *Addr, Instruction *Pos) {
  assert(Addr != RetvalTLS && "Reinstrumenting?");
  IRBuilder<> IRB(Pos);
  Value *ShadowPtrMaskValue;
  if (DFSanRuntimeShadowMask)
    ShadowPtrMaskValue = IRB.CreateLoad(IntptrTy, ExternalShadowMask);
  else
    ShadowPtrMaskValue = ShadowPtrMask;
  return IRB.CreateIntToPtr(
      IRB.CreateMul(
          IRB.CreateAnd(IRB.CreatePtrToInt(Addr, IntptrTy),
                        IRB.CreatePtrToInt(ShadowPtrMaskValue, IntptrTy)),
          ShadowPtrMul),
      ShadowPtrTy);
}

// Generates IR to compute the union of the two given shadows, inserting it
// before Pos.  Returns the computed union Value.
Value *DFSanFunction::combineShadows(Value *V1, Value *V2, Instruction *Pos) {
  if (V1 == DFS.ZeroShadow)
    return V2;
  if (V2 == DFS.ZeroShadow)
    return V1;
  if (V1 == V2)
    return V1;

  auto V1Elems = ShadowElements.find(V1);
  auto V2Elems = ShadowElements.find(V2);
  if (V1Elems != ShadowElements.end() && V2Elems != ShadowElements.end()) {
    if (std::includes(V1Elems->second.begin(), V1Elems->second.end(),
                      V2Elems->second.begin(), V2Elems->second.end())) {
      return V1;
    } else if (std::includes(V2Elems->second.begin(), V2Elems->second.end(),
                             V1Elems->second.begin(), V1Elems->second.end())) {
      return V2;
    }
  } else if (V1Elems != ShadowElements.end()) {
    if (V1Elems->second.count(V2))
      return V1;
  } else if (V2Elems != ShadowElements.end()) {
    if (V2Elems->second.count(V1))
      return V2;
  }

  auto Key = std::make_pair(V1, V2);
  if (V1 > V2)
    std::swap(Key.first, Key.second);
  CachedCombinedShadow &CCS = CachedCombinedShadows[Key];
  if (CCS.Block && DT.dominates(CCS.Block, Pos->getParent()))
    return CCS.Shadow;

  IRBuilder<> IRB(Pos);
  if (AvoidNewBlocks) {
    CallInst *Call = IRB.CreateCall(DFS.DFSanCheckedUnionFn, {V1, V2});
    Call->addAttribute(AttributeList::ReturnIndex, Attribute::ZExt);
    Call->addParamAttr(0, Attribute::ZExt);
    Call->addParamAttr(1, Attribute::ZExt);

    CCS.Block = Pos->getParent();
    CCS.Shadow = Call;
  } else {
    BasicBlock *Head = Pos->getParent();
    Value *Ne = IRB.CreateICmpNE(V1, V2);
    BranchInst *BI = cast<BranchInst>(SplitBlockAndInsertIfThen(
        Ne, Pos, /*Unreachable=*/false, DFS.ColdCallWeights, &DT));
    IRBuilder<> ThenIRB(BI);
    CallInst *Call = ThenIRB.CreateCall(DFS.DFSanUnionFn, {V1, V2});
    Call->addAttribute(AttributeList::ReturnIndex, Attribute::ZExt);
    Call->addParamAttr(0, Attribute::ZExt);
    Call->addParamAttr(1, Attribute::ZExt);

    BasicBlock *Tail = BI->getSuccessor(0);
    PHINode *Phi = PHINode::Create(DFS.ShadowTy, 2, "", &Tail->front());
    Phi->addIncoming(Call, Call->getParent());
    Phi->addIncoming(V1, Head);

    CCS.Block = Tail;
    CCS.Shadow = Phi;
  }

  std::set<Value *> UnionElems;
  if (V1Elems != ShadowElements.end()) {
    UnionElems = V1Elems->second;
  } else {
    UnionElems.insert(V1);
  }
  if (V2Elems != ShadowElements.end()) {
    UnionElems.insert(V2Elems->second.begin(), V2Elems->second.end());
  } else {
    UnionElems.insert(V2);
  }
  ShadowElements[CCS.Shadow] = std::move(UnionElems);

  return CCS.Shadow;
}

// A convenience function which folds the shadows of each of the operands
// of the provided instruction Inst, inserting the IR before Inst.  Returns
// the computed union Value.
Value *DFSanFunction::combineOperandShadows(Instruction *Inst) {
  if (Inst->getNumOperands() == 0)
    return DFS.ZeroShadow;

  Value *Shadow;

  // If the ClDiscovery flag is passed, instrument each assignment as follows:
  //
  // %x = call i64 @__dfsan_enter_assignment()
  // call void @__dfsan_print_data_flow(i16 zeroext %2, i64 %x)
  // call void @__dfsan_print_data_flow(i16 zeroext %1, i32 %x)
  // %3 = call zeroext i16 @__dfsan_create_label_with_definer(i64 %x)
  // %add = add nsw i32 %a2, %a1
  //
  // instead of the usual DataFlowSantizer sequence:
  //
  // (%2, %1 shadow addresses of %a2, %a1)
  // %3 = call zeroext i16 @dfsan_union(i16 zeroext %2, i16 zeroext %1)
  // %add = add nsw i32 %a2, %a1

  if (ClDiscovery) {
    IRBuilder<> IRB(Inst);
    // First, compute and print properties of the static instruction.
    std::stringstream StaticInstIDString;
    StaticInstIDString << F->getParent()->getModuleIdentifier() << ":"
                       << DFS.StaticInstID;
    Constant * StaticInstIDPtr =
      IRB.CreateGlobalStringPtr(StaticInstIDString.str());
    DFS.StaticInstID++;
    // If asked for, print whether the instruction is part of an iterator.
    if (ClDiscoveryMarkIterators) {
      if (IRInsts.count(Inst)) {
        IRB.CreateCall(DFS.DFSanPrintInstructionPropertyFn,
                       {StaticInstIDPtr,
                           IRB.CreateGlobalStringPtr("ITERATOR"),
                           IRB.CreateGlobalStringPtr("TRUE")});
      }
    }
    // Print whether the instruction has constant ("immediate") operands. This
    // is useful, for example, to identify count and increment patterns that
    // look like reductions but are not.
    bool HasConst = false;
    for (unsigned i = 0, n = Inst->getNumOperands(); i != n; ++i) {
      if (isa<Constant>(Inst->getOperand(i))) {
        HasConst = true;
        break;
      }
    }
    if (HasConst) {
      IRB.CreateCall(DFS.DFSanPrintInstructionPropertyFn,
                     {StaticInstIDPtr,
                         IRB.CreateGlobalStringPtr("IMMEDIATE"),
                         IRB.CreateGlobalStringPtr("TRUE")});
    }
    // Print whether the instruction is impure. A system call in this context is
    // a call to any external function that is opaque to DataFlowSanitizer (that
    // is, non-functional system calls in the DataFlowSanitizer's ABI
    // list). These are the only function calls that are observed here.
    if (CallInst *CI = dyn_cast<CallInst>(Inst)) {
      IRB.CreateCall(DFS.DFSanPrintInstructionPropertyFn,
                     {StaticInstIDPtr,
                         IRB.CreateGlobalStringPtr("IMPURE"),
                         IRB.CreateGlobalStringPtr("TRUE")});
      // Print whether the called function is non-commutative.
      if (!DFS.isCommutative(CI)) {
        IRB.CreateCall(DFS.DFSanPrintInstructionPropertyFn,
                       {StaticInstIDPtr,
                           IRB.CreateGlobalStringPtr("NONCOMMUTATIVE"),
                           IRB.CreateGlobalStringPtr("TRUE")});
        // In debug mode, report it.
        if (ClDiscoveryDebug) {
          std::stringstream Report;
          Report << "function \'"
                 << getCalleeName(*CI).str()
                 << "\' is not defined as commutative";
          IRB.CreateCall(DFS.DFSanReportFn,
                         {IRB.CreateGlobalStringPtr(Report.str())});
        }
      }
    // Print whether the instruction has control-flow (a conditional branch or a
    // return from main(), all other returns are not visible).
    } else if (isa<ReturnInst>(Inst) ||
               isa<BranchInst>(Inst)) {
      IRB.CreateCall(DFS.DFSanPrintInstructionPropertyFn,
                     {StaticInstIDPtr,
                         IRB.CreateGlobalStringPtr("CONTROL"),
                         IRB.CreateGlobalStringPtr("TRUE")});
    }
    // In debug mode, mark the name and location of each instruction for more
    // readable graphs.
    if (ClDiscoveryDebug) {
      StringRef Name;
      if (isa<CallInst>(Inst)) {
        Name = getCalleeName(*((CallInst *)Inst));
      } else {
        Name = Inst->getOpcodeName();
      }
      IRB.CreateCall(DFS.DFSanPrintInstructionPropertyFn,
                     {StaticInstIDPtr,
                         IRB.CreateGlobalStringPtr("NAME"),
                         IRB.CreateGlobalStringPtr(Name)});
      const DebugLoc &Loc = Inst->getDebugLoc();
      if (Loc) {
        std::stringstream LocString;
        LocString << Loc->getFilename().str()  << ":"
                  << Loc->getLine() << ":"
                  << Loc->getColumn();
        IRB.CreateCall(DFS.DFSanPrintInstructionPropertyFn,
                       {StaticInstIDPtr,
                           IRB.CreateGlobalStringPtr("LOCATION"),
                           IRB.CreateGlobalStringPtr
                           (LocString.str())});
      }
    }
    // Enter assignment and get a new block ID.
    CallInst *CallEA = IRB.CreateCall(DFS.DFSanEnterAssignmentFn, {});
    // Print the static instruction to which this block corresponds.
    IRB.CreateCall(DFS.DFSanPrintBlockPropertyFn,
                   {CallEA, IRB.CreateGlobalStringPtr("INSTRUCTION"),
                       IRB.CreateGlobalStringPtr(StaticInstIDString.str())});
    // Print whether the region to which the block belongs is impure (only has
    // effect on regions) and non-commutative. We print this on blocks rather
    // than on the region instruction definition because the region instruction
    // ID is not stored.
    if (CallInst *CI = dyn_cast<CallInst>(Inst)) {
      IRB.CreateCall(DFS.DFSanPrintRegionPropertyFn,
                     {CallEA, IRB.CreateGlobalStringPtr("IMPURE"),
                         IRB.CreateGlobalStringPtr("TRUE")});
      if (!DFS.isCommutative(CI)) {
        IRB.CreateCall(DFS.DFSanPrintRegionPropertyFn,
                       {CallEA, IRB.CreateGlobalStringPtr("NONCOMMUTATIVE"),
                           IRB.CreateGlobalStringPtr("TRUE")});
      }
    }
    // Print the data flow from each Inst operand's definer to the new block ID.
    for (unsigned i = 0, n = Inst->getNumOperands(); i != n; ++i) {
      Value * Op = Inst->getOperand(i);
      // FIXME: is there a higher-level way to detect labels?
      if (Op->getType()->getTypeID() == Type::LabelTyID)
        continue;
      CallInst *CallPDF = IRB.CreateCall(DFS.DFSanPrintDataFlowFn,
                                         {getShadow(Op), CallEA});
      CallPDF->addParamAttr(0, Attribute::ZExt);
    }
    // Create a new label for Inst's result defined by the new block ID.
    CallInst *CallCLWD =
      IRB.CreateCall(DFS.DFSanCreateLabelWithDefinerFn, {CallEA});
    CallCLWD->addAttribute(AttributeList::ReturnIndex, Attribute::ZExt);
    // Make the new label Inst's shadow instead of the union of the operands.
    Shadow = CallCLWD;
  } else {
    Shadow = getShadow(Inst->getOperand(0));
    for (unsigned i = 1, n = Inst->getNumOperands(); i != n; ++i) {
      Shadow = combineShadows(Shadow, getShadow(Inst->getOperand(i)), Inst);
    }
  }

  return Shadow;
}

void DFSanVisitor::visitOperandShadowInst(Instruction &I) {
  Value *CombinedShadow = DFSF.combineOperandShadows(&I);
  DFSF.setShadow(&I, CombinedShadow);
}

// Generates IR to load shadow corresponding to bytes [Addr, Addr+Size), where
// Addr has alignment Align, and take the union of each of those shadows.
Value *DFSanFunction::loadShadow(Value *Addr, uint64_t Size, uint64_t Align,
                                 Instruction *Pos) {
  if (AllocaInst *AI = dyn_cast<AllocaInst>(Addr)) {
    const auto i = AllocaShadowMap.find(AI);
    if (i != AllocaShadowMap.end()) {
      IRBuilder<> IRB(Pos);
      return IRB.CreateLoad(i->second);
    }
  }

  uint64_t ShadowAlign = Align * DFS.ShadowWidth / 8;
  SmallVector<Value *, 2> Objs;
  GetUnderlyingObjects(Addr, Objs, Pos->getModule()->getDataLayout());
  bool AllConstants = true;
  for (Value *Obj : Objs) {
    if (isa<Function>(Obj) || isa<BlockAddress>(Obj))
      continue;
    if (isa<GlobalVariable>(Obj) && cast<GlobalVariable>(Obj)->isConstant())
      continue;

    AllConstants = false;
    break;
  }
  if (AllConstants)
    return DFS.ZeroShadow;

  Value *ShadowAddr = DFS.getShadowAddress(Addr, Pos);
  switch (Size) {
  case 0:
    return DFS.ZeroShadow;
  case 1: {
    LoadInst *LI = new LoadInst(ShadowAddr, "", Pos);
    LI->setAlignment(ShadowAlign);
    return LI;
  }
  case 2: {
    IRBuilder<> IRB(Pos);
    Value *ShadowAddr1 = IRB.CreateGEP(DFS.ShadowTy, ShadowAddr,
                                       ConstantInt::get(DFS.IntptrTy, 1));
    return combineShadows(IRB.CreateAlignedLoad(ShadowAddr, ShadowAlign),
                          IRB.CreateAlignedLoad(ShadowAddr1, ShadowAlign), Pos);
  }
  }
  if (!AvoidNewBlocks && Size % (64 / DFS.ShadowWidth) == 0) {
    // Fast path for the common case where each byte has identical shadow: load
    // shadow 64 bits at a time, fall out to a __dfsan_union_load call if any
    // shadow is non-equal.
    BasicBlock *FallbackBB = BasicBlock::Create(*DFS.Ctx, "", F);
    IRBuilder<> FallbackIRB(FallbackBB);
    CallInst *FallbackCall = FallbackIRB.CreateCall(
        DFS.DFSanUnionLoadFn,
        {ShadowAddr, ConstantInt::get(DFS.IntptrTy, Size)});
    FallbackCall->addAttribute(AttributeList::ReturnIndex, Attribute::ZExt);

    // Compare each of the shadows stored in the loaded 64 bits to each other,
    // by computing (WideShadow rotl ShadowWidth) == WideShadow.
    IRBuilder<> IRB(Pos);
    Value *WideAddr =
        IRB.CreateBitCast(ShadowAddr, Type::getInt64PtrTy(*DFS.Ctx));
    Value *WideShadow = IRB.CreateAlignedLoad(WideAddr, ShadowAlign);
    Value *TruncShadow = IRB.CreateTrunc(WideShadow, DFS.ShadowTy);
    Value *ShlShadow = IRB.CreateShl(WideShadow, DFS.ShadowWidth);
    Value *ShrShadow = IRB.CreateLShr(WideShadow, 64 - DFS.ShadowWidth);
    Value *RotShadow = IRB.CreateOr(ShlShadow, ShrShadow);
    Value *ShadowsEq = IRB.CreateICmpEQ(WideShadow, RotShadow);

    BasicBlock *Head = Pos->getParent();
    BasicBlock *Tail = Head->splitBasicBlock(Pos->getIterator());

    if (DomTreeNode *OldNode = DT.getNode(Head)) {
      std::vector<DomTreeNode *> Children(OldNode->begin(), OldNode->end());

      DomTreeNode *NewNode = DT.addNewBlock(Tail, Head);
      for (auto Child : Children)
        DT.changeImmediateDominator(Child, NewNode);
    }

    // In the following code LastBr will refer to the previous basic block's
    // conditional branch instruction, whose true successor is fixed up to point
    // to the next block during the loop below or to the tail after the final
    // iteration.
    BranchInst *LastBr = BranchInst::Create(FallbackBB, FallbackBB, ShadowsEq);
    ReplaceInstWithInst(Head->getTerminator(), LastBr);
    DT.addNewBlock(FallbackBB, Head);

    for (uint64_t Ofs = 64 / DFS.ShadowWidth; Ofs != Size;
         Ofs += 64 / DFS.ShadowWidth) {
      BasicBlock *NextBB = BasicBlock::Create(*DFS.Ctx, "", F);
      DT.addNewBlock(NextBB, LastBr->getParent());
      IRBuilder<> NextIRB(NextBB);
      WideAddr = NextIRB.CreateGEP(Type::getInt64Ty(*DFS.Ctx), WideAddr,
                                   ConstantInt::get(DFS.IntptrTy, 1));
      Value *NextWideShadow = NextIRB.CreateAlignedLoad(WideAddr, ShadowAlign);
      ShadowsEq = NextIRB.CreateICmpEQ(WideShadow, NextWideShadow);
      LastBr->setSuccessor(0, NextBB);
      LastBr = NextIRB.CreateCondBr(ShadowsEq, FallbackBB, FallbackBB);
    }

    LastBr->setSuccessor(0, Tail);
    FallbackIRB.CreateBr(Tail);
    PHINode *Shadow = PHINode::Create(DFS.ShadowTy, 2, "", &Tail->front());
    Shadow->addIncoming(FallbackCall, FallbackBB);
    Shadow->addIncoming(TruncShadow, LastBr->getParent());
    return Shadow;
  }

  IRBuilder<> IRB(Pos);
  CallInst *FallbackCall = IRB.CreateCall(
      DFS.DFSanUnionLoadFn, {ShadowAddr, ConstantInt::get(DFS.IntptrTy, Size)});
  FallbackCall->addAttribute(AttributeList::ReturnIndex, Attribute::ZExt);
  return FallbackCall;
}

void DFSanVisitor::visitLoadInst(LoadInst &LI) {
  auto &DL = LI.getModule()->getDataLayout();
  uint64_t Size = DL.getTypeStoreSize(LI.getType());
  if (Size == 0) {
    DFSF.setShadow(&LI, DFSF.DFS.ZeroShadow);
    return;
  }

  uint64_t Align;
  if (ClPreserveAlignment) {
    Align = LI.getAlignment();
    if (Align == 0)
      Align = DL.getABITypeAlignment(LI.getType());
  } else {
    Align = 1;
  }
  IRBuilder<> IRB(&LI);
  Value *Shadow = DFSF.loadShadow(LI.getPointerOperand(), Size, Align, &LI);
  if (ClCombinePointerLabelsOnLoad) {
    Value *PtrShadow = DFSF.getShadow(LI.getPointerOperand());
    Shadow = DFSF.combineShadows(Shadow, PtrShadow, &LI);
  }
  if (Shadow != DFSF.DFS.ZeroShadow)
    DFSF.NonZeroChecks.push_back(Shadow);

  DFSF.setShadow(&LI, Shadow);
}

void DFSanFunction::storeShadow(Value *Addr, uint64_t Size, uint64_t Align,
                                Value *Shadow, Instruction *Pos) {
  if (AllocaInst *AI = dyn_cast<AllocaInst>(Addr)) {
    const auto i = AllocaShadowMap.find(AI);
    if (i != AllocaShadowMap.end()) {
      IRBuilder<> IRB(Pos);
      IRB.CreateStore(Shadow, i->second);
      return;
    }
  }

  uint64_t ShadowAlign = Align * DFS.ShadowWidth / 8;
  IRBuilder<> IRB(Pos);
  Value *ShadowAddr = DFS.getShadowAddress(Addr, Pos);
  if (Shadow == DFS.ZeroShadow) {
    IntegerType *ShadowTy = IntegerType::get(*DFS.Ctx, Size * DFS.ShadowWidth);
    Value *ExtZeroShadow = ConstantInt::get(ShadowTy, 0);
    Value *ExtShadowAddr =
        IRB.CreateBitCast(ShadowAddr, PointerType::getUnqual(ShadowTy));
    IRB.CreateAlignedStore(ExtZeroShadow, ExtShadowAddr, ShadowAlign);
    return;
  }

  const unsigned ShadowVecSize = 128 / DFS.ShadowWidth;
  uint64_t Offset = 0;
  if (Size >= ShadowVecSize) {
    VectorType *ShadowVecTy = VectorType::get(DFS.ShadowTy, ShadowVecSize);
    Value *ShadowVec = UndefValue::get(ShadowVecTy);
    for (unsigned i = 0; i != ShadowVecSize; ++i) {
      ShadowVec = IRB.CreateInsertElement(
          ShadowVec, Shadow, ConstantInt::get(Type::getInt32Ty(*DFS.Ctx), i));
    }
    Value *ShadowVecAddr =
        IRB.CreateBitCast(ShadowAddr, PointerType::getUnqual(ShadowVecTy));
    do {
      Value *CurShadowVecAddr =
          IRB.CreateConstGEP1_32(ShadowVecTy, ShadowVecAddr, Offset);
      IRB.CreateAlignedStore(ShadowVec, CurShadowVecAddr, ShadowAlign);
      Size -= ShadowVecSize;
      ++Offset;
    } while (Size >= ShadowVecSize);
    Offset *= ShadowVecSize;
  }
  while (Size > 0) {
    Value *CurShadowAddr =
        IRB.CreateConstGEP1_32(DFS.ShadowTy, ShadowAddr, Offset);
    IRB.CreateAlignedStore(Shadow, CurShadowAddr, ShadowAlign);
    --Size;
    ++Offset;
  }
}

void DFSanVisitor::visitStoreInst(StoreInst &SI) {
  auto &DL = SI.getModule()->getDataLayout();
  uint64_t Size = DL.getTypeStoreSize(SI.getValueOperand()->getType());
  if (Size == 0)
    return;

  uint64_t Align;
  if (ClPreserveAlignment) {
    Align = SI.getAlignment();
    if (Align == 0)
      Align = DL.getABITypeAlignment(SI.getValueOperand()->getType());
  } else {
    Align = 1;
  }

  Value* Shadow = DFSF.getShadow(SI.getValueOperand());
  if (ClCombinePointerLabelsOnStore) {
    Value *PtrShadow = DFSF.getShadow(SI.getPointerOperand());
    Shadow = DFSF.combineShadows(Shadow, PtrShadow, &SI);
  }
  DFSF.storeShadow(SI.getPointerOperand(), Size, Align, Shadow, &SI);
}

void DFSanVisitor::visitBinaryOperator(BinaryOperator &BO) {
  visitOperandShadowInst(BO);
}

void DFSanVisitor::visitCastInst(CastInst &CI) { visitOperandShadowInst(CI); }

void DFSanVisitor::visitCmpInst(CmpInst &CI) { visitOperandShadowInst(CI); }

void DFSanVisitor::visitGetElementPtrInst(GetElementPtrInst &GEPI) {
  visitOperandShadowInst(GEPI);
}

void DFSanVisitor::visitExtractElementInst(ExtractElementInst &I) {
  visitOperandShadowInst(I);
}

void DFSanVisitor::visitInsertElementInst(InsertElementInst &I) {
  visitOperandShadowInst(I);
}

void DFSanVisitor::visitShuffleVectorInst(ShuffleVectorInst &I) {
  visitOperandShadowInst(I);
}

void DFSanVisitor::visitExtractValueInst(ExtractValueInst &I) {
  visitOperandShadowInst(I);
}

void DFSanVisitor::visitInsertValueInst(InsertValueInst &I) {
  visitOperandShadowInst(I);
}

void DFSanVisitor::visitAllocaInst(AllocaInst &I) {
  bool AllLoadsStores = true;
  for (User *U : I.users()) {
    if (isa<LoadInst>(U))
      continue;

    if (StoreInst *SI = dyn_cast<StoreInst>(U)) {
      if (SI->getPointerOperand() == &I)
        continue;
    }

    AllLoadsStores = false;
    break;
  }
  if (AllLoadsStores) {
    IRBuilder<> IRB(&I);
    DFSF.AllocaShadowMap[&I] = IRB.CreateAlloca(DFSF.DFS.ShadowTy);
  }
  DFSF.setShadow(&I, DFSF.DFS.ZeroShadow);
}

void DFSanVisitor::visitSelectInst(SelectInst &I) {
  Value *CondShadow = DFSF.getShadow(I.getCondition());
  Value *TrueShadow = DFSF.getShadow(I.getTrueValue());
  Value *FalseShadow = DFSF.getShadow(I.getFalseValue());

  if (isa<VectorType>(I.getCondition()->getType())) {
    DFSF.setShadow(
        &I,
        DFSF.combineShadows(
            CondShadow, DFSF.combineShadows(TrueShadow, FalseShadow, &I), &I));
  } else {
    Value *ShadowSel;
    if (TrueShadow == FalseShadow) {
      ShadowSel = TrueShadow;
    } else {
      ShadowSel =
          SelectInst::Create(I.getCondition(), TrueShadow, FalseShadow, "", &I);
    }
    DFSF.setShadow(&I, DFSF.combineShadows(CondShadow, ShadowSel, &I));
  }
}

void DFSanVisitor::visitMemSetInst(MemSetInst &I) {
  IRBuilder<> IRB(&I);
  Value *ValShadow = DFSF.getShadow(I.getValue());
  IRB.CreateCall(DFSF.DFS.DFSanSetLabelFn,
                 {ValShadow, IRB.CreateBitCast(I.getDest(), Type::getInt8PtrTy(
                                                                *DFSF.DFS.Ctx)),
                  IRB.CreateZExtOrTrunc(I.getLength(), DFSF.DFS.IntptrTy)});
}

void DFSanVisitor::visitMemTransferInst(MemTransferInst &I) {
  IRBuilder<> IRB(&I);
  Value *DestShadow = DFSF.DFS.getShadowAddress(I.getDest(), &I);
  Value *SrcShadow = DFSF.DFS.getShadowAddress(I.getSource(), &I);
  Value *LenShadow = IRB.CreateMul(
      I.getLength(),
      ConstantInt::get(I.getLength()->getType(), DFSF.DFS.ShadowWidth / 8));
  Type *Int8Ptr = Type::getInt8PtrTy(*DFSF.DFS.Ctx);
  DestShadow = IRB.CreateBitCast(DestShadow, Int8Ptr);
  SrcShadow = IRB.CreateBitCast(SrcShadow, Int8Ptr);
  auto *MTI = cast<MemTransferInst>(
      IRB.CreateCall(I.getCalledValue(),
                     {DestShadow, SrcShadow, LenShadow, I.getVolatileCst()}));
  if (ClPreserveAlignment) {
    MTI->setDestAlignment(I.getDestAlignment() * (DFSF.DFS.ShadowWidth / 8));
    MTI->setSourceAlignment(I.getSourceAlignment() * (DFSF.DFS.ShadowWidth / 8));
  } else {
    MTI->setDestAlignment(DFSF.DFS.ShadowWidth / 8);
    MTI->setSourceAlignment(DFSF.DFS.ShadowWidth / 8);
  }
}

void DFSanVisitor::visitReturnInst(ReturnInst &RI) {
  if (ClDiscovery && DFSF.F->getName() == "main") {
    DFSF.combineOperandShadows(&RI);
  }
  if (!DFSF.IsNativeABI && RI.getReturnValue()) {
    switch (DFSF.IA) {
    case DataFlowSanitizer::IA_TLS: {
      Value *S = DFSF.getShadow(RI.getReturnValue());
      IRBuilder<> IRB(&RI);
      IRB.CreateStore(S, DFSF.getRetvalTLS());
      break;
    }
    case DataFlowSanitizer::IA_Args: {
      IRBuilder<> IRB(&RI);
      Type *RT = DFSF.F->getFunctionType()->getReturnType();
      Value *InsVal =
          IRB.CreateInsertValue(UndefValue::get(RT), RI.getReturnValue(), 0);
      Value *InsShadow =
          IRB.CreateInsertValue(InsVal, DFSF.getShadow(RI.getReturnValue()), 1);
      RI.setOperand(0, InsShadow);
      break;
    }
    }
  }
}

void DFSanVisitor::visitCallSite(CallSite CS) {
  Function *F = CS.getCalledFunction();

  // Ignore debug intrinsics in ClDiscovery mode.
  if (ClDiscovery && F && F->isIntrinsic() &&
      ((Intrinsic::ID)F->getIntrinsicID() == Intrinsic::dbg_declare ||
       (Intrinsic::ID)F->getIntrinsicID() == Intrinsic::dbg_value ||
       (Intrinsic::ID)F->getIntrinsicID() == Intrinsic::dbg_addr)) {
    return;
  }

  if ((F && F->isIntrinsic()) || isa<InlineAsm>(CS.getCalledValue())) {
    visitOperandShadowInst(*CS.getInstruction());
    return;
  }

  // Calls to this function are synthesized in wrappers, and we shouldn't
  // instrument them.
  if (F == DFSF.DFS.DFSanVarargWrapperFn)
    return;

  IRBuilder<> IRB(CS.getInstruction());

  DenseMap<Value *, Function *>::iterator i =
      DFSF.DFS.UnwrappedFnMap.find(CS.getCalledValue());
  if (i != DFSF.DFS.UnwrappedFnMap.end()) {
    Function *F = i->second;
    // In ClDiscovery mode, we trace the input data-flow to system calls such as
    // printf, to distinguish the computations that affect the behaviour of the
    // program. An exception is "functional" system calls, which are treated as
    // simple operations. After the execution, data-flow unreachable from system
    // calls, conditional branches, and return from "main" is pruned and only
    // the "essence" of the program is left (see "Redux" paper by Nethercote and
    // Mycroft). If ClCombinePointerLabelsOnLoad and
    // ClCombinePointerLabelsOnStore are set to false, address computations will
    // also be pruned as in Redux.
    switch (DFSF.DFS.getWrapperKind(F)) {
    case DataFlowSanitizer::WK_Warning:
      CS.setCalledFunction(F);
      // FIXME: rather than special-case here, create a new wrapper kind.
      if (ClDiscovery &&
          // std::ios_base::Init::Init()
          F->getName() != "_ZNSt8ios_base4InitC1Ev" &&
          // std::ios_base::Init::~Init()
          F->getName() != "_ZNSt8ios_base4InitD1Ev") {
        DFSF.combineOperandShadows(CS.getInstruction());
      }
      IRB.CreateCall(DFSF.DFS.DFSanUnimplementedFn,
                     IRB.CreateGlobalStringPtr(F->getName()));
      DFSF.setShadow(CS.getInstruction(), DFSF.DFS.ZeroShadow);
      return;
    case DataFlowSanitizer::WK_Discard:
      CS.setCalledFunction(F);
      // FIXME: rather than special-case here, create a new wrapper kind.
      if (ClDiscovery &&
          F->getName() != "main" &&
          F->getName() != "__cxa_atexit") {
        DFSF.combineOperandShadows(CS.getInstruction());
      }
      DFSF.setShadow(CS.getInstruction(), DFSF.DFS.ZeroShadow);
      return;
    case DataFlowSanitizer::WK_Functional:
      CS.setCalledFunction(F);
      visitOperandShadowInst(*CS.getInstruction());
      return;
    case DataFlowSanitizer::WK_Custom:
      // Don't try to handle invokes of custom functions, it's too complicated.
      // Instead, invoke the dfsw$ wrapper, which will in turn call the __dfsw_
      // wrapper.
      if (CallInst *CI = dyn_cast<CallInst>(CS.getInstruction())) {
        if (ClDiscovery) {
          DFSF.combineOperandShadows(CI);
        }
        FunctionType *FT = F->getFunctionType();
        TransformedFunction CustomFn = DFSF.DFS.getCustomFunctionType(FT);
        std::string CustomFName = "__dfsw_";
        CustomFName += F->getName();
        Constant *CustomF = DFSF.DFS.Mod->getOrInsertFunction(
            CustomFName, CustomFn.TransformedType);
        if (Function *CustomFn = dyn_cast<Function>(CustomF)) {
          CustomFn->copyAttributesFrom(F);

          // Custom functions returning non-void will write to the return label.
          if (!FT->getReturnType()->isVoidTy()) {
            CustomFn->removeAttributes(AttributeList::FunctionIndex,
                                       DFSF.DFS.ReadOnlyNoneAttrs);
          }
        }

        std::vector<Value *> Args;

        CallSite::arg_iterator i = CS.arg_begin();
        for (unsigned n = FT->getNumParams(); n != 0; ++i, --n) {
          Type *T = (*i)->getType();
          FunctionType *ParamFT;
          if (isa<PointerType>(T) &&
              (ParamFT = dyn_cast<FunctionType>(
                   cast<PointerType>(T)->getElementType()))) {
            std::string TName = "dfst";
            TName += utostr(FT->getNumParams() - n);
            TName += "$";
            TName += F->getName();
            Constant *T = DFSF.DFS.getOrBuildTrampolineFunction(ParamFT, TName);
            Args.push_back(T);
            Args.push_back(
                IRB.CreateBitCast(*i, Type::getInt8PtrTy(*DFSF.DFS.Ctx)));
          } else {
            Args.push_back(*i);
          }
        }

        i = CS.arg_begin();
        const unsigned ShadowArgStart = Args.size();
        for (unsigned n = FT->getNumParams(); n != 0; ++i, --n)
          Args.push_back(DFSF.getShadow(*i));

        if (FT->isVarArg()) {
          auto *LabelVATy = ArrayType::get(DFSF.DFS.ShadowTy,
                                           CS.arg_size() - FT->getNumParams());
          auto *LabelVAAlloca = new AllocaInst(
              LabelVATy, getDataLayout().getAllocaAddrSpace(),
              "labelva", &DFSF.F->getEntryBlock().front());

          for (unsigned n = 0; i != CS.arg_end(); ++i, ++n) {
            auto LabelVAPtr = IRB.CreateStructGEP(LabelVATy, LabelVAAlloca, n);
            IRB.CreateStore(DFSF.getShadow(*i), LabelVAPtr);
          }

          Args.push_back(IRB.CreateStructGEP(LabelVATy, LabelVAAlloca, 0));
        }

        if (!FT->getReturnType()->isVoidTy()) {
          if (!DFSF.LabelReturnAlloca) {
            DFSF.LabelReturnAlloca =
              new AllocaInst(DFSF.DFS.ShadowTy,
                             getDataLayout().getAllocaAddrSpace(),
                             "labelreturn", &DFSF.F->getEntryBlock().front());
          }
          Args.push_back(DFSF.LabelReturnAlloca);
        }

        for (i = CS.arg_begin() + FT->getNumParams(); i != CS.arg_end(); ++i)
          Args.push_back(*i);

        CallInst *CustomCI = IRB.CreateCall(CustomF, Args);
        CustomCI->setCallingConv(CI->getCallingConv());
        CustomCI->setAttributes(TransformFunctionAttributes(CustomFn,
            CI->getContext(), CI->getAttributes()));

        // Update the parameter attributes of the custom call instruction to
        // zero extend the shadow parameters. This is required for targets
        // which consider ShadowTy an illegal type.
        for (unsigned n = 0; n < FT->getNumParams(); n++) {
          const unsigned ArgNo = ShadowArgStart + n;
          if (CustomCI->getArgOperand(ArgNo)->getType() == DFSF.DFS.ShadowTy)
            CustomCI->addParamAttr(ArgNo, Attribute::ZExt);
        }

        if (!FT->getReturnType()->isVoidTy()) {
          LoadInst *LabelLoad = IRB.CreateLoad(DFSF.LabelReturnAlloca);
          DFSF.setShadow(CustomCI, LabelLoad);
        }

        CI->replaceAllUsesWith(CustomCI);
        CI->eraseFromParent();
        return;
      }
      break;
    }
  }

  FunctionType *FT = cast<FunctionType>(
      CS.getCalledValue()->getType()->getPointerElementType());
  if (DFSF.DFS.getInstrumentedABI() == DataFlowSanitizer::IA_TLS) {
    for (unsigned i = 0, n = FT->getNumParams(); i != n; ++i) {
      IRB.CreateStore(DFSF.getShadow(CS.getArgument(i)),
                      DFSF.getArgTLS(i, CS.getInstruction()));
    }
  }

  Instruction *Next = nullptr;
  if (!CS.getType()->isVoidTy()) {
    if (InvokeInst *II = dyn_cast<InvokeInst>(CS.getInstruction())) {
      if (II->getNormalDest()->getSinglePredecessor()) {
        Next = &II->getNormalDest()->front();
      } else {
        BasicBlock *NewBB =
            SplitEdge(II->getParent(), II->getNormalDest(), &DFSF.DT);
        Next = &NewBB->front();
      }
    } else {
      assert(CS->getIterator() != CS->getParent()->end());
      Next = CS->getNextNode();
    }

    if (DFSF.DFS.getInstrumentedABI() == DataFlowSanitizer::IA_TLS) {
      IRBuilder<> NextIRB(Next);
      LoadInst *LI = NextIRB.CreateLoad(DFSF.getRetvalTLS());
      DFSF.SkipInsts.insert(LI);
      DFSF.setShadow(CS.getInstruction(), LI);
      DFSF.NonZeroChecks.push_back(LI);
    }
  }

  // Do all instrumentation for IA_Args down here to defer tampering with the
  // CFG in a way that SplitEdge may be able to detect.
  if (DFSF.DFS.getInstrumentedABI() == DataFlowSanitizer::IA_Args) {
    FunctionType *NewFT = DFSF.DFS.getArgsFunctionType(FT);
    Value *Func =
        IRB.CreateBitCast(CS.getCalledValue(), PointerType::getUnqual(NewFT));
    std::vector<Value *> Args;

    CallSite::arg_iterator i = CS.arg_begin(), e = CS.arg_end();
    for (unsigned n = FT->getNumParams(); n != 0; ++i, --n)
      Args.push_back(*i);

    i = CS.arg_begin();
    for (unsigned n = FT->getNumParams(); n != 0; ++i, --n)
      Args.push_back(DFSF.getShadow(*i));

    if (FT->isVarArg()) {
      unsigned VarArgSize = CS.arg_size() - FT->getNumParams();
      ArrayType *VarArgArrayTy = ArrayType::get(DFSF.DFS.ShadowTy, VarArgSize);
      AllocaInst *VarArgShadow =
        new AllocaInst(VarArgArrayTy, getDataLayout().getAllocaAddrSpace(),
                       "", &DFSF.F->getEntryBlock().front());
      Args.push_back(IRB.CreateConstGEP2_32(VarArgArrayTy, VarArgShadow, 0, 0));
      for (unsigned n = 0; i != e; ++i, ++n) {
        IRB.CreateStore(
            DFSF.getShadow(*i),
            IRB.CreateConstGEP2_32(VarArgArrayTy, VarArgShadow, 0, n));
        Args.push_back(*i);
      }
    }

    CallSite NewCS;
    if (InvokeInst *II = dyn_cast<InvokeInst>(CS.getInstruction())) {
      NewCS = IRB.CreateInvoke(Func, II->getNormalDest(), II->getUnwindDest(),
                               Args);
    } else {
      NewCS = IRB.CreateCall(Func, Args);
    }
    NewCS.setCallingConv(CS.getCallingConv());
    NewCS.setAttributes(CS.getAttributes().removeAttributes(
        *DFSF.DFS.Ctx, AttributeList::ReturnIndex,
        AttributeFuncs::typeIncompatible(NewCS.getInstruction()->getType())));

    if (Next) {
      ExtractValueInst *ExVal =
          ExtractValueInst::Create(NewCS.getInstruction(), 0, "", Next);
      DFSF.SkipInsts.insert(ExVal);
      ExtractValueInst *ExShadow =
          ExtractValueInst::Create(NewCS.getInstruction(), 1, "", Next);
      DFSF.SkipInsts.insert(ExShadow);
      DFSF.setShadow(ExVal, ExShadow);
      DFSF.NonZeroChecks.push_back(ExShadow);

      CS.getInstruction()->replaceAllUsesWith(ExVal);
    }

    CS.getInstruction()->eraseFromParent();
  }
}

void DFSanVisitor::visitPHINode(PHINode &PN) {
  PHINode *ShadowPN =
      PHINode::Create(DFSF.DFS.ShadowTy, PN.getNumIncomingValues(), "", &PN);

  // Give the shadow phi node valid predecessors to fool SplitEdge into working.
  Value *UndefShadow = UndefValue::get(DFSF.DFS.ShadowTy);
  for (PHINode::block_iterator i = PN.block_begin(), e = PN.block_end(); i != e;
       ++i) {
    ShadowPN->addIncoming(UndefShadow, *i);
  }

  DFSF.PHIFixups.push_back(std::make_pair(&PN, ShadowPN));
  DFSF.setShadow(&PN, ShadowPN);
}

void DFSanVisitor::visitBranchInst(BranchInst &I) {
  // In ClDiscovery mode, the data reaching conditional branches is tracked.
  if (ClDiscovery && I.isConditional()) {
    visitOperandShadowInst(I);
  }
}
