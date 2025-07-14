//===-- reorder.h - Example Transformations ------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_TRANSFORMS_UTILS_REORDER_H
#define LLVM_TRANSFORMS_UTILS_REORDER_H

#include "llvm/IR/PassManager.h"
#include "llvm/Analysis/AliasGraph.h"
#include "llvm/Analysis/GlobalsModRef.h"
#include "llvm/Analysis/MemoryLocation.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/Passes.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/ADT/SetVector.h"
namespace llvm {
class AAResults;
class Function;
class FunctionPass;
class AAResultsWrapperPass;
class AnalysisUsage;
class ReorderPass : public PassInfoMixin<ReorderPass> {
private:
  PreservedAnalyses runonFunction(Function &F, ModuleAnalysisManager &MAM, FunctionAnalysisManager &FAM);
public:
  PreservedAnalyses run(Module &M, ModuleAnalysisManager &AM);
  int run_globalWasted = 0;
  int run_globalReorder = 0;
  int run_globalAcrossCallReorder = 0;
  int run_globalAcrossCallWasted = 0;
  int run_globaldiffchainedgraphaa = 0;
};

} // namespace llvm

#endif // LLVM_TRANSFORMS_UTILS_REORDER_H