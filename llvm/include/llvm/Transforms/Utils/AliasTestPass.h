//===-- AliasTestPass.h - Example Transformations ------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_TRANSFORMS_UTILS_AATEST_H
#define LLVM_TRANSFORMS_UTILS_AATEST_H

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
#include <vector>

namespace llvm {

struct MemInstSets {
  SetVector<LoadInst *> Loads;
  SetVector<StoreInst *> Stores;
  SetVector<AllocaInst *> Allocs;
  SetVector<CallInst *> Calls;

  bool empty() {
    return Loads.empty() && Stores.empty() 
        && Allocs.empty() && Calls.empty();
  }
};

class AliasTestPass : public PassInfoMixin<AliasTestPass> {
private:
  struct MemInstSets getMemInstr(Function &F);
  void iterateOnFunction(Function &F, FunctionAnalysisManager &FAM, 
                        ModuleAnalysisManager &MAM);

  void evaluate(Function &F, FunctionAnalysisManager &FAM, 
                ModuleAnalysisManager &MAM, std::vector<unsigned int> &counts);

  bool betterAliasResult(const AliasResult &AR1, const AliasResult &AR2) {
    return AR2 == AliasResult::MayAlias && AR1 != AliasResult::MayAlias;
  }

  AliasResult tryAliasOrigin(const MemoryLocation &LocA, const MemoryLocation &LocB, 
                    AliasGraph &graph, AliasAnalysis &AA);

  AliasResult aliasInterp(const Value * V1, const Value * V2, AliasAnalysis &defaultAA);

public:
  PreservedAnalyses run(Module &M, ModuleAnalysisManager &AM);
};

} // namespace llvm

#endif // LLVM_TRANSFORMS_UTILS_AATEST_H
