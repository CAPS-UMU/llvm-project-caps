//===-- AliasTestPass.h - Example Transformations ------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_TRANSFORMS_UTILS_AATEST_H
#define LLVM_TRANSFORMS_UTILS_AATEST_H

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

struct LdStInst {
    SetVector<Value *> Loads;
    SetVector<Value *> Stores;
};

class AAResults;
class Function;
class FunctionPass;
class AAResultsWrapperPass;
class AnalysisUsage;
class AliasTestPass : public PassInfoMixin<AliasTestPass> {
private:
  struct LdStInst getLoadAndStore(Function &F);

public:
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &AM);
};

} // namespace llvm

#endif // LLVM_TRANSFORMS_UTILS_AATEST_H
