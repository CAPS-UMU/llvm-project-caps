//===-- reordermlircombine.h - Example Transformations ------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_TRANSFORMS_UTILS_REORDER_SPECULATIVE_H
#define LLVM_TRANSFORMS_UTILS_REORDER_SPECULATIVE_H

#include "llvm/IR/PassManager.h"

namespace llvm {
class AAResults;
class Function;
class FunctionPass;
class AAResultsWrapperPass;
class AnalysisUsage;
class ReorderSpeculativePass : public PassInfoMixin<ReorderSpeculativePass> {
public:
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &AM);
};

} // namespace llvm

#endif // LLVM_TRANSFORMS_UTILS_REORDER_SPECULATIVE_H