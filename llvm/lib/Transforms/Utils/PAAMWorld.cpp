//===-- PAAMWorld.cpp - Example Transformations --------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
#include "llvm/Transforms/Utils/PAAMWorld.h"
#include "llvm/IR/Function.h"

using namespace llvm;

PreservedAnalyses PAAMWorldPass::run(Function &F,
                                      FunctionAnalysisManager &AM) {
  errs() << F.getName() << "\n";
  uint64_t count = 0;
  for (auto &BB : F) {
    for (auto &I : BB) {
      errs() << I << "\n";
      if(I.getOpcode() == Instruction::Load) {
        count++;
      }
    }
  }
  errs() << "Total number of loads: " << count << "\n";
  return PreservedAnalyses::all();
}
