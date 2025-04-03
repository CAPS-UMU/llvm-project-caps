//===-- UnrollInnerMostLoop.cpp - Example Transformations --------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
#include "llvm/Transforms/Utils/UnrollInnerMostLoop.h"
#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/Analysis/DomTreeUpdater.h"
#include "llvm/Analysis/TargetTransformInfo.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Transforms/Utils/UnrollLoop.h"
#include "llvm/IR/PassManager.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/Transforms/Utils/LoopUtils.h"
#include "llvm/Analysis/LoopAnalysisManager.h"
#include "llvm/Transforms/Scalar/LoopUnrollPass.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Transforms/Utils/LCSSA.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/Scalar/LoopUnrollPass.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/LoopIterator.h"
#include "llvm/Analysis/OptimizationRemarkEmitter.h"
#include "llvm/Analysis/ScalarEvolution.h"

using namespace llvm;

// Function to check if a loop has been unrolled before
bool isLoopUnrolled(Loop *L) {
    if (MDNode *MD = L->getLoopID()) {
        for (unsigned i = 0, e = MD->getNumOperands(); i != e; ++i) {
            if (MDString *S = dyn_cast<MDString>(MD->getOperand(i))) {
                if (S->getString() == "llvm.loop.unrolled") {
                    return true;
                }
            }
        }
    }
    return false;
}

// Function to mark a loop as unrolled
void markLoopAsUnrolled(Loop *L) {
    LLVMContext &Context = L->getHeader()->getContext();
    MDNode *MD = L->getLoopID();
    MDNode *NewMD = MDNode::get(Context, {MDString::get(Context, "llvm.loop.unrolled")});
    L->setLoopID(NewMD);
}
// struct UnrollInnermostLoop : public PassInfoMixin<UnrollInnermostLoop> {
//   PreservedAnalyses run(Function &F, FunctionAnalysisManager &AM) {
// static void unrollInnermostLoop_fn(Loop *L, FunctionAnalysisManager &FAM);

PreservedAnalyses UnrollInnermostLoopPass::run(Function &F, FunctionAnalysisManager &AM) {
    // Get the loop information
    auto &LI = AM.getResult<LoopAnalysis>(F);
    // Get required analyses for loop unrolling
    auto &SE = AM.getResult<ScalarEvolutionAnalysis>(F);
    auto &AC = AM.getResult<AssumptionAnalysis>(F);
    auto &DT = AM.getResult<DominatorTreeAnalysis>(F);
    auto &TTI = AM.getResult<TargetIRAnalysis>(F);

    // Collect all loops including subloops in the Loops vector
    std::vector<Loop *> Loops(LI.begin(), LI.end());

    for (unsigned long i = 0; i < Loops.size(); ++i)
        for (Loop *ChildL : Loops[i]->getSubLoops())
            Loops.push_back(ChildL);
           
    for (Loop *L : Loops) {
        if (!L->isInnermost())
            continue;
        // Ensure the loop is in LCSSA form before unrolling
        if (!L->isLCSSAForm(DT)) {
            formLCSSA(*L, DT, &LI, nullptr);
        }

    // Count the total number of instructions, loads, stores, and vector instructions
    int TotalInstructions = 0;
    int LoadInstructions = 0;
    int StoreInstructions = 0;
    int VectorLoadInstructions = 0;
    int VectorStoreInstructions = 0;

    for (BasicBlock *BB : L->blocks()) {
        for (Instruction &I : *BB) {
            TotalInstructions++;
            if (isa<LoadInst>(&I)) {
                LoadInstructions++;
                if (I.getType()->isVectorTy()) {
                    VectorLoadInstructions++;
                }
            } else if (isa<StoreInst>(&I)) {
                StoreInstructions++;
                if (I.getOperand(0)->getType()->isVectorTy()) {
                    VectorStoreInstructions++;
                }
            }
        }
    }

    errs() << "Innermost loop in function " << F.getName() << " has "
           << TotalInstructions << " instructions, "
           << LoadInstructions << " loads, "
           << StoreInstructions << " stores, "
           << VectorLoadInstructions << " vector loads, and "
           << VectorStoreInstructions << " vector stores.\n";

    // Unroll the loop only if it contains 0 vector loads/stores and fewer than 50 instructions
    if (((VectorLoadInstructions == 0 && LoadInstructions != 0) && TotalInstructions < 50)) {
        // Ensure the loop is in LCSSA form before unrolling
        // Set the unroll options with a factor of 2
        // LoopUnrollOptions UnrollOpts;
        // UnrollOpts.setUnrollFactor(2);
        // UnrollOpts.setUnrollRemainder(true);
        auto UnrollResult = LoopUnrollResult::Unmodified;
        // Perform loop unrolling
        bool PreserveLCSSA = true;
        UnrollResult = UnrollLoop(L, {/*Count*/ 2, /*Force*/ false, /*Runtime*/ true,
                        /*AllowExpensiveTripCount*/ false,
                        /*UnrollRemainder*/ false, false}, &LI, &SE, &DT, &AC, &TTI, /*ORE*/ nullptr, PreserveLCSSA);
        if (UnrollResult != LoopUnrollResult::Unmodified) {
            errs() << "Innermost loop unrolled with factor 2 in function: " << F.getName() << "\n";
        } 
        } else {
        errs() << "Innermost loop in function " << F.getName() << " is not unrolled due to vector instructions or too many instructions.\n";
    }
    }
    return PreservedAnalyses::none();
}

// Loop *L, UnrollLoopOptions ULO, LoopInfo *LI,
//                                   ScalarEvolution *SE, DominatorTree *DT,
//                                   AssumptionCache *AC,
//                                   const TargetTransformInfo *TTI,
//                                   OptimizationRemarkEmitter *ORE,
//                                   bool PreserveLCSSA, Loop **RemainderLoop