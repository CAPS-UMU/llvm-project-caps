//===-- MarkROI.cpp - Example Transformations --------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "llvm/Transforms/Utils/MarkROI.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/InlineAsm.h"

using namespace llvm;
using namespace std;
static cl::opt<std::string> FunctionName(
    "roi-function-name", cl::Hidden,
    cl::desc("ROI Function Name."));
//641.leela _ZN9FastBoard10self_atariEii FastBoard
//623.xalancbmk _ZN11xalanc_1_1022XStringCachedAllocator7destroyEPNS_13XStringCachedE XStringCachedAllocator
//631.deepjeng _Z7ProbeTTP7state_tPiiiPjS1_S1_S1_S1_i
//620.omnetpp cMessageHeap::shiftup _ZN12cMessageHeap7shiftupEi cMessageHeap
//605.mcf primal_bea_mpp pbeampp
//602.gcc bitmap_set_bit bitmap
//600.perlbench S_regmatch regexec
//625.x264 x264_encoder_encode encoder
PreservedAnalyses MarkROIPass::run(Function &F,
                                      FunctionAnalysisManager &AM) {
        // if (F.getName() != "_ZNK11xalanc_1_1013ElemWithParam12startElementERNS_26StylesheetExecutionContextE") {
        //     return PreservedAnalyses::all(); // Skip other functions
        // }

        // LLVMContext &Context = F.getContext();
        // IRBuilder<> Builder(Context);

        // // Inline assembly strings for start and end
        // std::string StartAsm = "srai zero, zero, 0";
        // std::string EndAsm = "srai zero, zero, 1";

        // // Insert "srai zero, zero, 0" at the beginning of the function
        // BasicBlock &EntryBlock = F.getEntryBlock();
        // Builder.SetInsertPoint(&EntryBlock, EntryBlock.begin());
        // FunctionType *VoidTy = FunctionType::get(Type::getVoidTy(Context), false);
        // InlineAsm *StartInlineAsm = InlineAsm::get(VoidTy, StartAsm, "", true);
        // Builder.CreateCall(StartInlineAsm);

        // // Create a unified exit block
        // BasicBlock *ExitBlock = BasicBlock::Create(Context, "exit_bb", &F);
        // Builder.SetInsertPoint(ExitBlock);
        // InlineAsm *EndInlineAsm = InlineAsm::get(VoidTy, EndAsm, "", true);
        // Builder.CreateCall(EndInlineAsm);

        // // Placeholder return type (assumes function returns i32, modify accordingly)
        // Type *RetType = F.getReturnType();
        // if (RetType->isVoidTy()) {
        //     Builder.CreateRetVoid();
        // } else {
        //     Builder.CreateRet(Constant::getNullValue(RetType)); // Adjust this as needed
        // }

        // // Redirect all return instructions to the new exit block
        // std::vector<ReturnInst *> ReturnInsts;
        // for (BasicBlock &BB : F) {
        //     for (Instruction &I : BB) {
        //         if (ReturnInst *RI = dyn_cast<ReturnInst>(&I)) {
        //             ReturnInsts.push_back(RI);
        //         }
        //     }
        // }

        // for (ReturnInst *RI : ReturnInsts) {
        //     IRBuilder<> RetBuilder(RI);
        //     RetBuilder.CreateBr(ExitBlock); // Replace return with a branch to exit block
        //     RI->eraseFromParent();          // Remove old return instruction
        // }
        //623.xalancbmk _ZNK11xalanc_1_1013ElemWithParam12startElementERNS_26StylesheetExecutionContextE
        //631.deepjeng _Z11search_rootP7state_tiii
        //641.leela _ZN9UCTSearch5thinkEii
        //657.xz lzma_code
        //600.perlbench Perl_regexec_flags
        //602.gcc execute_one_pass
        //605.mcf primal_net_simplex
        //619.lbm LBM_performStreamCollideTRT
        //620.omnetpp _ZN8EtherMAC22startFrameTransmissionEv
        //623.xalancbmk main //_ZN11xalanc_1_1027XalanReferenceCountedObject15removeReferenceEPS0_
        std::string function_name = FunctionName;
        if (function_name.empty())
        {
            errs() << "Function name not provided\n";
            assert(false && "Function name not provided");
            return PreservedAnalyses::all();
        }
        // Print the function name
        errs() << "Function Name: " << F.getName() << "\n";
        errs() << "Function Name Input: " << function_name << "\n";
        if (F.getName() != function_name) {
            return PreservedAnalyses::all(); // Skip other functions
        }

        LLVMContext &Context = F.getContext();
        IRBuilder<> Builder(Context);

        // Inline assembly strings for start and end
        std::string StartAsm = "srai zero, zero, 0";
        std::string EndAsm = "srai zero, zero, 1";

        // Insert "srai zero, zero, 0" at the beginning of the function
        BasicBlock &EntryBlock = F.getEntryBlock();
        Builder.SetInsertPoint(&EntryBlock, EntryBlock.begin());
        FunctionType *VoidTy = FunctionType::get(Type::getVoidTy(Context), false);
        InlineAsm *StartInlineAsm = InlineAsm::get(VoidTy, StartAsm, "", true);
        Builder.CreateCall(StartInlineAsm);

        // Insert "srai zero, zero, 1" before every return instruction
        for (BasicBlock &BB : F) {
            for (Instruction &I : BB) {
                if (isa<ReturnInst>(&I)) {
                    Builder.SetInsertPoint(&I);
                    InlineAsm *EndInlineAsm = InlineAsm::get(VoidTy, EndAsm, "", true);
                    Builder.CreateCall(EndInlineAsm);
                }
            }
        }
  return PreservedAnalyses::all();
}