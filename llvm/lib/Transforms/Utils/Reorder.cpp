//===-- Reorder.cpp - Example Transformations --------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

 
#include "llvm/Transforms/Utils/Reorder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/AliasAnalysisEvaluator.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/DependenceAnalysis.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include "llvm/ADT/SetVector.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/InitializePasses.h"
#include "llvm/Pass.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Analysis/BasicAliasAnalysis.h"
#include "llvm/Analysis/MemoryLocation.h"
#include "llvm/IR/PassManager.h"
#include "llvm/IR/CFG.h"
#include <queue>
 using namespace llvm;

 static cl::opt<bool> EnableSpeculativeReordering(
  "enable-spec-reordering", cl::init(false), cl::Hidden,
  cl::desc("Enable Speculative Reordering."));

  static cl::opt<bool> EnableAACallReordering(
    "enable-aa-call", cl::init(false), cl::Hidden,
    cl::desc("Enable AA Call Reordering."));

  static cl::opt<bool> EnableAcrossCallReordering(
    "enable-across-call-reordering", cl::init(false), cl::Hidden,
    cl::desc("Enable Reordering across calls."));

  static cl::opt<int> ReorderDistance(
    "reorder-distance", cl::init(10000000000), cl::Hidden,
    cl::desc("Reorder distance."));

 static bool isContiguous(APInt addr1, uint64_t size1, APInt addr2, uint64_t size2)
{
    // size1 = size1 / 8;
    // size2 = size2 / 8;
    // assert(size1.uge(1) && size1.ule(8) );
    // assert(size2.uge(1) && size2.ule(8));
    size1 = size1 / 8;
    size2 = size2 / 8;
    assert(size1 >= 1 && size1 <= 8);
    assert(size2 >= 1 && size2 <= 8);
    if (addr1 == addr2)
        return true;
    if (addr1.ult(addr2))
    {
        return (addr2 - addr1).ule(size1);
    }
    if (addr1.ugt(addr2))
    {
        return (addr1 - addr2).ule(size1);
    }
    return false;
}

static bool isSameLine(APInt StartAddr1, APInt EndAddr1, APInt StartAddr2, APInt EndAddr2)
{
    if ((StartAddr1.lshr(6) == StartAddr2.lshr(6)) && (EndAddr1.lshr(6) == StartAddr1.lshr(6)) && (EndAddr2.lshr(6) == StartAddr2.lshr(6)))
        return true;
    else
        return false;
}

static bool isNextLine(APInt StartAddr1, APInt EndAddr1, APInt StartAddr2, APInt EndAddr2)
{
    if ((StartAddr1.ule(StartAddr2) && ((EndAddr2 - StartAddr1).ult(64))) || (StartAddr2.ule(StartAddr1) && ((EndAddr1 - StartAddr2).ult(64))))
        return true;
    else
        return false;
}

static bool isOneLineApart(APInt StartAddr1, APInt EndAddr1, APInt StartAddr2, APInt EndAddr2)
{
    if ((StartAddr1.ult(StartAddr2) && ((StartAddr1.lshr(6)) + 2) == ((EndAddr2.slt(6)))) || (StartAddr2.ult(StartAddr1) && ((EndAddr1.ult(6))) == ((StartAddr2.ult(6)) +2 )))
        return true;
    else
        return false;
}

static bool isCacheCrosser(APInt StartAddr, APInt EndAddr)
{
    if ((StartAddr.lshr(6)) != (EndAddr.lshr(6)))
    {
        return true;
    }
    else
    {
        return false;
    }
}

static bool isTrueContiguous(APInt StartAddr1, APInt EndAddr1, APInt StartAddr2, APInt EndAddr2)
{
    if (((EndAddr1 + 1) == StartAddr2) || ((EndAddr2 + 1) == StartAddr1))
        return true;
    else
        return false;
}

// PreservedAnalyses HelloWorldPass::run(Function &F,
//                                       FunctionAnalysisManager &AM) {
//   errs() << F.getName() << "\n";
//   return PreservedAnalyses::all();
PreservedAnalyses ReorderPass::run(Function &F, FunctionAnalysisManager &AM) {

  AliasAnalysis &AA = AM.getResult<AAManager>(F);
  auto &DA = AM.getResult<DependenceAnalysis>(F);
  auto &DL = F.getParent()->getDataLayout();
  auto &SE = AM.getResult<ScalarEvolutionAnalysis>(F);
  std::vector<Instruction *> defChain;
  SetVector <Instruction *> Int_ins;
  SetVector <Instruction *> call_ins;
  SetVector <Instruction *> Int_dep;
  SetVector <Instruction *> useChain;
  SetVector <Instruction *> prev_load_usechain;
  SetVector <Instruction *> noDepChain;
  Instruction *int_mem_op = nullptr;
  Instruction *currentInst = nullptr;
  LoadInst *prevLoadInst = nullptr;
  std::queue<Instruction *> worklist;
  std::queue<Instruction *> worklist_prev;
  int distance = 0;
    // Transfer elements from set to vector
    //std::vector<Instruction *> tempVector(useChain.begin(), useChain.end());
  int Val;
  Instruction *startInst;
  int wasted = 0;
  int reorder = 0;
  bool UseChain_contains_prevLoad = false;
  bool UseChain_contains_currLoad = false;
  bool Aliases_with_prevLoad = false;
  bool Aliases_with_currLoad = false;
  bool successfully_reordered = false;
  bool contains_call_instruction = false;
  bool store_detected_call = false;
  bool call_inbetween = false; //comment
      for (auto &BB : F) {
        LoadInst *prevLoadInst = nullptr;
        call_inbetween = false; //comment
        errs() << "next BB " << "\n";
            BasicBlock::iterator it_bb = BB.begin();
            // BasicBlock::iterator end = BB.end();
            for(it_bb = BB.begin(); it_bb != BB.end();){
              Instruction &I = *it_bb;
              ++it_bb;
              if(it_bb == BB.end() && prevLoadInst != nullptr){
                errs() << "End of BB" << "\n";
                it_bb = prevLoadInst->getIterator();
                ++it_bb;
                prevLoadInst = nullptr;
                continue;
              }
              if (isa<LoadInst>(&I)) {
                if (I.getType()->isVectorTy()) {
                    continue;
                }
              }
              if(!EnableAcrossCallReordering && prevLoadInst != nullptr)
              {
                if(isa<CallInst>(&I)){
                  errs() << "Across call reordering disabled" << "\n";
                  call_inbetween = true; //comment
                  it_bb = prevLoadInst->getIterator();
                  ++it_bb;
                  prevLoadInst = nullptr;
                  distance = 0;
                  continue;
                }
              } 
            // else{
            //   errs() << "Across call reordering enabled" << "\n";
            // }
        //for (auto &I : BB) {
          if (LoadInst *loadInst = dyn_cast<LoadInst>(&I)) {
            successfully_reordered = false;
            // Print the def chain leading to the nextLoadInst
            errs() << "Entering 1 currload" << *loadInst << "\n";
            if (prevLoadInst) {
              // successfully_reordered = false;
              errs() << "Entering 2 Prevload:" << *prevLoadInst << "\n";
              currentInst = loadInst;
              startInst = prevLoadInst;
              Value *curLoadPtr = loadInst->getPointerOperand();
              Value *prevLoadPtr = prevLoadInst->getPointerOperand();
              Type *ElemTyA = getLoadStoreType(loadInst);
              // Value *scurLoadPtr = loadInst->getPointerOperand();
              // Value *sprevLoadPtr = prevLoadInst->getPointerOperand();
              // BasePointer_curLoadPtr = dyn_cast<SCEVUnknown>(curLoadPtr);
              // BasePointer_prevLoadPtr = dyn_cast<SCEVUnknown>(prevLoadPtr);
              errs() << "Instructions ptr :" << *curLoadPtr << " cur load base :" << *prevLoadPtr << "\n";
              unsigned ASA = curLoadPtr->getType()->getPointerAddressSpace();
              unsigned ASB = prevLoadPtr->getType()->getPointerAddressSpace();
              // errs() << "Instructions ptr pointer :" << *BasePointer_curLoadPtr << " cur load base pointer :" << *BasePointer_prevLoadPtr << "\n";
              APInt curloadOffset(DL.getIndexTypeSizeInBits(curLoadPtr->getType()), 0);
              APInt prevloadOffset(DL.getIndexTypeSizeInBits(prevLoadPtr->getType()), 0);
              Value *curLoadPtr_1 = curLoadPtr->stripAndAccumulateConstantOffsets(DL, curloadOffset, /* AllowNonInbounds */ true);
              Value *prevLoadPtr_1 = prevLoadPtr->stripAndAccumulateConstantOffsets(DL, prevloadOffset, /* AllowNonInbounds */ true);
              errs() << "Instructions ptr 1:" << *curLoadPtr_1 << " cur load base :" << *prevLoadPtr_1 << "\n";
              if (curLoadPtr_1 == prevLoadPtr_1) {
                // Retrieve the address space again as pointer stripping now tracks through
                // `addrspacecast`.
                ASA = cast<PointerType>(prevLoadPtr_1->getType())->getAddressSpace();
                ASB = cast<PointerType>(curLoadPtr_1->getType())->getAddressSpace();
                // Check that the address spaces match and that the pointers are valid.
                if (ASA != ASB)
                  errs() << "Instructions no common base:" << *curLoadPtr_1 << " cur load base :" << *prevLoadPtr_1 << "\n";

                unsigned IdxWidth = DL.getIndexSizeInBits(ASA);
                curloadOffset = curloadOffset.sextOrTrunc(IdxWidth);
                prevloadOffset = prevloadOffset.sextOrTrunc(IdxWidth);

                curloadOffset -= prevloadOffset;
                Val = curloadOffset.getSExtValue();
                errs() << "Instructions val:" << Val << "\n";
              } else {
                // Otherwise compute the distance with SCEV between the base pointers.
                const SCEV *PtrSCEVA = SE.getSCEV(curLoadPtr);
                const SCEV *PtrSCEVB = SE.getSCEV(prevLoadPtr);
                const auto *Diff = dyn_cast<SCEVConstant>(SE.getMinusSCEV(PtrSCEVB, PtrSCEVA));
                if (!Diff){
                  errs() << "Instructions scev no common base:" << *curLoadPtr_1 << " cur load base :" << *prevLoadPtr_1 << "\n";
                  // Val = Diff->getAPInt().getSExtValue(); 
                  continue;
                }else{
                  Val = Diff->getAPInt().getSExtValue();
                  errs() << "Instructions scev val:" << Val << "\n";
                }
              }
              int Size = DL.getTypeStoreSize(ElemTyA);
              int Dist = Val / Size;
              errs() << "Instructions val:" << Val << "\n";
              errs() << "Instructions Dist:" << Dist << "\n";
              MemoryLocation LocCurLoad = MemoryLocation::get(loadInst);
              MemoryLocation LocprevLoad = MemoryLocation::get(prevLoadInst);
              // errs() << "Instructions loc :" << LocCurLoad << " prev load loc :" << LocprevLoad << "\n";
              // if(AA.alias(LocCurLoad, LocprevLoad) != AliasResult:: NoAlias){
              if(!((Val >= -64 && Val < 0) || (Val >= 0 && Val < 64))){
                errs() << "Instructions Alias curLoad: " << *loadInst << " prev load :" << *prevLoadInst << "\n";
                currentInst = nullptr;
                loadInst = nullptr;
                it_bb++;
                continue;
              }
              errs() << "Instructions no Alias curLoad: " << *loadInst << " prev load :" << *prevLoadInst << "\n";
              // if (curLoadPtr != prevLoadPtr){
              //   loadInst = nullptr;
              //   currentInst = nullptr;
              //   errs() << "Instructions doesn't have same base, prev load base: " << curLoadPtr << " cur load base :" << prevLoadPtr << "\n";
              //   continue;
              // }
              // errs() << "Instructions have same base, prev load base: " << curLoadPtr << " cur load base :" << prevLoadPtr << "\n";

              // auto CurLoadAccessSize = LocationSize::precise(DL.getTypeStoreSize(curLoadPtr->getType()));
              // auto PrevLoadAccessSize = LocationSize::precise(DL.getTypeStoreSize(prevLoadPtr->getType()));
              
              // APInt offsetdiff = (curloadOffset + CurLoadAccessSize.toRaw()) - (prevloadOffset + PrevLoadAccessSize.toRaw());
              // APInt curloadStartaddress = curloadOffset;
              // APInt prevloadStartaddress = prevloadOffset;
              // APInt curloadEndaddress = curloadOffset + CurLoadAccessSize.toRaw();
              // APInt prevloadEndaddress = prevloadOffset + PrevLoadAccessSize.toRaw();
              // if(isContiguous(curloadStartaddress, CurLoadAccessSize.toRaw(), prevloadStartaddress, PrevLoadAccessSize.toRaw()) || isSameLine(curloadStartaddress, curloadEndaddress, prevloadStartaddress, prevloadEndaddress) || isNextLine(curloadStartaddress, curloadEndaddress, prevloadStartaddress, prevloadEndaddress) || isOneLineApart(curloadStartaddress, curloadEndaddress, prevloadStartaddress, prevloadEndaddress)){
              //   errs() << "yay! diff:" << offsetdiff << "\n";
              // }else{
              //   currentInst = nullptr;
              //   loadInst = nullptr;
              //   errs() << "Looking for next load to fuse this: " << *prevLoadInst << "Cur load" << *loadInst << "\n";
              //   continue;
              // }
              // auto curloadAccessSize = LocationSize::precise(DL.getTypeStoreSize(StoreTy));
              // ConstantRange LoadRange(LoadOffset, LoadOffset + LoadAccessSize.toRaw());
              // ConstantRange StoreRange(StoreOffset, StoreOffset + StoreAccessSize.toRaw());  
              errs() << "Def Chain leading to: " << *loadInst << "\n";
              errs() << "Prev load Inst: " << *prevLoadInst << "\n";
                while (currentInst && currentInst != startInst) {
                    defChain.push_back(currentInst);
                    Int_ins.insert(currentInst);
                    currentInst = currentInst->getPrevNode();
                }

                if (currentInst == startInst) {
                    defChain.push_back(currentInst);
                    Int_ins.insert(currentInst);

                    //Print the def chain in reverse order
                    for (auto it = defChain.rbegin(); it != defChain.rend(); ++it){
                      errs() << "Instructions in between" << *(*it) << "\n";
                      distance++;
                      if(dyn_cast<CallInst>(*it)){
                        errs() << "Call Inbetween" << "\n";
                        //break;
                        for (auto iy = call_ins.begin(); iy != call_ins.end(); ++iy){
                          errs() << "Instructions in call" << *(*iy) << "\n";
                          distance++;
                          if(StoreInst *store_in_call = dyn_cast<StoreInst>(*iy)){
                            errs() << "Store in call" << *store_in_call << "\n";
                            store_detected_call = true;
                            break; //Alias analysis doesn't work for interprocedural analysis
                            if((AA.alias(loadInst, store_in_call) == AliasResult:: MustAlias)){
                              errs() << "Load and Store in call Aliases: " << "True" << "\n";
                              //break;
                            }
                          }
                        }
                        if(store_detected_call){
                          distance = 0;
                          store_detected_call = false;
                          break;
                        }
                      }
                    }
                    errs() << "Distance" << (distance -2) << "\n";
                    if(store_detected_call){
                      distance = 0;
                      store_detected_call = false;
                      currentInst = nullptr;
                      loadInst = nullptr;
                      it_bb = prevLoadInst->getIterator();
                      ++it_bb;
                      prevLoadInst = nullptr;
                      distance = 0;
                      defChain.clear();
                      Int_ins.clear();
                      continue;
                    }
                    if((distance -2) > ReorderDistance){
                      currentInst = nullptr;
                      loadInst = nullptr;
                      it_bb = prevLoadInst->getIterator();
                      ++it_bb;
                      prevLoadInst = nullptr;
                      distance = 0;
                      defChain.clear();
                      Int_ins.clear();
                      continue;
                    }
                  
                    for (auto it = Int_ins.rbegin(); it != Int_ins.rend(); ++it){
                      //errs() << "Instructions in between" << *(*it) << "\n";
                      if (isa<StoreInst>(*it)){//&& (DA.depends(*it, startInst, true))){ 
                        int_mem_op =  dyn_cast<StoreInst>(*it);
                        errs() << "Int mem op: " << *int_mem_op << "\n";
                        if(!EnableSpeculativeReordering){
                          errs() << "Non Speculative reordering" << "\n";
                          if ((AA.alias(loadInst->getPointerOperand(), dyn_cast<StoreInst>(*it)->getPointerOperand()) == AliasResult::MayAlias ||
                              AA.alias(loadInst->getPointerOperand(), dyn_cast<StoreInst>(*it)->getPointerOperand()) == AliasResult::MustAlias) &&
                              (AA.alias(prevLoadInst->getPointerOperand(), dyn_cast<StoreInst>(*it)->getPointerOperand()) == AliasResult::MayAlias ||
                              AA.alias(prevLoadInst->getPointerOperand(), dyn_cast<StoreInst>(*it)->getPointerOperand()) == AliasResult::MustAlias)) {
                              Int_ins.clear();
                              wasted++;
                              Aliases_with_currLoad = true;
                              Aliases_with_prevLoad = true;
                              errs() << "Catalyst Store Aliases with prevload: " << "True" << "\n";
                              errs() << "Catalyst Store Aliases with load: " << "True" << "\n";
                              distance = 0;
                              it_bb = prevLoadInst->getIterator();
                              ++it_bb;
                              prevLoadInst = nullptr;
                              currentInst = nullptr;
                              loadInst = nullptr;
                              break;
                          } else if ((AA.alias(loadInst->getPointerOperand(), dyn_cast<StoreInst>(*it)->getPointerOperand()) == AliasResult::MayAlias ||
                                      AA.alias(loadInst->getPointerOperand(), dyn_cast<StoreInst>(*it)->getPointerOperand()) == AliasResult::MustAlias) &&
                                    (AA.alias(prevLoadInst->getPointerOperand(), dyn_cast<StoreInst>(*it)->getPointerOperand()) != AliasResult::MayAlias &&
                                      AA.alias(prevLoadInst->getPointerOperand(), dyn_cast<StoreInst>(*it)->getPointerOperand()) != AliasResult::MustAlias)) {
                              Aliases_with_currLoad = true;
                              Aliases_with_prevLoad = false;
                              errs() << "Catalyst Store Aliases with prevload: " << "False" << "\n";
                              errs() << "Catalyst Store Aliases with load: " << "True" << "\n";
                              distance = 0;
                              it_bb = prevLoadInst->getIterator();
                              ++it_bb;
                              prevLoadInst = nullptr;
                              currentInst = nullptr;
                              loadInst = nullptr;
                              break;
                          } else if ((AA.alias(loadInst->getPointerOperand(), dyn_cast<StoreInst>(*it)->getPointerOperand()) != AliasResult::MayAlias &&
                                      AA.alias(loadInst->getPointerOperand(), dyn_cast<StoreInst>(*it)->getPointerOperand()) != AliasResult::MustAlias) &&
                                    (AA.alias(prevLoadInst->getPointerOperand(), dyn_cast<StoreInst>(*it)->getPointerOperand()) == AliasResult::MayAlias ||
                                      AA.alias(prevLoadInst->getPointerOperand(), dyn_cast<StoreInst>(*it)->getPointerOperand()) == AliasResult::MustAlias)) {
                              Aliases_with_currLoad = false;
                              Aliases_with_prevLoad = true;
                              errs() << "Catalyst Store Aliases with prevload: " << "True" << "\n";
                              errs() << "Catalyst Store Aliases with load: " << "False" << "\n";
                          } else if ((AA.alias(loadInst->getPointerOperand(), dyn_cast<StoreInst>(*it)->getPointerOperand()) != AliasResult::MayAlias &&
                                      AA.alias(loadInst->getPointerOperand(), dyn_cast<StoreInst>(*it)->getPointerOperand()) != AliasResult::MustAlias) &&
                                    (AA.alias(prevLoadInst->getPointerOperand(), dyn_cast<StoreInst>(*it)->getPointerOperand()) != AliasResult::MayAlias &&
                                      AA.alias(prevLoadInst->getPointerOperand(), dyn_cast<StoreInst>(*it)->getPointerOperand()) != AliasResult::MustAlias)) {
                              Aliases_with_currLoad = false;
                              Aliases_with_prevLoad = false;
                              errs() << "Catalyst Store Aliases with prevload: " << "False" << "\n";
                              errs() << "Catalyst Store Aliases with load: " << "False" << "\n";
                          } 
                          if((AA.alias(loadInst->getPointerOperand(), dyn_cast<StoreInst>(*it)->getPointerOperand()) == AliasResult:: MayAlias)){
                            errs() << "Catalyst Store Aliases with load: " << "May Alias" << "\n";
                          }

                          if((AA.alias(prevLoadInst->getPointerOperand(), dyn_cast<StoreInst>(*it)->getPointerOperand()) == AliasResult:: MayAlias)){
                            errs() << "Catalyst Store Aliases with prevload: " << "May Alias" << "\n";
                          }
                        } else {
                          errs() << "Speculative reordering" << "\n";
                            if ((AA.alias(loadInst->getPointerOperand(), dyn_cast<StoreInst>(*it)->getPointerOperand()) == AliasResult::MustAlias) &&
                              (AA.alias(prevLoadInst->getPointerOperand(), dyn_cast<StoreInst>(*it)->getPointerOperand()) == AliasResult::MustAlias)) {
                              Int_ins.clear();
                              wasted++;
                              Aliases_with_currLoad = true;
                              Aliases_with_prevLoad = true;
                              errs() << "Catalyst Store Aliases with prevload: " << "True" << "\n";
                              errs() << "Catalyst Store Aliases with load: " << "True" << "\n";
                              distance = 0;
                              it_bb = prevLoadInst->getIterator();
                              ++it_bb;
                              prevLoadInst = nullptr;
                              currentInst = nullptr;
                              loadInst = nullptr;
                              break;
                          } else if ((AA.alias(loadInst->getPointerOperand(), dyn_cast<StoreInst>(*it)->getPointerOperand()) == AliasResult::MustAlias) &&
                                    (AA.alias(prevLoadInst->getPointerOperand(), dyn_cast<StoreInst>(*it)->getPointerOperand()) != AliasResult::MustAlias)) {
                              Aliases_with_currLoad = true;
                              Aliases_with_prevLoad = false;
                              errs() << "Catalyst Store Aliases with prevload: " << "False" << "\n";
                              errs() << "Catalyst Store Aliases with load: " << "True" << "\n";
                              distance = 0;
                              it_bb = prevLoadInst->getIterator();
                              ++it_bb;
                              prevLoadInst = nullptr;
                              currentInst = nullptr;
                              loadInst = nullptr;
                              break;
                          } else if ((AA.alias(loadInst->getPointerOperand(), dyn_cast<StoreInst>(*it)->getPointerOperand()) != AliasResult::MustAlias) &&
                                    (AA.alias(prevLoadInst->getPointerOperand(), dyn_cast<StoreInst>(*it)->getPointerOperand()) == AliasResult::MustAlias)) {
                              Aliases_with_currLoad = false;
                              Aliases_with_prevLoad = true;
                              errs() << "Catalyst Store Aliases with prevload: " << "True" << "\n";
                              errs() << "Catalyst Store Aliases with load: " << "False" << "\n";
                          } else if ((
                                      AA.alias(loadInst->getPointerOperand(), dyn_cast<StoreInst>(*it)->getPointerOperand()) != AliasResult::MustAlias) &&
                                    (AA.alias(prevLoadInst->getPointerOperand(), dyn_cast<StoreInst>(*it)->getPointerOperand()) != AliasResult::MustAlias)) {
                              Aliases_with_currLoad = false;
                              Aliases_with_prevLoad = false;
                              errs() << "Catalyst Store Aliases with prevload: " << "False" << "\n";
                              errs() << "Catalyst Store Aliases with load: " << "False" << "\n";
                          } 
                          if((AA.alias(loadInst->getPointerOperand(), dyn_cast<StoreInst>(*it)->getPointerOperand()) == AliasResult:: MayAlias)){
                            errs() << "Catalyst Store Aliases with load: " << "May Alias" << "\n";
                          }

                          if((AA.alias(prevLoadInst->getPointerOperand(), dyn_cast<StoreInst>(*it)->getPointerOperand()) == AliasResult:: MayAlias)){
                            errs() << "Catalyst Store Aliases with prevload: " << "May Alias" << "\n";
                          }
                        }
                      } else if(Instruction *LI = dyn_cast<LoadInst>(*it)){
                        // for (Use &U : LI->operands()) {
                        //   Value *v = U.get();
                        //   //Value *def = LI->getPointerOperand();
                        //   if(Instruction *LI2 = dyn_cast<Instruction>(v) ){
                        //     errs() << "Def: " << *LI2 << "\n";
                        //     if(!Int_ins.contains(LI2) && LI == loadInst){
                        //       loadInst->moveAfter(prevLoadInst);
                        //       reorder++;
                        //       //collectUseChain(loadInst, useChain);
                        //       errs() << "Use Chain for: " << *loadInst << "\n";
                        //       for (Instruction *inst : useChain) {
                        //         errs() << *inst << "\n";
                        //       }
                        //       errs() << "Def doesn't contain: " << *LI2 << "\n";
                        //     }
                        //   }
                        // }
                        if(LI == loadInst){
                          worklist.push(LI);
                          worklist_prev.push(prevLoadInst);
                          while (!worklist.empty()) { 
                            Instruction *inst = worklist.front();
                            Instruction *prev_ins_users = prevLoadInst;
                            worklist.pop();
                            // Add the instruction to the use chain set
                            // useChain.insert(inst);
                            if(useChain.contains(inst))
                            {
                              useChain.remove(inst);
                              useChain.insert(inst);
                            }else{
                              useChain.insert(inst);                                
                            }
                            //errs() << "Int pop: " << *inst << "\n";
                            //errs() << "Int pop: " << inst << "\n";
                            if (inst == prevLoadInst) {
                              // Stop collecting the use chain at prevLoadInst
                              //UseChain_contains_prevLoad = true;
                              continue;
                            }
                            // Iterate over the operands of the instruction
                            for (Use &operand : inst->operands()) {
                              for (Use &U : operand->uses()) {
                                //User *v = U.getUser();
                                Value *v = U.get();
                              if (Instruction *LI2 = dyn_cast<Instruction>(v)) {
                                //errs() << "X" << "\n";
                                //errs() << "Int use: " << *LI2 << "\n";
                                if (Int_ins.contains(LI2) && LI == loadInst) {
                                  //errs() << "Y" << "\n";
                                  //errs() << "Int check: " << *LI2 << "\n";
                                  //loadInst->moveAfter(prevLoadInst);
                                  // Add the operand instruction to the worklist
                                  worklist.push(LI2);
                                  if(useChain.contains(prevLoadInst)){ //Int_ins.contains(LI2) && inst == prevLoadInst
                                    UseChain_contains_prevLoad = true;
                                  }
                                } else if(!Int_ins.contains(LI2) && LI == loadInst){
                                  //std::queue<Instruction *>().swap(worklist);
                                  continue;
                                }
                              }
                            }
                            }
                          }

                          while (!worklist_prev.empty()) {
                            Instruction *inst = worklist_prev.front();
                            Instruction *prev_ins_users = prevLoadInst;
                            worklist_prev.pop();

                            // Add the instruction to the use chain set
                            prev_load_usechain.insert(inst);
                            //errs() << "Int pop: " << *inst << "\n";
                            //errs() << "Int pop: " << inst << "\n";
                            if (inst == loadInst) {
                              // Stop collecting the use chain at prevLoadInst
                              //UseChain_contains_prevLoad = true;
                              continue;
                            }
                            
                            for (User *U : inst->users()) {
                              if (Instruction *useInst = dyn_cast<Instruction>(U)) {
                                errs() << "Prev use: " << *useInst << "\n";
                                if (Int_ins.contains(useInst) && LI == loadInst) {
                                  worklist_prev.push(useInst);
                                  if(prev_load_usechain.contains(loadInst)){ //Int_ins.contains(LI2) && inst == prevLoadInst
                                          UseChain_contains_currLoad = true;
                                  }
                                }
                              //   }
                              // }
                                // for (Use &operand : inst->operands()) {
                                //   for (Use &U : operand->uses()) {
                                //     Value *v = U.get();
                                //     if (Instruction *LI2 = dyn_cast<Instruction>(v)) {
                                //     //errs() << "X" << "\n";
                                //     //errs() << "Int use: " << *LI2 << "\n";
                                //       if (Int_ins.contains(LI2) && LI == loadInst) {
                                //         //errs() << "Y" << "\n";
                                //         //errs() << "Int check: " << *LI2 << "\n";
                                //         //loadInst->moveAfter(prevLoadInst);
                                //         // reorder++;
                                //         // Add the operand instruction to the worklist
                                //         worklist_prev.push(LI2);
                                //         if(prev_load_usechain.contains(loadInst)){ //Int_ins.contains(LI2) && inst == prevLoadInst
                                //           UseChain_contains_currLoad = true;
                                //         }
                                //       }
                                //     }
                                //   }
                                // }
                              }
                            }
                          }

                          for (Instruction *I :Int_ins){
                            if(!prev_load_usechain.contains(I) && !useChain.contains(I)){
                              noDepChain.insert(I);
                              errs() << "No Dep: " << *I << "\n";
                            }
                          }

                          // Transfer elements from set to vector
                          // std::vector<Instruction *> tempVector(useChain.begin(), useChain.end());
                          // for (Instruction *inst : tempVector) {
                          //   errs() << "tempVector: " << *inst  << "\n";
                          // }
                          // // Sort the vector
                          // std::sort(tempVector.begin(), tempVector.end(), [](Instruction *inst1, Instruction *inst2) {
                          //   // Sort instructions based on their order in the LLVM IR
                          //   errs() << *inst1 << "comesBefore" << *inst2 << "\n";
                          //   return inst1->comesBefore(inst2);
                          // });
                          // useChain.clear();
                          // //useChain.insert(std::make_move_iterator(tempVector.begin()), std::make_move_iterator(tempVector.end()));
                          // for (Instruction *inst : tempVector) {
                          //   useChain.insert(inst);
                          // }
                          if(useChain.contains(prevLoadInst)){ //Int_ins.contains(LI2) && inst == prevLoadInst
                            UseChain_contains_prevLoad = true;
                          }

                          if(prev_load_usechain.contains(loadInst)){
                            UseChain_contains_currLoad = true;
                          }
                          
                          if(UseChain_contains_prevLoad){
                            errs() << "PrevLoad in the UseChain: " << "True" << "\n";
                          }else{
                            errs() << "PrevLoad in the UseChain: " << "False" << "\n";
                          }

                          if(UseChain_contains_currLoad){
                            errs() << "curLoad in the Prev Load UseChain: " << "True" << "\n";
                          }else{
                            errs() << "curLoad in the Prev Load UseChain: " << "False" << "\n";
                          }

                          if(LI == loadInst){
                            errs() << "Use Chain for: " << *loadInst << "\n";
                            for (auto it = useChain.rbegin(); it != useChain.rend(); ++it) {//for (Instruction *inst : useChain) {
                              Instruction *inst = *it;
                              errs() << "Inst in Use Chain" << *inst << "\n";
                            }
                            
                            if(UseChain_contains_prevLoad){
                              for (Instruction *inst : useChain) {//for (auto it = useChain.rbegin(); it != useChain.rend(); ++it) {
                                //Instruction *inst = *it;
                              // Process each instruction in reverse order
                                if(inst != prevLoadInst && UseChain_contains_prevLoad){
                                  errs() << "Ins move after prevLoad" << *inst << "\n";
                                  //inst->moveAfter(prevLoadInst); //TODO
                                }
                              }
                            }else{
                              for (auto it = useChain.rbegin(); it != useChain.rend(); ++it) {
                                Instruction *inst = *it;
                              //for (Instruction *inst : useChain) {
                                if(inst != prevLoadInst && inst == loadInst && !UseChain_contains_prevLoad){
                                  successfully_reordered = true;
                                  reorder++;
                                  inst->moveAfter(prevLoadInst);
                                  errs() << "Ins move after prevLoad" << *inst << "\n";
                                } else if(inst != prevLoadInst && inst != loadInst && !UseChain_contains_prevLoad && !Aliases_with_currLoad){
                                  inst->moveBefore(prevLoadInst);
                                  errs() << "Ins move before prevLoad" << *inst << "\n";
                                }  
                              }
                            } 
                          }

                          if(LI == loadInst){
                            errs() << "User Chain for: " << *prevLoadInst << "\n";
                            for (auto it = prev_load_usechain.rbegin(); it != prev_load_usechain.rend(); ++it) {//for (Instruction *inst : useChain) {
                              Instruction *inst = *it;
                              errs() << "Inst in Pre Load Use Chain" << *inst << "\n";
                            }
                          }
                        }

                      }else if(Instruction *I = dyn_cast<Instruction>(*it)){
                          for (Use &U : I->operands()) {
                            Value *v = U.get();
                            //Value *def = LI->getPointerOperand();
                            if(Instruction *I2 = dyn_cast<Instruction>(v)){
                              //errs() << "Def: " << *I2 << "\n";
                            } 
                          }
                        }
                    }
                }
              if(successfully_reordered){
                it_bb = ++loadInst->getIterator();
                prevLoadInst = nullptr;
                call_inbetween = false; //comment
                successfully_reordered = false;
                currentInst = nullptr;
                loadInst = nullptr;
                distance = 0;
              }else {
                currentInst = nullptr;
                loadInst = nullptr;
                it_bb++;
              }
              if(UseChain_contains_prevLoad){
                distance = 0;
              }
              errs() << "\n";
              defChain.clear();
              Int_ins.clear();
              Int_dep.clear();
              useChain.clear();
              call_inbetween = false; //comment
              prev_load_usechain.clear();
              noDepChain.clear();
              UseChain_contains_prevLoad = false;
              Aliases_with_prevLoad = false;
              Aliases_with_currLoad = false;
              std::queue<Instruction *>().swap(worklist);
            }
            // if(successfully_reordered){
            //     prevLoadInst = nullptr;
            //     currentInst = nullptr;
            //     loadInst = nullptr;
            //     call_inbetween = false; //comment
            //     distance = 0;
            //   }else{
            //     currentInst = nullptr;
            //     loadInst = nullptr;
            //     it_bb++;
            //   }
              if(!prevLoadInst){
                prevLoadInst = loadInst;
              }
          }
          else if(CallInst *callinst = dyn_cast<CallInst>(&I)){
            if(!loadInst && prevLoadInst){
              errs() << "Call Inst:" << I << "\n";
              contains_call_instruction = true;
              Function *parentFunc = callinst->getFunction();
              if (CallInst *callInst = dyn_cast<CallInst>(&I)) {
                // Analyze instructions within the called function
                Function *calledFunc = callInst->getCalledFunction();
                if (calledFunc && !calledFunc->isDeclaration()) {
                    // Look for potential aliasing stores in the called function
                    for (BasicBlock &calledBB : *calledFunc) {
                        for (Instruction &calledI : calledBB) {
                          call_ins.insert(&calledI);
                        }
                      }
                }
              }
            }
          }
        }
      }
      errs() << "Number of Reorders: " << reorder << "\n";
      errs() << "Number of wasted: " << wasted << "\n";
    return PreservedAnalyses::all();
 }

