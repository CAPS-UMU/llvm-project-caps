//===-- ReorderMLIRCombine.cpp - Example Transformations --------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//


#include "llvm/Transforms/Utils/ReorderSpeculative.h"
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
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/IRBuilder.h"
#include <queue>
 using namespace llvm;

 static cl::opt<bool> EnableSpeculativeReordering_spec(
  "enable-spec-reordering-mlir-llvm", cl::init(false), cl::Hidden,
  cl::desc("Enable Speculative Reordering."));

  static cl::opt<bool> EnableAACallReordering_spec(
    "enable-aa-call-mlir-llvm", cl::init(false), cl::Hidden,
    cl::desc("Enable AA Call Reordering."));

  static cl::opt<bool> EnableAcrossCallReordering_spec(
    "enable-across-call-reordering-mlir-llvm", cl::init(false), cl::Hidden,
    cl::desc("Enable Reordering across calls."));

  static cl::opt<int> ReorderDistance_spec(
    "reorder-distance-mlir-llvm", cl::init(10000000000), cl::Hidden,
    cl::desc("Reorder distance."));

//  static bool isContiguous(APInt addr1, uint64_t size1, APInt addr2, uint64_t size2)
// {
//     // size1 = size1 / 8;
//     // size2 = size2 / 8;
//     // assert(size1.uge(1) && size1.ule(8) );
//     // assert(size2.uge(1) && size2.ule(8));
//     size1 = size1 / 8;
//     size2 = size2 / 8;
//     assert(size1 >= 1 && size1 <= 8);
//     assert(size2 >= 1 && size2 <= 8);
//     if (addr1 == addr2)
//         return true;
//     if (addr1.ult(addr2))
//     {
//         return (addr2 - addr1).ule(size1);
//     }
//     if (addr1.ugt(addr2))
//     {
//         return (addr1 - addr2).ule(size1);
//     }
//     return false;
// }

// static bool isSameLine(APInt StartAddr1, APInt EndAddr1, APInt StartAddr2, APInt EndAddr2)
// {
//     if ((StartAddr1.lshr(6) == StartAddr2.lshr(6)) && (EndAddr1.lshr(6) == StartAddr1.lshr(6)) && (EndAddr2.lshr(6) == StartAddr2.lshr(6)))
//         return true;
//     else
//         return false;
// }

// static bool isNextLine(APInt StartAddr1, APInt EndAddr1, APInt StartAddr2, APInt EndAddr2)
// {
//     if ((StartAddr1.ule(StartAddr2) && ((EndAddr2 - StartAddr1).ult(64))) || (StartAddr2.ule(StartAddr1) && ((EndAddr1 - StartAddr2).ult(64))))
//         return true;
//     else
//         return false;
// }

// static bool isOneLineApart(APInt StartAddr1, APInt EndAddr1, APInt StartAddr2, APInt EndAddr2)
// {
//     if ((StartAddr1.ult(StartAddr2) && ((StartAddr1.lshr(6)) + 2) == ((EndAddr2.slt(6)))) || (StartAddr2.ult(StartAddr1) && ((EndAddr1.ult(6))) == ((StartAddr2.ult(6)) +2 )))
//         return true;
//     else
//         return false;
// }

// static bool isCacheCrosser(APInt StartAddr, APInt EndAddr)
// {
//     if ((StartAddr.lshr(6)) != (EndAddr.lshr(6)))
//     {
//         return true;
//     }
//     else
//     {
//         return false;
//     }
// }

// static bool isTrueContiguous(APInt StartAddr1, APInt EndAddr1, APInt StartAddr2, APInt EndAddr2)
// {
//     if (((EndAddr1 + 1) == StartAddr2) || ((EndAddr2 + 1) == StartAddr1))
//         return true;
//     else
//         return false;
// }

// PreservedAnalyses HelloWorldPass::run(Function &F,
//                                       FunctionAnalysisManager &AM) {
//   errs() << F.getName() << "\n";
//   return PreservedAnalyses::all();
PreservedAnalyses ReorderSpeculativePass::run(Function &F, FunctionAnalysisManager &AM) {

  AliasAnalysis &AA = AM.getResult<AAManager>(F);
  auto &DA = AM.getResult<DependenceAnalysis>(F);
  auto &DL = F.getParent()->getDataLayout();
  auto &SE = AM.getResult<ScalarEvolutionAnalysis>(F);
  LLVMContext &Context = F.getContext();
  errs() << "Reorder Speculative Pass" << "\n";
  std::vector<Instruction *> defChain;
  std::vector<StoreInst *> Store_queue;
  std::vector<StoreInst *> AliasingStores;
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
  bool Changed = false;
  bool Catalyst_mayalias = false;
  bool Catalyst_mustalias = false;
  bool Catalyst_noalias = false;
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
              if(!EnableAcrossCallReordering_spec && prevLoadInst != nullptr)
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
                    if((distance -2) > ReorderDistance_spec){
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

                    Store_queue.clear();
                    AliasingStores.clear();
                    Catalyst_mayalias = false;
                    Catalyst_mustalias = false;
                    Catalyst_noalias = false;
                    for(auto it_store = Int_ins.rbegin(); it_store != Int_ins.rend(); ++it_store){
                      if(dyn_cast<StoreInst>(*it_store)){
                        Store_queue.push_back(dyn_cast<StoreInst>(*it_store));
                        errs() << "Store Alias Queue: " << *(*it_store) << "\n";
                      }
                    }

                    for(auto *SI_int : Store_queue){
                      Value *SPtr = SI_int->getPointerOperand();
                      if(AA.alias(SPtr, loadInst->getPointerOperand()) == AliasResult::MustAlias){
                        errs() << "Store Must Alias with load: " << *SI_int << "\n";
                        Catalyst_mustalias = true;
                        break;
                      } else if(AA.alias(SPtr, loadInst->getPointerOperand()) == AliasResult::MayAlias){
                        errs() << "Store May Alias with load: " << *SI_int << "\n";
                        AliasingStores.push_back(dyn_cast<StoreInst>(SI_int));
                        Catalyst_mayalias = true;
                      } else if(AA.alias(SPtr, loadInst->getPointerOperand()) == AliasResult::NoAlias){
                        errs() << "Store No Alias with load: " << *SI_int << "\n";
                        Catalyst_noalias = true;
                      }
                    }
                    for (auto it = Int_ins.rbegin(); it != Int_ins.rend(); ++it){
                      //errs() << "Instructions in between" << *(*it) << "\n";
                      if (isa<StoreInst>(*it)){//&& (DA.depends(*it, startInst, true))){ 
                        int_mem_op =  dyn_cast<StoreInst>(*it);
                        errs() << "Int mem op: " << *int_mem_op << "\n";
                        if(!EnableSpeculativeReordering_spec){
                          errs() << "Non Speculative reordering" << "\n";
                          AliasResult AR = AA.alias(MemoryLocation::get(loadInst),MemoryLocation::get(cast<StoreInst>(*it)));
                          AliasResult AR2 = AA.alias(MemoryLocation::get(prevLoadInst),MemoryLocation::get(cast<StoreInst>(*it)));

                          if ((AR == AliasResult::MayAlias || AR == AliasResult::MustAlias) && (AR2 == AliasResult::MayAlias || AR2 == AliasResult::MustAlias)) {
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
                          } else if ((AR == AliasResult::MayAlias ||
                                      AR == AliasResult::MustAlias) &&
                                    (AR2 != AliasResult::MayAlias &&
                                      AR2 != AliasResult::MustAlias)) {
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
                          } else if ((AR != AliasResult::MayAlias &&
                                      AR != AliasResult::MustAlias) &&
                                    (AR2 == AliasResult::MayAlias ||
                                      AR2 == AliasResult::MustAlias)) {
                              Aliases_with_currLoad = false;
                              Aliases_with_prevLoad = true;
                              errs() << "Catalyst Store Aliases with prevload: " << "True" << "\n";
                              errs() << "Catalyst Store Aliases with load: " << "False" << "\n";
                          } else if ((AR != AliasResult::MayAlias &&
                                      AR != AliasResult::MustAlias) &&
                                    (AR2 != AliasResult::MayAlias &&
                                      AR2 != AliasResult::MustAlias)) {
                              Aliases_with_currLoad = false;
                              Aliases_with_prevLoad = false;
                              errs() << "Catalyst Store Aliases with prevload: " << "False" << "\n";
                              errs() << "Catalyst Store Aliases with load: " << "False" << "\n";
                          } 
                          if((AR == AliasResult:: MayAlias)){
                            errs() << "Catalyst Store Aliases with load: " << "May Alias" << "\n";
                          }

                          if((AR2 == AliasResult:: MayAlias)){
                            errs() << "Catalyst Store Aliases with prevload: " << "May Alias" << "\n";
                          }
                        } else {
                          errs() << "Speculative reordering" << "\n";
                          AliasResult AR = AA.alias(MemoryLocation::get(loadInst),MemoryLocation::get(cast<StoreInst>(*it)));
                          AliasResult AR2 = AA.alias(MemoryLocation::get(prevLoadInst),MemoryLocation::get(cast<StoreInst>(*it)));
                          if((AR == AliasResult:: MayAlias)){
                            errs() << "Catalyst Store Aliases with load: " << "May Alias" << "\n";
                          }
                          if((AR == AliasResult:: MustAlias)){
                            errs() << "Catalyst Store Aliases with load: " << "Must Alias" << "\n";
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
                          }
                          if((AR2 == AliasResult:: MayAlias)){
                            errs() << "Catalyst Store Aliases with prevload: " << "May Alias" << "\n";
                          }  
                      }
                    } else if(isa<LoadInst>(*it) && Catalyst_mayalias){
                      Instruction *LI = dyn_cast<LoadInst>(*it);
                      if(LI == loadInst){  
                          IRBuilder<> Builder(prevLoadInst);
                          Value *CombinedCmp = nullptr;
                          Value *L2Ptr = loadInst->getPointerOperand();
                          if(!L2Ptr->getType()->isPointerTy() || !L2Ptr) {
                            errs() << "Error: loadInst does not have a valid pointer operand: " << *loadInst << "\n";
                            continue;
                          }
                          Value *L2PtrInt = Builder.CreatePtrToInt(loadInst->getPointerOperand(), Builder.getInt64Ty());
                          for(StoreInst *SI : AliasingStores)
                          {
                            Value *StorePtr = SI->getPointerOperand();
                            if (StorePtr->getType()->isPointerTy()) {
                              continue;
                            }
                            errs() << "StorePtr type: " << *StorePtr->getType() << "\n";
                            Value *SPtrInt = Builder.CreatePtrToInt(StorePtr, Builder.getInt64Ty());
                            Value *Cmp = Builder.CreateICmpNE(L2PtrInt, SPtrInt);
                            CombinedCmp = CombinedCmp ? Builder.CreateAnd(CombinedCmp, Cmp) : Cmp;
                          }
                          BasicBlock *OrigBB = prevLoadInst->getParent();
                          Function *Fn = OrigBB->getParent();
                          BasicBlock *SpecBB = BasicBlock::Create(Context, "speculative", Fn);
                          BasicBlock *MergeBB = BasicBlock::Create(Context, "merge", Fn);

                          // Move original instructions to speculative block
                          IRBuilder<> SpecBuilder(SpecBB);
                          LoadInst *L1Spec = cast<LoadInst>(prevLoadInst->clone());
                          SpecBuilder.Insert(L1Spec);
                          ValueToValueMapTy VMap;
                          for (auto it_intermediate = Int_ins.rbegin(); it_intermediate != Int_ins.rend(); ++it_intermediate){
                            Instruction *Inst_intermediate = *it_intermediate;
                            //Inst_intermediate->removeFromParent();
                            Instruction *Cloned = Inst_intermediate->clone();
                            VMap[Inst_intermediate] = Cloned;
                            SpecBuilder.Insert(Cloned);
                          }
                          Instruction *L2Spec = loadInst->clone();
                          SpecBuilder.Insert(L2Spec);
                          SpecBuilder.CreateBr(MergeBB);

                      if(L2Spec){
                            //L1 = L1Spec;
                            worklist.push(L2Spec);
                            worklist_prev.push(L1Spec);
                            while (!worklist.empty()) { 
                              Instruction *inst = worklist.front();
                              Instruction *prev_ins_users = L1Spec;
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
                              if (inst == L1Spec) {
                                // Stop collecting the use chain at prevLoadInst
                                //UseChain_contains_prevLoad = true;
                                continue;
                              }
                              // Iterate over the operands of the instruction
                              for (Use &operand : inst->operands()) {
                                for (Use &U : operand->uses()) {
                                  Value *v = U.get();
                                if (Instruction *LI2 = dyn_cast<Instruction>(v)) {
                                  if (Int_ins.contains(LI2) && isa<LoadInst>(L2Spec)) {
                                    worklist.push(LI2);
                                    if(useChain.contains(L1Spec)){ //Int_ins.contains(LI2) && inst == prevLoadInst
                                      UseChain_contains_prevLoad = true;
                                    }
                                  } else if(!Int_ins.contains(LI2) && isa<LoadInst>(L2Spec)){
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
                                  if (Int_ins.contains(useInst) && isa<LoadInst>(L2Spec)) {
                                    worklist_prev.push(useInst);
                                    if(prev_load_usechain.contains(loadInst)){ //Int_ins.contains(LI2) && inst == prevLoadInst
                                            UseChain_contains_currLoad = true;
                                    }
                                  }
                                }
                              }
                            }

                            for (Instruction *I :Int_ins){
                              if(!prev_load_usechain.contains(I) && !useChain.contains(I)){
                                noDepChain.insert(I);
                                errs() << "No Dep: " << *I << "\n";
                              }
                            }

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

                            if(isa<LoadInst>(L2Spec)){
                              errs() << "Use Chain for: " << *loadInst << "\n";
                              for (auto it = useChain.rbegin(); it != useChain.rend(); ++it) {//for (Instruction *inst : useChain) {
                                Instruction *inst = *it;
                                errs() << "Inst in Use Chain" << *inst << "\n";
                              }
                              
                              if(UseChain_contains_prevLoad){
                                for (Instruction *inst : useChain) {//for (auto it = useChain.rbegin(); it != useChain.rend(); ++it) {
                                  //Instruction *inst = *it;
                                // Process each instruction in reverse order
                                  if(inst != L1Spec && UseChain_contains_prevLoad){
                                    errs() << "Ins move after prevLoad" << *inst << "\n";
                                    //inst->moveAfter(prevLoadInst); //TODO
                                  }
                                }
                              }else{
                                for (auto it = useChain.rbegin(); it != useChain.rend(); ++it) {
                                  Instruction *inst = *it;
                                //for (Instruction *inst : useChain) {
                                  if(inst != L1Spec && inst == L2Spec && !UseChain_contains_prevLoad){
                                    successfully_reordered = true;
                                    reorder++;
                                    inst->moveAfter(L1Spec);
                                    errs() << "Ins move after prevLoad" << *inst << "\n";
                                  } else if(inst != L1Spec && inst != L2Spec && !UseChain_contains_prevLoad && !Aliases_with_currLoad){
                                    inst->moveBefore(L1Spec);
                                    errs() << "Ins move before prevLoad" << *inst << "\n";
                                  }  
                                }
                              } 
                            }

                            if(isa<LoadInst>(LI)){
                              errs() << "User Chain for: " << *prevLoadInst << "\n";
                              for (auto it = prev_load_usechain.rbegin(); it != prev_load_usechain.rend(); ++it) {//for (Instruction *inst : useChain) {
                                Instruction *inst = *it;
                                errs() << "Inst in Pre Load Use Chain" << *inst << "\n";
                              }
                            }
                                                      // Original block gets conditional branch
                          // Builder.CreateCondBr(CombinedCmp, SpecBB, MergeBB);
                          // OrigBB->getTerminator()->eraseFromParent();
                          Instruction *OldTerm = OrigBB->getTerminator();
                          Builder.SetInsertPoint(OldTerm);
                          Builder.CreateCondBr(CombinedCmp, SpecBB, MergeBB);
                          OldTerm->eraseFromParent();
                          // Merge block and PHI
                          IRBuilder<> MergeBuilder(MergeBB);
                          PHINode *PHI = MergeBuilder.CreatePHI(loadInst->getType(), 2, "merged");
                          PHI->addIncoming(L2Spec, SpecBB);
                          PHI->addIncoming(loadInst, OrigBB);

                          // Replace Load2 uses
                          loadInst->replaceAllUsesWith(PHI);
                          loadInst->eraseFromParent();

                          Changed = true;
                      }
                     }
                    }else if(isa<LoadInst>(*it) && Catalyst_noalias) {
                      Instruction *LI = dyn_cast<LoadInst>(*it);
                      if(LI == loadInst){
                            //L1 = L1Spec;
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
                                  Value *v = U.get();
                                if (Instruction *LI2 = dyn_cast<Instruction>(v)) {
                                  if (Int_ins.contains(LI2) && isa<LoadInst>(LI)) {
                                    worklist.push(LI2);
                                    if(useChain.contains(prevLoadInst)){ //Int_ins.contains(LI2) && inst == prevLoadInst
                                      UseChain_contains_prevLoad = true;
                                    }
                                  } else if(!Int_ins.contains(LI2) && isa<LoadInst>(LI)){
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
                                  if (Int_ins.contains(useInst) && isa<LoadInst>(LI)) {
                                    worklist_prev.push(useInst);
                                    if(prev_load_usechain.contains(loadInst)){ //Int_ins.contains(LI2) && inst == prevLoadInst
                                            UseChain_contains_currLoad = true;
                                    }
                                  }
                                }
                              }
                            }

                            for (Instruction *I :Int_ins){
                              if(!prev_load_usechain.contains(I) && !useChain.contains(I)){
                                noDepChain.insert(I);
                                errs() << "No Dep: " << *I << "\n";
                              }
                            }

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

                            if(isa<LoadInst>(LI)){
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

                            if(isa<LoadInst>(LI)){
                              errs() << "User Chain for: " << *prevLoadInst << "\n";
                              for (auto it = prev_load_usechain.rbegin(); it != prev_load_usechain.rend(); ++it) {//for (Instruction *inst : useChain) {
                                Instruction *inst = *it;
                                errs() << "Inst in Pre Load Use Chain" << *inst << "\n";
                              }
                            }
                        }
                     }
                      else if(Instruction *I = dyn_cast<Instruction>(*it)){
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
                //Changed = true;
                Catalyst_mayalias = false;
                Catalyst_mustalias = false;
                Catalyst_noalias = false;
              }else {
                currentInst = nullptr;
                loadInst = nullptr;
                it_bb++;
                //Changed = false;
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
    return Changed ? PreservedAnalyses::none() : PreservedAnalyses::all();
 }

