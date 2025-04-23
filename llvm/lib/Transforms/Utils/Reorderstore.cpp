//===-- Reorderstore.cpp - Example Transformations --------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

 
#include "llvm/Transforms/Utils/Reorderstore.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/AliasAnalysisEvaluator.h"
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
#include "llvm/IR/PassManager.h"
#include "llvm/IR/CFG.h"
#include <queue>
 using namespace llvm;

 static cl::opt<bool> EnableSpeculativeReorderingStore(
  "enable-spec-reordering-store", cl::init(false), cl::Hidden,
  cl::desc("Enable Speculative Reordering."));

  static cl::opt<bool> EnableAACallReorderingStore(
    "enable-aa-call-store", cl::init(false), cl::Hidden,
    cl::desc("Enable AA Call Reordering."));

  static cl::opt<bool> EnableAcrossCallReorderingStore(
    "enable-across-call-reordering-store", cl::init(false), cl::Hidden,
    cl::desc("Enable Reordering across calls."));

  static cl::opt<int> ReorderDistanceStore(
    "reorder-distance-store", cl::init(10000000000), cl::Hidden,
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
PreservedAnalyses ReorderStorePass::run(Function &F, FunctionAnalysisManager &AM) {

  AliasAnalysis &AA = AM.getResult<AAManager>(F);
  auto &DA = AM.getResult<DependenceAnalysis>(F);
  auto &DL = F.getParent()->getDataLayout();
  auto &SE = AM.getResult<ScalarEvolutionAnalysis>(F);
  std::vector<Instruction *> defChain;
  SetVector <Instruction *> Int_ins;
  SetVector <Instruction *> call_ins;
  SetVector <Instruction *> Int_dep;
  SetVector <Instruction *> useChain;
  SetVector <Instruction *> prev_store_usechain;
  SetVector <Instruction *> noDepChain;
  Instruction *int_mem_op = nullptr;
  Instruction *currentInst = nullptr;
  StoreInst *prevStoreInst = nullptr;
  std::queue<Instruction *> worklist;
  std::queue<Instruction *> worklist_prev;
  int distance = 0;
    // Transfer elements from set to vector
    //std::vector<Instruction *> tempVector(useChain.begin(), useChain.end());
  int Val;
  Instruction *startInst;
  int wasted = 0;
  int reorder = 0;
  bool UseChain_contains_prevStore = false;
  bool UseChain_contains_currStore = false;
  bool Aliases_with_prevStore = false;
  bool Aliases_with_currStore = false;
  bool successfully_reordered = false;
  bool contains_call_instruction = false;
  bool load_detected_in_call = false;
  bool call_inbetween = false; //comment
  for (auto &BB : F) {
    StoreInst *prevStoreInst = nullptr;
    call_inbetween = false; //comment
    errs() << "next BB " << "\n";
    BasicBlock::iterator it_bb = BB.begin();
        // BasicBlock::iterator end = BB.end();
        for(it_bb = BB.begin(); it_bb != BB.end();){
          Instruction &I = *it_bb;
          ++it_bb;
          if(it_bb == BB.end() && prevStoreInst != nullptr){
            errs() << "End of BB" << "\n";
            it_bb = prevStoreInst->getIterator();
            ++it_bb;
            prevStoreInst = nullptr;
            continue;
          }
          if (isa<StoreInst>(&I)) {
            Value *storedValue = cast<StoreInst>(&I)->getValueOperand();
            Type *valType = storedValue->getType();
            if (valType->isVectorTy() || valType->isArrayTy()) {
              errs() << "Skipping vector or array store instruction: " << I << "\n";
              continue;
            }
          }
          if(!EnableAcrossCallReorderingStore && prevStoreInst != nullptr)
          {
            if(isa<CallInst>(&I)){
              errs() << "Across call reordering disabled" << "\n";
              call_inbetween = true; //comment
              it_bb = prevStoreInst->getIterator();
              ++it_bb;
              prevStoreInst = nullptr;
              distance = 0;
              continue;
            }
          } 
      //for (auto &I : BB) {
          if (StoreInst *storeInst = dyn_cast<StoreInst>(&I)) {
            successfully_reordered = false;
            // Print the def chain leading to the nextLoadInst
            if (prevStoreInst) {
              // successfully_reordered = false;
              errs() << "Entering 1 curstore" << *storeInst << "\n";
              errs() << "Entering 2 Prevstore:" << *prevStoreInst << "\n";
              currentInst = storeInst;
              startInst = prevStoreInst;
              Value *curStorePtr = storeInst->getPointerOperand();
              Value *prevStorePtr = prevStoreInst->getPointerOperand();
              Type *ElemTyA = getLoadStoreType(storeInst);
              // Value *scurLoadPtr = loadInst->getPointerOperand();
              // Value *sprevLoadPtr = prevLoadInst->getPointerOperand();
              // BasePointer_curLoadPtr = dyn_cast<SCEVUnknown>(curLoadPtr);
              // BasePointer_prevLoadPtr = dyn_cast<SCEVUnknown>(prevLoadPtr);
              errs() << "Instructions ptr :" << *curStorePtr << " cur store base :" << *prevStorePtr << "\n";
              unsigned ASA = curStorePtr->getType()->getPointerAddressSpace();
              unsigned ASB = prevStorePtr->getType()->getPointerAddressSpace();
              // errs() << "Instructions ptr pointer :" << *BasePointer_curLoadPtr << " cur load base pointer :" << *BasePointer_prevLoadPtr << "\n";
              APInt curstoreOffset(DL.getIndexTypeSizeInBits(curStorePtr->getType()), 0);
              APInt prevstoreOffset(DL.getIndexTypeSizeInBits(prevStorePtr->getType()), 0);
              const Value *curStorePtr_1 = curStorePtr->stripAndAccumulateConstantOffsets(DL, curstoreOffset, /* AllowNonInbounds */ true);
              const Value *prevStorePtr_1 = prevStoreInst->stripAndAccumulateConstantOffsets(DL, prevstoreOffset, /* AllowNonInbounds */ true);
              if (curStorePtr_1 == prevStorePtr_1) {
                // Retrieve the address space again as pointer stripping now tracks through
                // `addrspacecast`.
                ASA = cast<PointerType>(curStorePtr_1->getType())->getAddressSpace();
                ASB = cast<PointerType>(prevStorePtr_1->getType())->getAddressSpace();
                // Check that the address spaces match and that the pointers are valid.
                if (ASA != ASB)
                  errs() << "Instructions no common base:" << *curStorePtr_1 << " cur store base :" << *prevStorePtr_1 << "\n";

                unsigned IdxWidth = DL.getIndexSizeInBits(ASA);
                curstoreOffset = curstoreOffset.sextOrTrunc(IdxWidth);
                prevstoreOffset = prevstoreOffset.sextOrTrunc(IdxWidth);

                curstoreOffset -= prevstoreOffset;
                Val = curstoreOffset.getSExtValue();
                errs() << "Instructions val:" << Val << "\n";
              } else {
                // Otherwise compute the distance with SCEV between the base pointers.
                const SCEV *PtrSCEVA = SE.getSCEV(curStorePtr);
                const SCEV *PtrSCEVB = SE.getSCEV(prevStorePtr);
                const auto *Diff = dyn_cast<SCEVConstant>(SE.getMinusSCEV(PtrSCEVB, PtrSCEVA));
                if (!Diff){
                  errs() << "Instructions scev no common base:" << *curStorePtr_1 << " cur store base :" << *prevStorePtr_1 << "\n";
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
              MemoryLocation LocCurStore = MemoryLocation::get(storeInst);
              MemoryLocation LocprevStore = MemoryLocation::get(prevStoreInst);
              // errs() << "Instructions loc :" << LocCurLoad << " prev load loc :" << LocprevLoad << "\n";
              // if(AA.alias(LocCurLoad, LocprevLoad) != AliasResult:: NoAlias){
              if(!((Val >= -64 && Val < 0) || (Val >= 0 && Val < 64))){
                errs() << "Instructions Alias curStore: " << *storeInst << " prev store :" << *prevStoreInst << "\n";
                currentInst = nullptr;
                storeInst = nullptr;
                it_bb++;
                continue;
              }
              errs() << "Instructions no Alias curStore: " << *storeInst << " prev store :" << *prevStoreInst << "\n";
              errs() << "Def Chain leading to: " << *storeInst << "\n";
              errs() << "Prev store Inst: " << *prevStoreInst << "\n";
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
                          if(LoadInst *load_in_call = dyn_cast<LoadInst>(*iy)){
                            errs() << "Load in call" << *load_in_call << "\n";
                            load_detected_in_call = true;
                            break;//Alias analysis doesn't work for interprocedural analysis
                            if((AA.alias(storeInst, load_in_call) == AliasResult:: MustAlias)){
                              errs() << "Load and Store in call Aliases: " << "True" << "\n";
                              //break;
                            }
                          }
                        }
                        if(load_detected_in_call){
                          distance = 0;
                          load_detected_in_call = false;
                          break;
                        }                     
                      }
                    }
                    errs() << "Distance" << (distance -2) << "\n";
                    if(load_detected_in_call){
                      distance = 0;
                      load_detected_in_call = false;
                      currentInst = nullptr;
                      storeInst = nullptr;
                      it_bb = prevStoreInst->getIterator();
                      ++it_bb;
                      prevStoreInst = nullptr;
                      distance = 0;
                      defChain.clear();
                      Int_ins.clear();
                      continue;
                    }
                    if((distance -2) > ReorderDistanceStore){
                      currentInst = nullptr;
                      storeInst = nullptr;
                      it_bb = prevStoreInst->getIterator();
                      ++it_bb;
                      prevStoreInst = nullptr;
                      distance = 0;
                      defChain.clear();
                      Int_ins.clear();
                      continue;
                    }
                    
                    for (auto it = Int_ins.rbegin(); it != Int_ins.rend(); ++it){
                      //errs() << "Instructions in between" << *(*it) << "\n";
                      if (isa<LoadInst>(*it)){//&& (DA.depends(*it, startInst, true))){ 
                        int_mem_op =  dyn_cast<LoadInst>(*it);
                        errs() << "Int mem op: " << *int_mem_op << "\n";
                        if(!EnableSpeculativeReorderingStore){
                          errs() << "Non Speculative reordering" << "\n";
                          errs() << "Store Inst Operands: " << *storeInst->getPointerOperand() << "\n";
                          errs() << "Prev Store Inst Operands: " << *prevStoreInst->getPointerOperand() << "\n";
                          if ((AA.alias(storeInst->getPointerOperand(), dyn_cast<LoadInst>(*it)->getPointerOperand()) == AliasResult::MayAlias ||
                              AA.alias(storeInst->getPointerOperand(), dyn_cast<LoadInst>(*it)->getPointerOperand()) == AliasResult::MustAlias) &&
                              (AA.alias(prevStoreInst->getPointerOperand(), dyn_cast<LoadInst>(*it)->getPointerOperand()) == AliasResult::MayAlias ||
                              AA.alias(prevStoreInst->getPointerOperand(), dyn_cast<LoadInst>(*it)->getPointerOperand()) == AliasResult::MustAlias)) {
                              Int_ins.clear();
                              wasted++;
                              Aliases_with_currStore = true;
                              Aliases_with_prevStore = true;
                              errs() << "Catalyst Store Aliases with prevload: " << "True" << "\n";
                              errs() << "Catalyst Store Aliases with load: " << "True" << "\n";
                              distance = 0;
                              it_bb = prevStoreInst->getIterator();
                              ++it_bb;
                              prevStoreInst = nullptr;
                              currentInst = nullptr;
                              storeInst = nullptr;
                              break;
                          } else if ((AA.alias(storeInst->getPointerOperand(), dyn_cast<LoadInst>(*it)->getPointerOperand()) == AliasResult::MayAlias ||
                                      AA.alias(storeInst->getPointerOperand(), dyn_cast<LoadInst>(*it)->getPointerOperand()) == AliasResult::MustAlias) &&
                                    (AA.alias(prevStoreInst->getPointerOperand(), dyn_cast<LoadInst>(*it)->getPointerOperand()) != AliasResult::MayAlias &&
                                      AA.alias(prevStoreInst->getPointerOperand(), dyn_cast<LoadInst>(*it)->getPointerOperand()) != AliasResult::MustAlias)) {
                              Aliases_with_currStore = true;
                              Aliases_with_prevStore = false;
                              errs() << "Catalyst Store Aliases with prevload: " << "False" << "\n";
                              errs() << "Catalyst Store Aliases with load: " << "True" << "\n";
                              distance = 0;
                              it_bb = prevStoreInst->getIterator();
                              ++it_bb;
                              prevStoreInst = nullptr;
                              currentInst = nullptr;
                              storeInst = nullptr;
                              break;
                          } else if ((AA.alias(storeInst->getPointerOperand(), dyn_cast<LoadInst>(*it)->getPointerOperand()) != AliasResult::MayAlias &&
                                      AA.alias(storeInst->getPointerOperand(), dyn_cast<LoadInst>(*it)->getPointerOperand()) != AliasResult::MustAlias) &&
                                    (AA.alias(prevStoreInst->getPointerOperand(), dyn_cast<LoadInst>(*it)->getPointerOperand()) == AliasResult::MayAlias ||
                                      AA.alias(prevStoreInst->getPointerOperand(), dyn_cast<LoadInst>(*it)->getPointerOperand()) == AliasResult::MustAlias)) {
                              Aliases_with_currStore = false;
                              Aliases_with_prevStore = true;
                              errs() << "Catalyst Store Aliases with prevload: " << "True" << "\n";
                              errs() << "Catalyst Store Aliases with load: " << "False" << "\n";
                          } else if ((AA.alias(storeInst->getPointerOperand(), dyn_cast<LoadInst>(*it)->getPointerOperand()) != AliasResult::MayAlias &&
                                      AA.alias(storeInst->getPointerOperand(), dyn_cast<LoadInst>(*it)->getPointerOperand()) != AliasResult::MustAlias) &&
                                    (AA.alias(prevStoreInst->getPointerOperand(), dyn_cast<LoadInst>(*it)->getPointerOperand()) != AliasResult::MayAlias &&
                                      AA.alias(prevStoreInst->getPointerOperand(), dyn_cast<LoadInst>(*it)->getPointerOperand()) != AliasResult::MustAlias)) {
                              Aliases_with_currStore = false;
                              Aliases_with_prevStore = false;
                              errs() << "Catalyst Store Aliases with prevload: " << "False" << "\n";
                              errs() << "Catalyst Store Aliases with load: " << "False" << "\n";
                          } 
                          if((AA.alias(storeInst->getPointerOperand(), dyn_cast<LoadInst>(*it)->getPointerOperand()) == AliasResult:: MayAlias)){
                            errs() << "Catalyst Store Aliases with load: " << "May Alias" << "\n";
                          }

                          if((AA.alias(prevStoreInst->getPointerOperand(), dyn_cast<LoadInst>(*it)->getPointerOperand()) == AliasResult:: MayAlias)){
                            errs() << "Catalyst Store Aliases with prevload: " << "May Alias" << "\n";
                          }
                        } else {
                          errs() << "Speculative reordering" << "\n";
                          errs() << "Store Inst Operands: " << *storeInst->getPointerOperand() << "\n";
                          errs() << "Prev Store Inst Operands: " << *prevStoreInst->getPointerOperand() << "\n";
                        if( (AA.alias(storeInst->getPointerOperand(), dyn_cast<LoadInst>(*it)->getPointerOperand()) == AliasResult:: MustAlias) &&
                         (AA.alias(prevStoreInst->getPointerOperand(), dyn_cast<LoadInst>(*it)->getPointerOperand()) == AliasResult:: MustAlias)){
                            Int_ins.clear();
                            wasted++;
                            Aliases_with_currStore = true;
                            Aliases_with_prevStore = true;
                            errs() << "Catalyst Store Aliases with prevstore: " << "True" << "\n";
                            errs() << "Catalyst Store Aliases with store: " << "True" << "\n";
                            distance = 0;
                            it_bb = prevStoreInst->getIterator();
                            ++it_bb;
                            prevStoreInst = nullptr;
                            currentInst = nullptr;
                            storeInst = nullptr;
                            break;
                        } else if((AA.alias(storeInst->getPointerOperand(), dyn_cast<LoadInst>(*it)->getPointerOperand()) == AliasResult:: MustAlias) &&
                         (AA.alias(prevStoreInst->getPointerOperand(), dyn_cast<LoadInst>(*it)->getPointerOperand()) != AliasResult:: MustAlias)){
                          Aliases_with_currStore = true;
                          Aliases_with_prevStore = false;
                          errs() << "Catalyst Store Aliases with prevstore: " << "False" << "\n";
                          errs() << "Catalyst Store Aliases with store: " << "True" << "\n";
                          distance = 0;
                          it_bb = prevStoreInst->getIterator();
                          ++it_bb;
                          prevStoreInst = nullptr;
                          currentInst = nullptr;
                          storeInst = nullptr;
                          break;
                        } else if((AA.alias(storeInst->getPointerOperand(), dyn_cast<LoadInst>(*it)->getPointerOperand()) != AliasResult:: MustAlias) &&
                         (AA.alias(prevStoreInst->getPointerOperand(), dyn_cast<LoadInst>(*it)->getPointerOperand()) == AliasResult:: MustAlias)){
                          Aliases_with_currStore = false;
                          Aliases_with_prevStore = true;
                          errs() << "Catalyst Store Aliases with prevstore: " << "True" << "\n";
                          errs() << "Catalyst Store Aliases with store: " << "False" << "\n";
                        } else if((AA.alias(storeInst->getPointerOperand(), dyn_cast<LoadInst>(*it)->getPointerOperand()) != AliasResult:: MustAlias) &&
                         (AA.alias(prevStoreInst->getPointerOperand(), dyn_cast<LoadInst>(*it)->getPointerOperand()) != AliasResult:: MustAlias)){
                          Aliases_with_currStore = false;
                          Aliases_with_prevStore = false;
                          errs() << "Catalyst Store Aliases with prevstore: " << "False" << "\n";
                          errs() << "Catalyst Store Aliases with store: " << "False" << "\n";
                        }
                        
                        if((AA.alias(storeInst->getPointerOperand(), dyn_cast<LoadInst>(*it)->getPointerOperand()) == AliasResult:: MayAlias)){
                          errs() << "Catalyst Store Aliases with prevstore: " << "May Alias" << "\n";
                        }
                        if((AA.alias(prevStoreInst->getPointerOperand(), dyn_cast<LoadInst>(*it)->getPointerOperand()) == AliasResult:: MayAlias)){
                          errs() << "Catalyst Store Aliases with store: " << "May Alias" << "\n";
                        }
                        }

                      }else if(Instruction *LI = dyn_cast<StoreInst>(*it)){
                        if(LI == storeInst){
                          worklist.push(LI);
                          worklist_prev.push(prevStoreInst);
                          while (!worklist.empty()) { 
                            Instruction *inst = worklist.front();
                            Instruction *prev_ins_users = prevStoreInst;
                            worklist.pop();

                            // Add the instruction to the use chain set
                            if(useChain.contains(inst))
                            {
                                useChain.remove(inst);
                                useChain.insert(inst);
                            }else{
                                useChain.insert(inst);                                
                            }
                            //errs() << "Int pop: " << *inst << "\n";
                            //errs() << "Int pop: " << inst << "\n";
                            if (inst == prevStoreInst) {
                              // Stop collecting the use chain at prevStoreInst
                              //UseChain_contains_prevStore = true;
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
                                if (Int_ins.contains(LI2) && LI == storeInst) {
                                  //errs() << "Y" << "\n";
                                  //errs() << "Int check: " << *LI2 << "\n";
                                  //storeInst->moveAfter(prevStoreInst);
                                  // Add the operand instruction to the worklist
                                  worklist.push(LI2);
                                  if(useChain.contains(prevStoreInst)){ //Int_ins.contains(LI2) && inst == prevStoreInst
                                    UseChain_contains_prevStore = true;
                                  }
                                } else if(!Int_ins.contains(LI2) && LI == storeInst){
                                  //std::queue<Instruction *>().swap(worklist);
                                  continue;
                                }
                              }
                            }
                            }
                          }

                          while (!worklist_prev.empty()) {
                            Instruction *inst = worklist_prev.front();
                            Instruction *prev_ins_users = prevStoreInst;
                            worklist_prev.pop();

                            // Add the instruction to the use chain set
                            prev_store_usechain.insert(inst);
                            //errs() << "Int pop: " << *inst << "\n";
                            //errs() << "Int pop: " << inst << "\n";
                            if (inst == storeInst) {
                              // Stop collecting the use chain at prevStoreInst
                              //UseChain_contains_prevStore = true;
                              continue;
                            }
                            
                            for (User *U : inst->users()) {
                              if (Instruction *useInst = dyn_cast<Instruction>(U)) {
                                errs() << "Prev use: " << *useInst << "\n";
                                if (Int_ins.contains(useInst) && LI == storeInst) {
                                  worklist_prev.push(useInst);
                                  if(prev_store_usechain.contains(storeInst)){ //Int_ins.contains(LI2) && inst == prevStoreInst
                                          UseChain_contains_currStore = true;
                                  }
                                }
                              }
                            }
                          }

                          for (Instruction *I :Int_ins){
                            if(!prev_store_usechain.contains(I) && !useChain.contains(I)){
                              noDepChain.insert(I);
                              errs() << "No Dep: " << *I << "\n";
                            }
                          }
                          if(useChain.contains(prevStoreInst)){ //Int_ins.contains(LI2) && inst == prevStoreInst
                            UseChain_contains_prevStore = true;
                          }

                          if(prev_store_usechain.contains(storeInst)){
                            UseChain_contains_currStore = true;
                          }
                          
                          if(UseChain_contains_prevStore){
                            errs() << "PrevStore in the UseChain: " << "True" << "\n";
                          }else{
                            errs() << "PrevStore in the UseChain: " << "False" << "\n";
                          }

                          if(UseChain_contains_currStore){
                            errs() << "curStore in the Prev Store UseChain: " << "True" << "\n";
                          }else{
                            errs() << "curStore in the Prev Store UseChain: " << "False" << "\n";
                          }

                          if(LI == storeInst){
                            errs() << "Use Chain for: " << *storeInst << "\n";
                            for (auto it = useChain.rbegin(); it != useChain.rend(); ++it) {//for (Instruction *inst : useChain) {
                              Instruction *inst = *it;
                              errs() << "Inst in Use Chain" << *inst << "\n";
                            }
                            
                            if(UseChain_contains_prevStore){
                              for (Instruction *inst : useChain) {//for (auto it = useChain.rbegin(); it != useChain.rend(); ++it) {
                                //Instruction *inst = *it;
                              // Process each instruction in reverse order
                                if(inst != prevStoreInst && UseChain_contains_prevStore){
                                  errs() << "Ins move after PrevStore" << *inst << "\n";
                                  //inst->moveAfter(prevStoreInst); //TODO
                                }
                              }
                            }else{
                              for (auto it = useChain.rbegin(); it != useChain.rend(); ++it) {
                                Instruction *inst = *it;
                              //for (Instruction *inst : useChain) {
                                if(inst != prevStoreInst && inst == storeInst && !UseChain_contains_prevStore){
                                  successfully_reordered = true;
                                  reorder++;
                                  inst->moveAfter(prevStoreInst);
                                  errs() << "Ins move after PrevStore" << *inst << "\n";
                                } else if(inst != prevStoreInst && inst != storeInst && !UseChain_contains_prevStore && !Aliases_with_currStore){
                                  inst->moveBefore(prevStoreInst);
                                  errs() << "Ins move before PrevStore" << *inst << "\n";
                                }  
                              }
                            } 
                          }

                          if(LI == storeInst){
                            errs() << "User Chain for: " << *prevStoreInst << "\n";
                            for (auto it = prev_store_usechain.rbegin(); it != prev_store_usechain.rend(); ++it) {//for (Instruction *inst : useChain) {
                              Instruction *inst = *it;
                              errs() << "Inst in Prev Store Use Chain" << *inst << "\n";
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
                it_bb = ++storeInst->getIterator();
                prevStoreInst = nullptr;
                call_inbetween = false; //comment
                successfully_reordered = false;
                currentInst = nullptr;
                storeInst = nullptr;
                distance = 0;
              }else{
                currentInst = nullptr;
                storeInst = nullptr;
                if(!Aliases_with_currStore)
                  it_bb++;
              }
              if(UseChain_contains_prevStore){
                distance = 0;
              }
              errs() << "\n";
              defChain.clear();
              Int_ins.clear();
              Int_dep.clear();
              useChain.clear();
              call_inbetween = false; //comment
              prev_store_usechain.clear();
              noDepChain.clear();
              UseChain_contains_prevStore = false;
              Aliases_with_prevStore = false;
              Aliases_with_currStore = false;
              std::queue<Instruction *>().swap(worklist);
            }
            // if(successfully_reordered){
            //     prevStoreInst = nullptr;
            //     currentInst = nullptr;
            //     storeInst = nullptr;
            //     distance = 0;
            //   }else{
            //     prevStoreInst = storeInst;
            //   }
            if(!prevStoreInst){
              prevStoreInst = storeInst;
            }
          }
          else if(CallInst *callinst = dyn_cast<CallInst>(&I)){
            if(!storeInst && prevStoreInst){
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

