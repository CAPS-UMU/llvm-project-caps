//===-- HelloWorld.cpp - Example Transformations --------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

 
 #include "llvm/Transforms/Utils/HelloWorld.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/AliasAnalysisEvaluator.h"
#include "llvm/Analysis/DependenceAnalysis.h"
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
    if ((StartAddr1 == StartAddr2.lshr(6)) && (EndAddr1.lshr(6) == StartAddr1.lshr(6)) && (EndAddr2.lshr(6) == StartAddr2.lshr(6)))
        return true;
    else
        return false;
    return false;
}

static bool isNextLine(APInt StartAddr1, APInt EndAddr1, APInt StartAddr2, APInt EndAddr2)
{
    if ((StartAddr1.ule(StartAddr2) && ((EndAddr2 - StartAddr1).ult(64))) || (StartAddr2.ule(StartAddr1) && ((EndAddr1 - StartAddr2).ult(64))))
        return true;
    else
        return false;
    return false;
}

static bool isOneLineApart(APInt StartAddr1, APInt EndAddr1, APInt StartAddr2, APInt EndAddr2)
{
    if ((StartAddr1.ult(StartAddr2) && ((StartAddr1.lshr(6)) + 2) == ((EndAddr2.slt(6)))) || (StartAddr2.ult(StartAddr1) && ((EndAddr1.ult(6))) == ((StartAddr2.ult(6)) +2 )))
        return true;
    else
        return false;
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

bool isTrueContiguous(APInt StartAddr1, APInt EndAddr1, APInt StartAddr2, APInt EndAddr2)
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
PreservedAnalyses HelloWorldPass::run(Function &F, FunctionAnalysisManager &AM) {

  AliasAnalysis &AA = AM.getResult<AAManager>(F);
  auto &DA = AM.getResult<DependenceAnalysis>(F);
  auto &DL = F.getParent()->getDataLayout();
    std::vector<Instruction *> defChain;
    SetVector <Instruction *> Int_ins;
    SetVector <Instruction *> Int_dep;
    SetVector <Instruction *> useChain;
    SetVector <Instruction *> prev_load_usechain;
    SetVector <Instruction *> noDepChain;
    Instruction *int_mem_op = nullptr;
    Instruction *currentInst = nullptr;
    LoadInst *prevLoadInst = nullptr;
    std::queue<Instruction *> worklist;
    std::queue<Instruction *> worklist_prev;
    // Transfer elements from set to vector
    //std::vector<Instruction *> tempVector(useChain.begin(), useChain.end());

    Instruction *startInst;
    int wasted = 0;
    int reorder = 0;
    bool UseChain_contains_prevLoad = false;
    bool UseChain_contains_currLoad = false;
    bool Aliases_with_prevLoad = false;
    bool Aliases_with_currLoad = false;
    bool successfully_reordered = false;
      for (auto &BB : F) {
        LoadInst *prevLoadInst = nullptr;
        for (auto &I : BB) {
          if (LoadInst *loadInst = dyn_cast<LoadInst>(&I)) {
            successfully_reordered = false;
            // Print the def chain leading to the nextLoadInst
            if (prevLoadInst) {
              // successfully_reordered = false;
              currentInst = loadInst;
              startInst = prevLoadInst;
              Value *curLoadPtr = loadInst->getPointerOperand()->stripPointerCasts();
              Value *prevLoadPtr = loadInst->getPointerOperand()->stripPointerCasts();
              APInt curloadOffset(DL.getIndexTypeSizeInBits(curLoadPtr->getType()), 0);
              APInt prevloadOffset(DL.getIndexTypeSizeInBits(prevLoadPtr->getType()), 0);
              const Value  *curLoadBase = curLoadPtr->stripAndAccumulateConstantOffsets(DL, curloadOffset, /* AllowNonInbounds */ false);
              const Value  *prevLoadBase = prevLoadPtr->stripAndAccumulateConstantOffsets(DL, prevloadOffset, /* AllowNonInbounds */ false);
              if (curLoadBase != prevLoadBase){
                break;
                errs() << "Instructions doesn't have same base, prev load base: " << prevLoadBase << " cur load base :" << curLoadBase << "\n";
              }
              errs() << "Instructions have same base, prev load base: " << prevLoadBase << " cur load base :" << curLoadBase << "\n";

              auto CurLoadAccessSize = LocationSize::precise(DL.getTypeStoreSize(curLoadPtr->getType()));
              auto PrevLoadAccessSize = LocationSize::precise(DL.getTypeStoreSize(prevLoadPtr->getType()));
              
              APInt offsetdiff = (curloadOffset + CurLoadAccessSize.toRaw()) - (prevloadOffset + PrevLoadAccessSize.toRaw());
              APInt curloadStartaddress = curloadOffset;
              APInt prevloadStartaddress = prevloadOffset;
              APInt curloadEndaddress = curloadOffset + CurLoadAccessSize.toRaw();
              APInt prevloadEndaddress = prevloadOffset + PrevLoadAccessSize.toRaw();
              if(isContiguous(curloadStartaddress, CurLoadAccessSize.toRaw(), prevloadStartaddress, PrevLoadAccessSize.toRaw()) || isSameLine(curloadStartaddress, curloadEndaddress, prevloadStartaddress, prevloadEndaddress) || isNextLine(curloadStartaddress, curloadEndaddress, prevloadStartaddress, prevloadEndaddress) || isOneLineApart(curloadStartaddress, curloadEndaddress, prevloadStartaddress, prevloadEndaddress)){
                errs() << "yay! diff:" << offsetdiff << "\n";
              }else{
                break;
              }
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
                      if(Instruction *LI = dyn_cast<Instruction>(*it)){
                        for (Use &U : LI->operands()) {
                          Value *v = U.get();
                          //Value *def = LI->getPointerOperand();
                          if(Instruction *SI = dyn_cast<Instruction>(v)){
                            //errs() << "Def: " << *SI << "\n";
                          }
                          
                        }

                      }

                    }

                    for (auto it = Int_ins.rbegin(); it != Int_ins.rend(); ++it){
                      //errs() << "Instructions in between" << *(*it) << "\n";
                      if (isa<StoreInst>(*it)){//&& (DA.depends(*it, startInst, true))){ 
                        int_mem_op =  dyn_cast<StoreInst>(*it);
                        if( (AA.alias(startInst, int_mem_op) == AliasResult:: MustAlias) && (AA.alias(prevLoadInst, int_mem_op) == AliasResult:: MustAlias)){//(DA.depends(prevLoad, int_mem_op, true))){ //){
                            Int_ins.clear();
                            wasted++;
                            Aliases_with_currLoad = true;
                            Aliases_with_prevLoad = true;
                            break;
                        } else if((AA.alias(startInst, int_mem_op) == AliasResult:: MustAlias) && (AA.alias(prevLoadInst, int_mem_op) != AliasResult:: MustAlias)){
                          //int_mem_op->moveAfter(currLoad);
                          Aliases_with_currLoad = true;
                          Aliases_with_prevLoad = false;
                          continue;
                        } else if((AA.alias(startInst, int_mem_op) != AliasResult:: MustAlias) && (AA.alias(prevLoadInst, int_mem_op) == AliasResult:: MustAlias)){
                          //int_mem_op->moveBefore(prevLoad);
                          Aliases_with_currLoad = false;
                          Aliases_with_prevLoad = true;
                          continue;
                        } else if((AA.alias(startInst, int_mem_op) != AliasResult:: MustAlias) && (AA.alias(prevLoadInst, int_mem_op) != AliasResult:: MustAlias)){
                          //int_mem_op->moveAfter(currLoad);
                          Aliases_with_currLoad = false;
                          Aliases_with_prevLoad = false;
                          continue;
                        }
                      }else if(Instruction *LI = dyn_cast<LoadInst>(*it)){
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
                            useChain.insert(inst);
                            //errs() << "Int pop: " << *inst << "\n";
                            //errs() << "Int pop: " << inst << "\n";
                            if (inst == prevLoadInst) {
                              // Stop collecting the use chain at prevLoadInst
                              //UseChain_contains_prevLoad = true;
                              break;
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
                                  break;
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
                              break;
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
                                } else if(inst != prevLoadInst && inst != loadInst && !UseChain_contains_prevLoad && !Aliases_with_prevLoad){
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
                        //     if(UseChain_contains_currLoad){
                        //       for (Instruction *inst : useChain) {//for (auto it = useChain.rbegin(); it != useChain.rend(); ++it) {
                        //         //Instruction *inst = *it;
                        //       // Process each instruction in reverse order
                        //         if(inst != loadInst && UseChain_contains_currLoad){
                        //           errs() << "Can't move after prevLoad" << *inst << "\n";
                        //           //inst->moveAfter(prevLoadInst); //TODO
                        //         }
                        //       }
                        //     }else{
                        //       for (auto it = useChain.rbegin(); it != useChain.rend(); ++it) {
                        //         Instruction *inst = *it;
                        //       //for (Instruction *inst : useChain) {
                        //         if(inst != prevLoadInst && inst == loadInst && !UseChain_contains_currLoad){
                        //           inst->moveAfter(prevLoadInst);
                        //           errs() << "Ins move after prevLoad" << *inst << "\n";
                        //         } else if(inst != prevLoadInst && inst != loadInst && !UseChain_contains_currLoad && !Aliases_with_prevLoad){
                        //           inst->moveBefore(prevLoadInst);
                        //           errs() << "Ins move before prevLoad" << *inst << "\n";
                        //         }  
                        //       }
                        //     }  
                        // }
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
                prevLoadInst = nullptr;
                currentInst = nullptr;
              }
              errs() << "\n";
              defChain.clear();
              Int_ins.clear();
              Int_dep.clear();
              useChain.clear();
              prev_load_usechain.clear();
              noDepChain.clear();
              UseChain_contains_prevLoad = false;
              Aliases_with_prevLoad = false;
              Aliases_with_currLoad = false;
              std::queue<Instruction *>().swap(worklist);
            }
            if(successfully_reordered){
                prevLoadInst = nullptr;
                currentInst = nullptr;
                loadInst = nullptr;
              }else{
                prevLoadInst = loadInst;
              }
          }
        }
        errs() << "Number of Reorders: " << reorder << "\n";
        errs() << "Number of wasted: " << wasted << "\n";
      }
    return PreservedAnalyses::all();
 }

// bool isContiguous(uint64_t addr1, uint64_t size1, uint64_t addr2, uint64_t size2)
// {
//     size1 = size1 / 8;
//     size2 = size2 / 8;
//     assert(size1 >= 1 && size1 <= 8);
//     assert(size2 >= 1 && size2 <= 8);
//     if (addr1 == addr2)
//         return true;
//     if (addr1 < addr2)
//     {
//         return addr2 - addr1 <= size1;
//     }
//     if (addr1 > addr2)
//     {
//         return addr1 - addr2 <= size2;
//     }
//     return false;
// }

// bool isSameLine(uint64_t StartAddr1, uint64_t EndAddr1, uint64_t StartAddr2, uint64_t EndAddr2)
// {
//     if ((StartAddr1 >> 6 == StartAddr2 >> 6) && (EndAddr1 >> 6 == StartAddr1 >> 6) && (EndAddr2 >> 6 == StartAddr2 >> 6))
//         return true;
//     else
//         return false;
//     return false;
// }

// bool isNextLine(uint64_t StartAddr1, uint64_t EndAddr1, uint64_t StartAddr2, uint64_t EndAddr2)
// {
//     if ((StartAddr1 <= StartAddr2 && (EndAddr2 - StartAddr1 < 64)) || (StartAddr2 <= StartAddr1 && (EndAddr1 - StartAddr2 < 64)))
//         return true;
//     else
//         return false;
//     return false;
// }

// bool isOneLineApart(uint64_t StartAddr1, uint64_t EndAddr1, uint64_t StartAddr2, uint64_t EndAddr2)
// {
//     if ((StartAddr1 < StartAddr2 && ((StartAddr1 >> 6) + 2) == ((EndAddr2 >> 6))) || (StartAddr2 < StartAddr1 && ((EndAddr1 >> 6)) == ((StartAddr2 >> 6) +2 )))
//         return true;
//     else
//         return false;
//     return false;
// }

// bool isCacheCrosser(uint64_t StartAddr, uint64_t EndAddr)
// {
//     if ((StartAddr >> 6) != (EndAddr >> 6))
//     {
//         return true;
//     }
//     else
//     {
//         return false;
//     }
// }

// bool isTrueContiguous(uint64_t StartAddr1, uint64_t EndAddr1, uint64_t StartAddr2, uint64_t EndAddr2)
// {
//     if (((EndAddr1 + 1) == StartAddr2) || ((EndAddr2 + 1) == StartAddr1))
//         return true;
//     else
//         return false;
// }


  // void collectUseChain(Instruction *inst, std::set<Instruction *> &useChain) {
  //   // Add the instruction to the use chain set
  //   useChain.insert(inst);

  //   // Iterate over the operands of the instruction
  //   for (Use &U : inst->operands()) {
  //     Instruction *operandInst = dyn_cast<Instruction>(U.get());
  //     if (operandInst && !useChain.count(operandInst)) {
  //       // Recursively collect use chain for the operand instruction
  //       collectUseChain(operandInst, useChain);
  //     }
  //   }
  // }
//}



//            bool modified = false;
  
//   int reorder = 0;
//   int wasted = 0;
//   bool usedby_curr_load = false;
//   bool usedby_prev_load = false;
//   int number_gep = 0;
//   int number_store = 0;
//   int number_ins = 0;
//   LoadInst *prevLoad = nullptr;
//   LoadInst *currLoad = nullptr;
//   Instruction *int_mem_op = nullptr;
//   Instruction *int_gep_op = nullptr;
//   GetElementPtrInst *currGEP = nullptr;
//   SetVector <Instruction *> Int_ins;
//       for (BasicBlock &BB : F) {
//         prevLoad = nullptr;
//         for (Instruction &I : BB) {
          
//           Int_ins.insert(&I);
//           if (isa<LoadInst>(I)) {
//             currLoad = dyn_cast<LoadInst>(&I);
//             //errs() << "Number of Re Orders  " << '0' << '\n';
//             errs() << "size of vector  " << Int_ins.size() << '\n';
//             //errs() << "prevLoad  " << prevLoad << '\n';
//             if (prevLoad) {
//               //errs() << "Number of Re Orders  " << '0' << '\n';
//               // Check for dependencies
//               bool hasDependencies = false;
//               bool isContinuousAccess = false;
//               number_gep = 0;
//               number_store = 0;
//               number_ins = 0;
//               int_mem_op = nullptr;
//               int_gep_op = nullptr;
//               currGEP = nullptr;
//              // errs() << "Number of Re Orders  " << 'Q' << '\n';
//               for (Instruction *II : Int_ins){
//                // errs() << "Number of Re Orders  " << 'W' << '\n';
//                 //errs() << "R  " << prevLoad->getIterator() << '\n';
//                 //errs() << "A  " << currLoad->getIterator() << '\n';              
//                 if(isa<StoreInst>(II)){
//                   number_store++;
//                 }else if(isa<GetElementPtrInst>(II)){
//                   number_gep++;
//                 }
//                 number_ins++;
//                 // errs() << "R  " << prevLoad << '\n';
//                 // errs() << "A  " << currLoad << '\n';
//                 // errs() << "number_ins  " << II << '\n';
//               }
//               for (Instruction *II : Int_ins){
//                 //errs() << "Number of Re Orders  " << 'X' << '\n';
//                 if (isa<StoreInst>(II)){//&& (DA.depends(&II, prevLoad, true) || DA.depends(prevLoad, &II, true))){ 
//                   int_mem_op =  dyn_cast<StoreInst>(II);
//                   if( (AA.alias(prevLoad, int_mem_op) == AliasResult:: MustAlias) && (AA.alias(currLoad, int_mem_op) == AliasResult:: MustAlias)){//(DA.depends(prevLoad, int_mem_op, true))){ //){
//                       prevLoad = currLoad;
//                       currLoad = nullptr;
//                       Int_ins.clear();
//                       wasted++;
//                       break;
//                   } else if((AA.alias(prevLoad, int_mem_op) == AliasResult:: MustAlias) && (AA.alias(currLoad, int_mem_op) != AliasResult:: MustAlias)){
//                     //int_mem_op->moveAfter(currLoad);
//                     continue;
//                   } else if((AA.alias(prevLoad, int_mem_op) != AliasResult:: MustAlias) && (AA.alias(currLoad, int_mem_op) == AliasResult:: MustAlias)){
//                     //int_mem_op->moveBefore(prevLoad);
//                     continue;
//                   } else if((AA.alias(prevLoad, int_mem_op) != AliasResult:: MustAlias) && (AA.alias(currLoad, int_mem_op) != AliasResult:: MustAlias)){
//                     //int_mem_op->moveAfter(currLoad);
//                     continue;
//                   }
//                   //errs() << "Number of Re Orders  " << '1' << '\n';
//                 } else if (isa<GetElementPtrInst>(II)) {
//                     //errs() << "Number of Re Orders  " << 'Y' << '\n';
//                     wasted++;
//                     currGEP = dyn_cast<GetElementPtrInst>(II);
//                     usedby_curr_load = false;
//                     usedby_prev_load = false;
//                     for (User *U : currGEP->users()) {
//                       // Check if the `getelementptr` instruction is among the users of the `load`
//                       errs() << "User  " << *U << "\n";
//                       if (U == currLoad) {
//                         //  if the `getelementptr` uses the output of the `load`
//                         usedby_curr_load = true;
//                       }
//                     }
//                     for (User *U : prevLoad->users()) {
//                         errs() << "User  " << *U << "\n";
//                       // Check if the `getelementptr` instruction is among the users of the `load`
//                       if (U == currGEP) {
//                         //  if the `getelementptr` uses the output of the `load`
//                         usedby_prev_load = true;
//                       }
//                     }
//                     if( !usedby_curr_load && usedby_prev_load ){ //){
//                       //currGEP->moveAfter(currLoad);
//                       continue;
//                     } else if(usedby_curr_load && !usedby_prev_load){
//                       //currGEP->moveBefore(prevLoad);
//                       continue;
//                     } else if(!usedby_curr_load && !usedby_prev_load){
//                       //currGEP->moveAfter(currLoad);
//                       continue;
//                     }
//                     //errs() << "Number of Re Orders  " << '2' << '\n';
//                 }else if (number_gep == 0){
//                   //currLoad->moveAfter(prevLoad);
//                   //errs() << "Number of Re Orders  " << '3' << '\n';
//                 }else if(isa<BranchInst>(II)){
//                   //errs() << "Number of Re Orders  " << 'z' << '\n';
//                   prevLoad = nullptr;
//                   currLoad = nullptr;
//                   Int_ins.clear();
//                   wasted++;
//                   //errs() << "Number of Re Orders  " << '4' << '\n';
//                   break; 
//                 } else{
//                   //currLoad->moveAfter(prevLoad);
//                   //errs() << "Number of Re Orders  " << '5' << '\n';
//                 }
//               }
//               prevLoad = currLoad;
//               Int_ins.clear();
//             }
//             //Int_ins.clear();
//             prevLoad = currLoad;
//             // prevLoad = currLoad;
//             //errs() << "Number of Re Orders  " << '6' << '\n'; 
//           }
//           //prevLoad = currLoad;
//            //errs() << "Number of Re Orders  " << '7' << '\n';
//           // errs() << "prevLoad " << prevLoad << '\n';
//           // errs() << "currLoad " << currLoad << '\n';
//         }
//       }
//     SetVector<StoreInst *> Stores_int;
//   SetVector<GetElementPtrInst *> GetElementPtrInst_int;

//   int Count=0;
//   int num_reorder=0;
//   int wasted = 0;
// for (BasicBlock &BB : F) {
//     LoadInst *prevLoadInst = nullptr;
//     //Instruction *prevStoreInst = nullptr;
//     GetElementPtrInst *prevGEPInst = nullptr;
//     for (Instruction &I : BB) {  
//       if (LoadInst *LI = dyn_cast<LoadInst>(&I)) {
//         if (prevLoadInst) {
//           // Check for dependencies between the loads and the stores
//           for (StoreInst *Store : Stores_int) { //this for loop and queue can be eliminated by directly checking for the alias and depends if store is encountered.
//               if (DA.depends(Store, LI, true)) { //depnds also verifies if two loads or store alias. so we can remove the above step
//               //  if(AA.alias(MemoryLocation::get(prevLoadInst), MemoryLocation::get(Store)) == AliasResult:: MustAlias){
//                 // There is a dependence between the stores and the loads, so we cannot safely reorder them
//                 Stores_int.clear();
//                 wasted++;
//                 //GetElementPtrInst_int.clear();
//                 prevLoadInst = LI;
//                 continue;
//               } else{
//                 Store->moveAfter(LI);
//               }
//           }
//           // Swap the positions of the two load instructions
//          // errs() <<  "Re Order Instructions"  << '\n';
//           if (GetElementPtrInst_int.empty()) {
//             I.moveAfter(prevLoadInst);
//             num_reorder++;
//           } else {
//             wasted++;
//               for (GetElementPtrInst *GEP : GetElementPtrInst_int) { //this for loop and queue can be eliminated by directly checking for the alias and depends if store is encountered.
//                     for (const User *user : prevLoadInst->users()) {
//                        for (User::user_iterator U = GEP->user_begin(); U != GEP->user_end(); ++U) {
//                           //if (const Instruction *inst = dyn_cast<Instruction>(user)) {
//                               if (dyn_cast<LoadInst>(*U) == LI) {
//                                   GEP->moveBefore(LI);
//                                   num_reorder++;
//                               }
//                            // }
//                       }   
//           if (GetElementPtrInst_int.empty()) {
//             LI->moveAfter(prevLoadInst);
//             num_reorder++;
//           } 
//           else {
//               for (GetElementPtrInst *GEP : GetElementPtrInst_int) { //this for loop and queue can be eliminated by directly checking for the alias and depends if store is encountered.
//                 if (GEP->getOperand(0) == LI->getPointerOperand()) { //depnds also verifies if two loads or store alias. so we can remove the above step
//                   // There is a dependence between the stores and the loads, so we cannot safely reorder them
//                   GEP->moveAfter(LI);
//                   num_reorder++;
//                 } else {
//                   int d_LI_GEP = 0;
//                     for (User::user_iterator U = GEP->user_begin(); U != GEP->user_end(); ++U) {
//                       if (dyn_cast<LoadInst>(*U) == LI) {
//                         GEP->moveBefore(LI);
//                         d_LI_GEP++;
//                       }else if(GetElementPtrInst_int.contains(dyn_cast<GetElementPtrInst>(*U)) || Stores_int.contains(dyn_cast<StoreInst>(*U))){
//                         //GEP->moveBefore(dyn_cast<GetElementPtrInst>(*U));
//                         break; //can add some more logic to reorder
//                       }
//                       else if(U == GEP->user_end() && d_LI_GEP == 0){
//                         prevLoadInst->moveBefore(LI);
//                         num_reorder++;
//                       }
//                     }
//                 }
//               }
//             }
//                 }
//               }
//             }
//           GetElementPtrInst_int.clear();
//           prevLoadInst = LI;
//           Stores_int.clear();
//         } else {
//             prevLoadInst = LI;
//         }
//       } else if (GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(&I)) {
//           GetElementPtrInst_int.insert(GEP);
//       } else if (StoreInst *SI = dyn_cast<StoreInst>(&I)) {
//           Stores_int.insert(SI);
//       } else if (BranchInst *branchInst = dyn_cast<BranchInst>(&I)){
//           GetElementPtrInst_int.clear();
//           prevLoadInst = nullptr;
//           Stores_int.clear();
//           wasted++;
//       }
//     }
//   }

//   //errs() << "Number of Re Orders  " << num_reorder << '\n';
//   errs() << "Number of wasted  " << wasted << '\n';
//     return PreservedAnalyses::all();
// }
// #include "llvm/Transforms/Utils/HelloWorld.h"
// #include "llvm/IR/InstIterator.h"
// #include "llvm/IR/Instructions.h"
// #include "llvm/Analysis/AliasAnalysis.h"
// #include "llvm/Analysis/AliasAnalysisEvaluator.h"
// #include "llvm/Analysis/DependenceAnalysis.h"
// #include "llvm/ADT/SetVector.h"
// #include "llvm/IR/DataLayout.h"
// #include "llvm/IR/Function.h"
// #include "llvm/IR/Module.h"
// #include "llvm/InitializePasses.h"
// #include "llvm/Pass.h"
// #include "llvm/Support/CommandLine.h"
// #include "llvm/Support/raw_ostream.h"
// #include "llvm/Support/SourceMgr.h"
// #include "llvm/Analysis/BasicAliasAnalysis.h"
// #include "llvm/IR/PassManager.h"
// #include "llvm/IR/CFG.h"

// using namespace llvm;

// PreservedAnalyses HelloWorldPass::run(Function &F, FunctionAnalysisManager &AM) {

//   AliasAnalysis &AA = AM.getResult<AAManager>(F);
//   auto &DA = AM.getResult<DependenceAnalysis>(F);

//   SetVector<StoreInst *> Stores_int;
//   SetVector<GetElementPtrInst *> GetElementPtrInst_int;

//   int Count=0;
//   int num_reorder=0;
//   int wasted = 0;
// for (BasicBlock &BB : F) {
//     LoadInst *prevLoadInst = nullptr;
//     //Instruction *prevStoreInst = nullptr;
//     GetElementPtrInst *prevGEPInst = nullptr;
//     for (Instruction &I : BB) {  
//       if (LoadInst *LI = dyn_cast<LoadInst>(&I)) {
//         if (prevLoadInst) {
//           // Check for dependencies between the loads and the stores
//           for (StoreInst *Store : Stores_int) { //this for loop and queue can be eliminated by directly checking for the alias and depends if store is encountered.
//               if (DA.depends(Store, LI, true)) { //depnds also verifies if two loads or store alias. so we can remove the above step
//               //  if(AA.alias(MemoryLocation::get(prevLoadInst), MemoryLocation::get(Store)) == AliasResult:: MustAlias){
//                 // There is a dependence between the stores and the loads, so we cannot safely reorder them
//                 Stores_int.clear();
//                 wasted++;
//                 //GetElementPtrInst_int.clear();
//                 prevLoadInst = LI;
//                 continue;
//               } else{
//                 Store->moveAfter(LI);
//               }
//           }
//           // Swap the positions of the two load instructions
//          // errs() <<  "Re Order Instructions"  << '\n';
//           if (GetElementPtrInst_int.empty()) {
//             I.moveAfter(prevLoadInst);
//             num_reorder++;
//           } else {
//               for (GetElementPtrInst *GEP : GetElementPtrInst_int) { //this for loop and queue can be eliminated by directly checking for the alias and depends if store is encountered.
//                     for (const User *user : prevLoadInst->users()) {
//                        for (User::user_iterator U = GEP->user_begin(); U != GEP->user_end(); ++U) {
//                           if (const Instruction *inst = dyn_cast<Instruction>(user)) {
//                               if (inst != GEP && dyn_cast<LoadInst>(*U) == LI) {
//                                   GEP->moveBefore(LI);
//                                   num_reorder++;
//                               } else if(inst != GEP && dyn_cast<LoadInst>(*U) != LI){
//                                 GEP->moveBefore(prevLoadInst);
//                                 num_reorder++;
//                               } else if(inst == GEP && dyn_cast<LoadInst>(*U) != LI){
//                               }
//                             }
//                     }   
//                 // if (GEP->getOperand(0) == LI->getPointerOperand()){ //depnds also verifies if two loads or store alias. so we can remove the above step
//                 //   errs() << "  " << "prevLoadInst" << ": " << *prevLoadInst << " <-> " <<  '\n';
//                 //   errs() << "  " << "GEP" << ": " << *GEP << " <-> " <<  '\n';
//                 //   errs() << "  " << "Load" << ": " << *LI << " <-> " <<  '\n';
//                 //   GEP->moveBefore(LI);
                
//                 // }
//                 // if {
//                 //   int d_LI_GEP = 0;
                 
//                 //       if (dyn_cast<LoadInst>(*U) == LI) {
//                 //         // errs() << "  " << "Load" << ": " << *LI << " <-> " <<  '\n';
//                 //         // errs() << "  " << "GEP" << ": " << *GEP << " <-> " <<  '\n';
//                 //         // errs() << "  " <<  '\n';
//                 //         GEP->moveBefore(LI);
//                 //         d_LI_GEP++;
//                 //       }else if(GetElementPtrInst_int.contains(dyn_cast<GetElementPtrInst>(*U))){
//                 //         //GEP->moveBefore(dyn_cast<GetElementPtrInst>(*U));
//                 //         break; //can add some more logic to reorder
//                 //       }else if(U == GEP->user_end() && d_LI_GEP == 0){
//                 //         LI->moveAfter(prevLoadInst);
//                 //         num_reorder++;
//                 //       }
//                 //       //  else{
//                 //       //     GEP->moveAfter(LI);
//                 //       //     num_reorder++;
//                 //       // }
//                 //     }
//                 }
//               }
//             }
//           GetElementPtrInst_int.clear();
//           prevLoadInst = LI;
//           Stores_int.clear();
//         } else {
//             prevLoadInst = LI;
//         }
//       } else if (GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(&I)) {
//           GetElementPtrInst_int.insert(GEP);
//       } else if (StoreInst *SI = dyn_cast<StoreInst>(&I)) {
//           Stores_int.insert(SI);
//       } else if (BranchInst *branchInst = dyn_cast<BranchInst>(&I)){
//           GetElementPtrInst_int.clear();
//           prevLoadInst = nullptr;
//           Stores_int.clear();
//       }
//     }
//   }

//   errs() << "Number of Re Orders  " << num_reorder << '\n';
//   errs() << "Number of wasted  " << wasted << '\n';
//   return PreservedAnalyses::all();
// }
      
      // Helper function to check if an instruction has dependencies on subsequent instructions,
      // excluding dependencies with getelementptr instructions that increment the address for the store
      // bool hasDependencies(StoreInst *store, std::vector<GetElementPtrInst *> &getelementptrs) {
      //     for (User *U : store->users()) {
      //         if (Instruction *I = dyn_cast<Instruction>(U)) {
      //             if (isa<GetElementPtrInst>(I) && std::find(getelementptrs.begin(), getelementptrs.end(), I) != getelementptrs.end())
      //                 continue;
                  
      //             if (I->comesBefore(store))
      //                 return true;
      //         }
      //     }
      //     return false;
      // }

        
      // void haveIntermediateInstructions(Instruction *startInst, Instruction *endInst) {
      //     BasicBlock *startBB = startInst->getParent();
      //     BasicBlock *endBB = endInst->getParent();
          
      //     if (startBB != endBB) {
      //         return true;
      //     }
          
      //     for (BasicBlock::iterator it = ++startInst->getIterator(); &(*it) != endInst; ++it) {
      //         if (it->mayReadOrWriteMemory()) {
      //             return true;
      //         }
      //     }
          
      //     return false;
      // }
      
      // bool areIndependentInstructions(Instruction *inst1, Instruction *inst2) {
      //     SmallPtrSet<Value *, 8> defs;
          
      //     for (User *user : inst1->users()) {
      //         if (auto *userInst = dyn_cast<Instruction>(user)) {
      //             defs.insert(userInst);
      //         }
      //     }
          
      //     for (Use &use : inst2->operands()) {
      //         Value *value = use.get();
      //         if (defs.count(value)) {
      //             return false;
      //         }
      //     }
          
      //     return true;
      // }
      
      // void reorderStores(std::vector<StoreInst *> &stores) {
      //     if (stores.size() < 2) {
      //         return;
      //     }
          
      //     BasicBlock *BB = stores[0]->getParent();
      //     Instruction *insertPoint = stores.back()->getNextNode();
          
      //     for (unsigned int i = stores.size() - 1; i > 0; --i) {
      //         stores[i]->moveBefore(insertPoint);
      //     }
      // }
// #include "llvm/Transforms/Utils/HelloWorld.h"
// #include "llvm/IR/InstIterator.h"
// #include "llvm/IR/Instructions.h"
// #include "llvm/Analysis/AliasAnalysis.h"
// #include "llvm/Analysis/AliasAnalysisEvaluator.h"
// #include "llvm/Analysis/DependenceAnalysis.h"
// #include "llvm/ADT/SetVector.h"
// #include "llvm/IR/DataLayout.h"
// #include "llvm/IR/Function.h"
// #include "llvm/IR/Module.h"
// #include "llvm/InitializePasses.h"
// #include "llvm/Pass.h"
// #include "llvm/Support/CommandLine.h"
// #include "llvm/Support/raw_ostream.h"
// #include "llvm/Support/SourceMgr.h"
// #include "llvm/Analysis/BasicAliasAnalysis.h"

// using namespace llvm;

// namespace {
//   struct BringLoadsTogetherPass : public FunctionPass {
//     static char ID;

//     BringLoadsTogetherPass() : FunctionPass(ID) {}

//     bool runOnFunction(Function &F) override {
//       AliasAnalysis &AA = getAnalysis<AliasAnalysis>();
//       DependenceAnalysis &DA = getAnalysis<DependenceAnalysis>();

//       for (BasicBlock &BB : F) {
//         Instruction *prevLoadInst = nullptr;
//         StoreInst *prevStoreInst = nullptr;

//         for (Instruction &I : BB) {
//           if (LoadInst *LI = dyn_cast<LoadInst>(&I)) {
//             if (prevLoadInst) {
//               // Check for dependencies between the loads and the stores
//               if (prevStoreInst && AA.alias(prevLoadInst, prevStoreInst)) {
//                 if (DA.depends(prevStoreInst, prevLoadInst, true)) {
//                   // There is a dependence between the stores and the loads, so we cannot safely reorder them
//                   continue;
//                 }
//               }

//               // Swap the positions of the two load instructions
//               I.moveBefore(prevLoadInst);
//               prevLoadInst = LI;
//             } else {
//               prevLoadInst = LI;
//             }
//           } else if (StoreInst *SI = dyn_cast<StoreInst>(&I)) {
//             prevStoreInst = SI;
//           }
//         }
//       }

//       return true;
//     }

//     void getAnalysisUsage(AnalysisUsage &AU) const override {
//       AU.addRequired<AAResultsWrapperPass>();
//       AU.addRequired<DependenceAnalysisWrapperPass>();
//       AU.setPreservesAll();
//     }
//   };
// }

// char BringLoadsTogetherPass::ID = 0;

// static RegisterPass<BringLoadsTogetherPass> X("bringloads", "Bring Load Instructions Together Pass");

//##################################################################################################
// SetVector<Value *> Loads;
// SetVector<Value *> Stores;
// AliasAnalysis &AA = AM.getResult<AAManager>(F);
// //DependenceAnalysis &DA = AM.getResult<DependenceAnalysis>(F);
// auto &DA = AM.getResult<DependenceAnalysis>(F);
// //errs() << F.getName() << "\n";
// for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I)
// {
//   //errs() << *I << "\n";
//   if(isa<LoadInst>(*I))
//   {
//     //errs() << *I << "\n";
//   }
//   if(isa<StoreInst>(*I))
//   {
//     //errs() << *I << "\n";
//   }
// }

// for (Instruction &Inst : instructions(F)) {
//   if (auto *LI = dyn_cast<LoadInst>(&Inst)) {
//     Loads.insert(LI);
//   } else if (auto *SI = dyn_cast<StoreInst>(&Inst)) {
//     Stores.insert(SI);
//   } 
// }
// for (Value *Store : Stores) {
//   for (Value *Load : Loads) {
//     AliasResult AR = AA.alias(MemoryLocation::get(cast<LoadInst>(Load)),  MemoryLocation::get(cast<StoreInst>(Store)));
//     switch (AR) {
//     case AliasResult::NoAlias:
//       //errs() << "  " << AR << ": " << *Load << " <-> " << *Store << '\n';
//       //++NoAliasCount;
//       break;
//     case AliasResult::MayAlias:
//       //errs() << "  " << AR << ": " << *Load << " <-> " << *Store << '\n';
//       //++MayAliasCount;
//       break;
//     case AliasResult::PartialAlias:
//       //errs() << "  " << AR << ": " << *Load << " <-> " << *Store << '\n';
//       //++PartialAliasCount;
//       break;
//     case AliasResult::MustAlias:
//       //errs() << "  " << AR << ": " << *Load << " <-> " << *Store << '\n';
//       //++MustAliasCount;
//       break;
//     }
//   }
// }

// //SetVector<Value *> Loads_int;
// SetVector<Value *> Stores_int;
// //SetVector<Value *> Arth_int;
// int Count=0;
// int num_reorder=0;
//     for (BasicBlock &BB : F) {
//       LoadInst *prevLoadInst = nullptr;
//       //Instruction *prevStoreInst = nullptr;
//       GetElementPtrInst *prevGEPInst = nullptr;
//       for (Instruction &I : BB) {   //TODO: How do we tackle when there's a branch between two loads? (Do we reset the previous load to null)
//         //errs() << "Instructions  " << I << '\n';
//         if (LoadInst *LI = dyn_cast<LoadInst>(&I)) {
//           if (prevLoadInst) {
//             // Check for dependencies between the loads and the stores
//             for (Value *Store : Stores_int) { //this for loop and queue can be eliminated by directly checking for the alias and depends if store is encountered.
//               if (AA.alias(LI, dyn_cast<StoreInst>(Store))) {
//                 if (DA.depends(dyn_cast<StoreInst>(Store), LI, true)) { //depnds also verifies if two loads or store alias. so we can remove the above step
//                   // There is a dependence between the stores and the loads, so we cannot safely reorder them
//                   Stores_int.clear();
//                   prevGEPInst = nullptr;
//                   Count = 0;
//                   prevLoadInst = LI;
//                   continue;
//                 }
//               }
//             }
//             // Swap the positions of the two load instructions
//             errs() <<  "Re Order Instructions"  << '\n';
//             if (prevGEPInst == nullptr && Count == 0) {
//               I.moveAfter(prevLoadInst);
//               num_reorder++;
//             } else if (prevGEPInst == nullptr && Count) {
//                 prevLoadInst = LI;
//                 Count = 0;
//                 continue;
//             } else if ( prevGEPInst && Count){
//                 I.moveAfter(prevGEPInst);
//                 num_reorder++;
//             }
//           Count = 0;
//           // if (prevGEPInst) {
//           //   prevGEPInst->moveBefore(&I);
//           // }
//           // errs() << "prevGEPInst  " << prevGEPInst << '\n';
//           // errs() << "prevLoadInst  " << prevLoadInst << '\n';
//           // errs() << "currentLoadInst  " << I << '\n';
//             prevGEPInst = nullptr;
//             prevLoadInst = LI;
//             Stores_int.clear();
//           } else {
//             prevLoadInst = LI;
//           }
//         } else if (GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(&I)) {
//           Count++;
//         // Check if the GEP instruction accesses a continuous address range
//         if (prevLoadInst && GEP->hasOneUse() && GEP->getOperand(0) == prevLoadInst->getPointerOperand()) {
//           // Include the GEP instruction after the reordered load instruction
//           GEP->moveAfter(prevLoadInst);
//           prevGEPInst = GEP;
//         } else {
//           prevGEPInst = nullptr;
//         }
//       } else if (StoreInst *SI = dyn_cast<StoreInst>(&I)) {
//           //prevStoreInst = SI;
//           Stores_int.insert(SI);
//         }
//       }
//     }
// //SetVector<Value *> Loads_int;
// //SetVector<Value *> Stores_int;
// SetVector<Value *> Loads_int;
// int Count_s=0;
//     for (BasicBlock &BB : F) {
//       StoreInst *prevStoreInst = nullptr;
//       //Instruction *prevStoreInst = nullptr;
//       GetElementPtrInst *prevGEPInst = nullptr;
//       for (Instruction &I : BB) {   //TODO: How do we tackle when there's a branch between two loads? (Do we reset the previous load to null)
//         //errs() << "Instructions  " << I << '\n';
//         if (StoreInst *SI = dyn_cast<StoreInst>(&I)) {
//           if (prevStoreInst) {
//             // Check for dependencies between the loads and the stores
//             for (Value *Loads : Loads_int) { //this for loop and queue can be eliminated by directly checking for the alias and depends if store is encountered.
//               if (AA.alias(SI, dyn_cast<LoadInst>(Loads))) {
//                 if (DA.depends(dyn_cast<LoadInst>(Loads), SI, true)) { //depnds also verifies if two loads or store alias. so we can remove the above step
//                   // There is a dependence between the stores and the loads, so we cannot safely reorder them
//                   Loads_int.clear();
//                   prevGEPInst = nullptr;
//                   Count_s = 0;
//                   prevStoreInst = SI;
//                   continue;
//                 }
//               }
//             }
//             // Swap the positions of the two load instructions
//             // errs() <<  "Re Order Instructions"  << '\n';
//             if (prevGEPInst == nullptr && Count_s == 0) {
//               I.moveAfter(prevStoreInst);
//               num_reorder++;
//             } else if (prevGEPInst == nullptr && Count_s) {
//                 prevStoreInst = SI;
//                 Count_s = 0;
//                 continue;
//             } else if ( prevGEPInst && Count_s){
//                 I.moveAfter(prevGEPInst);
//                 num_reorder++;
//             }
//           Count_s = 0;
//           // if (prevGEPInst) {
//           //   prevGEPInst->moveBefore(&I);
//           // }
//           // errs() << "prevGEPInst  " << prevGEPInst << '\n';
//           // errs() << "prevStoreInst  " << prevStoreInst << '\n';
//             prevGEPInst = nullptr;
//             prevStoreInst = SI;
//             Loads_int.clear();
//           } else {
//             prevStoreInst = SI;
//           }
//         } else if (GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(&I)) {
//           Count_s++;
//         // Check if the GEP instruction accesses a continuous address range
//         if (prevStoreInst && GEP->hasOneUse() && GEP->getOperand(0) == prevStoreInst->getPointerOperand()) {
//           // Include the GEP instruction after the reordered load instruction
//           GEP->moveAfter(prevStoreInst);
//           prevGEPInst = GEP;
//         } else {
//           prevGEPInst = nullptr;
//         }
//       } else if (LoadInst *LI = dyn_cast<LoadInst>(&I)) {
//           //prevStoreInst = SI;
//           Loads_int.insert(LI);
//         }
//       }
//     }
//     errs() << "Number of Reorders  " << num_reorder  << '\n';
//           return PreservedAnalyses::all();