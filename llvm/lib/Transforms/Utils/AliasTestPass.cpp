//===-- AliasTestPass.cpp - Example Transformations --------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "llvm/Transforms/Utils/AliasTestPass.h"
#include "llvm/ADT/SetVector.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/MemoryLocation.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Pass.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/ModRef.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

struct LdStInst AliasTestPass::getLoadAndStore(Function &F) {
  SetVector<Value *> Loads;
  SetVector<Value *> Stores;

  for(BasicBlock &BB : F) 
    for (Instruction &Inst : BB)
      if (auto *LI = dyn_cast<LoadInst>(&Inst)) {
        Loads.insert(LI);
      } else if (auto *SI = dyn_cast<StoreInst>(&Inst)) {
        Stores.insert(SI);
      }
  
  return {Loads, Stores};
}

PreservedAnalyses AliasTestPass::run(Function &F,
                                      FunctionAnalysisManager &AM) {
  auto LdStTables = getLoadAndStore(F);

  // Get the alias analysis results for this module
  AliasAnalysis &AA = AM.getResult<AAManager>(F);

  errs() << F.getName() << " contains the following load and store : \n";
  for (Value *Load : LdStTables.Loads) errs() << *Load << "\n";
  for (Value *Store : LdStTables.Stores) errs() << *Store << "\n";

  // declaring counts for differents answers of alias analysis
  int countMayAlias = 0;
  int countNotAlias = 0;
  int countMustAlias = 0;
  int countPartialAlias = 0;

  int countMod = 0;
  int countRef = 0;
  int countModRef = 0;
  int countNoModRef = 0;
  
  for (Value *Load : LdStTables.Loads) {
    for (Value *Store : LdStTables.Stores) {
      AliasResult AR = AA.alias(MemoryLocation::get(cast<LoadInst>(Load)),
                                MemoryLocation::get(cast<StoreInst>(Store)));
      switch(AR) {
        case AliasResult::MayAlias:     countMayAlias++;     break;
        case AliasResult::MustAlias:    countMustAlias++;    break;
        case AliasResult::NoAlias:      countNotAlias++;     break;
        case AliasResult::PartialAlias: countPartialAlias++; break;
      }

      ModRefInfo StoreLocModRef = AA.getModRefInfo(dyn_cast<LoadInst>(Load), 
        MemoryLocation::get(dyn_cast<StoreInst>(Store)));

      ModRefInfo LoadLocModRef = AA.getModRefInfo(dyn_cast<StoreInst>(Store), 
        MemoryLocation::get(dyn_cast<LoadInst>(Load)));

      std::string MemDep = (
        LoadLocModRef == ModRefInfo::NoModRef && StoreLocModRef == ModRefInfo::NoModRef
      ) ? "NO" : "THERE IS A";

      errs() << "  " << AR << " ;"
             << MemDep << " mem-dep between : "
             << *Load << " <-> " << *Store << '\n';
    }
  }

  errs() << "Count of may alias : " << countMayAlias << "\n";
  errs() << "Count of no alias : " << countNotAlias << "\n";
  errs() << "Count of must alias : " << countMustAlias << "\n";
  errs() << "Count of partial alias : " << countPartialAlias << "\n";

  errs() << "Count of mod : " << countMod << "\n";
  errs() << "Count of ref : " << countRef << "\n";
  errs() << "Count of modref : " << countModRef << "\n";
  errs() << "Count of nomodref : " << countNoModRef << "\n";
  return PreservedAnalyses::all();
}
