//===-- AliasTestPass.cpp - Example Transformations --------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "llvm/Transforms/Utils/AliasTestPass.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SetVector.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/AliasGraph.h"
#include "llvm/Analysis/GlobalsModRef.h"
#include "llvm/Analysis/MemoryLocation.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalAlias.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Pass.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/FormatVariadic.h"
#include "llvm/Support/ModRef.h"
#include "llvm/Support/ScopedPrinter.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

//#define QUERY_STATS
//#define TEST_MODREF
#define COMPARE_RESULT

#define INCR_COUNTER(result, cpt1, cpt2, cpt3, cpt4) do { \
  switch(result) { \
    case 0: cpt1++; break; \
    case 1: cpt2++; break; \
    case 2: cpt3++; break; \
    case 3: cpt4++; break; \
  } \
} while(false)

struct MemInstSets AliasTestPass::getMemInstr(Function &F) {
  SetVector<Value *> Loads;
  SetVector<Value *> Stores;
  SetVector<Value *> Allocs;

  for(BasicBlock &BB : F) 
    for (Instruction &Inst : BB)
      if (auto *LI = dyn_cast<LoadInst>(&Inst))
        Loads.insert(LI);
      else if (auto *SI = dyn_cast<StoreInst>(&Inst))
        Stores.insert(SI);
      else if (auto *AI = dyn_cast<AllocaInst>(&Inst))
        Allocs.insert(AI);
  
  return {Loads, Stores, Allocs};
}

AliasResult AliasTestPass::tryAliasOrigin(const MemoryLocation &LocA, const MemoryLocation &LocB, 
                                  AliasGraph &graph, AliasAnalysis &AA) {
  AliasNode * node1 = graph.retraceOrigin(LocA);
  AliasNode * node2 = graph.retraceOrigin(LocB);

  if(*node1 == *node2) return AliasResult::MustAlias;

  //getting the partition over function of the two nodes 
  auto FPNode1 = node1->partitionOverFunctions();
  auto FPNode2 = node2->partitionOverFunctions();

  int no=0,may=0,part=0,must=0,total=0;

  for(auto it = FPNode1.begin(); it != FPNode1.end(); it++) {
    if( ! FPNode2.count(it->first)) continue;

    for(auto * valNode1 : it->second) {
      for (auto * valNode2 : FPNode2[it->first]) {
        AliasResult AAR = AA.alias(valNode1, valNode2); 
        switch(AAR) {
          case AliasResult::NoAlias : no++; break;
          case AliasResult::MayAlias : may++; break;
          case AliasResult::PartialAlias : part++; break;
          case AliasResult::MustAlias : must++; break;
        }
        total++;
      }
    }
  }

  errs() << "Over the two node's origin : no="<<no<<"/may="<<may<<"/part="<<part<<"/must="<<must<<"/total="<<total<<"\n";
  if(must > 0) return AliasResult::MustAlias;
  if(part > 0) return AliasResult::PartialAlias;
  
  return (may > no) ? AliasResult::MayAlias : AliasResult::NoAlias;
}

void AliasTestPass::iterateOnFunction(Function &F, FunctionAnalysisManager &FAM,
                      ModuleAnalysisManager &MAM) {
  errs() << F.getName();
  if (F.empty()) {
    errs() << " is empty. Moving to the next function.\n";
    return;
  }
  
  AliasAnalysis &AA = FAM.getResult<AAManager>(F);

#ifdef COMPARE_RESULT  
  auto & GraphAAR = MAM.getResult<GraphAA>( *(F.getParent()));
  auto & GlobalsAAR = MAM.getResult<GlobalsAA>(*(F.getParent()));
  SimpleAAQueryInfo SimpleAAQI (AA);
#endif // COMPARE_RESULT

  auto Sets = getMemInstr(F);

  errs() << " contains the following load and store : \n";
  for (Value *Load : Sets.Loads)   {
    Load->printAsOperand(errs());
    errs() << " : " << *Load << "\n";
  }
  for (Value *Store : Sets.Stores) {
    errs() << *Store << "\n";
  }

#ifdef COMPARE_RESULT
  int betterResult = 0;
#endif //COMPARE_RESULT

#ifdef QUERY_STATS
  // declaring counts for differents answers of alias analysis
  int countMayAlias = 0;
  int countNotAlias = 0;
  int countMustAlias = 0;
  int countPartialAlias = 0;

  int countMod = 0;
  int countRef = 0;
  int countModRef = 0;
  int countNoModRef = 0;
#endif // QUERY_STATS

  int totalRequest = 0;
  for (Value *Load : Sets.Loads) {
    for (Value *Store : Sets.Stores) {
      MemoryLocation LoadLoc = MemoryLocation::get(dyn_cast<LoadInst>(Load));
      MemoryLocation StoreLoc = MemoryLocation::get(dyn_cast<StoreInst>(Store));
    
      AliasResult ARFunc = AA.alias(LoadLoc, StoreLoc);
	    totalRequest++;

#ifdef COMPARE_RESULT
      AliasResult ARMod = GraphAAR.alias(LoadLoc, StoreLoc, SimpleAAQI, nullptr);
      AliasResult ARGlob = GlobalsAAR.alias(LoadLoc, StoreLoc, SimpleAAQI, nullptr);

      if(betterAliasResult(ARMod, ARFunc)) {
        errs() << "\n ----------------------\n Values : \n" << *Load << " <--> " << *Store << " ]\n";
        AliasResult originAlias = tryAliasOrigin(LoadLoc, StoreLoc, GraphAAR.getGraph(), AA);  
        errs() << "Are said to be : [" << ARFunc << "] according to AA default pipeline | "
              << "[" << ARMod << "] according to GraphAA | " 
              << "[" << ARGlob << "] according to GlobalsAA.\n";
        errs() << "The origin of the memory location are likely to \033[32m" << originAlias << "\033[0m according to the already implemented AA.\n"
               << " -------------------------------- \n"; 
        betterResult++;
      }
#endif //COMPARE_RESULT

#ifdef QUERY_STATS
      INCR_COUNTER(ARFunc, countNotAlias, countMayAlias, countPartialAlias, countMustAlias);
#endif // QUERY_STATS

#ifdef TEST_MODREF
      ModRefInfo StoreLocModRef = AA.getModRefInfo(dyn_cast<LoadInst>(Load), 
        StoreLoc);

      ModRefInfo LoadLocModRef = AA.getModRefInfo(dyn_cast<StoreInst>(Store), 
        LoadLoc);

      errs() << "LdLoc::" << LoadLocModRef << " | StLoc::" << StoreLocModRef << " : "
             << *Load << " <-> " << *Store << '\n';
#ifdef QUERY_STATS
      INCR_COUNTER((int)StoreLocModRef, countNoModRef, countRef, countMod, countModRef);
      INCR_COUNTER((int)LoadLocModRef, countNoModRef, countRef, countMod, countModRef);
#endif // QUERY_STATS
#endif // TEST_MODREF

    }
  }

  errs() << "STATS ON FUNCTION " << F.getName() << " ---------------------------\n";

#ifdef COMPARE_RESULT
  errs() << "GraphAA result that are better than default AA result :  " << betterResult << "\n"
  		 << "Total number of queries : " << totalRequest << "\n"
  		 << "Percentgage over the total of queries : " << (int)(100 * (float)betterResult / (float)totalRequest) << "%\n";
#endif //COMPARE_RESULT

#ifdef QUERY_STATS
  errs() << "Count of may alias : " << countMayAlias << "\n";
  errs() << "Count of no alias : " << countNotAlias << "\n";
  errs() << "Count of must alias : " << countMustAlias << "\n";
  errs() << "Count of partial alias : " << countPartialAlias << "\n";

  errs() << "Count of mod : " << countMod << "\n";
  errs() << "Count of ref : " << countRef << "\n";
  errs() << "Count of modref : " << countModRef << "\n";
  errs() << "Count of nomodref : " << countNoModRef << "\n";
#endif //QUERY_STATS

  errs() << "END OF ANALYSIS OVER " << F.getName() << "-------------------\n"; 
}

PreservedAnalyses AliasTestPass::run(Module &M,
                                      ModuleAnalysisManager &AM) {
  FunctionAnalysisManager &FAM =
        AM.getResult<FunctionAnalysisManagerModuleProxy>(M).getManager();
  for(auto &F : M)
    this->iterateOnFunction(F, FAM, AM);

  return PreservedAnalyses::all();
}
