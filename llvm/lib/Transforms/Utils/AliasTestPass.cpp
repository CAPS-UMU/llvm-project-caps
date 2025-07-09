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
#include "llvm/Analysis/BasicAliasAnalysis.h"
#include "llvm/Analysis/GlobalsModRef.h"
#include "llvm/Analysis/MemoryLocation.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalAlias.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/PassManager.h"
#include "llvm/IR/Value.h"
#include "llvm/Pass.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/DynamicLibrary.h"
#include "llvm/Support/FormatVariadic.h"
#include "llvm/Support/ModRef.h"
#include "llvm/Support/ScopedPrinter.h"
#include "llvm/Support/raw_ostream.h"
#include <vector>

using namespace llvm;
#define DEBUG_TYPE "caps-alias-pass"

//#define QUERY_STATS
//#define TEST_MODREF
#define COMPARE_RESULT
//#define CALL_MODREF
#define SIMPLE_EVAL
//#define TEST_ALL_MEMLOC

#define INCR_COUNTER(result, cpt1, cpt2, cpt3, cpt4) do { \
  switch(result) { \
    case 0: cpt1++; break; \
    case 1: cpt2++; break; \
    case 2: cpt3++; break; \
    case 3: cpt4++; break; \
  } \
} while(false)

#define PROP(n, m) ((m != 0) ? (int)(100. * (float)n / (float)m) : 0)

// Check if a Value is a null op or a null ptr
bool isNull(const Value * V) {
  if(auto * cst = dyn_cast<Constant>(V))
    return cst->isNullValue();
  return false;
}

// Return true if the 2 given function have the equivalent signatures
// based on func name and argument type comparison
bool EqSignatures(const Function * F1, const Function * F2) {
  if(F1->getNumOperands() != F2->getNumOperands())
    return false;

  bool res = F1->getName().equals(F2->getName());
  auto * itArgF1 = F1->arg_begin();
  auto * itArgF2 = F2->arg_begin();
  while(res && itArgF1 != F1->arg_end() && itArgF2 != F2->arg_end()) {
    res = res && itArgF1->getType()->getTypeID() == itArgF2->getType()->getTypeID();
    itArgF1++;
    itArgF2++;
  }

  return res && itArgF1 == F1->arg_end() && itArgF2 == F2->arg_end();
}

// Check if the first function calls the other
// return 0 if it is sure to not call, 1 if sure to call, -1 if can't say
// gives the pointer to the callsite if any
int isCaller(const Function * F1, const Function * F2,
                      CallInst * &callsite) {
  bool hasIndirectCall = false;
  for(auto &block : *F1) for(auto &instr : block) {
    if(auto * callinst = dyn_cast<CallInst>(&instr)){
      auto * callee = callinst->getCalledFunction();
      if(callee && EqSignatures(F2, callee)) {
        callsite = const_cast<CallInst*>(callinst);
        return 1;
      }
      hasIndirectCall = true;
    }
  }

  callsite = nullptr;
  return (hasIndirectCall) ? -1 : 0;
}

// Getting all the found memory 
// location inside the given function
SetVector<Value*> getPointers(const Function &F) {
  SetVector<Value*> Ptrs;

  for(auto * arg = F.arg_begin(); arg != F.arg_end(); arg++)
    if(arg->getType()->isPtrOrPtrVectorTy() && !arg->getType()->isFunctionTy()) {
      Ptrs.insert(const_cast<Argument*>(arg));
    }

  for(auto &B : F) {
    for(auto &I : B) {
      if (I.getType()->isPointerTy()) {
          Ptrs.insert(const_cast<Instruction*>(&I));
      }
    
      for (auto &Op : I.operands()) {
        Value *v = Op.get();
        if (v->getType()->isPointerTy()) {
          if(auto *f=dyn_cast<Function>(v)) continue;
          Ptrs.insert(v);
        }
      }
    }
  }

  for(auto * v : Ptrs) errs() << "Ptrs : " << *v << "\n";
  return Ptrs;
}

// Get the memory manipulating instruction from the IR
struct MemInstSets AliasTestPass::getMemInstr(Function &F) {
  SetVector<LoadInst *>   Loads;
  SetVector<StoreInst *>  Stores;
  SetVector<AllocaInst *> Allocs;
  SetVector<CallInst *>   Calls;

  for(BasicBlock &BB : F) 
    for (Instruction &Inst : BB)
      if (auto *LI = dyn_cast<LoadInst>(&Inst))
        Loads.insert(LI);
      else if (auto *SI = dyn_cast<StoreInst>(&Inst))
        Stores.insert(SI);
      else if (auto *AI = dyn_cast<AllocaInst>(&Inst))
        Allocs.insert(AI);
      else if(auto *CAI = dyn_cast<CallInst>(&Inst))
        Calls.insert(CAI);
  
  return {Loads, Stores, Allocs, Calls};
}

// Get the potential parent of a Value
// we are in particular interested in the value being an instruction / func arg
const Function * getValueFunction(const Value * V) {
  if(auto * instr = dyn_cast<Instruction>(V))
    return instr->getParent()->getParent();
  if(auto * arg = dyn_cast<Argument>(V))
    return arg->getParent();

  return nullptr;
}

// Try to determine if two pointers from different functions can be 
// alias using the default AA pipeline.
AliasResult AliasTestPass::aliasInterp(const Value * V1, const Value * V2, AliasAnalysis &defaultAA) {
  if(isNull(V1) || isNull(V2)) return AliasResult::NoAlias;

  auto * F1 = getValueFunction(V1);
  assert(F1 != nullptr);
  auto * F2 = getValueFunction(V2);
  assert(F2 != nullptr);

  // if the two values are used in the same function apply the default AA pipeline
  if(EqSignatures(F1, F2)) return defaultAA.alias(V1, V2);

  // if the parent function cannot call to one another :
  if(F1->getNumUses() == 0 && !F1->hasAddressTaken() &&
     F2->getNumUses() == 0 && !F2->hasAddressTaken()) {
    // At least one of the functions is not used at all, the pointers can't alias.
    // Still, it could be a call by interruption, in an OS Kernel for instance,
    // then if a glb variable is used in both function there could be an alias relation ?
    return AliasResult::NoAlias;
  }
  
  const Function * caller; // calling function
  const Value * callParam; // pointer used as a parameter by the calling function
  const Function * called; // called function
  const Value * calledVal; // pointer used inside the called function
  CallInst * callsite;     // call site for the called func in the caller func

  // Determine which function is the caller and which is the called one
  CallInst * CSinF1, * CSinF2;
  int F1callF2 = isCaller(F1, F2, CSinF1);
  int F2callF1 = isCaller(F2, F1, CSinF2);
  if(F1callF2 == -1 && F2callF1 == -1) 
    // can't be sure that one func call the other, can't determine the alias relationship
    return AliasResult::MayAlias;
  
  if((!F1callF2 && !F2callF1) || (F1callF2 == -1 && !F2callF1)
    || (!F1callF2 && F2callF1 == -1))
    // we are sure that the two function cannot call one another
    return AliasResult::NoAlias;

  if(F1callF2 == 1) { // F1 is the caller
    caller = F1; called = F2;
    callParam = V1; calledVal = V2;
    callsite = CSinF1;
  } else {  // F2 is the caller
    caller = F2; called = F1;
    callParam = V2; calledVal = V1;
    callsite = CSinF2;
  }

  assert(callsite != nullptr);
  // We must find if the value in the caller function is used as a parameter of the called function 
  auto it = callsite->arg_begin();
  auto paramName = callParam->getNameOrAsOperand();

  LLVM_DEBUG(dbgs() << "Iterating through callsite "<< *callsite 
                    << " ; Looking for " << paramName << " : " << *callParam << " in the call parameters :\n");

  bool usedByCall = it->get()->getNameOrAsOperand() == paramName;
  while(it != callsite->arg_end() && !usedByCall) {
    LLVM_DEBUG(dbgs() << "id : " << it->get()->getNameOrAsOperand() 
                      << " : " << *it->get() << "\n");
    usedByCall = (it->get()->getNameOrAsOperand() == paramName);
    if(!usedByCall) it++;
    LLVM_DEBUG(if(usedByCall) dbgs() << "Param found in the call\n");
  }

  if (!usedByCall || called->getMemoryEffects().doesNotAccessMemory())
    // If the value in the caller function isn't used in the call, or 
    // if the called function does not modify memory, then it won't alias any 
    // pointer inside the called function
    return AliasResult::NoAlias;

  // if we couldn't tell from context information of the function, we have to know
  // if the value in the called function alias with the argument that was given the value
  // of the caller function
  auto const * Arg = called->getArg(it->getOperandNo());

  LLVM_DEBUG(dbgs() << paramName << " matches argument : " << *Arg << '\n');
  if(Arg->onlyReadsMemory()) return AliasResult::NoAlias;
  return defaultAA.alias(Arg, calledVal);
}

// Check if the origin nodes of the 2 memory location don't alias in the alias graph, according
// to the given alias analysis object.
AliasResult AliasTestPass::tryAliasOrigin(const MemoryLocation &LocA, const MemoryLocation &LocB, 
                                  AliasGraph &graph, AliasAnalysis &AA) {
  AliasNode * node1 = graph.retraceOrigin(LocA);
  AliasNode * node2 = graph.retraceOrigin(LocB);

  if(*node1 == *node2) return AliasResult::MustAlias;

  int no=0,may=0,part=0,must=0,total=0;

  for(auto * ptrN1 : *node1) {
    for(auto * ptrN2 : *node2) {
      AliasResult AAR = aliasInterp(ptrN1, ptrN2, AA);

      if(AAR == AliasResult::MustAlias) {
        auto infoPTN1 = to_string(*ptrN1);
        if(auto * arg = dyn_cast<Argument>(ptrN1))
          infoPTN1 = "{func["+arg->getParent()->getName().str()+"]; arg["+arg->getNameOrAsOperand()+"]}";

        errs() << "\033[31m Checking the origin of : " << *LocA.Ptr
               << AAR << " found between : " << infoPTN1 << " <--> " << *ptrN2;
        node1->print_set();
        node2->print_set();
        errs() << " \033[0m\n";
      }
      INCR_COUNTER(AAR, no, may, part, must);
      total++;
    }
  }

  errs() << "Over the two node's origin : no="<<no<<"/may="<<may<<"/part="<<part<<"/must="<<must<<"/total="<<total<<"\n";
  if(must > 0) return AliasResult::MustAlias;
  if(part > 0) return AliasResult::PartialAlias;
  
  return (may > no) ? AliasResult::MayAlias : AliasResult::NoAlias;
}

// execute the alias analysis on a function and display different result
// according to what macro is enabled/defined
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
  for (auto *Load : Sets.Loads) {
     MemoryLocation LoadLoc = MemoryLocation::get(Load);

#ifdef CALL_MODREF
    for (auto *Call : Sets.Calls){
      ModRefInfo MRIAA = AA.getModRefInfo(Load, Call);
      ModRefInfo MRIGraphAA = GraphAAR.getModRefInfo(Call, LoadLoc, SimpleAAQI);

      errs() << " In func " << Call->getParent()->getName() << " : " 
            << *Call << " : " << MRIAA << " ~ " << MRIGraphAA << " : " << *Load << "\n";
    }

#else
    for (auto *Store : Sets.Stores) {
      MemoryLocation StoreLoc = MemoryLocation::get(Store);
    
      AliasResult ARFunc = AA.alias(LoadLoc, StoreLoc);
	    totalRequest++;

#ifdef COMPARE_RESULT
      AliasResult ARModule = GraphAAR.alias(LoadLoc, StoreLoc, SimpleAAQI, nullptr);
      AliasResult ARGlob = GlobalsAAR.alias(LoadLoc, StoreLoc, SimpleAAQI, nullptr);

      if(betterAliasResult(ARModule, ARFunc)) {
        errs() << "\n ----------------------\n Values : \n" << *Load << " <--> " << *Store << " ]\n";
        AliasResult originAlias = tryAliasOrigin(LoadLoc, StoreLoc, GraphAAR.getGraph(), AA);  
        errs() << "Are said to be : [" << ARFunc << "] according to AA default pipeline | "
              << "[" << ARModule << "] according to GraphAA | " 
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
#endif // CALL_MODREF
  }

  errs() << "STATS ON FUNCTION " << F.getName() << " ---------------------------\n";

#ifdef COMPARE_RESULT
  errs() << "GraphAA result that are better than default AA result :  " << betterResult << "\n"
  		 << "Total number of queries : " << totalRequest << "\n"
  		 << "Percentgage over the total of queries : " 
       << ((!totalRequest)? 0 : 
          (int)(100 * (float)betterResult / (float)totalRequest)) << "%\n";
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

// Test between all the pair of memory location found in each function
void pairEvaluate(Function &F, ModuleAnalysisManager &MAM,
                  FunctionAnalysisManager &FAM) {
  if(F.empty()) return;

  AliasAnalysis &AA = FAM.getResult<AAManager>(F);
  GraphAAResult &GraphAAR = MAM.getResult<GraphAA>(*(F.getParent()));
  SimpleAAQueryInfo SimpleAAQI (AA);

  SetVector<Value*> Ptrs = getPointers(F);

  errs() << "// *************************************************************************** //\n"
         << " IN FUNCTION : " << F.getName() << "\n"
         << "// *************************************************************************** //\n";
  for(auto * ptr1 : Ptrs) {
    for(auto * ptr2 : Ptrs) {
      AliasResult GrAR = GraphAAR.alias(
          MemoryLocation(ptr1, LocationSize::beforeOrAfterPointer()), 
          MemoryLocation(ptr2, LocationSize::beforeOrAfterPointer()), 
          SimpleAAQI, nullptr);
      AliasResult DefAR = AA.alias(ptr1, ptr2);

      assert(
        (GrAR != AliasResult::NoAlias) || (DefAR != AliasResult::MustAlias && DefAR != AliasResult::PartialAlias)
        && "Contradiction in results between graph-aa and default-aa-pipeline."
      );
      AliasResult AAR = (GrAR == AliasResult::NoAlias) ? GrAR : DefAR;

      errs() << "alias ( " << *ptr1 << ", \n"
             << "        " << *ptr2 << ") = \033[32m" << AAR << "\033[0m;\n"
             << "//===-------------------------------------------------------------------==//\n";
    }
  }
}

//////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////
std::vector<unsigned int> defCounts      (5,0);
std::vector<unsigned int> basicCounts    (5,0);
std::vector<unsigned int> graphCounts    (5,0);
std::vector<unsigned int> graphDefCounts (5,0);

#define PRINT_STAT(aa_name, counts) do { \
    errs() << "Result of " << aa_name << " query on loads and store : \n" \
        << "Total query performed : " << counts[4] << "\n" \
        << "NoAlias : " << counts[0] << "; MayAlias :" << counts[1]  \
        << "; PartialAlias : " << counts[2] << "; MustAlias : " << counts[3] << "\n"; \
   \
    if(counts[4]!=0) { \
      errs() << "Part in percent : no=" << PROP(counts[0], counts[4]) << "%/"  \
             << "may=" << PROP(counts[1], counts[4]) << "%/" \
             << "part=" << PROP(counts[2], counts[4]) << "%/" \
             << "must=" << PROP(counts[3], counts[4]) << "%\n" \
             << " // -------------------------------------------------- //\n"; \
    } \
} while(false)


// Simple evaluation of the alias pipeline
void AliasTestPass::evaluate(Function &F, FunctionAnalysisManager &FAM, 
                            ModuleAnalysisManager &MAM,
                            std::vector<unsigned int> &counts){
  if(F.empty()) return;

  AliasAnalysis &DefAAPipeline = FAM.getResult<AAManager>(F);
  BasicAAResult &BasicAAR = FAM.getResult<BasicAA>(F);
  GraphAAResult &GraphAAR = MAM.getResult<GraphAA>(*(F.getParent()));

  SimpleAAQueryInfo SimpleAAQI (DefAAPipeline);

  struct MemInstSets Sets = getMemInstr(F);
  for(auto * Load : Sets.Loads){
    MemoryLocation LoadLoc = MemoryLocation::get(dyn_cast<LoadInst>(Load));
    
    for(auto * Store : Sets.Stores){
      MemoryLocation StoreLoc = MemoryLocation::get(dyn_cast<StoreInst>(Store));
      AliasResult GrAR = GraphAAR.alias(LoadLoc, StoreLoc, SimpleAAQI, nullptr);
      AliasResult BasAR = BasicAAR.alias(LoadLoc, StoreLoc, SimpleAAQI, nullptr);
      AliasResult DefAR = DefAAPipeline.alias(LoadLoc, StoreLoc);

      assert(
        (GrAR != AliasResult::NoAlias) || (DefAR != AliasResult::MustAlias && DefAR != AliasResult::PartialAlias)
        && "Contradiction in results between graph-aa and default-aa-pipeline."
      );
      AliasResult GraphDefAR = (GrAR == AliasResult::MayAlias) ? DefAR : GrAR;
      
      defCounts[(int)DefAR]++; defCounts[4]++;
      basicCounts[(int)BasAR]++; basicCounts[4]++;
      graphCounts[(int)GrAR]++; graphCounts[4]++;
      graphDefCounts[(int)GraphDefAR]++; graphDefCounts[4]++;
    }
  }

  errs() << "In function : \033[31m" << F.getName() << "\033[0m \n";
  PRINT_STAT("\033[32mSTANDALONE GRAPH AA\033[0m", graphCounts);
  PRINT_STAT("\033[32mSTANDALONE BASIC AA\033[0m", basicCounts);
  PRINT_STAT("\033[32mDEFAULT AA PIPELINE\033[0m", defCounts);
  PRINT_STAT("\033[32mGRAPH AA CHAINED WITH DEF PIPELINE\033[0m", graphDefCounts);
  errs() << "//====================================================================//\n\n";
}

// ---------------------------------------------
PreservedAnalyses AliasTestPass::run(Module &M,
                                      ModuleAnalysisManager &AM) {
  FunctionAnalysisManager &FAM =
        AM.getResult<FunctionAnalysisManagerModuleProxy>(M).getManager();
  
  /* Triple ModuleTriple(M.getTargetTriple());
  auto * TLII = new TargetLibraryInfoImpl(ModuleTriple);
  auto * TLI = new TargetLibraryInfo(*TLII); */

  std::vector<unsigned int> counts (5, 0);
  for(auto &F : M) {
#ifdef SIMPLE_EVAL
    this->evaluate(F, FAM, AM, counts);
#elif defined(TEST_ALL_MEMLOC)
    pairEvaluate(F, AM, FAM);
#else
    this->iterateOnFunction(F, FAM, AM);
#endif //SIMPLE_EVAL
  }

  return PreservedAnalyses::all();
}
