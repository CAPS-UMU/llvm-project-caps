#include "llvm/Analysis/AliasGraphBuilder.h"
#include "llvm/ADT/SetVector.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Analysis/AliasGraph.h"
#include "llvm/Analysis/BlockFrequencyInfo.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalAlias.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Operator.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/GraphWriter.h"

#include "llvm/Support/FileSystem.h"
#include "llvm/Support/raw_ostream.h"
#include <set>
#include <string>

#define DEBUG_TYPE "graphbuilder-aa"

using namespace llvm;

AliasGraph *AG = nullptr;

void buildGlobalAliasGraph(Module &M) {
  AG = new AliasGraph(M);

  LLVM_DEBUG(
    errs() << "Final Alias Graph {\n\n";
    std::set<AliasNode*> printedNode;
    int nodeCount = 0;
    for(auto [value, node] : AG->NodeMap) {
      if ( ! printedNode.count(node)) {
        errs() << "Node " << ++nodeCount << " : ";
        node->print_set();
        errs() << "\n";
        printedNode.insert(node);
      }
    }
    errs() << "}\n\n"
  );
}

void outputInstructionMetadata(Module &M) {
  SmallVector<std::pair<unsigned int, MDNode *>> MDs;
  errs()<< "//===----------------------------------------------==//\n" 
        << "DISPLAYING METADATA ON INSTRUCTIONS -----------------\n"
        << "//===----------------------------------------------==//\n";

  for(auto &F : M)
    for(auto &B : F)
      for(auto &I : B) {
        auto AAMD = I.getAAMetadata();
        if(!AAMD.NoAlias && !AAMD.Scope && !AAMD.TBAA && !AAMD.TBAAStruct) continue;
        errs() << I << " ; \n";
        if(AAMD.NoAlias) { 
          errs() << "no_alias MD : "; 
          AAMD.NoAlias->printTree(errs(), &M);
          errs() << "\n";
        }
        if(AAMD.Scope) { 
          errs() << "scope MD : "; 
          AAMD.Scope->printTree(errs(), &M);
          errs() << "\n";
        }
        if(AAMD.TBAA) { 
          errs() << "tbaa MD : "; 
          AAMD.TBAA->printTree(errs(), &M);
          errs() << "\n";
        }
        if(AAMD.TBAAStruct) { 
          errs() << "tbaa_struct MD : "; 
          AAMD.TBAAStruct->printTree(errs(), &M);
          errs() << "\n";
        }
        errs() << "// -------------------------------------------- //\n";
      }
}

PreservedAnalyses AliasGraphBuilder::run(Module &M, ModuleAnalysisManager &AM) {
  buildGlobalAliasGraph(M);
  AG->writeToDot("aliasgraph.dot");

  outputInstructionMetadata(M);
  return PreservedAnalyses::all();
}