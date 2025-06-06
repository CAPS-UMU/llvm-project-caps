#include "llvm/Analysis/AliasGraphBuilder.h"
#include "llvm/ADT/SetVector.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Analysis/AliasGraph.h"
#include "llvm/Analysis/BlockFrequencyInfo.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/GlobalAlias.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
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

AliasGraph *GLOBAL_GRAPH = nullptr;

void buildGlobalAliasGraph(Module &M) {
  GLOBAL_GRAPH = new AliasGraph();

  for(Function &F : M)
    for(BasicBlock &B : F)
      for(Instruction &I : B) {
        LLVM_DEBUG(errs() << "Handling instruction : " << I);
        HandleInst(&I, GLOBAL_GRAPH);
        LLVM_DEBUG(
          for(auto [value, node] : GLOBAL_GRAPH->NodeMap) {
            if (auto ival = dyn_cast<Instruction>(value))
              if (ival->getOpcode() == I.getOpcode()) 
                errs() << " : Instruction put in graph.";
          }
          errs() << "\n";
        );
      }
  LLVM_DEBUG(
          errs() << "Final Alias Graph {\n\n";
          std::set<AliasNode*> printedNode;
          int nodeCount = 0;
          for(auto [value, node] : GLOBAL_GRAPH->NodeMap) {
            if ( ! printedNode.count(node)) {
              errs() << "Node " << nodeCount++ << " : ";
              node->print_set();
              errs() << "\n";
              printedNode.insert(node);
            }
          }
          errs() << "}\n\n"
  );
}

void writingAliasGraphToDot() {
  std::string Filename = "aliasgraph.dot";
  errs() << "Writing '" << Filename << "'...\n";

  std::error_code EC;
  raw_fd_ostream File(Filename, EC, sys::fs::OF_Text);

  if (EC) {
    errs() << " error opening file : '" << Filename << "'for writing! Returning from '" << __func__ << "'\n";
    return;
  }

  File << "digraph AliasGraph {\n";

  std::map<AliasNode*, std::string> writtenNodes;
  int nodeCount = 0;

#define WRITE_IFN_WRITTEN(node) do { \
  if (writtenNodes.find(node) == writtenNodes.end()) { \
    std::string name = std::string("N"+to_string(++nodeCount)); \
    node->writeToDot(File, name); \
    writtenNodes[node] = name; \
  } \
} while(false)

  for(auto [_, node] : GLOBAL_GRAPH->NodeMap) {
    WRITE_IFN_WRITTEN(node);
  }

  for(auto [n1, n2] : GLOBAL_GRAPH->ToNodeMap) {
    WRITE_IFN_WRITTEN(n1);
    WRITE_IFN_WRITTEN(n2);
    File << writtenNodes[n1] << " -> " << writtenNodes[n2] << " ; \n";
  }
#undef WRITE_IFN_WRITTEN

  File << "}\n";
  File.close();
}

PreservedAnalyses AliasGraphBuilder::run(Module &M, ModuleAnalysisManager &AM) {
  buildGlobalAliasGraph(M);
  writingAliasGraphToDot();
  return PreservedAnalyses::all();
}