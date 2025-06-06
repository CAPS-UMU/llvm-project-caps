#ifndef LLVM_ALIAS_GRAPH_BUILDER
#define LLVM_ALIAS_GRAPH_BUILDER

#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Pass.h"

using namespace llvm;

class AliasGraphBuilder : public PassInfoMixin<AliasGraphBuilder> {
  public:
    PreservedAnalyses run(Module &M, ModuleAnalysisManager &AM);
};

#endif