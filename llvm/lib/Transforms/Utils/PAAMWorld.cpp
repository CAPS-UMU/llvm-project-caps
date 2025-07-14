//===-- PAAMWorld.cpp - Example Transformations --------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
#include "llvm/Transforms/Utils/PAAMWorld.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Metadata.h"
#include "llvm/IR/MDBuilder.h"
#include "llvm/Pass.h"
#include "llvm/Support/Regex.h"
using namespace llvm;

bool matchCallName(StringRef name, std::string &yOut, std::string &xOut) {
  // Example: may_al_3_7
  Regex re("^may_al_([0-9]+)_([0-9]+)$");
  Regex re1("^no_al([0-9]+)_([0-9]+)$");
  Regex re2("^must_al([0-9]+)_([0-9]+)$");
  SmallVector<StringRef, 3> matches;
  if (!re.match(name, &matches) && !re1.match(name, &matches) && !re2.match(name, &matches) || matches.size() < 3)
    return false;

  yOut = matches[1].str(); // store index
  xOut = matches[2].str(); // load index
  return true;
}

PreservedAnalyses PAAMWorldPass::run(Function &F, FunctionAnalysisManager &AM) {
  SmallVector<CallInst *, 4> markers;

  LLVMContext &Ctx = F.getContext();
  MDBuilder MDB(Ctx);
  // SmallVector<CallInst*, 4> toErase;
  std::vector<Instruction *> toErase;
  std::string yStr, xStr;
  std::string tag;


  for (auto &BB : F) {
    SmallVector<LoadInst*, 8> loads;
    SmallVector<StoreInst*, 8> stores;
    DenseMap<int, LoadInst*> loadIdxMap;
    DenseMap<int, StoreInst*> storeIdxMap;
    DenseMap<LoadInst*, SmallVector<std::string, 4>> loadAliasTags;

    int lIdx = 0, sIdx = 0;

    // First, number the loads/stores
    for (Instruction &I : BB) {
      if (auto *L = dyn_cast<LoadInst>(&I)) {
        loads.push_back(L);
        loadIdxMap[lIdx++] = L;
      } else if (auto *S = dyn_cast<StoreInst>(&I)) {
        stores.push_back(S);
        storeIdxMap[sIdx++] = S;
      }
    }

    // Then parse call markers
    for (Instruction &I : BB) {
      auto *call = dyn_cast<CallInst>(&I);
      if (!call) continue;

      Function *calledFunc = call->getCalledFunction();
      if (!calledFunc) continue;

      StringRef name = calledFunc->getName();

      if (!name.startswith("may_al") && !name.startswith("no_al") && !name.startswith("must_al"))
        continue;

      // Parse format: kind_storeIdx_loadIdx
      std::string nameStr = name.str();
      std::string kind;
      int sIndex = -1, lIndex = -1;
      
      if (nameStr.compare(0, 7, "may_al_") == 0) {
        kind = "may_al";
        if (sscanf(nameStr.c_str(), "may_al_%d_%d", &sIndex, &lIndex) == 2) {
          // valid format
        }
      } else if (nameStr.compare(0, 7, "must_al") == 0) {
        kind = "must_al";
        if (sscanf(nameStr.c_str(), "must_al%d_%d", &sIndex, &lIndex) == 2) {
          // valid format
        }
      } else if (nameStr.compare(0, 5, "no_al") == 0) {
        kind = "no_al";
        if (sscanf(nameStr.c_str(), "no_al%d_%d", &sIndex, &lIndex) == 2) {
          // valid format
        }
      }
      
      if (!kind.empty()) {
        auto *LI = loadIdxMap.lookup(lIndex);
        if (LI) {
          std::string tag = kind + ".store." + std::to_string(sIndex);
          loadAliasTags[LI].push_back(tag);
        }
        toErase.push_back(call); // Mark for deletion after loop
      }
      
    }

    // Attach metadata to each load
    for (auto &entry : loadAliasTags) {
      LoadInst *LI = entry.first;
      const auto &tags = entry.second;
    
      std::vector<Metadata *> mdElems;
      for (const std::string &tag : tags) {
        mdElems.push_back(MDString::get(Ctx, tag));
      }
    
      MDNode *mdNode = MDNode::getDistinct(Ctx, mdElems);
      LI->setMetadata("aliasinfo", mdNode);
    }
  }
  for (Instruction *I : toErase)
    I->eraseFromParent();

  return PreservedAnalyses::all();
}
