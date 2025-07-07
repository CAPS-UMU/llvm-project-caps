#include <cstddef>
#include <cstdlib>
#include <llvm/IR/Function.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/LegacyPassManager.h>
#include <utility>
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SetVector.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/IR/Argument.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Value.h"
#include "llvm/InitializePasses.h"

#include "llvm/Analysis/AliasGraph.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/BasicAliasAnalysis.h"
#include "llvm/Analysis/MemoryLocation.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Pass.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/ModRef.h"
#include "llvm/Support/ScopedPrinter.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;
using namespace std;

#define DEBUG_TYPE "alias-graph-aa"

// Build the alias graph upon a module
AliasGraph::AliasGraph(Module &M) {
    NodeMap.clear();
    ToNodeMap.clear();
    FromNodeMap.clear();
    Is_Analyze_Success = true;
    failreason = none;
    AnalyzedFuncSet.clear();
    this->M = &M;

    set<Function *> uncalledFunctions;

    for(Function &F : M) 
        if (F.use_empty())
            uncalledFunctions.insert(&F);
    
    for(Function * F : uncalledFunctions) {
        errs() << "Analyzing function : " << F->getName() << "\n";
        this->analyzeFunction(F);
    }
}

//Merge n1 into n2
void AliasGraph::mergeNode(AliasNode* n1, AliasNode* n2){

    if(*n1 == *n2)    
        return;

    //First merge node values
    for(auto it = n1->aliasclass.begin(); it != n1->aliasclass.end(); it++){
        Value* v = *it;
        n2->insert(v);
        this->NodeMap[v] = n2;
    }
    n1->aliasclass.clear();

    //Then change edges
    if(this->ToNodeMap.count(n1)){
        AliasNode* n1_toNode = this->ToNodeMap[n1];

        if(this->ToNodeMap.count(n2)){
            AliasNode* n2_toNode = this->ToNodeMap[n2];

            //n1 and n2 point to the same node
            //This cannot happen because one node only has one pre and post node in field-sensitive analysis,
            //but it could occur in field-insensitive analysis
            if(n1_toNode != n2_toNode){
                this->ToNodeMap.erase(n1);
                this->ToNodeMap.erase(n2);
                this->FromNodeMap.erase(n1_toNode);
                this->FromNodeMap.erase(n2_toNode);
                mergeNode(n1_toNode, n2_toNode);
                this->ToNodeMap[n2] = n2_toNode;
                this->FromNodeMap[n2_toNode] = n2;
            }
        }else{
            this->ToNodeMap.erase(n1);
            this->ToNodeMap[n2] = n1_toNode;
            this->FromNodeMap[n1_toNode] = n2;
        }
    }

    //Check which node points to n1
    if(this->FromNodeMap.count(n1)){
        AliasNode* n1_fromNode = this->FromNodeMap[n1];

        if(this->FromNodeMap.count(n2)){
            AliasNode* n2_fromNode = this->FromNodeMap[n2];

            if(n1_fromNode != n2_fromNode){
                this->FromNodeMap.erase(n1);
                this->FromNodeMap.erase(n2);
                this->ToNodeMap.erase(n1_fromNode);
                this->ToNodeMap.erase(n2_fromNode);
                mergeNode(n1_fromNode, n2_fromNode);
                this->FromNodeMap[n2] = n2_fromNode;
                this->ToNodeMap[n2_fromNode] = n2;
            }
        }else{ //n2 has no pre node
            this->FromNodeMap.erase(n1);
            this->FromNodeMap[n2] = n1_fromNode;
            this->ToNodeMap[n1_fromNode] = n2;
        }
    }
}

AliasNode * AliasGraph::getNode(Value *V){
    //Use a map to speed up query
    if(this->NodeMap.count(V))
        return this->NodeMap[V];

    return nullptr;
}

AliasNode * AliasGraph::getNode(const MemoryLocation &MemLoc){
    LLVM_DEBUG(
        dbgs() << "Getting node of : "; 
        MemLoc.Ptr->printAsOperand(dbgs());
        dbgs() << "\n"
    );
    
    auto entry = this->NodeMap.find(const_cast<Value*>(MemLoc.Ptr));
    if(entry != this->NodeMap.end()) {
        LLVM_DEBUG(dbgs() << "\t -> From instruction : " << *entry->first << "\n");
        return entry->second;
    }

    return nullptr;
}

// From the alias node matching the given memory location,
// gets the node's "origin" (i.e its parent without parent) in the graph
AliasNode * AliasGraph::retraceOrigin(const MemoryLocation &MemLoc) {
    AliasNode * node = this->getNode(MemLoc);
    if(node == nullptr) return nullptr;

    AliasNode * parent = nullptr;
    auto it = FromNodeMap.find(node);
    while(it != FromNodeMap.end()) {
        parent = it->second;
        it = FromNodeMap.find(parent);
    }

    if (parent == nullptr) return node;
    return parent;
}

// Return a partition of the alias class over the function
// to which the instruction belongs
DenseMap<Function*, SetVector<Value*>> AliasNode::partitionOverFunctions() {
    DenseMap<Function*, SetVector<Value*>> mapping;
    for (auto * val : aliasclass) {
        auto * instr = dyn_cast<Instruction>(val);
        auto * arg = dyn_cast<Argument>(val);
        if(! (instr || arg)) continue;

        Function * func = (instr) ?
            instr->getParent()->getParent() : arg->getParent();
        if(mapping.count(func) == 0) 
            mapping.insert(std::pair<Function*, SetVector<Value*>> (func, SetVector<Value*>()));
        mapping[func].insert(val);
    }
    return mapping;
}

//merge S2 into S1
void valueSetMerge(set<Value*> &S1, set<Value*> &S2){
	for(auto v : S2)
		S1.insert(v);
}

unsigned getArgIndex(Function* F, Argument *Arg){

    unsigned index = 0;
    for(auto it = F->arg_begin(); it != F->arg_end(); it++){
        Value* F_arg = it;
        if(Arg == F_arg){
            break;
        }
        index++;
    }

    return index;
}

unsigned getMin(unsigned n1, unsigned n2){
    if(n1 < n2)
        return n1;
    else
        return n2;
}


bool AliasGraph::checkNodeConnectivity(AliasNode* node1, AliasNode* node2){

    if(!node1 || !node2)
        return false;

	list<AliasNode *>LN; // list of node to explore
	LN.push_back(node1);
	set<AliasNode *> PN; //Global value set to avoid loop
	PN.clear();

	while (!LN.empty()) {
		AliasNode *CN = LN.front();
		LN.pop_front();

		if (PN.find(CN) != PN.end()){ 
			// if CN in PN, go to next iteration
            // as this node have already been explored
            continue;
		}
		PN.insert(CN);

        if(CN == node2) 
            // if we found the other node during 
            // exploration then the 2 nodes are connected
            return true;

        // Check if CN is connected to other node and 
        // add them to the list of potential successor
		if(this->ToNodeMap.count(CN)){
			LN.push_back(this->ToNodeMap[CN]);
		}

		if(this->FromNodeMap.count(CN)){
			LN.push_back(this->FromNodeMap[CN]);
		}
	}

    return false;
}

/// INTERPROCEDURAL ALIAS ANALYSIS
int instrCount = 0; // for debug only
void AliasGraph::analyzeFunction(Function* F){
    if(!F) return;
    //testing what happens if a function is analyzed several times
    LLVM_DEBUG(errs() << "Analyzing function " << F->getName() << "\n"); 

    for (inst_iterator i = inst_begin(F), ei = inst_end(F); i != ei; ++i) {
      Instruction *iInst = dyn_cast<Instruction>(&(*i));
      this->HandleInst(iInst);
      LLVM_DEBUG(writeToDot("aliasgraph"+itostr(instrCount++)+".dot"));
    }
}

/// INSTRUCTION HANDLER
/// Get called function name of V.
StringRef getCalledFuncName(CallInst *CI) {

  	Value *V;
	V = CI->getCalledOperand();
	assert(V);

	if (InlineAsm *IA = dyn_cast<InlineAsm>(V))
		return StringRef(IA->getAsmString());

	User *UV = dyn_cast<User>(V);
	if (UV && UV->getNumOperands() > 0) {
		Value *VUV = UV->getOperand(0);
		return VUV->getName();
	}

	return V->getName();
}

void AliasGraph::HandleOperator(Value* v){
    GEPOperator *GEPO = dyn_cast<GEPOperator>(v);
    if(GEPO){
        this->HandleGEP(GEPO);
        this->HandleOperator(GEPO->getOperand(0));
    }

    BitCastOperator *CastO = dyn_cast<BitCastOperator>(v);
    if(CastO){
        this->HandleMove(CastO, CastO->getOperand(0));
        this->HandleOperator(CastO->getOperand(0));
    }

    PtrToIntOperator *PTIO = dyn_cast<PtrToIntOperator>(v);
    if(PTIO){
        this->HandleMove(PTIO, PTIO->getOperand(0));
        this->HandleOperator(PTIO->getOperand(0));
    }
}

void AliasGraph::HandleInst(Instruction* I){
    // Handle GEP and Cast operator
    // Arguments of a call are also caught here
    for(unsigned int i = 0; i < I->getNumOperands(); i++){
        Value* op = I->getOperand(i);
        this->HandleOperator(op);
    }

    //Handle target instruction
    AllocaInst* ALI = dyn_cast<AllocaInst>(I);
    if(ALI){
        this->HandleAlloc(ALI);
        return;
    }

    StoreInst *STI = dyn_cast<StoreInst>(I);
    if(STI){
        this->HandleStore(STI);
        return;
    }

    LoadInst* LI = dyn_cast<LoadInst>(I);
    if(LI){
        this->HandleLoad(LI);
        return;
    }

    GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(I);
    if(GEP){
        this->HandleGEP(GEP);
        return;
    }

    BitCastInst *BCI = dyn_cast<BitCastInst>(I);
    ZExtInst *ZEXI = dyn_cast<ZExtInst>(I);
    SExtInst *SEXI = dyn_cast<SExtInst>(I);
    TruncInst *TRUI = dyn_cast<TruncInst>(I);
    IntToPtrInst *ITPI = dyn_cast<IntToPtrInst>(I);
    PtrToIntInst *PTII = dyn_cast<PtrToIntInst>(I);
    if(BCI || ZEXI || SEXI || TRUI || ITPI || PTII){
        auto op = I->getOperand(0);
        this->HandleMove(I, op);
        return;
    }

    PHINode *PHI = dyn_cast<PHINode>(I);
    if(PHI){
        for (unsigned i = 0, e = PHI->getNumIncomingValues(); i != e; ++i){
            Value *IV = PHI->getIncomingValue(i);
            this->HandleMove(I, IV);
        }
        return;
    }

    SelectInst *SLI = dyn_cast<SelectInst>(I);
    if(SLI){
        auto TV = SLI->getTrueValue();
        auto FV = SLI->getFalseValue();
        this->HandleMove(I, TV);
        this->HandleMove(I, FV);
        return;
    }

    CallInst *CAI = dyn_cast<CallInst>(I);
    if(CAI){
        this->HandleCai(CAI);
        return;
    }

    ReturnInst *RI = dyn_cast<ReturnInst>(I);
    if(RI){
        Value* return_v = RI->getReturnValue();
        if(return_v == nullptr)
            return;
        
        if(isa<ConstantData>(return_v))
            return;
            
        this->HandleMove(I, return_v);
    }

}

// p1 = alloc(size)
void AliasGraph::HandleAlloc(AllocaInst* ALI){
    
    if(getNode(ALI) == nullptr){
        auto node = new AliasNode();
        node->insert(ALI);
        this->NodeMap[ALI] = node;
    }
}

// v1 = *v2
void AliasGraph::HandleLoad(LoadInst* LI){
    
    AliasNode* node1 = getNode(LI);
    if(node1 == nullptr){
        node1 = new AliasNode();
        node1->insert(LI);
        this->NodeMap[LI] = node1;
    }

    Value* op = LI->getOperand(0);
    AliasNode* node2 = getNode(op);
    if(node2 == nullptr){
        node2 = new AliasNode();
        node2->insert(op);
        this->NodeMap[op] = node2;
    }

    //node2 has pointed to some nodes
    if(this->ToNodeMap.count(node2)){
        AliasNode* node2_toNode = this->ToNodeMap[node2];
        this->mergeNode(node1 ,node2_toNode);
    }
    //For load, this usually does not happen
    else if(this->FromNodeMap.count(node1)){
        AliasNode* node1_fromNode = this->FromNodeMap[node1];
        this->mergeNode(node1_fromNode, node2);
    }
    else{
        this->ToNodeMap[node2] = node1;
        this->FromNodeMap[node1] = node2;
    }
}

// *v2 = v1
void AliasGraph::HandleStore(StoreInst* STI){
    
    //store vop to pop
    Value* vop = STI->getValueOperand(); //v1
    Value* pop = STI->getPointerOperand(); //v2

    if(isa<ConstantData>(vop))
        return;

    AliasNode* node1 = getNode(vop);
    if(node1 == nullptr){
        node1 = new AliasNode();
        node1->insert(vop);
        this->NodeMap[vop] = node1;
    }

    AliasNode* node2 = getNode(pop);
    if(node2 == nullptr){
        node2 = new AliasNode();
        node2->insert(pop);
        this->NodeMap[pop] = node2;
    }

    //Under test
    if(checkNodeConnectivity(node1, node2)){
        return;
    }

    //node2 has pointed to some nodes
    if(this->ToNodeMap.count(node2)){
        AliasNode* node2_toNode = this->ToNodeMap[node2];
        this->mergeNode(node1 ,node2_toNode);
    }
    else if(this->FromNodeMap.count(node1)){
        AliasNode* node1_fromNode = this->FromNodeMap[node1];
        this->mergeNode(node1_fromNode, node2);
    }
    else{
        this->ToNodeMap[node2] = node1;
        this->FromNodeMap[node1] = node2;
    }
}

// v1 = &v2->f
void AliasGraph::HandleGEP(GetElementPtrInst* GEP){
    // TODO : make it field sensitive
    this->HandleMove(GEP, GEP->getPointerOperand());
}

// v1 = &v2->f
void AliasGraph::HandleGEP(GEPOperator* GEP){
    // TODO : make it field sensitive
    this->HandleMove(GEP, GEP->getPointerOperand());
}

// v1 = v2
void AliasGraph::HandleMove(Value* v1, Value* v2){

    AliasNode* node2 = getNode(v2);
    if(node2 == nullptr){
        node2 = new AliasNode();
        node2->insert(v2);
        this->NodeMap[v2] = node2;
    }


    AliasNode* node1 = getNode(v1);
    if(node1 == nullptr){
        node2->insert(v1);
        this->NodeMap[v1] = node2;
        return;
    }

    if(*node1 == *node2) // redundant, checkNodeConnectivity already verifies it
        return;
    
    if(checkNodeConnectivity(node1, node2)){
        return;
    }

    this->mergeNode(node1, node2);
}

// f(p1, p2, ...)
void AliasGraph::HandleCai(CallInst *CAI) {
    // ignore debug information
    if(CAI->isDebugOrPseudoInst()) return;

    //TODO : transform it to the SPATA handle call function
    if(getNode(CAI) == nullptr){
        auto* node = new AliasNode();
        node->insert(CAI);
        this->NodeMap[CAI] = node;
    }

    auto calledFunc = CAI->getCalledFunction();
    if(calledFunc == nullptr) return; // indirect call

    auto argCallIt = CAI->arg_begin();
    auto funcArgIt = calledFunc->arg_begin();
    while (argCallIt != CAI->arg_end() && funcArgIt != calledFunc->arg_end()) {
        if(getNode(*argCallIt) == nullptr){
            AliasNode* node = new AliasNode();
            node->insert(*argCallIt);
            this->NodeMap[*argCallIt] = node;
        }

        // Moving the parameter of the call to the argument of the function
        this->HandleMove(funcArgIt, *argCallIt);
        funcArgIt++;
        argCallIt++;
    } 

    auto entry = AnalyzedFuncSet.find(calledFunc);
    if(entry == AnalyzedFuncSet.end() || ! entry->second.contains(CAI)) {
        if(entry == AnalyzedFuncSet.end()) {
            SetVector<CallInst*> initSVCall;
            initSVCall.insert(CAI);
            std::pair<Function*,SetVector<CallInst*>> newEntry (calledFunc, initSVCall);
            AnalyzedFuncSet.insert(newEntry);
        } else {
            entry->second.insert(CAI);
        }
        analyzeFunction(calledFunc);
    }

}

// v = f(...)
void AliasGraph::HandleReturn(Function* F, CallInst* cai){
    for (inst_iterator i = inst_begin(F), ei = inst_end(F); i != ei; ++i)
        if(ReturnInst *returnStatement = dyn_cast<ReturnInst>(&*i))
            if(Value* returnValue = returnStatement->getReturnValue())
                this->HandleMove(returnValue, cai);
}

//===----------------------------------------------------------------------===//
// For displaying the alias graph
//===----------------------------------------------------------------------===//
void AliasGraph::writeToDot(std::string Filename) {
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

#define WRITE_IFNOT_WRITTEN(node) do { \
  if (writtenNodes.find(node) == writtenNodes.end()) { \
    std::string name = std::string("N"+to_string(++nodeCount)); \
    node->writeToDot(File, name, M); \
    writtenNodes[node] = name; \
  } \
} while(false)

  for(auto [_, node] : NodeMap) {
    WRITE_IFNOT_WRITTEN(node);
  }

  for(auto [n1, n2] : ToNodeMap) {
    WRITE_IFNOT_WRITTEN(n1);
    WRITE_IFNOT_WRITTEN(n2);
    File << writtenNodes[n1] << " -> " << writtenNodes[n2] << " ; \n";
  }
#undef WRITE_IFNOT_WRITTEN

  File << "}\n";
  File.close();
}

//===----------------------------------------------------------------------===//
// GraphAliasAnalysis Pass
//===----------------------------------------------------------------------===//
AnalysisKey GraphAA::Key;
char GraphAAWrapperPass::ID = 0;

bool GraphAAResult::invalidate(Module &M, const PreservedAnalyses &PA,
                  ModuleAnalysisManager::Invalidator &Inv){
    auto PAC = PA.getChecker<GraphAA>();
  return !PAC.preservedWhenStateless();
}

AliasResult GraphAAResult::alias(const MemoryLocation &LocA, const MemoryLocation &LocB,
                    AAQueryInfo &, const Instruction *) {
    LLVM_DEBUG(
        dbgs()  << "Executing GraphAAResult::" << __func__ << "\n"
                << "On memory location : \n";
        LocA.print(dbgs());
        LocB.print(dbgs())
    );
    AliasNode * node1 = AG.getNode(LocA);
    AliasNode * node2 = AG.getNode(LocB);

    LLVM_DEBUG(
        dbgs() << "Node for ";
        LocA.Ptr->printAsOperand(dbgs());
        if (node1 != nullptr) {
            dbgs() << "\n"; node1->print_set();
        } else {
            dbgs() << " not found.\n";
        }

        dbgs() << "Node for ";
        LocB.Ptr->printAsOperand(dbgs());
        if (node2 != nullptr) {
            dbgs() << "\n"; node2->print_set();
        } else {
            dbgs() << " not found.\n";
        }
    );

    if (node1 != nullptr && node2 != nullptr &&
        ! AG.checkNodeConnectivity(node1, node2)) {
        LLVM_DEBUG(dbgs() << "Returning no alias.\n");
        return AliasResult::NoAlias;
    }

    return AliasResult::MayAlias;
}

ModRefInfo GraphAAResult::getModRefInfo(const CallBase *Call, const MemoryLocation &Loc,
                         AAQueryInfo &AAQI) {
    AliasNode * node = AG.getNode(Loc);
    Function * CalledF = Call->getCalledFunction();
    
    for(auto &param : Call->args()){
        auto val = node->aliasclass.find(param.get());
        auto arg = CalledF->getArg(param.getOperandNo());
        if(val != node->end() && ! arg->onlyReadsMemory()) {
            return ModRefInfo::ModRef;
        }
    }
    
    return AAResultBase::getModRefInfo(Call, Loc, AAQI);
}

MemoryEffects GraphAAResult::getMemoryEffects(const Function *F) {
    return AAResultBase::getMemoryEffects(F);
}

GraphAAResult GraphAA::run(Module &M, ModuleAnalysisManager &AM) {
    return GraphAAResult(M);
}

GraphAAWrapperPass::GraphAAWrapperPass() : llvm::ModulePass(ID) {
  initializeGraphAAWrapperPassPass(*PassRegistry::getPassRegistry());
}

INITIALIZE_PASS_BEGIN(GraphAAWrapperPass, "alias-graph-aa",
                      "Alias Graph based interprocedural alias analysis", false, true)
INITIALIZE_PASS_END(GraphAAWrapperPass, "alias-graph-aa",
                    "Alias Graph based interprocedural alias analysis", false, true)

ModulePass *llvm::createGraphAAWrapperPass() {
  return new GraphAAWrapperPass();
}

bool GraphAAWrapperPass::runOnModule(Module &M) {
  Result.reset(new GraphAAResult(M));
  return false;
}

bool GraphAAWrapperPass::doFinalization(Module &M) {
    return false;
}

void GraphAAWrapperPass::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.setPreservesAll();
}