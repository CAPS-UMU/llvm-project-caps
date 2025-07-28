#include <cstdlib>
#include <llvm/IR/Function.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/LegacyPassManager.h>
#include <set>
#include <utility>
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SetVector.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Analysis/TargetTransformInfo.h"
#include "llvm/IR/Argument.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/GlobalAlias.h"
#include "llvm/IR/GlobalValue.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/Operator.h"
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
#include "llvm/Support/Timer.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;
using namespace std;

//#define AAGRAPH_BUILD_FRAMES

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

    set<Function *> unusedFunc;
    set<Function *> notAnalyzedFunctions;

    for(Function &F : M) {
        if (F.use_empty())
            unusedFunc.insert(&F);
        else
            notAnalyzedFunctions.insert(&F);
    }

    // begin by analyzing the function used in this module
    for(Function * F : unusedFunc) {
        LLVM_DEBUG(dbgs() << "Analyzing : \033[30m" << F->getName() << "\033[0m\n");
        this->analyzeFunction(F);
    }

    // continue by analyzing function that have no use in the module
    for(auto *F : notAnalyzedFunctions) {
        LLVM_DEBUG(dbgs() << "Analyzing : \033[33m" << F->getName() << "\033[0m\n");
        this->analyzeFunction(F);
    }

    // compute alias information with the callsite that were analyzed
    // when return value were not known
    for(auto [F , CallSet] : AliasFunctionCallSite) {
        auto NonVoidRetVal = AnalyzedFuncSet[F];
        for (auto * CI : CallSet) {
            for (auto * RI : NonVoidRetVal) {
                HandleMove(RI->getReturnValue(), CI);
            }
        }
    }
}

//Merge n1 into n2
void AliasGraph::mergeNode(AliasNode* n1, AliasNode* n2){
    
#ifdef FIELD_SENSITIVITY
    if(n1 == n2)    
        return;
    
    for(auto it = n1->aliasclass.begin(); it != n1->aliasclass.end(); it++){
        Value* v = *it;
        n2->insert(v);
        NodeMap[v] = n2;
    }
    n1->aliasclass.clear();

    //Then change edges
    //Check n1 points to which node
    //All point-to nodes should be merged
    if(ToNodeMap.count(n1)){
        auto n1_toNodeMap = ToNodeMap[n1];

        //Both n1 and n2 have point to nodes
        if(ToNodeMap.count(n2)){
            auto n2_toNodeMap = ToNodeMap[n2];

            for(auto n1_pair : n1_toNodeMap){
                
                int n1_edge = n1_pair.first;
                AliasNode* n1_toNode= n1_pair.second;

                //merge the same edge : n1_edge
                if(n2_toNodeMap.count(n1_edge)){
                    AliasNode* n2_toNode = n2_toNodeMap[n1_edge];
                    if(n1_toNode == n2_toNode){
                        //do nothing here
                    }
                    else{
                        ToNodeMap[n1].erase(n1_edge);
                        ToNodeMap[n2].erase(n1_edge);
                        FromNodeMap[n1_toNode].erase(n1_edge);
                        FromNodeMap[n2_toNode].erase(n1_edge);
                        mergeNode(n1_toNode, n2_toNode);
                        ToNodeMap[n2][n1_edge] = n2_toNode;
                        FromNodeMap[n2_toNode][n1_edge].insert(n2);
                    }
                }
                //n1 has, but n2 has no such edge, merge the edge
                else{
                    ToNodeMap[n1].erase(n1_edge);
                    ToNodeMap[n2][n1_edge] = n1_toNode;
                    FromNodeMap[n1_toNode][n1_edge].insert(n2);
                }
            }
        }

        //n2 has no pointed node
        else{
            ToNodeMap.erase(n1);
            ToNodeMap[n2] = n1_toNodeMap;
            for(auto n: n1_toNodeMap){
                FromNodeMap[n.second][n.first].erase(n1);
                FromNodeMap[n.second][n.first].insert(n2);
            }
        }
    }

    //Check which node points to n1
    //For previous node, only merge * edge
    if(FromNodeMap.count(n1)){
        auto n1_fromNodeMap = FromNodeMap[n1];

        //Both n1 and n2 have previous(from) nodes
        if(FromNodeMap.count(n2)){
            auto n2_fromNodeMap = FromNodeMap[n2];

            for(auto n1_pair : n1_fromNodeMap){

                int n1_edge = n1_pair.first;
                set<AliasNode*> n1_fromNodeSet = n1_pair.second;
                if(n1_edge == -1){

                    if(n1_fromNodeSet.size() != 1){
                        //OP<<"WARNING IN NODE MERGE 1!!!\n";
                    }
                    AliasNode* n1_fromNode = *n1_fromNodeSet.begin();

                    //merge the same edge : * edge
                    if(n2_fromNodeMap.count(n1_edge)){
                        set<AliasNode*> n2_fromNodeSet = n2_fromNodeMap[n1_edge];
                        if(n2_fromNodeSet.size() != 1){
                            //OP<<"WARNING IN NODE MERGE 2!!!"<<n2_fromNodeSet.size()<<"\n";
                        }
                         
                        AliasNode* n2_fromNode = *n2_fromNodeSet.begin();
                        if(n1_fromNode == n2_fromNode){
                            //do nothing here
                        }
                        else{
                            FromNodeMap[n1].erase(n1_edge);
                            FromNodeMap[n2].erase(n1_edge);
                            ToNodeMap[n1_fromNode].erase(n1_edge);
                            ToNodeMap[n2_fromNode].erase(n1_edge);
                            mergeNode(n1_fromNode, n2_fromNode);
                            FromNodeMap[n2][n1_edge].insert(n2_fromNode);
                            ToNodeMap[n2_fromNode][n1_edge] = n2;
                        }
                    }
                    //n1 has, but n2 has no such edge, merge the edge
                    else{
                        FromNodeMap[n1].erase(n1_edge);
                        FromNodeMap[n2][n1_edge].insert(n1_fromNode);
                        ToNodeMap[n1_fromNode][n1_edge] = n2;
                    }
                }
                //The previous edge is not *, just add them to the graph
                else{
                    for(AliasNode* n1_fromNode : n1_fromNodeSet){
                        FromNodeMap[n1].erase(n1_edge);
                        FromNodeMap[n2][n1_edge].insert(n1_fromNode);
                        ToNodeMap[n1_fromNode][n1_edge] = n2;
                    }
                }
            }
        }

        //n2 has no pre node
        else{
            FromNodeMap.erase(n1);
            FromNodeMap[n2] = n1_fromNodeMap;
            for(auto m: n1_fromNodeMap)
                for(auto n: m.second)
                    ToNodeMap[n][m.first] = n2;
        }
    }
#else
    if(n1 == n2)    
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
#endif //
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
#ifdef FIELD_SENSITIVITY
    assert(false && "TODO : Implement retrace origin function for field sensitive alias graph.");
#else
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
#endif // FIELD_SENSITIVITY
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

// Checking if their is a dereferencing chain between two nodes
bool AliasGraph::checkNodeConnectivity(AliasNode* node1, AliasNode* node2){
#ifdef FIELD_SENSITIVITY
    if(!node1 || !node2)
        return false;

    list<AliasNode *>LN;
    LN.push_back(node1);
    set<AliasNode *> PN; //Global value set to avoid loop
    PN.clear();

    while (!LN.empty()) {
        AliasNode *CN = LN.front();
        LN.pop_front();

        if (PN.find(CN) != PN.end()){
            continue;
        }
        PN.insert(CN);

        if(CN == node2)
            return true;

        if(ToNodeMap.count(CN)){
            for(auto n : ToNodeMap[CN]){
                if(n.first == -1)
                    LN.push_back(n.second);
            }
        }

        if(FromNodeMap.count(CN)){
            for(auto m : FromNodeMap[CN]){
                if(m.first == -1){
                    for(auto n : m.second)
                        LN.push_back(n);
                }
            }
        }
    }

    return false;
#else
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
#endif //FIELD_SENSITIVITY
}

/// INTERPROCEDURAL ALIAS ANALYSIS
int instrCount = 0; // for debug only

void AliasGraph::analyzeFunction(Function* F){
    SetVector<ReturnInst*> NonVoidRetSites;
    SetVector<GlobalValue*> GlobalsUsed;

    if(AnalyzedFuncSet.contains(F))
        return;

    LLVM_DEBUG(errs() << "Analyzing function " << F->getName() << "\n");

    // For function whose argument could be function pointer, we need
    // to register the function argument in alias graph, as we don't 
    // know in which order will the function be analyzed : hence a function pointer
    // passed as an agrument could not have been registered in the alias graph
    for(auto arg = F->arg_begin(); arg != F->arg_end(); arg++) {
        if(arg->getType()->isPointerTy() && getNode(arg) == nullptr) {
            AliasNode *node = new AliasNode();
            node->insert(arg);
            NodeMap[arg] = node;
        }
    }

    if(!F || F->isDeclaration() || F->getName().starts_with("llvm.lifetime")) {
        auto FuncEntry = std::pair<Function*,SetVector<ReturnInst*>> (F, NonVoidRetSites);
        AnalyzedFuncSet.insert(FuncEntry);
        auto GlbUseEntry = std::pair<Function*,SetVector<GlobalValue*>> (F, GlobalsUsed);
        FuncGlobalUsed.insert(GlbUseEntry);
        return;
    }

    for (inst_iterator i = inst_begin(F), ei = inst_end(F); i != ei; ++i) {
        if( auto * RI = dyn_cast<ReturnInst>(&(*i)); 
            RI && RI->getReturnValue()
        ) {
            NonVoidRetSites.insert(RI);
        }
        
        Instruction *iInst = dyn_cast<Instruction>(&(*i));
        this->HandleInst(iInst);

#ifdef AAGRAPH_BUILD_FRAMES
        writeToDot("../aliasgraph"+itostr(instrCount++)+".dot");
#endif // AAGRAPH_BUILD_FRAMES

    }

    auto newEntry = std::pair<Function*,SetVector<ReturnInst*>> (F, NonVoidRetSites);
    AnalyzedFuncSet.insert(newEntry);
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
    for(unsigned int i = 0; i < I->getNumOperands(); i++){
        Value* op = I->getOperand(i);

        if(auto * Glb = dyn_cast<GlobalValue>(op))
            FuncGlobalUsed[I->getFunction()].insert(Glb);

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

    auto *GEP = dyn_cast<GEPOperator>(I);
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
        NodeMap[LI] = node1;
    }

    Value* op = LI->getOperand(0);
    AliasNode* node2 = getNode(op);
    if(node2 == nullptr){
        node2 = new AliasNode();
        node2->insert(op);
        NodeMap[op] = node2;
    }

#ifdef FIELD_SENSITIVITY
    //node2 has pointed to some nodes
    if(ToNodeMap.count(node2)){

        auto node2_toNodeMap = ToNodeMap[node2];
        if(node2_toNodeMap.count(-1)){
            mergeNode(node1 ,node2_toNodeMap[-1]);
            goto end;
        }
    }
    //For load, this usually does not happen
    if(FromNodeMap.count(node1)){

        auto node1_fromNodeMap = FromNodeMap[node1];
        if(node1_fromNodeMap.count(-1)){
            if(node1_fromNodeMap[-1].size() != 1){
                //OP<<"WARNING IN NODE MERGE 3!!!\n";
            }
            mergeNode(*node1_fromNodeMap[-1].begin(), node2);
            goto end;
        }
    }

    ToNodeMap[node2][-1] = node1;
    FromNodeMap[node1][-1].insert(node2);

end:
    return;
#else
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
#endif //FIELD_SENSITIVITY
}

// *v2 = v1
void AliasGraph::HandleStore(StoreInst* STI){

    //store vop to pop
    Value* vop = STI->getValueOperand(); //v1
    Value* pop = STI->getPointerOperand(); //v2

    AliasNode* node2 = getNode(pop);
    if(node2 == nullptr){
        node2 = new AliasNode();
        node2->insert(pop);
        NodeMap[pop] = node2;
    }

    if(isa<ConstantData>(vop))
        return;

    AliasNode* node1 = getNode(vop);
    if(node1 == nullptr){
        node1 = new AliasNode();
        node1->insert(vop);
        NodeMap[vop] = node1;
    }

    //Under test
    if(checkNodeConnectivity(node1, node2)){
        return;
    }

#ifdef FIELD_SENSITIVITY
    //node2 has pointed to some nodes
    if(ToNodeMap.count(node2)){
        auto node2_toNodeMap = ToNodeMap[node2];
        if(node2_toNodeMap.count(-1)){
            mergeNode(node1 ,node2_toNodeMap[-1]);
            goto end;
        }
    }

    if(FromNodeMap.count(node1)){
        auto node1_fromNodeMap = FromNodeMap[node1];
        if(node1_fromNodeMap.count(-1)){
            if(node1_fromNodeMap[-1].size() != 1){
                //OP<<"WARNING IN NODE MERGE 4!!!" << node1_fromNodeMap[-1].size() <<"\n";;
            }
            mergeNode(*node1_fromNodeMap[-1].begin(), node2);
            goto end;
        }
    }

    ToNodeMap[node2][-1] = node1;
    FromNodeMap[node1][-1].insert(node2);

end:
    return;
#else
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
#endif // FIELD_SENSITIVITY
}

#ifdef FIELD_SENSITIVITY

bool checkValidStructName(Type *Ty){
    if( ! Ty->isStructTy())
        return false;

    StructType* STy = dyn_cast<StructType>(Ty);
    if(STy->isLiteral())
        return false;

    auto TyName = Ty->getStructName();
    return  ! (
        TyName.contains(".union") ||
        TyName.contains(".anon")
    );
}

//Return true if we successfully find the layered type
bool getGEPLayerIndex(GEPOperator *GEP, int &Index) {

    Type *PTy = GEP->getPointerOperand()->getType();
    if(!PTy->isPointerTy())
        return false;

    Type *Ty = GEP->getSourceElementType(); // check if this works; previous : PTy->getPointerElementType();
    
    int Idx;

    //Expect the PointerOperand is an identified struct
    if (Ty->isStructTy() && GEP->hasAllConstantIndices()) {
        User::op_iterator ie = GEP->idx_end();
        ConstantInt *ConstI = dyn_cast<ConstantInt>((--ie)->get());
        Idx = ConstI->getSExtValue(); //Idx is the last indice
        
        if(Idx < 0 || !checkValidStructName(Ty))
            return false;

        unsigned indice_num = GEP->getNumIndices();

        //Filter GEP that has invalid indice
        ConstantInt *ConstI_first = dyn_cast<ConstantInt>(GEP->idx_begin()->get());
        int Idx_first = ConstI_first->getSExtValue();
        if((Idx_first != 0 && Ty->isStructTy())
            || indice_num < 2){
            return false;
        }

        Index = Idx;
        return true;
    }
    
    if(Ty->isStructTy() || Ty->isArrayTy()){
        Index = 999;
        return true;
    }

    return false;
    
}
#endif // FIELD_SENSITIVITY 

// v1 = &v2->f
void AliasGraph::HandleGEP(GEPOperator* GEP){
    // TODO : make it field sensitive
#ifndef FIELD_SENSITIVITY
    this->HandleMove(GEP, GEP->getPointerOperand());
#else
        int idx = 0;
    if(getGEPLayerIndex(GEP, idx)){
        Value* v2 = GEP->getPointerOperand();
        Value* v1 = GEP;

        AliasNode* node2 = getNode(v2);
        if(node2 == nullptr){
            node2 = new AliasNode();
            node2->insert(v2);
            NodeMap[v2] = node2;
        }

        AliasNode* node1 = getNode(v1);
        if(node1 == nullptr){
            node1 = new AliasNode();
            node1->insert(v1);
            NodeMap[v1] = node1;
        }

        //node2 has pointed to some nodes
        if(ToNodeMap.count(node2)){
            auto node2_toNodeMap = ToNodeMap[node2];
            if(node2_toNodeMap.count(idx)){
                mergeNode(node1 ,node2_toNodeMap[idx]);
                goto end;
            }
        }

        ToNodeMap[node2][idx] = node1;
        FromNodeMap[node1][idx].insert(node2);

    }
    else{
        //Use move may not suitable here
        HandleMove(GEP, GEP->getPointerOperand());
    }

end:
    return;
#endif // FIELD_SENSITIVITY

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

// Allow for filtering of debug & "llvm.lifetime" call that produces wrong alias result
bool AliasGraph::IrrelevantCall(CallInst *Call) {
    auto * CalledFunc = Call->getCalledFunction();
    return Call->isDebugOrPseudoInst() || (
        CalledFunc != nullptr && CalledFunc->getName().starts_with("llvm.lifetime"));
}

// Handling of undefined target for call, like a function that is only declared.
// All pointer argument of the call are supposed to alias, as these function
// can always be memcopy of memove function for instance.
void AliasGraph::HandleUndefTarget(CallInst * Call) {
    auto * Param = Call->arg_begin();
    while(Param != Call->arg_end() && ! Param->get()->getType()->isPointerTy()) 
        Param++;

    if(Param == Call->arg_end())
        // no ptr parameter found
        return;

    auto *OtherParam = Param + 1;
    while(OtherParam != Call->arg_end()) {
        if(OtherParam->get()->getType()->isPointerTy())
            HandleMove(Param->get(), OtherParam->get());
        OtherParam++;
}
}

// Register aliasing relation between argument and parameter of the call
void AliasGraph::HandleParamArgAliasing(CallInst * CAI, Function * Target) {
    auto * CallArg = CAI->arg_begin();
    auto * FuncArg = Target->arg_begin();
    
    while (CallArg != CAI->arg_end() && FuncArg != Target->arg_end()) {
        if(getNode(CallArg->get()) == nullptr){
            AliasNode* node = new AliasNode();
            node->insert(CallArg->get());
            this->NodeMap[CallArg->get()] = node;
        }

        this->HandleMove(FuncArg, CallArg->get());
        FuncArg++;
        CallArg++;
    }
}

// getting all the function that can be potentially called
// weither the function is fully called to or it is an indirect call
SetVector<Function*> AliasGraph::getCallTargetSet(CallInst *Call) {
    SetVector<Function*> CallTarget;
    
    if(! Call->isIndirectCall()) {
        CallTarget.insert(Call->getCalledFunction());
        return CallTarget;
    }

    AliasNode * node = getNode(Call->getCalledOperand());

#ifdef DEBUG_TARGET
    if(!node) {
        auto op = Call->getCalledOperand();
        errs() << "\033[31mOn " << to_string(*Call) << " ; \ncalled operand : " << *op << " ; is not registered in a-graph.\n";
        assert(false && "Aborting.");
    }
#else
    assert(node && "ICall operand node isn't in graph.");
#endif
    
    SetVector<AliasNode*> toExplore;
    SetVector<AliasNode*> explored;
    toExplore.insert(node);

    while(!toExplore.empty()) {
        auto * currentNode = toExplore.back();
        toExplore.pop_back();

        if(explored.contains(currentNode))
            continue;

        for(auto * V : currentNode->aliasclass) {
            if (auto * F = dyn_cast<Function>(V))
                CallTarget.insert(F);
            
            // if V is an array type containing function ptr
            if (auto * Glb = dyn_cast<GlobalValue>(V)) {
                for(int i=0; i<Glb->getNumOperands(); i++) {
                    if (auto * F = dyn_cast<Function>(Glb->getOperand(i)))
                        CallTarget.insert(F);
                }
            }
        }

        explored.insert(currentNode);
        if(FromNodeMap.count(currentNode) > 0) toExplore.insert(FromNodeMap[currentNode]);
        if(ToNodeMap.count(currentNode)   > 0) toExplore.insert(ToNodeMap[currentNode]);
    }

    return CallTarget;
}

// f(p1, p2, ...)
void AliasGraph::HandleCai(CallInst *CAI) {
    // ignore debug information
    if(IrrelevantCall(CAI)) return;

    // create node for the call
    if(getNode(CAI) == nullptr){
        auto* node = new AliasNode();
        node->insert(CAI);
        this->NodeMap[CAI] = node;
    }

    // indirect call or undefined function
    SetVector<Function*> Targets = getCallTargetSet(CAI);
    if(CAI->isIndirectCall()) {
        SetVector<Function*> TargetDONE;
        auto newEntry = std::pair<CallInst*, SetVector<Function*>> 
            (CAI, TargetDONE);
        ICallTargets.insert(newEntry);
    }

    for(auto * F : Targets) {

        if(F->isDeclaration())
            HandleUndefTarget(CAI);

        // Moving the parameter of the call to the argument of the function
        HandleParamArgAliasing(CAI, F);
        if(ICallTargets.contains(CAI))
            // the aliasing between arg and param on this function is done
            ICallTargets[CAI].insert(F); 

        // computing the aliasing with the return values of the call
        auto funcRetvalEntry = AnalyzedFuncSet.find(F);
        auto funcCallsiteEntry = UnknownCallRetVal.find(F);
        if(funcRetvalEntry == AnalyzedFuncSet.end()) { 
            // the function was not analyzed yet, we need to register
            // the call so that it will be handled later
            if(funcCallsiteEntry == UnknownCallRetVal.end()) {
                SetVector<CallInst*> CallSet;
                CallSet.insert(CAI);
                auto newEntry = std::pair<Function*, SetVector<CallInst*>> (F, CallSet);
                UnknownCallRetVal.insert(newEntry);
            } else {
                funcCallsiteEntry->second.insert(CAI);
            }
        } else {
            // function was analyzed and the ret values are known, we can use the according alias information
            auto NonVoidRetVal = funcRetvalEntry->second;
            // handling aliasing with the return values of the function called
            for(auto *RI : NonVoidRetVal) {
                HandleMove(RI->getReturnValue(), CAI);
            }
        }
    }
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

#ifdef FIELD_SENSITIVITY  
    for(auto [n1, children] : ToNodeMap) {
        WRITE_IFNOT_WRITTEN(n1);
        for(auto [idx, node] : children) {
            WRITE_IFNOT_WRITTEN(node);
            File << writtenNodes[n1] << " -> " << writtenNodes[node]
                 << " [label=\"" << idx << "\"]; \n";
        }
    }
#else
    for(auto [n1, n2] : ToNodeMap) {
      WRITE_IFNOT_WRITTEN(n1);
      WRITE_IFNOT_WRITTEN(n2);
      File << writtenNodes[n1] << " -> " << writtenNodes[n2] << " ; \n";
    }
#endif // FIELD_SENSITIVITY
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

// Check for each parameter of the call if they alias with the given memory location
// i.e is in the same node in the alias graph.
// If so, and if the corresponding argument in the function call is not readonly,
// then return ModRef.
// Also check for aliasing with a potential return value, and take into account if the call
// is indirect call
ModRefInfo GraphAAResult::getModRefInfo(const CallBase *Call, const MemoryLocation &Loc,
                         AAQueryInfo &AAQI) {
    AliasNode * node = AG.getNode(Loc);

#ifdef DEBUG_TARGET
    if(node == nullptr) {
        AG.dbg_msg = "\033[31m"+to_string(*Loc.Ptr)+" : has no node in aa graph, can't proceed with getModRef.\033[0m\n";
        return ModRefInfo::ModRef;
    }
#else
    assert(node != nullptr);
#endif // DEBUG_TARGET

    // check for aliasing with the return value
    if (Call->isReturnNonNull()) {
        AliasNode * retNode = AG.getNode(const_cast<CallBase*>(Call));

#ifdef DEBUG_TARGET
        if(!retNode) {
            AG.dbg_msg = to_string(*Call) + " not registered in a-graph.";
            return ModRefInfo::ModRef;
        }
#else
        assert(retNode);
#endif //DEBUG_TARGET

        if(AG.checkNodeConnectivity(node, retNode))
            return ModRefInfo::ModRef;
    }

    SetVector<Function*> Targets;
    if (auto * CAI = dyn_cast<CallInst>(Call))
        Targets = AG.getCallTargetSet(const_cast<CallInst*>(CAI));

#ifdef DEBUG_TARGET
    if(Targets.empty()) {
        AG.dbg_msg = to_string(*Call) + " ; has no target function found.";
        return ModRefInfo::ModRef;
    }
#else
    assert(!Targets.empty() && "Call has no target function.");
#endif

    auto Result = ModRefInfo::NoModRef;
    for (auto * F : Targets) {
        // checking for each possible target function
        MemoryEffects ME = F->getMemoryEffects();
        if(ME.doesNotAccessMemory() || ! ME.doesAccessArgPointees())
            Result |= ModRefInfo::NoModRef;

        // checking for aliasing with th global variable used inside the function
        for(auto * Glb : AG.FuncGlobalUsed[F]) {
            AliasNode * glbNode = AG.getNode(Glb);
            if(!glbNode) continue;

            if(AG.checkNodeConnectivity(node, glbNode))
                return ModRefInfo::ModRef;
        }

        // we can exploit the argument indication to check for ModRefInfo
        auto paramIt = Call->arg_begin();
        auto argIt = F->arg_begin();
        while(paramIt != Call->arg_end() && argIt != F->arg_end()){
            auto *paramNode = AG.getNode(paramIt->get());
            if(AG.checkNodeConnectivity(node, paramNode)) {
                if(argIt->onlyReadsMemory()) {
                    Result |= ModRefInfo::Ref;
                } else {
                    return ModRefInfo::ModRef;
                }
            }
            paramIt++;
            argIt++;
        }
    }

    return Result;
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