#include <llvm/IR/Instructions.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/LegacyPassManager.h>

#include "llvm/Analysis/AliasGraph.h"

void HandleOperator(Value* v, AliasGraph *aliasCtx){
    GEPOperator *GEPO = dyn_cast<GEPOperator>(v);
    if(GEPO){
        HandleGEP(GEPO, aliasCtx);
        HandleOperator(GEPO->getOperand(0), aliasCtx);
    }

    BitCastOperator *CastO = dyn_cast<BitCastOperator>(v);
    if(CastO){
        HandleMove(CastO, CastO->getOperand(0), aliasCtx);
        HandleOperator(CastO->getOperand(0), aliasCtx);
    }

    PtrToIntOperator *PTIO = dyn_cast<PtrToIntOperator>(v);
    if(PTIO){
        HandleMove(PTIO, PTIO->getOperand(0), aliasCtx);
        HandleOperator(PTIO->getOperand(0), aliasCtx);
    }
}

void HandleInst(Instruction* I, AliasGraph *aliasCtx){

    // Handle GEP and Cast operator
    // Arguments of a call are also caught here
    for(unsigned int i = 0; i < I->getNumOperands(); i++){
        Value* op = I->getOperand(i);
        HandleOperator(op, aliasCtx);
    }

    //Handle target instruction
    AllocaInst* ALI = dyn_cast<AllocaInst>(I);
    if(ALI){
        HandleAlloc(ALI, aliasCtx);
        return;
    }

    StoreInst *STI = dyn_cast<StoreInst>(I);
    if(STI){
        HandleStore(STI, aliasCtx);
        return;
    }

    LoadInst* LI = dyn_cast<LoadInst>(I);
    if(LI){
        HandleLoad(LI, aliasCtx);
        return;
    }

    GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(I);
    if(GEP){
        HandleGEP(GEP, aliasCtx);
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
        HandleMove(I, op, aliasCtx);
        return;
    }

    PHINode *PHI = dyn_cast<PHINode>(I);
    if(PHI){
        for (unsigned i = 0, e = PHI->getNumIncomingValues(); i != e; ++i){
            Value *IV = PHI->getIncomingValue(i);
            HandleMove(I, IV, aliasCtx);
        }
        return;
    }

    SelectInst *SLI = dyn_cast<SelectInst>(I);
    if(SLI){
        auto TV = SLI->getTrueValue();
        auto FV = SLI->getFalseValue();
        HandleMove(I, TV, aliasCtx);
        HandleMove(I, FV, aliasCtx);
        return;
    }

    ReturnInst *RI = dyn_cast<ReturnInst>(I);
    if(RI){
        Value* return_v = RI->getReturnValue();
        if(return_v == NULL)
            return;
        
        if(isa<ConstantData>(return_v))
            return;
            
        HandleMove(I, return_v, aliasCtx);
    }

}

// p1 = alloc(size)
void HandleAlloc(AllocaInst* ALI, AliasGraph *aliasCtx){
    
    if(getNode(ALI, aliasCtx) == nullptr){
        auto node = new AliasNode();
        node->insert(ALI);
        aliasCtx->NodeMap[ALI] = node;
    }
}

// v1 = *v2
void HandleLoad(LoadInst* LI, AliasGraph *aliasCtx){
    
    AliasNode* node1 = getNode(LI, aliasCtx);
    if(node1 == NULL){
        node1 = new AliasNode();
        node1->insert(LI);
        aliasCtx->NodeMap[LI] = node1;
    }

    Value* op = LI->getOperand(0);
    AliasNode* node2 = getNode(op, aliasCtx);
    if(node2 == NULL){
        node2 = new AliasNode();
        node2->insert(op);
        aliasCtx->NodeMap[op] = node2;
    }

    //node2 has pointed to some nodes
    if(aliasCtx->ToNodeMap.count(node2)){
        AliasNode* node2_toNode = aliasCtx->ToNodeMap[node2];
        mergeNode(node1 ,node2_toNode, aliasCtx);
    }
    //For load, this usually does not happen
    else if(aliasCtx->FromNodeMap.count(node1)){
        AliasNode* node1_fromNode = aliasCtx->FromNodeMap[node1];
        mergeNode(node1_fromNode, node2, aliasCtx);
    }
    else{
        aliasCtx->ToNodeMap[node2] = node1;
        aliasCtx->FromNodeMap[node1] = node2;
    }
}

// *v2 = v1
void HandleStore(StoreInst* STI, AliasGraph *aliasCtx){
    
    //store vop to pop
    Value* vop = STI->getValueOperand(); //v1
    Value* pop = STI->getPointerOperand(); //v2

    if(isa<ConstantData>(vop))
        return;

    AliasNode* node1 = getNode(vop, aliasCtx);
    if(node1 == NULL){
        node1 = new AliasNode();
        node1->insert(vop);
        aliasCtx->NodeMap[vop] = node1;
    }

    AliasNode* node2 = getNode(pop, aliasCtx);
    if(node2 == NULL){
        node2 = new AliasNode();
        node2->insert(pop);
        aliasCtx->NodeMap[pop] = node2;
    }

    //Under test
    if(checkNodeConnectivity(node1, node2, aliasCtx)){
        return;
    }

    //node2 has pointed to some nodes
    if(aliasCtx->ToNodeMap.count(node2)){
        AliasNode* node2_toNode = aliasCtx->ToNodeMap[node2];
        mergeNode(node1 ,node2_toNode, aliasCtx);
    }
    else if(aliasCtx->FromNodeMap.count(node1)){
        AliasNode* node1_fromNode = aliasCtx->FromNodeMap[node1];
        mergeNode(node1_fromNode, node2, aliasCtx);
    }
    else{
        aliasCtx->ToNodeMap[node2] = node1;
        aliasCtx->FromNodeMap[node1] = node2;
    }
}

//store vop to pop
void HandleStore(Value* vop, Value* pop, AliasGraph *aliasCtx){

    if(isa<ConstantData>(vop))
        return;

    AliasNode* node1 = getNode(vop, aliasCtx);
    if(node1 == NULL){
        node1 = new AliasNode();
        node1->insert(vop);
        aliasCtx->NodeMap[vop] = node1;
    }

    AliasNode* node2 = getNode(pop, aliasCtx);
    if(node2 == NULL){
        node2 = new AliasNode();
        node2->insert(pop);
        aliasCtx->NodeMap[pop] = node2;
    }

    //Under test
    if(checkNodeConnectivity(node1, node2, aliasCtx)){
        return;
    }

    //node2 has pointed to some nodes
    if(aliasCtx->ToNodeMap.count(node2)){
        AliasNode* node2_toNode = aliasCtx->ToNodeMap[node2];
        mergeNode(node1 ,node2_toNode, aliasCtx);
    }
    else if(aliasCtx->FromNodeMap.count(node1)){
        AliasNode* node1_fromNode = aliasCtx->FromNodeMap[node1];
        mergeNode(node1_fromNode, node2, aliasCtx);
    }
    else{
        aliasCtx->ToNodeMap[node2] = node1;
        aliasCtx->FromNodeMap[node1] = node2;
    }
}

// v1 = &v2->f
void HandleGEP(GetElementPtrInst* GEP, AliasGraph *aliasCtx){
    HandleMove(GEP, GEP->getPointerOperand(), aliasCtx);
}

// v1 = &v2->f
void HandleGEP(GEPOperator* GEP, AliasGraph *aliasCtx){
    HandleMove(GEP, GEP->getPointerOperand(), aliasCtx);
}

// v1 = v2
void HandleMove(Value* v1, Value* v2, AliasGraph *aliasCtx){

    AliasNode* node2 = getNode(v2, aliasCtx);
    if(node2 == NULL){
        node2 = new AliasNode();
        node2->insert(v2);
        aliasCtx->NodeMap[v2] = node2;
    }


    AliasNode* node1 = getNode(v1, aliasCtx);
    if(node1 == NULL){
        node2->insert(v1);
        aliasCtx->NodeMap[v1] = node2;
        return;
    }

    if(node1 == node2) // redundant, checkNodeConnectivity already verifies it
        return;
    
    if(checkNodeConnectivity(node1, node2, aliasCtx)){
        return;
    }

    mergeNode(node1, node2, aliasCtx);
}

void HandleReturn(Function* F, CallInst* cai, AliasGraph *aliasCtx){
    for (inst_iterator i = inst_begin(F), ei = inst_end(F); i != ei; ++i)
        if(ReturnInst *returnStatement = dyn_cast<ReturnInst>(&*i))
            if(Value* returnValue = returnStatement->getReturnValue())
                HandleMove(returnValue, cai, aliasCtx);
}