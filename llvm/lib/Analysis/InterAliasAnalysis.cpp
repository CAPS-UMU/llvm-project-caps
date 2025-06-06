#include <llvm/IR/Instructions.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/LegacyPassManager.h>

#include "llvm/Analysis/AliasGraph.h"

void getClusterNodes(AliasNode* startNode, set<AliasNode*> &nodeSet, AliasGraph *aliasCtx){

	if(startNode == NULL)
		return;
	
	nodeSet.insert(startNode);

	list<AliasNode *>LN;
	LN.push_back(startNode);
	set<AliasNode *> PN;
	PN.clear();

	while (!LN.empty()) {
		AliasNode *CN = LN.front();
		LN.pop_front();

		if (PN.find(CN) != PN.end()){
			continue;
		}
		PN.insert(CN);

		if(aliasCtx->ToNodeMap.count(CN)){
			LN.push_back(aliasCtx->ToNodeMap[CN]);
			nodeSet.insert(aliasCtx->ToNodeMap[CN]);
		}

		if(aliasCtx->FromNodeMap.count(CN)){
			LN.push_back(aliasCtx->FromNodeMap[CN]);
			nodeSet.insert(aliasCtx->FromNodeMap[CN]);
		}
	}
}

void getClusterValues(Value* v, set<Value*> &valueSet, AliasGraph *aliasCtx){

    if(v == NULL)
        return;

    AliasNode *n = getNode(v, aliasCtx);
	if(!n)
		return;

	//Get the cluster of values to enable inter-procedural analysis
	set<AliasNode*> targetNodeSet;
	targetNodeSet.clear();
	getClusterNodes(n, targetNodeSet, aliasCtx);
	
	valueSet.clear();
	for(auto it = targetNodeSet.begin(); it != targetNodeSet.end(); it++){
		AliasNode *n = *it;
		valueSetMerge(valueSet, n->aliasclass);
	}
}