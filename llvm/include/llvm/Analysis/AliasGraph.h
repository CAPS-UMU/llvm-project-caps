#ifndef ALIAS_GRAPH
#define ALIAS_GRAPH

#include <llvm/IR/DebugInfo.h>
#include <llvm/Pass.h>
#include <llvm/IR/Instructions.h>
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SetVector.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/MemoryLocation.h"
#include "llvm/CodeGen/MachineMemOperand.h"
#include "llvm/IR/Argument.h"
#include "llvm/IR/Constant.h"
#include "llvm/IR/DerivedUser.h"
#include "llvm/IR/GlobalAlias.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/Instruction.h"
#include <llvm/Support/Debug.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Constants.h>
#include <llvm/ADT/StringExtras.h>
#include <llvm/Analysis/CallGraph.h>
#include "llvm/IR/Function.h"
#include "llvm/IR/Metadata.h"
#include "llvm/IR/Operator.h"
#include "llvm/IR/PassManager.h"
#include "llvm/IR/Value.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/ScopedPrinter.h"
#include "llvm/Support/raw_ostream.h"  
#include "llvm/IR/InstrTypes.h" 
#include "llvm/IR/BasicBlock.h" 
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/LoopPass.h"
#include <llvm/IR/LegacyPassManager.h>

#include <regex>

#define MAX_ANALYSIS_NUM 500

namespace llvm {

//#define FIELD_SENSITIVITY
#define DEBUG_TARGET

#define PRINT_DOT_FUNC(fd_dot, F) do { \
  std::string StrF = to_string(*F); \
  std::string content = ""; \
  bool endDeclaration = false; \
	for(int i=0; i<StrF.size() && !endDeclaration; i++) \
		switch(StrF[i]) {  \
			case '<'  : content += R"(\<)"; break;  \
			case '>'  : content += R"(\>)"; break;  \
 \
			case '{'  :  \
        if(StrF[i+1] == '\n')  \
          endDeclaration = true; \
        else  \
          content += R"(\{)"; \
        break; \
 \
			case '}'  : content += R"(\})"; break;  \
			case '\"' : content += R"(')"; break;  \
			default: content += StrF[i];  \
    } \
  fd_dot << content << R"( ; \l)";  \
} while(false)

#define PRINT_DOT(fd_dot, value_ptr) do {\
  std::string content = ""; \
	for(char c : to_string(*value_ptr)) \
		switch(c) { \
			case '<'  : content += R"(\<)"; break; \
			case '>'  : content += R"(\>)"; break; \
			case '{'  : content += R"(\{)"; break; \
			case '}'  : content += R"(\})"; break; \
			case '\"' : content += R"(')"; break; \
			default: content += c; \
		} \
  fd_dot << content << R"( ; \l)"; \
} while(false)

#define PRINT_DOT_FUNC_SIMPLE(fd_dot, F) do { \
  fd_dot << F->getName() << " ( "; \
  for (auto * Arg = F->arg_begin(); Arg != F->arg_end(); Arg++) { \
    fd_dot << *Arg << ", "; \
  } \
  fd_dot << R"( ) ; \l )"; \
} while(false)

// MAIN CLASS NEEDED FOR ALIAS ANALYSIS USING ALIAS GRAPH
class AliasNode;
class AliasGraph;

enum AliasFailureReasons{
	none = 0,
	F_has_no_global_definition = 1,
  binary_operation = 2,
	llvm_used = 3,
	exceed_max = 4,
	success = 5,
	ignore_analysis = 6,
	inline_asm = 7,
	init_in_asm = 8,
	strip_invariant_group = 9,
};

class AliasNode {
public:
    std::set<Value*> aliasclass;
    DenseMap<Function*, SetVector<Value*>> partitionOverFunctions();

    AliasNode(){
        aliasclass.clear();
    }

    int count(Value* V){
        return aliasclass.count(V);
    }

    void insert(Value* V){
        aliasclass.insert(V);
    }

    bool empty(){
        return aliasclass.empty();
    }

    void erase(Value* V){
      if(aliasclass.count(V) == 0)
          return;
      aliasclass.erase(V);
    }

    std::set<Value*>::iterator begin() {
      return aliasclass.begin();
    }

    std::set<Value*>::iterator end() {
      return aliasclass.end();
    }

    bool operator==(const AliasNode &node) {
      if (node.aliasclass.size() != this->aliasclass.size()) return false;

      for(auto it=aliasclass.begin(); it!=aliasclass.end(); it++) {
        if(node.aliasclass.count(*it) == 0) return false;
      }

      return true;
    }

    void print_set(){
			for(auto it = aliasclass.begin(); it != aliasclass.end(); it++){
      	Value *v = *it;
      	if(Function *F = dyn_cast<Function>(v)){
      	  errs() << "func: " << F->getName() << "\n";
      	} else if(auto *Inst = dyn_cast<Instruction>(v)) {
					Function * containingFunc = Inst->getParent()->getParent();
					errs() << containingFunc->getName() << " : ";
				}
      	errs() << *v << "\n";
			}
    }

    void writeToDot(raw_ostream &dotFile, std::string nodeName, const Module * M){
        if(aliasclass.empty()) {
          errs() << "NOT PRINTING EMPTY NODE, RETURNS\n";
          return;
        }

        dotFile << nodeName+" [shape=record,label=\"{"+nodeName+"\\l| ";
        for(auto it = aliasclass.begin(); it != aliasclass.end(); it++){
          Value *v = *it;
          
          assert(v);

          if(Function *F = dyn_cast<Function>(v)){
              dotFile << "func: ";
              PRINT_DOT_FUNC_SIMPLE(dotFile, F);
          } else {
            if(auto *Inst = dyn_cast<Instruction>(v)) {
					  	Function * containingFunc = Inst->getParent()->getParent();
					  	dotFile << containingFunc->getName() << " : ";
					  } else if(auto *Arg = dyn_cast<Argument>(v)) {
					  	Function * containingFunc = Arg->getParent();
					  	dotFile << containingFunc->getName() << " [arg] : ";
            }
            PRINT_DOT(dotFile, v);
          }
          
        }
        dotFile << "}\"];\n";
    }
};

// Actually represent an alias graph data structure
// edges are memory acces from the pointers inside the node
class AliasGraph {
public:
    const Module * M;
    std::map<Value*, AliasNode*> NodeMap;

// this macro exists to detect error during aa analysis
// I use it kinda like an exception :
// - if the dbg_msg variable is empty, then no error message was registered and everything is fine
// - if I stumbled into an error case, I fill the variable with the correct debugging info and return
//   from the function where the error was found : I can then emulate "try" in the caller function
//   by testing if the dbg_msg variable is empty or not
// When deactivated, the corresponding part in the code are mostly replaced by "assert()"
#ifdef DEBUG_TARGET
    std::string dbg_msg;
#endif

#ifdef FIELD_SENSITIVITY
    std::map<AliasNode*, std::map<int,AliasNode*>> ToNodeMap;
    std::map<AliasNode*, std::map<int,std::set<AliasNode*>>> FromNodeMap; 
#else
    std::map<AliasNode*, AliasNode*> ToNodeMap;
    std::map<AliasNode*, AliasNode*> FromNodeMap; 
#endif
  
    bool Is_Analyze_Success;
    AliasFailureReasons failreason;

    DenseMap<Function*, SetVector<CallInst*>> AnalyzedFuncSet;

    AliasGraph(){
      NodeMap.clear();
      ToNodeMap.clear();
      FromNodeMap.clear();
      Is_Analyze_Success = true;
      failreason = none;
      AnalyzedFuncSet.clear();
    }

		AliasGraph(Module &M);

    ~AliasGraph(){
      NodeMap.clear();
      ToNodeMap.clear();
      FromNodeMap.clear();
    }

		AliasNode* getNode(Value *V);
		AliasNode* getNode(const MemoryLocation &MemLoc);
		void mergeNode(AliasNode* n1, AliasNode* n2);
		bool checkNodeConnectivity(AliasNode* node1, AliasNode* node2);
    AliasNode* retraceOrigin(const MemoryLocation &MemLoc);

    // To display the alias graph
    void writeToDot(std::string Filename);

		//InstHandler
		void HandleInst(Instruction* I);
		void HandleLoad(LoadInst* LI);
		void HandleStore(StoreInst* STI);
		void HandleStore(Value* vop, Value* pop);
		void HandleGEP(GEPOperator* GEP);
		void HandleAlloc(AllocaInst* ALI);
		void HandleMove(Value* v1, Value* v2);
    void HandleOperator(Value* v);

    // Call handling
    bool IrrelevantCall(CallInst *Call);
    SetVector<Function*> getCallTargetSet(CallInst*);
    void HandleUndefTarget(CallInst *Call);
		void HandleCai(CallInst *CAI);

		//Interprocedural analysis
	  SetVector<ReturnInst*> analyzeFunction(Function* F);
};

// Alias Analysis result on the alias graph
class GraphAAResult : public AAResultBase {
protected:
	AliasGraph AG;

public:
	GraphAAResult(Module &M) : AG(M) {};

	bool invalidate(Module &M, const PreservedAnalyses &PA,
                  ModuleAnalysisManager::Invalidator &Inv);

	//------------------------------------------------
  // Implement the AliasAnalysis API
  //
  AliasResult alias(const MemoryLocation &LocA, const MemoryLocation &LocB,
                    AAQueryInfo &AAQI, const Instruction *CtxI);

  using AAResultBase::getModRefInfo;
  ModRefInfo getModRefInfo(const CallBase *Call, const MemoryLocation &Loc,
                           AAQueryInfo &AAQI);

  using AAResultBase::getMemoryEffects;
  /// getMemoryEffects - Return the behavior of the specified function if
  /// called from the specified call site.  The call site may be null in which
  /// case the most generic behavior of this function should be returned.
  MemoryEffects getMemoryEffects(const Function *F);

  AliasGraph &getGraph() {return AG; }
};

class GraphAA : public AnalysisInfoMixin<GraphAA> {
  friend AnalysisInfoMixin<GraphAA>;
  static AnalysisKey Key;

public:
  using Result = GraphAAResult;

  GraphAAResult run(Module &M, ModuleAnalysisManager &AM);
};

/// Legacy wrapper pass to provide the GraphAAResult object.
class GraphAAWrapperPass : public ModulePass {
  std::unique_ptr<GraphAAResult> Result;

public:
  static char ID;

  GraphAAWrapperPass();

  GraphAAResult &getResult() { return *Result; }
  const GraphAAResult &getResult() const { return *Result; }

  bool runOnModule(Module &M) override;
  bool doFinalization(Module &M) override;
  void getAnalysisUsage(AnalysisUsage &AU) const override;
};

ModulePass *createGraphAAWrapperPass();

} // namespace llvm

#endif
