#ifndef __AUFBV_JITGEN_H__
#define __AUFBV_JITGEN_H__

#include <list>
#include <vector>
#include <map>
#include <set>

#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Verifier.h"
#include "llvm/IR/LegacyPassManager.h"
// #include "llvm/IR/PassManager.h"
#include "llvm/ADT/APFloat.h"
#include "llvm/Support/Error.h"
#include "llvm/Transforms/InstCombine/InstCombine.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Scalar/GVN.h"
#include "llvm/Transforms/Utils.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Transforms/Utils/Cloning.h"

#include "context/cdlist.h"
#include "context/context.h"
#include "expr/kind.h"
#include "expr/node.h"
#include "theory/theory.h"
#include "theory/uf/theory_uf.h"
#include "theory/uf/equality_engine.h"
#include "smt/assertions.h"
#ifdef ENABLE_LLVM11
#include "aufbv-jit-11.h"
#else
#include "aufbv-jit.h"
#endif
#include "aufbv-wrafl.h"
#include "fsolve.h"

struct AUFBVFuzzStat;

namespace cvc5 {
extern bool fuzzSolveFirst;
extern bool FPMergedInBV;
namespace api {
  // Signal from symbolic execution
  extern bool call_from_symbolic_execution;
}
namespace cgen {
extern AUFBVJitGenerator* jitgen;
extern std::vector<std::map<std::string, uint64_t>> ModelsFromSMTSolver;
extern cvc5::smt::Assertions *AssertionListPtr;
/*
* JIT environments
*/
extern std::unique_ptr<llvm::orc::AUFBVJIT> TheJIT;
extern std::set<std::string> JITFunctionNames;
extern std::set<std::string> specialFunctions;
extern bool registerJITFunction(void* F);
extern bool isSpecialFunction(std::string name);
extern std::string getSpecialFunctionName(std::string name);

/*
* JIT environments ends
*/

class AUFBVJitGenerator {
private:
  /*
  * LLVM environments
  */
  bool cleaned;
  #ifdef ENABLE_LLVM11
  #else
  llvm::orc::ResourceTrackerSP RT;
  llvm::orc::ThreadSafeModule TSM;
  #endif
  std::unique_ptr<llvm::Module> TheModule;
  std::unique_ptr<llvm::IRBuilder<>> Builder;
  std::unique_ptr<llvm::legacy::FunctionPassManager> TheFPM;
  std::map<std::string, llvm::Function*> functionMap;
  // Important pointers
  llvm::Function* TargetFunction;
  llvm::BasicBlock *EntryBB, *ThenBB, *ElseBB;
  llvm::Value* OracleInfoPtr;
  // helper functions
  llvm::AllocaInst *CreateEntryBlockAlloca(llvm::Function *TheFunction, const std::string &VarName, llvm::Type *type);
  llvm::Value *CreateGlobalVar(const std::string &VarName, llvm::Type *type);
  llvm::Value* FPExtOrFPTrunc(llvm::Value* v, llvm::Type* toType, std::string name="");
  llvm::Value* FPAndConstCmp(llvm::Value* v, double cv, llvm::CmpInst::Predicate pred, std::string name="");
  /*
  * LLVM environments ends
  */

  /*
  * Constraints information
  */
  // function information
  std::map<std::string, std::pair<std::vector<unsigned int>, std::vector<bool>>> function_declarations; // function name, <function_declaration_sizes, function_declaration_is_float_vector> (e.g., (return value size, arg sizes))
  std::map<std::string, std::vector<Node>> function_to_nodes; // function name to node
  // constraint information
  std::set<Node> reused_subexpressions;
  theory::NodeSet varlist; // simple variables, array variables
  std::map<Node, Node> derived_vars;
  std::map<Node, std::set<Node>> eq_vars;
  std::set<size_t> skipped_facts_indices;
  std::map<std::string, uint64_t> arraySizeMap; // array size needed
  std::map<std::string, std::map<size_t, uint64_t>> arrayConstMap; // constants in arrays
  // helper variables and functions
  void collectFunctionDeclarations();
  theory::NodeSet findApplyUF(const Node &nd) const;
  std::set<Node> visited_nodes;
  void collectConstraintsInformation();
  void visitExpr(Node const& node, size_t level, size_t assertion_index, bool under_or=false);
  bool check_same_varname(Node const& node, std::string& varname);
  bool check_pattern_bv_incremental_polynomial(Node const& node);
  bool check_pattern_bv_divisible(Node const& node);
  bool check_pattern_bv_divisible_2(Node const& node);
  bool check_pattern_bv_or(Node const& node);

  bool collectReusedInformation(Node const& node); // return whether the node is reused
  void collectVariableInformation(Node const& node);
  void collectDerivedInformation(Node const& node, size_t level, size_t assertion_index, bool under_or=false);
  /*
  * Constraints information ends
  */

  /*
  * Fuzzing information
  */
  // seed information
  size_t seedSize;
  std::map<std::string, std::pair<size_t,size_t>> varPosMap; // variable name, <start index, byte length>
  std::vector<std::vector<size_t>> dataInfo; // [[1, start, len], [0, start, len]]
  std::map<std::string, std::vector<size_t>> varFlexibleConstraints; // _DIVISIBLE, const1, _REQUIRE_STRICT_MODE, _LT, const2, _REAL_MODE
  // std::map<Node, llvm::AllocaInst*> varLLVMAllocas; // allocations
  std::map<Node, llvm::Value*> varLLVMAllocas; // var values
  std::vector<std::string> addedGlobalVarSymbols; // added global variable names
  std::map<Node, llvm::Value*> tempVarLLVMValues; // temp values
  // target function information
  static const std::string targetFunctionBaseName;
  size_t targetFunctionCnt;
  std::vector<std::vector<uint8_t>> targetFunctionRelatedBits; // 1 represents related
  // solution information
  static uint8_t solutionMagicPtr;
  std::pair<std::shared_ptr<uint8_t>, size_t> solution;
  std::map<std::string, std::vector<uint64_t>> arrayModels;
  std::map<Node, Node> crashModel;
  std::map<std::string, uint64_t> oracleIdMap;
  std::map<uint64_t, std::string> oracleIdReverseMap;
  std::map<uint64_t, size_t> oracleIdToLen;
  uint64_t oracleIdCnt;
  size_t oracleInfoLen;
  /*
  * Fuzzing information ends
  */

  /*
  * Core interfaces: initializer, reset, fuzz, codegen, read crash input
  */
  void codegen();
  void createDataCopyFunction(bool switchEndian=false);
  void createDataInitFunction();
  void createDataStoreFunction();
  void storeOracleInfo(Node const& node, llvm::Value* value);
  void codegenLoadLocalVars();
  llvm::Value* codegenRecursive(Node const& node, bool reverse=false, bool tempDump=false);
  llvm::Value* codegenBvConcat2(Node const& node);
  llvm::Value* codegenBvConcat(Node const& node);
  bool concatIsLSHR(Node const& nd);
  llvm::Value* ltLoss(llvm::Value* dlhs, llvm::Value* drhs);
  llvm::Value* leqLoss(llvm::Value* dlhs, llvm::Value* drhs);
  llvm::Value* gtLoss(llvm::Value* dlhs, llvm::Value* drhs);
  llvm::Value* geqLoss(llvm::Value* dlhs, llvm::Value* drhs);
  llvm::Value* eqLoss(llvm::Value* dlhs, llvm::Value* drhs);
  llvm::Value* neqLoss(llvm::Value* dlhs, llvm::Value* drhs);
  llvm::Value* specialPredicateLoss(Node const& node, bool reverse=false);
  llvm::Value* isNanLoss(Node const& node, bool reverse=false);
  llvm::Value* isInfLoss(Node const& node, bool reverse=false);
  llvm::Value* isSNLoss(Node const& node, bool reverse=false);
  llvm::Value* isNLoss(Node const& node, bool reverse=false);
  llvm::Value* isZLoss(Node const& node, bool reverse=false);
  llvm::Value* isPosLoss(Node const& node, bool reverse=false);
  llvm::Value* isNegLoss(Node const& node, bool reverse=false);
  /*
  * Core interfaces ends
  */

  /*
  * JIT interfaces
  */
  void addSpecialFunctionsDeclarations();
  void InitializeModuleAndPassManager();
  void InitializeTargetFunctionInModule(std::string funcname);
  void ClearModuleAndPassManager();
  /*
  * JIT interfaces ends
  */

  /*
  * Miscellaneous helper functions
  */
  std::string getNodeName(Node const&) const;
  size_t bvSize2byteSize(size_t bvsize);
  void get_all_varnames(Node const& node, std::vector<std::string>& dest);
  void get_all_varnodes(Node const& node, std::vector<Node>& dest);
  void get_all_kinds(Node const& node, std::set<Kind>& dest);
  bool evaluate_bitvector(Node const& nd, uint64_t& result);
  /*
  * Miscellaneous helper functions ends
  */
public:
  /*
  * Core interfaces: initializer, reset, fuzz, codegen, read crash input
  */
  void reset();
  AUFBVJitGenerator(theory::Theory *Th);
  // ~AUFBVJitGenerator();
  AUFBVFuzzStat fuzz(bool dofuzz, unsigned int timeout);
  AUFBVFuzzStat fuzz(bool dofuzz);  // default timeout 60s
  void readCrashInput();
  inline std::map<Node, Node> getCrashModel() { return crashModel; }
  void learnOracleInfo();
  /*
  * Core interfaces ends
  */

  /*
  * SMT environments
  */
  theory::Theory* theoryPtr;
  theory::eq::EqualityEngine* ee;
  /*
  * SMT environments ends
  */

  /*
  * Helper functions
  */
  inline bool hasInputVars() {
    return (varlist.size());
  }
  void load_target(std::string dlib_path);
  bool evaluate_uf(std::string& funcname, uint64_t& result, std::vector<uint64_t>& args, std::vector<unsigned int>& arg_width_vector, std::vector<bool>& arg_is_float_vector);
  /*
  * Helper functions ends
  */

  /*
  * Deprecated functions: only to keep the program compiled successfully
  */
  void dumpPartialModel(std::map<Node, Node> nmap);
  /*
  * Deprecated functions ends
  */
};
}  // namespace cgen
}  // namespace cvc5

#endif
