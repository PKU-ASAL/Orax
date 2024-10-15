#include "aufbv-jitgen.h"
#include "aufbv-utils.h"
#include <boost/throw_exception.hpp>
#include "theory/bv/theory_bv_rewrite_rules_constant_evaluation.h"
#include "theory/bv/theory_bv_rewrite_rules_normalization.h"
#include "theory/bv/theory_bv_utils.h"
#include <chrono>
#include <sys/stat.h>
#include <future>
#include <chrono>
#include <thread>
#include <functional>
#include "expr/node_traversal.h"
#include "expr/type_node.h"
#include <set>
#include <stack>
#include "aufbv-evaluator.h"
#include "llvm/IR/ValueSymbolTable.h"
#include "aufbv-utils.h"

namespace cvc5 {
// orax
theory::NodeSet oracleInfo;
namespace theory {
  cvc5::Result fuzzResult = cvc5::Result::UNSAT;
  bool unsatFlag = false;
  bool reuseLastFuzz = false;
}
namespace api {
  // Signal from symbolic execution
  bool call_from_symbolic_execution = false;
}
namespace cgen {
AUFBVJitGenerator* jitgen = nullptr;
std::vector<std::map<std::string, uint64_t>> ModelsFromSMTSolver;
cvc5::smt::Assertions *AssertionListPtr = nullptr;
static bool ContainOr = false;
bool VerificationMode = false;
// extern bool VerificationModeFsolve;
// extern bool VerificationModeResult;
bool registered = false;
static bool open_derived_vars = true;
static u_int64_t getMask(unsigned int len){
  assert(len <= 64 && len > 0);
  uint64_t res;
  if (len == 64)
    res = 0xFFFFFFFFFFFFFFFF;
  else
    res = (1ULL << len) - 1;
  assert(res != 0);
  return res;
}
/*
* LLVM environments
*/
static llvm::ExitOnError ExitOnErr;
static std::unique_ptr<llvm::LLVMContext> TheContext = std::make_unique<llvm::LLVMContext>();
llvm::AllocaInst *AUFBVJitGenerator::CreateEntryBlockAlloca(llvm::Function *TheFunction,
                                          const std::string &VarName, llvm::Type *type) {
  llvm::IRBuilder<> TmpB(ElseBB, ElseBB->begin());
  return TmpB.CreateAlloca(type, nullptr, VarName);
}
llvm::Value *AUFBVJitGenerator::CreateGlobalVar(const std::string &VarName, llvm::Type *type) {
  // create global variable
  // check the existence of the global variable
  llvm::GlobalVariable *gvar = TheModule->getGlobalVariable(VarName);
  if (gvar)
    assert(false);
  gvar = new llvm::GlobalVariable(*TheModule, type, false, llvm::GlobalValue::ExternalLinkage, nullptr, VarName);
  // initialize the global variable
  llvm::Constant *init = llvm::Constant::getNullValue(type);
  gvar->setInitializer(init);
  // record the global variable name
  addedGlobalVarSymbols.push_back(VarName);
  return gvar;
}
void AUFBVJitGenerator::load_target(std::string dlib_path) {
  // dlib_path ends with .a
  assert(dlib_path.substr(dlib_path.size() - 2) == ".a");
  // Replace .a with .bc
  std::string bc_path = dlib_path.substr(0, dlib_path.size() - 2) + ".bc";
  llvm::SMDiagnostic error;
  // Load the module from .bc file
  std::unique_ptr<llvm::LLVMContext> context = std::make_unique<llvm::LLVMContext>();
  std::unique_ptr<llvm::Module> externalModule = llvm::parseIRFile(bc_path, error, *context);
  if (!externalModule) {
    // print in red
    llvm::errs() << "\033[31m" << "Failed to load the module " << dlib_path << ": " << error.getMessage().str() << "\n" << "\033[0m";
  }
  // Verify the module
  if (verifyModule(*externalModule, &llvm::errs())) {
    // print in red
    llvm::errs() << "\033[31m" << "Failed to verify the module " << dlib_path << "\n" << "\033[0m";
  }
  externalModule->setDataLayout(TheJIT->getDataLayout());
  // unset target triple
  externalModule->setTargetTriple("");
  #ifdef ENABLE_CBF_DEBUG
  // print externalModule
  llvm::errs() << "\033[36m" << "* External Module:\n" << "\033[0m";
  externalModule->print(llvm::errs(), nullptr);
  // print all symbols in the module
  llvm::errs() << "\033[36m" << "* Symbols in External Module:\n" << "\033[0m";
  #endif
  llvm::ValueSymbolTable &VST = externalModule->getValueSymbolTable();
  std::vector<std::string> symbolNames;
  for (llvm::ValueSymbolTable::iterator i = VST.begin(); i != VST.end(); i++) {
      #ifdef ENABLE_CBF_DEBUG
      llvm::outs() << i->getKey() << "\n";
      #endif
      symbolNames.push_back(i->getKey().str());
  }
  std::string module_name = "register-function";
  std::unique_ptr<llvm::Module> newModule = std::make_unique<llvm::Module>(module_name, *context);
  newModule->setDataLayout(TheJIT->getDataLayout());
  // register all functions in the module
  #ifdef ENABLE_CBF_DEBUG
  llvm::errs() << "\033[36m" << "* Symbols in External Module:\n" << "\033[0m";
  llvm::errs() << "\033[36m" << "symbolNames.size(): " << symbolNames.size() << "\n" << "\033[0m";
  #endif
  for (auto& symbolName : symbolNames){
    #ifdef ENABLE_CBF_DEBUG
    llvm::errs() << "\033[36m" << "symbolName: " << symbolName << "\n" << "\033[0m";
    #endif
    // get function
    llvm::Function* func = externalModule->getFunction(symbolName);
    if (!func) {
      continue;
    }
    #ifdef ENABLE_CBF_DEBUG
    if (func->getLinkage() == llvm::GlobalValue::LinkageTypes::ExternalLinkage)
      llvm::errs() << "\033[36m" << "ExternalLinkage: " << symbolName << "\n" << "\033[0m";
    else if (func->getLinkage() == llvm::GlobalValue::LinkageTypes::InternalLinkage)
      llvm::errs() << "\033[36m" << "InternalLinkage: " << symbolName << "\n" << "\033[0m";
    else
      llvm::errs() << "\033[36m" << "OtherLinkage: " << symbolName << "\n" << "\033[0m";
    #endif
    func->setLinkage(llvm::GlobalValue::LinkageTypes::ExternalLinkage);
    if (!copyLLVMFunctionToModule(func, newModule.get())){
      // Prompt in red
      llvm::errs() << "\033[31m" << "load_target: failed to copy function " << func->getName() << " to module\n" << "\033[0m";
      assert(false);
    }
  }
  // Add the new module to the JIT
  #ifdef ENABLE_LLVM11
  // TheJIT->addModule(std::move(newModule));
  ExitOnErr(TheJIT->addModule(std::move(newModule)));
  #else
  auto RT = TheJIT->getMainJITDylib().createResourceTracker();
  auto TSM = llvm::orc::ThreadSafeModule(std::move(newModule), std::move(context));
  ExitOnErr(TheJIT->addModule(std::move(TSM), RT));
  #endif
  // make sure all functions can be found in JIT
  for (auto& symbolName : symbolNames){
    llvm::Function* func = externalModule->getFunction(symbolName);
    if (!func)
      continue;
    #ifdef ENABLE_CBF_DEBUG
    llvm::errs() << "\033[36m" << "Checking symbolName: " << symbolName << "\n" << "\033[0m";
    #endif
    #ifdef ENABLE_LLVM11
    auto ExprSymbol = ExitOnErr(TheJIT->lookup(symbolName));
    #else
    llvm::JITEvaluatedSymbol ExprSymbol = ExitOnErr(TheJIT->lookup(symbolName));
    #endif
    assert(ExprSymbol && "Function not found");
  }
  return;
}

bool AUFBVJitGenerator::evaluate_uf(std::string& funcname, uint64_t& result, std::vector<uint64_t>& args, std::vector<unsigned int>& arg_width_vector, std::vector<bool>& arg_is_float_vector){
  #ifdef CVC4_USE_SYMFPU
  assert(false);
  #endif
  // find the runtime address of the function
  #ifdef ENABLE_LLVM11
  auto ExprSymbol = ExitOnErr(TheJIT->lookup(funcname));
  #else
  llvm::JITEvaluatedSymbol ExprSymbol = ExitOnErr(TheJIT->lookup(funcname));
  #endif
  assert(ExprSymbol && "Function not found");
  #ifdef ENABLE_LLVM11
  auto func = ExprSymbol.getAddress();
  #else
  auto func = ExprSymbol.getAddress();
  #endif
  uint64_t retValue = 0;
  assert(arg_width_vector.size() > 0);
  auto retWidth = arg_width_vector[0];
  uint64_t mask = getMask(retWidth);
  retValue = evaluateExFunc((void*)func, arg_width_vector, arg_is_float_vector, args);
  result = retValue & mask;
  return true;
}

/*
* LLVM environments ends
*/

/*
* JIT environments
*/
std::unique_ptr<llvm::orc::AUFBVJIT> TheJIT = nullptr;
std::set<std::string> JITFunctionNames = std::set<std::string>();
static void InitializeJIT() {
  llvm::InitializeNativeTarget();
  llvm::InitializeNativeTargetAsmPrinter();
  llvm::InitializeNativeTargetAsmParser();
#ifdef ENABLE_LLVM11
  TheJIT = ExitOnErr(llvm::orc::AUFBVJIT::Create());
#else
  llvm::Error error = llvm::orc::AUFBVJIT::Create().moveInto(TheJIT);
  if (error) {
    llvm::errs() << "Failed to create TheJIT: " << error << "\n";
  }
#endif
}
static std::set<std::string> specialPredicates = {"isinf", "isnan"};
// std::set<std::string> specialFunctions = {"fabs", "sqrt", "isinf", "isfinite", "isnan", "sin", "cos", "tan", "floor", "ceil", "pow", "log", "exp", "expm1", "fmod", "fmax", "fmin"};
// FIXME: buggy with logic of declareRelatedFunctionsInOrder
std::set<std::string> specialFunctions = {};
bool isSpecialFunction(std::string name){
  bool isMangled = false;
  // check if the name is mangled
  if (name.size() >= 2 && name[0] == '_' && name[1] == 'Z')
    isMangled = true;
  // count the number of _
  int cnt = 0;
  int cnt_threshold = isMangled ? 1 : 0;
  for (size_t i = 0; i < name.size(); ++i){
    if (name[i] == '_')
      cnt++;
  }
  if (cnt > cnt_threshold)
    return false;
  for (auto it = specialFunctions.begin(); it != specialFunctions.end(); ++it){
    if (name.find(*it) != std::string::npos)
      return true;
  }
  return false;
}
std::string getSpecialFunctionName(std::string name){
  if (!isSpecialFunction(name))
    return name;
  for (auto it = specialFunctions.begin(); it != specialFunctions.end(); ++it){
    if (name.find(*it) != std::string::npos)
      return *it;
  }
  assert(false);
}
bool registerJITFunction(void* F){
  llvm::Function* func = (llvm::Function*)F;
  std::string funcname = func->getName().str();
  // if function is a special function, return true
  bool special = isSpecialFunction(funcname);
  if (special)
    return true;
  // Already registered
  if(JITFunctionNames.find(funcname) != JITFunctionNames.end())
    return true;
  // Make sure the JIT environment is initialized
  if(!TheJIT)
    InitializeJIT();
  // Prepare new module
  std::string module_name = "register-function";
  std::unique_ptr<llvm::Module> m = std::make_unique<llvm::Module>(module_name, *TheContext);
  m->setDataLayout(TheJIT->getDataLayout());
  // Add cloned function and its definition into the new module
  if (!special && !copyLLVMFunctionToModule(func, m.get())){
    // Prompt in red
    llvm::errs() << "\033[31m" << "registerJITFunction: failed to copy function " << func->getName() << " to module\n" << "\033[0m";
    assert(false);
    return false;
  }
  // Add the new module to JIT
  #ifdef ENABLE_LLVM11
  ExitOnErr(TheJIT->addModule(std::move(m)));
  #else
  auto RT = TheJIT->getMainJITDylib().createResourceTracker();
  auto TSM = llvm::orc::ThreadSafeModule(std::move(m), std::move(TheContext));
  ExitOnErr(TheJIT->addModule(std::move(TSM), RT));
  #endif
  JITFunctionNames.insert(func->getName().str());
  registered = true;
  return true;
}
/*
* JIT environments ends
*/

/*
* Constraints information
*/
// helper functions
theory::NodeSet AUFBVJitGenerator::findApplyUF(const Node &nd) const{
  NodeDfsIterable ndfs(nd, VisitOrder::PREORDER);
  NodeDfsIterator bi = ndfs.begin();
  NodeDfsIterator be = ndfs.end();

  theory::NodeSet ufs;

  for (; bi != be; ++bi) {
    Node node = *bi;
    if (node.getKind() == kind::APPLY_UF) {
      ufs.insert(node);
    }
  }

  return ufs;
}
void AUFBVJitGenerator::collectFunctionDeclarations(){
  auto thi = theoryPtr->facts_begin();
  auto the = theoryPtr->facts_end();
  auto _thi = AssertionListPtr->getAssertionList()->begin();
  auto _the = AssertionListPtr->getAssertionList()->end();
  std::set<std::string> function_declared;
  if (ContainOr) {
    for (;_thi != _the;++_thi) {
      Node tnode = Node(*_thi);
      // find all APPLY_UF nodes
      theory::NodeSet ns = findApplyUF(tnode);
      for (auto n: ns){
        assert(n.getKind() == kind::APPLY_UF);
        std::string funcName = n.getOperator().toString();
        // store function node
        if (function_to_nodes.find(funcName) == function_to_nodes.end()){
          function_to_nodes[funcName] = std::vector<Node>();
        }
        function_to_nodes[funcName].push_back(n);
        if (function_declared.find(funcName) != function_declared.end())
          continue;
        // FIXME: assert return type is bitvector or boolean
        assert(n.getType().isBitVector() || n.getType().isBoolean() || n.getType().isFloatingPoint());
        // type of return value
        size_t retWidth;
        llvm::Type* retType;
        if (n.getType().isBitVector()){
          retWidth = n.getType().getBitVectorSize();
          retType = llvm::Type::getIntNTy(*TheContext, retWidth);
        }
        else if (n.getType().isBoolean()){
          retWidth = 1;
          retType = llvm::Type::getInt1Ty(*TheContext);
        }
        else if (n.getType().isFloatingPoint())
        {
          retWidth = n.getType().getFloatingPointExponentSize() + n.getType().getFloatingPointSignificandSize();
          assert(retWidth == 32 || retWidth == 64);
          if (retWidth == 32)
            retType = llvm::Type::getFloatTy(*TheContext);
          else if (retWidth == 64)
            retType = llvm::Type::getDoubleTy(*TheContext);
          else
            assert(false);
        }
        else {
          assert(false);
        }
        // type of arguments
        size_t argc = n.getNumChildren();
        std::vector<llvm::Type*> argTypes(argc);
        for (size_t i = 0; i < argc; ++i){
          // FIXME: assert arg type is bitvector or floating point
          if (n[i].getType().isBitVector()){
            size_t width = n[i].getType().getBitVectorSize();
            argTypes[i] = llvm::Type::getIntNTy(*TheContext, width);
          }
          else if (n[i].getType().isFloatingPoint()){
            size_t width = n[i].getType().getFloatingPointExponentSize() + n[i].getType().getFloatingPointSignificandSize();
            assert(width == 32 || width == 64);
            if (width == 32)
              argTypes[i] = llvm::Type::getFloatTy(*TheContext);
            else if (width == 64)
              argTypes[i] = llvm::Type::getDoubleTy(*TheContext);
            else
              assert(false);
          }
          else {
            assert(false);
          }
        }
        // declare function
        #ifdef ENABLE_CBF_DEBUG
        llvm::errs() << "declare function: " << funcName << "\n";
        #endif
        if (functionMap.find(funcName) == functionMap.end()){
          // function not declared
          llvm::FunctionType *FT = llvm::FunctionType::get(retType, argTypes, false);
          llvm::Function *f = llvm::Function::Create(FT, llvm::Function::ExternalLinkage, funcName, TheModule.get());
          functionMap[funcName] = f;
        }
        // store declaration information
        assert(function_declarations.find(funcName) == function_declarations.end());
        std::vector<bool> function_declaration_is_float_vector;
        std::vector<unsigned int> function_declaration_sizes;
        if (n.getType().isFloatingPoint())
        {
          function_declaration_is_float_vector.push_back(true);
          function_declaration_sizes.push_back(retWidth);
        }
        else
        {
          function_declaration_is_float_vector.push_back(false);
          function_declaration_sizes.push_back(retWidth);
        }
        for (size_t i = 0; i < argc; ++i){
          if (n[i].getType().isFloatingPoint())
          {
            function_declaration_is_float_vector.push_back(true);
            function_declaration_sizes.push_back(n[i].getType().getFloatingPointExponentSize() + n[i].getType().getFloatingPointSignificandSize());
          }
          else if (n[i].getType().isBitVector())
          {
            function_declaration_is_float_vector.push_back(false);
            function_declaration_sizes.push_back(n[i].getType().getBitVectorSize());
          }
          else
          {
            assert(false);
          }
        }
        function_declarations[funcName] = std::make_pair(function_declaration_sizes, function_declaration_is_float_vector);
        function_declared.insert(funcName);
      }
    }
  }
  else {
    for (;thi != the;++thi) {
      Node tnode = Node(*thi);
      // find all APPLY_UF nodes
      theory::NodeSet ns = findApplyUF(tnode);
      for (auto n: ns){
        assert(n.getKind() == kind::APPLY_UF);
        std::string funcName = n.getOperator().toString();
        // store function node
        if (function_to_nodes.find(funcName) == function_to_nodes.end()){
          function_to_nodes[funcName] = std::vector<Node>();
        }
        function_to_nodes[funcName].push_back(n);
        if (function_declared.find(funcName) != function_declared.end())
          continue;
        // FIXME: assert return type is bitvector or boolean
        assert(n.getType().isBitVector() || n.getType().isBoolean() || n.getType().isFloatingPoint());
        // type of return value
        size_t retWidth;
        llvm::Type* retType;
        if (n.getType().isBitVector()){
          retWidth = n.getType().getBitVectorSize();
          retType = llvm::Type::getIntNTy(*TheContext, retWidth);
        }
        else if (n.getType().isBoolean()){
          retWidth = 1;
          retType = llvm::Type::getInt1Ty(*TheContext);
        }
        else if (n.getType().isFloatingPoint())
        {
          retWidth = n.getType().getFloatingPointExponentSize() + n.getType().getFloatingPointSignificandSize();
          assert(retWidth == 32 || retWidth == 64);
          if (retWidth == 32)
            retType = llvm::Type::getFloatTy(*TheContext);
          else if (retWidth == 64)
            retType = llvm::Type::getDoubleTy(*TheContext);
          else
            assert(false);
        }
        else {
          assert(false);
        }
        // type of arguments
        size_t argc = n.getNumChildren();
        std::vector<llvm::Type*> argTypes(argc);
        for (size_t i = 0; i < argc; ++i){
          // FIXME: assert arg type is bitvector or floating point
          if (n[i].getType().isBitVector()){
            size_t width = n[i].getType().getBitVectorSize();
            argTypes[i] = llvm::Type::getIntNTy(*TheContext, width);
          }
          else if (n[i].getType().isFloatingPoint()){
            size_t width = n[i].getType().getFloatingPointExponentSize() + n[i].getType().getFloatingPointSignificandSize();
            assert(width == 32 || width == 64);
            if (width == 32)
              argTypes[i] = llvm::Type::getFloatTy(*TheContext);
            else if (width == 64)
              argTypes[i] = llvm::Type::getDoubleTy(*TheContext);
            else
              assert(false);
          }
          else {
            assert(false);
          }
        }
        // declare function
        #ifdef ENABLE_CBF_DEBUG
        llvm::errs() << "declare function: " << funcName << "\n";
        #endif
        if (functionMap.find(funcName) == functionMap.end()){
          // function not declared
          llvm::FunctionType *FT = llvm::FunctionType::get(retType, argTypes, false);
          llvm::Function *f = llvm::Function::Create(FT, llvm::Function::ExternalLinkage, funcName, TheModule.get());
          functionMap[funcName] = f;
        }
        // store declaration information
        assert(function_declarations.find(funcName) == function_declarations.end());
        std::vector<bool> function_declaration_is_float_vector;
        std::vector<unsigned int> function_declaration_sizes;
        if (n.getType().isFloatingPoint())
        {
          function_declaration_is_float_vector.push_back(true);
          function_declaration_sizes.push_back(retWidth);
        }
        else
        {
          function_declaration_is_float_vector.push_back(false);
          function_declaration_sizes.push_back(retWidth);
        }
        for (size_t i = 0; i < argc; ++i){
          if (n[i].getType().isFloatingPoint())
          {
            function_declaration_is_float_vector.push_back(true);
            function_declaration_sizes.push_back(n[i].getType().getFloatingPointExponentSize() + n[i].getType().getFloatingPointSignificandSize());
          }
          else if (n[i].getType().isBitVector())
          {
            function_declaration_is_float_vector.push_back(false);
            function_declaration_sizes.push_back(n[i].getType().getBitVectorSize());
          }
          else
          {
            assert(false);
          }
        }
        function_declarations[funcName] = std::make_pair(function_declaration_sizes, function_declaration_is_float_vector);
        function_declared.insert(funcName);
      }
    }
  }
}
bool AUFBVJitGenerator::check_pattern_bv_incremental_polynomial(Node const& node){
  // check pattern 1
  // f(a, b, c) < const, f with only bvadd and bvmul -> a/b/c: _LT, const2, _REQUIRE_STRICT_MODE
  if (node.getKind() != kind::LT && node.getKind() != kind::LEQ && node.getKind() != kind::EQUAL){
    return false;
  }
  assert(node.getNumChildren() == 2);
  Node expr = node[0];
  Node constNode = node[1];
  if (constNode.getKind() != kind::CONST_BITVECTOR){
    return false;
  }
  std::set<Kind> ops;
  get_all_kinds(expr, ops);
  // make sure ops only contain bvadd, bvmul, bv variables and constants
  std::set<Kind> allowed_ops = {kind::BITVECTOR_PLUS, kind::BITVECTOR_MULT, kind::VARIABLE, kind::CONST_BITVECTOR};
  for (auto it = ops.begin(); it != ops.end(); ++it){
    if (allowed_ops.find(*it) == allowed_ops.end()){
      return false;
    }
  }
  // make sure all variables are in varlist
  std::vector<Node> vars;
  get_all_varnodes(expr, vars);
  for (auto it = vars.begin(); it != vars.end(); ++it){
    assert(it->getKind() == kind::VARIABLE);
    // assert(varlist.find(*it) != varlist.end());
    auto varname = getNodeName(*it);
    if (varFlexibleConstraints.find(varname) == varFlexibleConstraints.end()){
      varFlexibleConstraints[varname] = std::vector<size_t>();
    }
    if (node.getKind() == kind::LT)
      varFlexibleConstraints[varname].push_back(_LT);
    else if (node.getKind() == kind::LEQ)
      varFlexibleConstraints[varname].push_back(_LEQ);
    else if (node.getKind() == kind::EQUAL)
      varFlexibleConstraints[varname].push_back(_LEQ);
    else
      assert(false);
    varFlexibleConstraints[varname].push_back(constNode.getConst<BitVector>().getValue().getUnsignedLong());
    varFlexibleConstraints[varname].push_back(_REQUIRE_STRICT_MODE);
  }
  return true;
}
bool AUFBVJitGenerator::check_pattern_bv_divisible(Node const& node){
  // check pattern 2
  // a * b * c = const -> a/b/c: _DIVISIBLE, const, _REQUIRE_STRICT_MODE
  if (node.getKind() != kind::EQUAL){
    return false;
  }
  assert(node.getNumChildren() == 2);
  if (node[0].getKind() != kind::CONST_BITVECTOR && node[1].getKind() != kind::CONST_BITVECTOR){
    return false;
  }
  Node expr, constNode;
  if (node[0].getKind() == kind::CONST_BITVECTOR){
    expr = node[1];
    constNode = node[0];
  }
  else {
    expr = node[0];
    constNode = node[1];
  }
  assert(constNode.getKind() == kind::CONST_BITVECTOR);
  if (constNode.getConst<BitVector>().getValue().getUnsignedLong() == 0){
    // a * b * c = 0: easy to solve, save cmp_value 0 for later
    return false;
  }
  std::set<Kind> ops;
  get_all_kinds(expr, ops);
  // make sure ops only contain bvmul, bv variables and constants
  std::set<Kind> allowed_ops = {kind::BITVECTOR_MULT, kind::VARIABLE, kind::CONST_BITVECTOR};
  for (auto it = ops.begin(); it != ops.end(); ++it){
    if (allowed_ops.find(*it) == allowed_ops.end()){
      return false;
    }
  }
  // make sure all variables are in varlist
  std::vector<Node> vars;
  get_all_varnodes(expr, vars);
  for (auto it = vars.begin(); it != vars.end(); ++it){
    assert(it->getKind() == kind::VARIABLE);
    // assert(varlist.find(*it) != varlist.end());
    auto varname = getNodeName(*it);
    if (varFlexibleConstraints.find(varname) == varFlexibleConstraints.end()){
      varFlexibleConstraints[varname] = std::vector<size_t>();
    }
    varFlexibleConstraints[varname].push_back(_DIVISIBLE);
    varFlexibleConstraints[varname].push_back(constNode.getConst<BitVector>().getValue().getUnsignedLong());
    varFlexibleConstraints[varname].push_back(_REQUIRE_STRICT_MODE);
  }
  return true;
}
bool AUFBVJitGenerator::check_pattern_bv_divisible_2(Node const& node){
  // check pattern 3
  // a * b * c = var -> a/b/c: _DIVISIBLE, const, _REQUIRE_STRICT_MODE
  if (node.getKind() != kind::EQUAL){
    return false;
  }
  assert(node.getNumChildren() == 2);
  if (node[0].getKind() != kind::VARIABLE && node[1].getKind() != kind::VARIABLE){
    return false;
  }
  Node expr, varNode;
  if (node[0].getKind() == kind::VARIABLE){
    expr = node[1];
    varNode = node[0];
  }
  else {
    expr = node[0];
    varNode = node[1];
  }
  assert(varNode.getKind() == kind::VARIABLE);
  std::set<Kind> ops;
  get_all_kinds(expr, ops);
  // make sure ops only contain bvmul, bv variables and constants
  std::set<Kind> allowed_ops = {kind::BITVECTOR_MULT, kind::VARIABLE, kind::CONST_BITVECTOR};
  for (auto it = ops.begin(); it != ops.end(); ++it){
    if (allowed_ops.find(*it) == allowed_ops.end()){
      return false;
    }
  }
  // if ops only contain VARIABLE, return false
  if (ops.size() == 1 && ops.find(kind::VARIABLE) != ops.end()){
    return false;
  }
  // make sure all variables are in varlist
  std::vector<Node> vars;
  get_all_varnodes(expr, vars);
  for (auto it = vars.begin(); it != vars.end(); ++it){
    assert(it->getKind() == kind::VARIABLE);
    // assert(varlist.find(*it) != varlist.end());
    auto varname = getNodeName(*it);
    if (varFlexibleConstraints.find(varname) == varFlexibleConstraints.end()){
      varFlexibleConstraints[varname] = std::vector<size_t>();
    }
    varFlexibleConstraints[varname].push_back(_DIVISIBLE);
    varFlexibleConstraints[varname].push_back(0);
    varFlexibleConstraints[varname].push_back(_REQUIRE_STRICT_MODE);
  }
  return true;
}
bool AUFBVJitGenerator::check_pattern_bv_or(Node const& node){
  // check pattern 4
  // (or (x = q) (x = q)) -> x: _OR, possible value cnt, possible value1, ..., _REQUIRE_STRICT_MODE
  if (node.getKind() != kind::OR){
    return false;
  }
  std::set<std::string> varnames;
  for (unsigned int i = 0; i < node.getNumChildren(); ++i){
    if (node[i].getKind() != kind::EQUAL){
      return false;
    }
    assert(node[i].getNumChildren() == 2);
    if (!((node[i][0].getKind() == kind::VARIABLE && node[i][1].getKind() == kind::CONST_BITVECTOR) || (node[i][1].getKind() == kind::VARIABLE && node[i][0].getKind() == kind::CONST_BITVECTOR))){
      return false;
    }
    else {
      Node varNode, constNode;
      if (node[i][0].getKind() == kind::VARIABLE){
        varNode = node[i][0];
        constNode = node[i][1];
      }
      else {
        varNode = node[i][1];
        constNode = node[i][0];
      }
      assert(varNode.getKind() == kind::VARIABLE);
      varnames.insert(getNodeName(varNode));
    }
  }
  if (varnames.size() != 1){
    return false;
  }
  assert(varnames.size() == 1);
  auto varname = *varnames.begin();
  if (varFlexibleConstraints.find(varname) == varFlexibleConstraints.end()){
    varFlexibleConstraints[varname] = std::vector<size_t>();
  }
  varFlexibleConstraints[varname].push_back(_OR);
  varFlexibleConstraints[varname].push_back(node.getNumChildren());
  for (unsigned int i = 0; i < node.getNumChildren(); ++i){
    Node constNode;
    if (node[i][0].getKind() == kind::VARIABLE){
      constNode = node[i][1];
    }
    else {
      constNode = node[i][0];
    }
    assert(constNode.getKind() == kind::CONST_BITVECTOR);
    varFlexibleConstraints[varname].push_back(constNode.getConst<BitVector>().getValue().getUnsignedLong());
  }
  varFlexibleConstraints[varname].push_back(_REQUIRE_STRICT_MODE);
  return true;
}
void AUFBVJitGenerator::collectConstraintsInformation(){
  visited_nodes.clear();
  reused_subexpressions.clear();
  size_t assertion_index = 0;
  if (ContainOr){
    auto thi = AssertionListPtr->getAssertionList()->begin();
    auto the = AssertionListPtr->getAssertionList()->end();
    for (; thi != the; ++thi){
      Node tnode = Node(*thi);
      auto _ = check_pattern_bv_incremental_polynomial(tnode);
      auto __ = check_pattern_bv_divisible(tnode);
      auto ___ = check_pattern_bv_divisible_2(tnode);
    }
    thi = AssertionListPtr->getAssertionList()->begin();
    for (; thi != the; ++thi){
      Node tnode = Node(*thi);
      visitExpr(tnode, 0, assertion_index++);
    }
  }
  else{
    auto thi = theoryPtr->facts_begin();
    auto the = theoryPtr->facts_end();
    for (; thi != the; ++thi){
      Node tnode = Node(*thi);
      // f(a, b, c) < const, f with only bvadd and bvmul -> a/b/c: _LT, const2, _REQUIRE_STRICT_MODE
      // a * b * c = const -> a/b/c: _DIVISIBLE, const, _REQUIRE_STRICT_MODE
      auto _ = check_pattern_bv_incremental_polynomial(tnode);
      auto __ = check_pattern_bv_divisible(tnode);
      auto ___ = check_pattern_bv_divisible_2(tnode);
      auto ____ = check_pattern_bv_or(tnode);
    }
    thi = theoryPtr->facts_begin();
    for (; thi != the; ++thi){
      Node tnode = Node(*thi);
      visitExpr(tnode, 0, assertion_index++);
    }
  }
  return;
}
void AUFBVJitGenerator::visitExpr(Node const& node, size_t level, size_t assertion_index, bool under_or){
  /*
  * Reused information
  */
  if(collectReusedInformation(node)){
    return;
  }
  /*
  * Reused information ends
  */

  /*
  * Variable information
  */
  collectVariableInformation(node);
  /*
  * Variable information ends
  */

  /*
  * Derived information
  */
  if (open_derived_vars){
    collectDerivedInformation(node, level, assertion_index, under_or);
  }
  /*
  * Derived information ends
  */

  // recursively visit expressions
  for(unsigned int i = 0; i < node.getNumChildren(); ++i){
    if (node.getKind() == kind::OR)
      visitExpr(node[i], level + 1, assertion_index, true);
    else
      visitExpr(node[i], level + 1, assertion_index, under_or);
  }
  return;
}
bool AUFBVJitGenerator::check_same_varname(Node const& node, std::string& varname){
  if (node.getKind() == kind::VARIABLE){
    if (getNodeName(node) == varname)
      return true;
  }
  for (unsigned int i = 0; i < node.getNumChildren(); ++i){
    if (check_same_varname(node[i], varname))
      return true;
  }
  return false;
}
bool AUFBVJitGenerator::collectReusedInformation(Node const& node){
  // once visited
  if (visited_nodes.find(node) != visited_nodes.end()){
    // constants and variables not included
    if (node.getKind() != kind::CONST_RATIONAL && node.getKind() != kind::CONST_BITVECTOR && node.getKind() != kind::VARIABLE)
      reused_subexpressions.insert(node);
    return true;
  }
  visited_nodes.insert(node);
  return false;
}
void AUFBVJitGenerator::collectVariableInformation(Node const& node){
  if (node.getKind() == kind::VARIABLE){
    // add new variable
    if (varlist.end() == varlist.find(node)) varlist.insert(node);
  }
  else if (node.getKind() == kind::SELECT){
    // update array size information
    assert(node.getNumChildren() == 2);
    std::string arrayName = getNodeName(node[0]);
    uint64_t index;
    // get index
    if (node[1].isConst()){
      index = node[1].getConst<BitVector>().getValue().getUnsignedLong();
    }
    else {
      if (!evaluate_bitvector(node[1], index)){
        // array access with a variable index
        assert(false);
      }
    }
    // update
    if (arraySizeMap.find(arrayName) == arraySizeMap.end()){
      arraySizeMap[arrayName] = index + 1;
    }
    else {
      if (arraySizeMap[arrayName] < index + 1)
        arraySizeMap[arrayName] = index + 1;
    }
  }
}
void AUFBVJitGenerator::collectDerivedInformation(Node const& node, size_t level, size_t assertion_index, bool under_or){
  if (under_or)
    return;
  // If var = expr(other vars), this variable doesn't need to be fuzzed
  // Need to make sure this EQUAL is not part of NOT EQUAL
  // Not on the top level: confusing, maybe buggy
  // if (node.getKind() != kind::NOT){
  // FIXME: this does not handle (and (and (and ...))) very well
  if (node.getKind() == kind::AND){
    for (unsigned int i = 0; i < node.getNumChildren(); ++i){
      // EQUAL, not NOT EQUAL
      if (node[i].getKind() == Kind::EQUAL){
        assert(node[i].getNumChildren() == 2);
        Node varNode, exprNode;
        bool isCandidate = false;
        if (node[i][0].getKind() == Kind::VARIABLE && !node[i][0].getType().isArray()){
          // var = expr(other vars)
          varNode = node[i][0];
          exprNode = node[i][1];
          isCandidate = true;
        }
        else if (node[i][1].getKind() == Kind::VARIABLE && !node[i][1].getType().isArray()){
          // expr(other vars) = var
          varNode = node[i][1];
          exprNode = node[i][0];
          isCandidate = true;
        }
        if (isCandidate){
          std::string varname = getNodeName(varNode);
          bool ignore = false;
          // check in varFlexibleConstraints whether v of v = expr has _OR constraints
          if (varFlexibleConstraints.find(varname) != varFlexibleConstraints.end()){
            auto info = varFlexibleConstraints[varname];
            int step = 3;
            for (int i = 0; i < info.size(); i+=step){
              auto op = info[i];
              if (op == _OR){
                  auto value_cnt = info[i + 1];
                  auto mode = info[i + 1 + value_cnt + 1];
                  assert(mode == _REQUIRE_STRICT_MODE);
                  ignore = true;
                  break;
                  step = 1 + value_cnt + 2;
              }
              else {
                  step = 3;
              }
            }
          }
          // if (!ignore && !check_same_varname(exprNode, varname)){
          if (!check_same_varname(exprNode, varname)){
            assert(derived_vars.find(varNode) == derived_vars.end());
            derived_vars[varNode] = exprNode;
          }
        }
      }
    }
  }
  // On the top level
  // FIXME: buggy? expr1 = x, x = expr2
  if (level == 0 && node.getKind() == Kind::EQUAL){
    assert(node.getNumChildren() == 2);
    Node varNode, exprNode;
    bool isCandidate = false;
    if (node[0].getKind() == Kind::VARIABLE && node[1].getKind() == Kind::VARIABLE){
      // a=b, b=a both exist
      std::string varname1 = getNodeName(node[0]);
      std::string varname2 = getNodeName(node[1]);
      assert(varname1 != varname2);
      if (varname1 < varname2){
        varNode = node[0];
        exprNode = node[1];
      }
      else {
        varNode = node[1];
        exprNode = node[0];
      }
      isCandidate = true;
    }
    else if (node[0].getKind() == Kind::VARIABLE && !node[0].getType().isArray()){
      // var = expr(other vars)
      varNode = node[0];
      exprNode = node[1];
      isCandidate = true;
    }
    else if (node[1].getKind() == Kind:: VARIABLE && !node[1].getType().isArray()){
      // expr(other vars) = var
      varNode = node[1];
      exprNode = node[0];
      isCandidate = true;
    }
    if (isCandidate){
      std::string varname = getNodeName(varNode);
      bool ignore = false;
      // check in varFlexibleConstraints whether v of v = expr has _OR constraints
      if (varFlexibleConstraints.find(varname) != varFlexibleConstraints.end()){
        auto info = varFlexibleConstraints[varname];
        int step = 3;
        for (int i = 0; i < info.size(); i+=step){
          auto op = info[i];
          if (op == _OR){
              auto value_cnt = info[i + 1];
              auto mode = info[i + 1 + value_cnt + 1];
              assert(mode == _REQUIRE_STRICT_MODE);
              ignore = true;
              break;
              step = 1 + value_cnt + 2;
          }
          else {
              step = 3;
          }
        }
      }
      // if (!ignore && !check_same_varname(exprNode, varname)){
      if (!check_same_varname(exprNode, varname)){
        if (derived_vars.find(varNode) == derived_vars.end()){
          derived_vars[varNode] = exprNode;
          skipped_facts_indices.insert(assertion_index);
        }
      }
    }
  }
  // If array[const index] = constant, this element of array doesn't need to be fuzzed
  // On the top level
  if (level == 0 && node.getKind() == Kind::EQUAL){
    assert(node.getNumChildren() == 2);
    Node elementNode, exprNode;
    bool isCandidate = false;
    if (node[0].getKind() == Kind::SELECT && node[0][0].getType().isArray() && node[0][1].isConst() && node[1].isConst()) {
      // array[const index] = constant
      elementNode = node[0];
      exprNode = node[1];
      isCandidate = true;
    }
    else if (node[1].getKind() == Kind::SELECT && node[1][0].getType().isArray() && node[1][1].isConst() && node[0].isConst()) {
      // constant = array[const index]
      elementNode = node[1];
      exprNode = node[0];
      isCandidate = true;
    }
    if (isCandidate){
      uint64_t index = elementNode[1].getConst<BitVector>().getValue().getUnsignedLong();
      uint64_t value = exprNode.getConst<BitVector>().getValue().getUnsignedLong();
      std::string arrayName = getNodeName(elementNode[0]);
      // update arrayConstMap
      if (arrayConstMap.find(arrayName) == arrayConstMap.end())
        arrayConstMap[arrayName] = std::map<size_t, uint64_t>();
      arrayConstMap[arrayName][index] = value;
      // update arrayModels
      if (arrayModels.find(arrayName) == arrayModels.end())
        arrayModels[arrayName] = std::vector<uint64_t>(index + 1);
      if (arrayModels[arrayName].size() < index + 1)
        arrayModels[arrayName].resize(index + 1);
      arrayModels[arrayName][index] = value;
    }
  }
}
/*
* Constraints information ends
*/

/*
* Core interfaces: initializer, reset, fuzz, codegen, read crash input
*/
// In-class variable initialization
uint8_t AUFBVJitGenerator::solutionMagicPtr = 0x10;
const std::string AUFBVJitGenerator::targetFunctionBaseName = "targetFunction";
// Initializer
void AUFBVJitGenerator::reset(){
  /*
  * LLVM environments
  */
  cleaned = true;
  functionMap.clear();
  /*
  * LLVM environments ends
  */

  /*
  * Constraints information
  */
  // function information
  function_declarations.clear();
  function_to_nodes.clear();
  // constraint information
  reused_subexpressions.clear();
  varlist.clear();
  derived_vars.clear();
  eq_vars.clear();
  skipped_facts_indices.clear();
  arraySizeMap.clear();
  arrayConstMap.clear();
  // helper variables and functions
  visited_nodes.clear();
  /*
  * Constraints information ends
  */

  /*
  * Fuzzing information
  */
  // seed information
  seedSize = 0;
  varPosMap.clear();
  dataInfo.clear();
  varFlexibleConstraints.clear();
  varLLVMAllocas.clear();
  addedGlobalVarSymbols.clear();
  tempVarLLVMValues.clear();
  // target function information
  targetFunctionCnt = 0;
  targetFunctionRelatedBits.clear();
  // solution information
  solution = std::make_pair(nullptr, 0);
  arrayModels.clear();
  crashModel.clear();
  oracleIdMap.clear();
  oracleIdReverseMap.clear();
  oracleIdToLen.clear();
  oracleIdCnt = 0;
  oracleInfoLen = 0;
  OracleInfoPtr = nullptr;
  /*
  * Fuzzing information ends
  */
}
AUFBVJitGenerator::AUFBVJitGenerator(theory::Theory *Th): theoryPtr(Th){
  ee = theoryPtr->getEqualityEngine();
  // Initialize variables
  reset();
  // Initialize JIT environment
  if (!TheJIT)
    InitializeJIT();
}
// Fuzz interfaces
AUFBVFuzzStat AUFBVJitGenerator::fuzz(bool dofuzz) {
  auto start = std::chrono::steady_clock::now();
  auto result = fuzz(dofuzz, 60);
  auto end = std::chrono::steady_clock::now();
  if (cvc5::theory::fuzzResult == cvc5::Result::UNSAT){
    learnOracleInfo();
  }
  else {
    oracleKeyPoints.clear();
  }

  // time in seconds (double)
  double elapsed_time = std::chrono::duration_cast<std::chrono::milliseconds>(end - start).count() / 1000.0;
  #ifdef ENABLE_CBF_DEBUG
  // print in green
  llvm::errs() << "\033[32m" << "Total elapsed time: " << elapsed_time << "s\n" << "\033[0m";
  #endif
  return result;
}
AUFBVFuzzStat AUFBVJitGenerator::fuzz(bool dofuzz, unsigned int timeout)
{
  #ifdef ENABLE_CBF_DEBUG
  auto fstart = std::chrono::steady_clock::now();
  #endif
  dofuzz = true;
  AUFBVFuzzStat fuzzStat;
  assert(dofuzz);
  if (dofuzz)
  {
    // orax
    auto start = std::chrono::steady_clock::now();
    /*
    * Code generation
    */
    if (!cleaned && cvc5::theory::reuseLastFuzz) {
      #ifdef ENABLE_CBF_DEBUG
      llvm::errs() << "\033[36m" << "* Reuse Code Generated Last Time.\n" << "\033[0m";
      #endif
    }
    else {
      #ifdef ENABLE_CBF_DEBUG
      llvm::errs() << "\033[36m" << "* Start Code Generation.\n" << "\033[0m";
      #endif
      codegen();
      #ifdef ENABLE_CBF_DEBUG
      llvm::errs() << "\033[36m" << "* Finish Code Generation.\n" << "\033[0m";
      llvm::errs() << "\033[36m" << "* Current Module:\n" << "\033[0m";
      TheModule->print(llvm::errs(), nullptr);
      #endif
    }
    /*
    * Code generation ends
    */

    // if seedSize == 0, then it is satisfiable?
    if (seedSize == 0) {
      if (!VerificationMode){
        // update fuzz state
        fuzzStat.crashed = true;
        fuzzStat.timeOut = false;
        // update fuzz solution
        solution.first = std::make_shared<uint8_t>(solutionMagicPtr);
        return fuzzStat;
      }
    }

    /*
    * JIT generated code
    */
    // JIT generated code
    if(!cleaned && cvc5::theory::reuseLastFuzz){
      #ifdef ENABLE_CBF_DEBUG
      llvm::errs() << "\033[36m" << "* Reuse JITed Code Last Time.\n" << "\033[0m";
      #endif
    }
    else {
    #ifdef ENABLE_LLVM11
        ExitOnErr(TheJIT->addModule(std::move(TheModule)));
    #else
        RT = TheJIT->getMainJITDylib().createResourceTracker();
        TSM = llvm::orc::ThreadSafeModule(std::move(TheModule), std::move(TheContext));
        ExitOnErr(TheJIT->addModule(std::move(TSM), RT));
    #endif
        assert(targetFunctionCnt >= 1);
        jitgen = this;
    }
    cleaned = false;

    // Find runtime address of JITed target functions
    std::vector<loss_function_ptr> targets(targetFunctionCnt);

    for(size_t i = 0; i < targetFunctionCnt; ++i){
      std::string funcname = targetFunctionBaseName + std::to_string(i);
      // Find runtime address of JITed target function
      #ifdef ENABLE_LLVM11
      auto ExprSymbol = ExitOnErr(TheJIT->lookup(funcname));
      #else
      llvm::JITEvaluatedSymbol ExprSymbol = ExitOnErr(TheJIT->lookup(funcname));
      #endif
      assert(ExprSymbol && "Function not found");
      #ifdef ENABLE_LLVM11
      targets[i] = (loss_function_ptr)ExprSymbol.getAddress();
      #else
      targets[i] = (loss_function_ptr)ExprSymbol.getAddress();
      #endif
    }
    /*
    * JIT generated code ends
    */

    /*
    * Fuzz solve
    */
    #ifdef ENABLE_CBF_DEBUG
    // print in yellow
    llvm::errs() << "\033[33m" << "* Start fsolve_targets.\n" << "\033[0m";
    auto startf = std::chrono::steady_clock::now();
    llvm::errs() << "\033[33m" << "* Codegen time taken: " << std::chrono::duration_cast<std::chrono::milliseconds>(startf - fstart).count()/1000.0 << "sec\n" << "\033[0m";
    #endif
    // prepare fuzz initial seeds from ModelsFromSMTSolver
    std::vector<std::vector<uint8_t>> initialFuzzSeeds;
    for (auto &model : ModelsFromSMTSolver){
      std::vector<uint8_t> fuzzSeed(seedSize, 0);
      // get information from varPosMap
      for (auto &p : varPosMap){
        std::string varname = p.first;
        auto pospair = p.second;
        size_t start, len;
        start = pospair.first;
        len = pospair.second;
        assert(start + len <= seedSize);
        assert(model.find(varname) != model.end());
        auto value = model[varname];
        for (size_t i = 0; i < len; ++i){
          fuzzSeed[start + i] = (value >> ((len - 1 - i) * 8)) & 0xff;
        }
      }
      initialFuzzSeeds.push_back(fuzzSeed);
    }
    if (VerificationMode){
      VerificationModeFsolve = true;
      VerificationModeResult = false;
    }
    else {
      VerificationModeFsolve = false;
      VerificationModeResult = false;
    }
    solution = fsolve_targets(targets, seedSize, targetFunctionRelatedBits, dataInfo, oracleInfoLen, oracleIdToLen, oracleIdReverseMap, initialFuzzSeeds);
    if (VerificationMode){
      if (VerificationModeResult){
        cvc5::theory::unsatFlag = false;
        // update fuzz state
        fuzzStat.crashed = true;
        fuzzStat.timeOut = false;
      }
      else {
        cvc5::theory::unsatFlag = true;
        // update fuzz state
        fuzzStat.crashed = false;
        fuzzStat.timeOut = false;
      }
      cvc5::theory::timeoutFlag = false;
      cvc5::theory::fuzzResult = cvc5::Result::UNSAT;
      return fuzzStat;
    }
    #ifdef ENABLE_CBF_DEBUG
    auto stopf = std::chrono::steady_clock::now();
    // print in yellow
    llvm::errs() << "\033[33m" << "* Finish fsolve_targets.\n" << "\033[0m";
    llvm::errs() << "\033[33m" << "* Fuzzing time taken: " << std::chrono::duration_cast<std::chrono::milliseconds>(stopf - startf).count()/1000.0 << "sec\n" << "\033[0m";
    #endif
    /*
    * Fuzz solve ends
    */
    auto stop = std::chrono::steady_clock::now();

    /*
    * Clear JITed functions
    */
   if (!cvc5::theory::reuseLastFuzz){
    #ifdef ENABLE_LLVM11
      // ExitOnErr(TheJIT->removeTargets(targetFunctionCnt));
      std::vector<std::string> symbolNames;
      symbolNames.push_back("dataCopy");
      symbolNames.push_back("dataInit");
      symbolNames.push_back("dataStore");
      for (size_t i = 0; i < targetFunctionCnt; ++i){
        std::string funcname = targetFunctionBaseName + std::to_string(i);
        symbolNames.push_back(funcname);
      }
      for (auto it = addedGlobalVarSymbols.begin(); it != addedGlobalVarSymbols.end(); ++it){
        symbolNames.push_back(*it);
      }
      ExitOnErr(TheJIT->removeSymbols(symbolNames));
    #else
      ExitOnErr(RT->remove());
    #endif
      ClearModuleAndPassManager();
      cleaned = true;
      jitgen = nullptr;
    }
    /*
    * Clear JITed functions ends
    */

    // check solutions
    if (solution.first == nullptr){
      fuzzStat.timeOut = true;
    }
    #ifdef ENABLE_CBF_DEBUG
    llvm::errs() << "\033[36m" << "* Solution of fsolve_targets:\n" << "\033[0m";
    llvm::errs() << "Timed out : " << fuzzStat.timeOut << "\n";
    #endif

    if (fuzzStat.timeOut) {
      #ifdef ENABLE_CBF_DEBUG
      // print in red
      llvm::errs() << "\033[31m" << "Timeout.\n" << "\033[0m";
      llvm::errs() << "\033[31m" << "Satisfiability: UNKNOWN.\n" << "\033[0m";
      #endif
      fuzzStat.crashed = false;
      fuzzStat.timeOut = true;
      cvc5::theory::timeoutFlag = true;
      // FIXME: SAT_UNKNOWN may be a better choice, but it requires a reason
      cvc5::theory::fuzzResult = cvc5::Result::UNSAT;
    }
    else {
      #ifdef ENABLE_CBF_DEBUG
      // print in green
      llvm::errs() << "\033[32m" << "No Timeout.\n" << "\033[0m";
      llvm::errs() << "\033[32m" << "Satisfiability: SAT.\n" << "\033[0m";
      #endif
      fuzzStat.crashed = true;
      fuzzStat.timeOut = false;
      cvc5::theory::timeoutFlag = false;
      cvc5::theory::fuzzResult = cvc5::Result::SAT;
    }
  }
  else
  {
    // orax
    assert(false);
  }
  return fuzzStat;
}
// codegen
void AUFBVJitGenerator::codegen(){
  // Reset environments
  reset();
  InitializeModuleAndPassManager();

  Trace("fuzzer-codegen") << "Generating fuzz target program..." << std::endl;

  /*
  * Collect information from constraints
  */
  auto _thi_ = AssertionListPtr->getAssertionList()->begin();
  auto _the_ = AssertionListPtr->getAssertionList()->end();
  cvc5::cgen::ContainOr = false;
  for (; _thi_ != _the_; ++_thi_){
    Node tnode = Node(*_thi_);
    if (check_pattern_bv_or(tnode)){
      cvc5::cgen::ContainOr = true;
      break;
    }
  }
  // collect function declarations
  collectFunctionDeclarations();
  // collect constraints information
  collectConstraintsInformation();

  #ifdef ENABLE_CBF_DEBUG
  // print derived_vars
  llvm::errs() << "\033[36m" << "* Variables that can be induced:\n" << "\033[0m";
  if (derived_vars.size() == 0)
    llvm::errs() << "\033[36m" << "None\n" << "\033[0m\n";
  for (auto it = derived_vars.begin(); it != derived_vars.end(); ++it){
    if (it != derived_vars.begin())
      llvm::errs() << ", ";
    llvm::errs() << getNodeName(it->first);
  }
  llvm::errs() << "\n";
  #endif
  /*
  * Collect information from constraints ends
  */

  /*
  * Seed information organization: seed size, variable positions, target related bits
  */
  // prepare variable positions and update seedSize
  auto thi = theoryPtr->facts_begin();
  auto the = theoryPtr->facts_end();
  auto _thi = AssertionListPtr->getAssertionList()->begin();
  auto _the = AssertionListPtr->getAssertionList()->end();
  assert(seedSize == 0);
  for (Node nd : varlist) {
    // skip variables that can be derived from other variables
    if (derived_vars.find(nd) != derived_vars.end()) {
      continue;
    }
    if (nd.getType().isInteger()) {
      // integer variables
      size_t bvsize = 32;
      size_t bytesize = bvSize2byteSize(bvsize);
      std::string varname = getNodeName(nd);
      assert(varPosMap.find(varname) == varPosMap.end());
      varPosMap[varname] = std::make_pair(seedSize, bytesize);
      dataInfo.push_back(std::vector<size_t>{_INTEGER_TYPE, seedSize, bytesize});
      seedSize += bytesize;
    }
    else if (nd.getType().isBitVector()) {
      // bitvector variables
      size_t bvsize = nd.getType().getBitVectorSize();
      size_t bytesize = bvSize2byteSize(bvsize);
      std::string varname = getNodeName(nd);
      assert(varPosMap.find(varname) == varPosMap.end());
      varPosMap[varname] = std::make_pair(seedSize, bytesize);
      auto _info = std::vector<size_t>{_BITVECTOR_TYPE, seedSize, bytesize};
      // TODO: add varFlexibleConstraints for bv only
      if (varFlexibleConstraints.find(varname) != varFlexibleConstraints.end()){
        for (auto &c : varFlexibleConstraints[varname]){
          _info.push_back(c);
        }
      }
      dataInfo.push_back(_info);
      seedSize += bytesize;
    }
    else if (nd.getType().isArray()) {
      // array variables
      std::string aname = getNodeName(nd);
      uint32_t arrayfullsize = arraySizeMap[aname];
      uint32_t arraysize = arrayfullsize;
      // remove constant elements
      if (arrayConstMap.find(aname) != arrayConstMap.end()){
        arraysize -= arrayConstMap[aname].size();
      }
      assert(nd.getType().getArrayConstituentType().isBitVector());
      size_t elementsize = nd.getType().getArrayConstituentType().getBitVectorSize();
      size_t elementbytesize = bvSize2byteSize(elementsize);
      assert(varPosMap.find(aname) == varPosMap.end());
      varPosMap[aname] = std::make_pair(seedSize, arraysize * elementbytesize);
      // FIXME: only support bitvector array
      dataInfo.push_back(std::vector<size_t>{_ARRAY_TYPE, seedSize, arraysize * elementbytesize, _BITVECTOR_TYPE, elementbytesize});
      seedSize += arraysize * elementbytesize;
    }
    else if (nd.getType().isFloatingPoint()) {
      // floating point variables
      auto exponentSize = nd.getType().getFloatingPointExponentSize();
      auto significandSize = nd.getType().getFloatingPointSignificandSize();
      auto bitSize = exponentSize + significandSize;
      auto bytesize = bvSize2byteSize(bitSize);
      assert(exponentSize == 8 || exponentSize == 11);
      assert(significandSize == 24 || significandSize == 53);
      assert(bitSize == 32 || bitSize == 64);
      std::string varname = getNodeName(nd);
      assert(varPosMap.find(varname) == varPosMap.end());
      varPosMap[varname] = std::make_pair(seedSize, bytesize);
      dataInfo.push_back(std::vector<size_t>{_FLOAT_TYPE, seedSize, bytesize});
      seedSize += bytesize;
    }
    else {
      BOOST_THROW_EXCEPTION(std::runtime_error("Unsupported variable type"));
      exit(1);
    }
  }
  #ifdef ENABLE_CBF_DEBUG
  // print seedSize
  llvm::errs() << "* Seed size: " << seedSize << "\n";
  #endif
  VerificationMode = false;
  if (seedSize == 0){
    if (skipped_facts_indices.size() != AssertionListPtr->getAssertionList()->size()){
      VerificationMode = true;
    }
    else {
      // no seed/fuzzing needed
      return;
    }
  }
  // prepare target related bits
  assert(targetFunctionRelatedBits.size() == 0);
  size_t assertion_index = 0;
  if (ContainOr){
    for (;_thi != _the;++_thi) {
      if (skipped_facts_indices.find(assertion_index++) != skipped_facts_indices.end())
        continue;
      Node tnode = Node(*_thi);
      std::vector<std::string> varnames;
      // relatedBits initialized as all 0 with the length seedSize
      std::vector<uint8_t> relatedBits(seedSize, 0);
      // find target related variables
      get_all_varnames(tnode, varnames);
      for (std::string& name : varnames){
        // skip variables that can be derived from other variables (not in the seed)
        if (varPosMap.find(name) == varPosMap.end())
          continue;
        auto pospair = varPosMap[name];
        size_t start, len;
        start = pospair.first;
        len = pospair.second;
        assert(start + len <= seedSize);
        for (size_t i = 0; i < len; ++i){
          relatedBits[start + i] = 0xff;
        }
      }
      targetFunctionRelatedBits.push_back(relatedBits);
    }
  }
  else {
    for (;thi != the;++thi) {
      if (skipped_facts_indices.find(assertion_index++) != skipped_facts_indices.end())
        continue;
      Node tnode = Node(*thi);
      std::vector<std::string> varnames;
      // relatedBits initialized as all 0 with the length seedSize
      std::vector<uint8_t> relatedBits(seedSize, 0);
      // find target related variables
      get_all_varnames(tnode, varnames);
      for (std::string& name : varnames){
        // skip variables that can be derived from other variables (not in the seed)
        if (varPosMap.find(name) == varPosMap.end())
          continue;
        auto pospair = varPosMap[name];
        size_t start, len;
        start = pospair.first;
        len = pospair.second;
        assert(start + len <= seedSize);
        for (size_t i = 0; i < len; ++i){
          relatedBits[start + i] = 0xff;
        }
      }
      targetFunctionRelatedBits.push_back(relatedBits);
    }
  }
  /*
  * Seed information organization ends
  */

  /*
  * Utility functions generation
  */
  createDataCopyFunction();
  createDataInitFunction();
  createDataStoreFunction();
  /*
  * Utility functions generation ends
  */

  /*
  * Loss function generation
  */
  // create loss function for constraints which are not skipped
  thi = theoryPtr->facts_begin();
  _thi = AssertionListPtr->getAssertionList()->begin();
  assert(targetFunctionCnt == 0);
  assertion_index = 0;
  /*
  * Loss function generation: initialization
  */
  std::string funcname = targetFunctionBaseName + std::to_string(targetFunctionCnt++);
  InitializeTargetFunctionInModule(funcname);
  EntryBB = llvm::BasicBlock::Create(*TheContext, "entry", TargetFunction);
  ThenBB = llvm::BasicBlock::Create(*TheContext, "then", TargetFunction);
  ElseBB = llvm::BasicBlock::Create(*TheContext, "else", TargetFunction);
  Builder->SetInsertPoint(ElseBB);
  /*
  * Loss function generation: initialization ends
  */
  /*
  * Loss function generation: seed size check
  */
  // if function arg size is less than seedSize, then function return DBL_MAX
  // save insertpoint
  auto oip = Builder->saveIP();
  Builder->SetInsertPoint(EntryBB);
  llvm::Value* size = TargetFunction->getArg(1);
  llvm::Value* cmp = Builder->CreateICmpULT(size, llvm::ConstantInt::get(*TheContext, llvm::APInt(64, seedSize)), "cmp");
  Builder->CreateCondBr(cmp, ThenBB, ElseBB);
  Builder->SetInsertPoint(ThenBB);
  // return false
  Builder->CreateRet(llvm::ConstantInt::get(*TheContext, llvm::APInt(1, 0)));
  // restore insertpoint
  Builder->restoreIP(oip);
  /*
  * Loss function generation: seed size check ends
  */
  /*
  * Loss function generation: key local variables and dataInit
  */
  // Target function prototype: void target(uint8_t *data, size_t size, double *losses, size_t loss_cnt, uint64_t * oracle_info)
  llvm::Value* data = TargetFunction->getArg(0);
  llvm::Value* dataSize = TargetFunction->getArg(1);
  llvm::Value* losses = TargetFunction->getArg(2);
  llvm::Value* lossCnt = TargetFunction->getArg(3);
  llvm::Value* oracleInfo = TargetFunction->getArg(4);
  OracleInfoPtr = oracleInfo;
  Builder->CreateCall(TheModule->getFunction("dataInit"), {data, dataSize});
  /*
  * Loss function generation: key local variables and dataInit ends
  */
  size_t loss_index = 0;
  if (ContainOr){
    for (;_thi != _the;++_thi) {
      if (skipped_facts_indices.find(assertion_index++) != skipped_facts_indices.end())
        continue;
      Node tnode = Node(*_thi);
      /*
      * Loss function generation: recursively
      */
      llvm::Value* tloss = codegenRecursive(tnode);
      // save loss to losses[loss_index]
      Builder->CreateStore(tloss, Builder->CreateGEP(llvm::Type::getDoubleTy(*TheContext), losses, llvm::ConstantInt::get(*TheContext, llvm::APInt(64, loss_index))));
      loss_index++;
      /*
      * Loss function generation: recursively ends
      */
    }
  }
  else {
    for (;thi != the;++thi) {
      if (skipped_facts_indices.find(assertion_index++) != skipped_facts_indices.end())
        continue;
      Node tnode = Node(*thi);
      /*
      * Loss function generation: recursively
      */
      llvm::Value* tloss = codegenRecursive(tnode);
      // save loss to losses[loss_index]
      Builder->CreateStore(tloss, Builder->CreateGEP(llvm::Type::getDoubleTy(*TheContext), losses, llvm::ConstantInt::get(*TheContext, llvm::APInt(64, loss_index))));
      loss_index++;
      /*
      * Loss function generation: recursively ends
      */
    }
  }
  // return true
  Builder->CreateRet(llvm::ConstantInt::get(*TheContext, llvm::APInt(1, 1)));
  /*
  * Loss function generation: check consistency, optimization
  */
  // Verify the generated code, checking for consistency
  llvm::verifyFunction(*TargetFunction);
  // Optimize the function
  TheFPM->doInitialization();
  TheFPM->run(*TargetFunction);
  TheFPM->doFinalization();
  /*
  * Loss function generation: check consistency, optimization ends
  */
  if (targetFunctionCnt == 0){
    // no loss function generated, use a dummy function
    // dummy function: return 0;
    std::string funcname = targetFunctionBaseName + std::to_string(targetFunctionCnt++);
    InitializeTargetFunctionInModule(funcname);
    EntryBB = llvm::BasicBlock::Create(*TheContext, "entry", TargetFunction);
    Builder->SetInsertPoint(EntryBB);
    Builder->CreateRet(llvm::ConstantInt::get(*TheContext, llvm::APInt(1, 0)));
    // Verify the generated code, checking for consistency
    llvm::verifyFunction(*TargetFunction);
    return;
  }
  return;
}
void AUFBVJitGenerator::createDataCopyFunction(bool switchEndian){
  // void dataCopy(uint8_t* dest, uint8_t* data, size_t start, size_t len)
  llvm::FunctionType *dataCopyType = llvm::FunctionType::get(llvm::Type::getVoidTy(*TheContext), {llvm::Type::getInt8PtrTy(*TheContext), llvm::Type::getInt8PtrTy(*TheContext), llvm::Type::getInt64Ty(*TheContext), llvm::Type::getInt64Ty(*TheContext)}, false);
  llvm::Function *dataCopyFunction = llvm::Function::Create(dataCopyType, llvm::Function::ExternalLinkage, "dataCopy", TheModule.get());
  llvm::Function::arg_iterator args = dataCopyFunction->arg_begin();
  llvm::Value* dest = &*args++;
  llvm::Value* data = &*args++;
  llvm::Value* start = &*args++;
  llvm::Value* len = &*args++;
  // set arg names
  dest->setName("dest");
  data->setName("data");
  start->setName("start");
  len->setName("len");
  llvm::Type* elementType = llvm::Type::getInt8Ty(*TheContext);
  std::vector<llvm::Value *> gepIndices(1);
  // #ifdef ENABLE_LLVM11
  // move byte one by one
  // 1234(data) -> 4321(dest)
  // create a loop for moving bytes
  llvm::BasicBlock *entry = llvm::BasicBlock::Create(*TheContext, "entry", dataCopyFunction);
  llvm::BasicBlock *check = llvm::BasicBlock::Create(*TheContext, "check", dataCopyFunction);
  llvm::BasicBlock *loop = llvm::BasicBlock::Create(*TheContext, "loop", dataCopyFunction);
  llvm::BasicBlock *end = llvm::BasicBlock::Create(*TheContext, "end", dataCopyFunction);
  Builder->SetInsertPoint(entry);
  // i = 0
  auto i = Builder->CreateAlloca(llvm::Type::getInt64Ty(*TheContext), nullptr, "i");
  Builder->CreateStore(llvm::ConstantInt::get(llvm::Type::getInt64Ty(*TheContext), 0), i);
  Builder->CreateBr(check);
  Builder->SetInsertPoint(check);
  // check i < len
  #ifdef ENABLE_LLVM11
  llvm::Value* icmp = Builder->CreateICmpULT(Builder->CreateLoad(i), len, "icmp");
  #else
  llvm::Value* icmp = Builder->CreateICmpULT(Builder->CreateLoad(i->getAllocatedType(), i), len, "icmp");
  #endif
  Builder->CreateCondBr(icmp, loop, end);
  Builder->SetInsertPoint(loop);
  // move byte: dest[i] = data[start + len - 1 - i]
  #ifdef ENABLE_LLVM11
  gepIndices[0] = Builder->CreateAdd(start, Builder->CreateSub(len, Builder->CreateAdd(Builder->CreateLoad(i), llvm::ConstantInt::get(llvm::Type::getInt64Ty(*TheContext), 1))), "gepIndex");
  #else
  gepIndices[0] = Builder->CreateAdd(start, Builder->CreateSub(len, Builder->CreateAdd(Builder->CreateLoad(i->getAllocatedType(), i), llvm::ConstantInt::get(llvm::Type::getInt64Ty(*TheContext), 1))), "gepIndex");
  #endif
  llvm::Value* loadElementPtr = Builder->CreateGEP(elementType, data, gepIndices, "ptrToDataElement");
  llvm::Value* element = Builder->CreateLoad(elementType, loadElementPtr, "loadedElement");
  #ifdef ENABLE_LLVM11
  gepIndices[0] = Builder->CreateLoad(i);
  #else
  gepIndices[0] = Builder->CreateLoad(i->getAllocatedType(), i);
  #endif
  llvm::Value* storeElementPtr = Builder->CreateGEP(elementType, dest, gepIndices, "ptrToStoreElement");
  Builder->CreateStore(element, storeElementPtr);
  // i++
  #ifdef ENABLE_LLVM11
  Builder->CreateStore(Builder->CreateAdd(Builder->CreateLoad(i), llvm::ConstantInt::get(llvm::Type::getInt64Ty(*TheContext), 1)), i);
  #else
  Builder->CreateStore(Builder->CreateAdd(Builder->CreateLoad(i->getAllocatedType(), i), llvm::ConstantInt::get(llvm::Type::getInt64Ty(*TheContext), 1)), i);
  #endif
  Builder->CreateBr(check);
  Builder->SetInsertPoint(end);
  Builder->CreateRetVoid();
  return;
}
void AUFBVJitGenerator::createDataInitFunction(){
  // void dataInit(uint8_t* data, size_t len)
  llvm::FunctionType *dataInitType = llvm::FunctionType::get(llvm::Type::getVoidTy(*TheContext), {llvm::Type::getInt8PtrTy(*TheContext), llvm::Type::getInt64Ty(*TheContext)}, false);
  llvm::Function *dataInitFunction = llvm::Function::Create(dataInitType, llvm::Function::ExternalLinkage, "dataInit", TheModule.get());
  llvm::Function::arg_iterator args = dataInitFunction->arg_begin();
  llvm::Value* data = &*args++;
  llvm::Value* len = &*args++;
  // set arg names
  data->setName("data");
  len->setName("len");
  llvm::Type* elementType = llvm::Type::getInt8Ty(*TheContext);
  llvm::BasicBlock *entry = llvm::BasicBlock::Create(*TheContext, "entry", dataInitFunction);
  Builder->SetInsertPoint(entry);
  for (Node nd : varlist) {
    // skip variables that can be derived from other variables
    if (derived_vars.find(nd) != derived_vars.end()) {
      continue;
    }
    if (nd.getType().isInteger()) {
      // integer variables
      // FIXME: currently, only 32-bit integer is supported
      size_t bvsize = 32;
      size_t bytesize = bvSize2byteSize(bvsize);
      std::string vname = getNodeName(nd);
      // allocation
      llvm::Value* gvar = CreateGlobalVar(vname, llvm::Type::getIntNTy(*TheContext, bytesize << 3));
      varLLVMAllocas[nd] = gvar;
      // initialization from seed
      auto pospair = varPosMap[vname];
      size_t start = pospair.first, len = pospair.second;
      assert(len == bytesize);
      // call dataCopy
      gvar = Builder->CreateBitCast(gvar, llvm::PointerType::getUnqual(llvm::Type::getInt8Ty(*TheContext)));
      std::vector<llvm::Value *> args = {gvar, data, llvm::ConstantInt::get(llvm::Type::getInt64Ty(*TheContext), start), llvm::ConstantInt::get(llvm::Type::getInt64Ty(*TheContext), len)};
      Builder->CreateCall(TheModule->getFunction("dataCopy"), args);
    }
    else if (nd.getType().isBitVector()) {
      // bitvector variables
      std::vector<llvm::Value *> gepIndices(1);
      size_t bvsize = nd.getType().getBitVectorSize();
      size_t bytesize = bvSize2byteSize(bvsize);
      std::string vname = getNodeName(nd);
      // allocation
      llvm::Value* gvar = CreateGlobalVar(vname, llvm::Type::getIntNTy(*TheContext, bytesize << 3));
      varLLVMAllocas[nd] = gvar;
      // initialization from seed
      auto pospair = varPosMap[vname];
      size_t start = pospair.first, len = pospair.second;
      assert(len == bytesize);
      // call dataCopy
      gvar = Builder->CreateBitCast(gvar, llvm::PointerType::getUnqual(llvm::Type::getInt8Ty(*TheContext)));
      std::vector<llvm::Value *> args = {gvar, data, llvm::ConstantInt::get(llvm::Type::getInt64Ty(*TheContext), start), llvm::ConstantInt::get(llvm::Type::getInt64Ty(*TheContext), len)};
      Builder->CreateCall(TheModule->getFunction("dataCopy"), args);
    }
    else if (nd.getType().isArray()) {
      // array variables
      std::string aname = getNodeName(nd);
      uint32_t arrayfullsize = arraySizeMap[aname];
      assert(nd.getType().getArrayConstituentType().isBitVector());
      size_t elementsize = nd.getType().getArrayConstituentType().getBitVectorSize();
      size_t elementbytesize = bvSize2byteSize(elementsize);
      llvm::Type* I = llvm::IntegerType::getIntNTy(*TheContext, elementbytesize << 3);
      llvm::ArrayType* arrayType = llvm::ArrayType::get(I, arrayfullsize);
      // allocation
      llvm::Value* gvar = CreateGlobalVar(aname, arrayType);
      varLLVMAllocas[nd] = gvar;
      // initialization from seed, remember to add constant elements
      auto pospair = varPosMap[aname];
      size_t start = pospair.first, arraySeedLen = pospair.second;
      size_t seedIndexFromStart = 0;
      llvm::Value* constElementValue = CreateGlobalVar(aname + "_const_element_value", I);
      llvm::Value* constElementValueData = Builder->CreateBitCast(constElementValue, llvm::PointerType::getUnqual(llvm::Type::getInt8Ty(*TheContext)));
      for (uint32_t i = 0; i < arrayfullsize; ++i){
        llvm::Value *gvarBytePtr = Builder->CreateBitCast(gvar, llvm::PointerType::getUnqual(llvm::Type::getInt8Ty(*TheContext)));
        std::vector<llvm::Value *> gepIndices(1);
        gepIndices[0] = llvm::ConstantInt::get(llvm::Type::getInt64Ty(*TheContext), i * elementbytesize);
        llvm::Value *dest = Builder->CreateGEP(elementType, gvarBytePtr, gepIndices, "dest");
        // constant element
        if (arrayConstMap.find(aname) != arrayConstMap.end() && arrayConstMap[aname].find(i) != arrayConstMap[aname].end()){
          uint64_t constValue = arrayConstMap[aname][i];
          // switch endian
          for (int j = 0; j < elementbytesize; ++j){
            int pos1 = j, pos2 = elementbytesize - 1 - j;
            if (pos1 >= pos2)
              break;
            uint64_t byte1 = (constValue >> (pos1 << 3)) & 0xff;
            uint64_t byte2 = (constValue >> (pos2 << 3)) & 0xff;
            constValue &= ~((uint64_t)0xff << (pos1 << 3));
            constValue &= ~((uint64_t)0xff << (pos2 << 3));
            constValue |= byte1 << (pos2 << 3);
            constValue |= byte2 << (pos1 << 3);
          }
          Builder->CreateStore(llvm::ConstantInt::get(I, constValue), constElementValue);
          // call dataCopy
          // dest addr: the address of the i-th element of the array
          std::vector<llvm::Value *> args = {dest, constElementValueData, llvm::ConstantInt::get(llvm::Type::getInt64Ty(*TheContext), 0), llvm::ConstantInt::get(llvm::Type::getInt64Ty(*TheContext), elementbytesize)};
          Builder->CreateCall(TheModule->getFunction("dataCopy"), args);
          continue;
        }
        // non-constant element
        // call dataCopy
        std::vector<llvm::Value *> args = {dest, data, llvm::ConstantInt::get(llvm::Type::getInt64Ty(*TheContext), start + seedIndexFromStart), llvm::ConstantInt::get(llvm::Type::getInt64Ty(*TheContext), elementbytesize)};
        Builder->CreateCall(TheModule->getFunction("dataCopy"), args);
        seedIndexFromStart += elementbytesize;
        assert(seedIndexFromStart <= arraySeedLen);
      }
    }
    else if (nd.getType().isFloatingPoint()) {
      // floating point variables
      std::string vname = getNodeName(nd);
      auto exponentSize = nd.getType().getFloatingPointExponentSize();
      auto significandSize = nd.getType().getFloatingPointSignificandSize();
      auto bitSize = exponentSize + significandSize;
      auto bytesize = bvSize2byteSize(bitSize);
      assert(exponentSize == 8 || exponentSize == 11);
      assert(significandSize == 24 || significandSize == 53);
      assert(bitSize == 32 || bitSize == 64);
      llvm::Type* F = nullptr;
      if (bitSize == 32){
        F = llvm::Type::getFloatTy(*TheContext);
      }
      else if (bitSize == 64){
        F = llvm::Type::getDoubleTy(*TheContext);
      }
      else {
        BOOST_THROW_EXCEPTION(std::runtime_error("codegen vars implementation incomplete"));
        exit(1);
      }
      assert(F != nullptr);
      // allocation
      llvm::Value* gvar = CreateGlobalVar(vname, F);
      varLLVMAllocas[nd] = gvar;
      // initialization from seed
      auto pospair = varPosMap[vname];
      size_t start = pospair.first, len = pospair.second;
      assert(len == bytesize);
      // call dataCopy
      gvar = Builder->CreateBitCast(gvar, llvm::PointerType::getUnqual(llvm::Type::getInt8Ty(*TheContext)));
      std::vector<llvm::Value *> args = {gvar, data, llvm::ConstantInt::get(llvm::Type::getInt64Ty(*TheContext), start), llvm::ConstantInt::get(llvm::Type::getInt64Ty(*TheContext), len)};
      Builder->CreateCall(TheModule->getFunction("dataCopy"), args);
    }
    else {
      BOOST_THROW_EXCEPTION(std::runtime_error("codegen vars implementation incomplete"));
      exit(1);
    }
  }
  Builder->CreateRetVoid();
  return;
}
void AUFBVJitGenerator::createDataStoreFunction(){
  // void dataStore(uint64_t* dest, size_t index, uint64_t value)
  llvm::FunctionType *dataStoreType = llvm::FunctionType::get(llvm::Type::getVoidTy(*TheContext), {llvm::Type::getInt64PtrTy(*TheContext), llvm::Type::getInt64Ty(*TheContext), llvm::Type::getInt64Ty(*TheContext)}, false);
  llvm::Function *dataStoreFunction = llvm::Function::Create(dataStoreType, llvm::Function::ExternalLinkage, "dataStore", TheModule.get());
  llvm::Function::arg_iterator args = dataStoreFunction->arg_begin();
  llvm::Value* dest = &*args++;
  llvm::Value* index = &*args++;
  llvm::Value* value = &*args++;
  // set arg names
  dest->setName("dest");
  index->setName("index");
  value->setName("value");
  llvm::Type* elementType = llvm::Type::getInt64Ty(*TheContext);
  llvm::Type* byteType = llvm::Type::getInt8Ty(*TheContext);
  llvm::BasicBlock *entry = llvm::BasicBlock::Create(*TheContext, "entry", dataStoreFunction);
  Builder->SetInsertPoint(entry);
  std::vector<llvm::Value *> gepIndices(1);
  // #ifdef ENABLE_LLVM11
  // store value to dest[index]
  gepIndices[0] = index;
  llvm::Value* storeElementPtr = Builder->CreateGEP(elementType, dest, gepIndices, "ptrToStoreElement");
  Builder->CreateStore(value, storeElementPtr);
  Builder->CreateRetVoid();
  return;
}

void AUFBVJitGenerator::storeOracleInfo(Node const& nd, llvm::Value* value){
  // void dataStore(uint64_t* dest, size_t index, uint64_t value)
  auto dataStoreFunction = TheModule->getFunction("dataStore");
  std::vector<llvm::Value *> dataStoreArgs(3);
  dataStoreArgs[0] = OracleInfoPtr;
  dataStoreArgs[1] = llvm::ConstantInt::get(*TheContext, llvm::APInt(64, oracleInfoLen));
  dataStoreArgs[2] = value;
  if (nd == Node::null()){
    Builder->CreateCall(dataStoreFunction, dataStoreArgs);
    oracleInfoLen++;
    return;
  }
  llvm::Value* arg2 = nullptr;
  if (nd.getType().isInteger()){
    unsigned int originalWidth = nd.getType().getBitVectorSize();
    if (originalWidth != 64){
      llvm::Value* zext = Builder->CreateZExt(value, llvm::Type::getInt64Ty(*TheContext), "zext");
      arg2 = zext;
    }
    else {
      arg2 = value;
    }
  }
  else if (nd.getType().isBitVector()){
    unsigned int originalWidth = nd.getType().getBitVectorSize();
    if (originalWidth != 64){
      llvm::Value* zext = Builder->CreateZExt(value, llvm::Type::getInt64Ty(*TheContext), "zext");
      arg2 = zext;
    }
    else {
      arg2 = value;
    }
  }
  else if (nd.getType().isFloatingPoint()){
    unsigned int exp_size = nd.getType().getFloatingPointExponentSize();
    unsigned int sig_size = nd.getType().getFloatingPointSignificandSize();
    assert((exp_size == 8 && sig_size == 24) || (exp_size == 11 && sig_size == 53));
    unsigned int dst_width = exp_size + sig_size;
    if (dst_width == 32){
      arg2 = Builder->CreateBitCast(value, llvm::Type::getInt32Ty(*TheContext), "bitcast");
      arg2 = Builder->CreateZExt(arg2, llvm::Type::getInt64Ty(*TheContext), "zext");
    }
    else if (dst_width == 64){
      arg2 = Builder->CreateBitCast(value, llvm::Type::getInt64Ty(*TheContext), "bitcast");
    }
    else {
      assert(false);
    }
  }
  else {
    assert(false);
  }
  dataStoreArgs[2] = arg2;
  Builder->CreateCall(dataStoreFunction, dataStoreArgs);
  oracleInfoLen++;
  return;
}

void AUFBVJitGenerator::codegenLoadLocalVars(){
  llvm::Value* dataPtr = TargetFunction->getArg(0);
  llvm::Type* dataPtrType = dataPtr->getType();
  llvm::Type* elementType = llvm::Type::getInt8Ty(*TheContext);

  for (Node nd : varlist) {
    // skip variables that can be derived from other variables
    if (derived_vars.find(nd) != derived_vars.end()) {
      continue;
    }
    if (nd.getType().isInteger()) {
      // integer variables
      std::vector<llvm::Value *> gepIndices(1);
      size_t bvsize = 32;
      size_t bytesize = bvSize2byteSize(bvsize);
      std::string vname = getNodeName(nd);
      // allocation
      llvm::AllocaInst *Alloca = CreateEntryBlockAlloca(TargetFunction, vname, llvm::Type::getIntNTy(*TheContext, bytesize << 3));
      varLLVMAllocas[nd] = Alloca;
      // initialization from seed
      auto pospair = varPosMap[vname];
      size_t start = pospair.first, len = pospair.second;
      assert(len == bytesize);
      #ifdef ENABLE_LLVM11
      llvm::Value *AllocaElement = Builder->CreateBitCast(Alloca, llvm::PointerType::getUnqual(elementType));
      // move byte one by one
      // 1234(bv) -> 4321(buffer)
      for (size_t i = 0; i < bytesize; ++i){
        gepIndices[0] = llvm::ConstantInt::get(llvm::Type::getInt64Ty(*TheContext), start + i);
        llvm::Value* loadElementPtr = Builder->CreateGEP(elementType, dataPtr, gepIndices, "ptrToDataElement");
        llvm::Value* element = Builder->CreateLoad(elementType, loadElementPtr, "loadedElement");
        gepIndices[0] = llvm::ConstantInt::get(llvm::Type::getInt64Ty(*TheContext), bytesize - 1 - i);
        llvm::Value* storeElementPtr = Builder->CreateGEP(elementType, AllocaElement, gepIndices, "ptrToStoreElement");
        Builder->CreateStore(element, storeElementPtr);
      }
      #else
      gepIndices[0] = llvm::ConstantInt::get(llvm::Type::getInt64Ty(*TheContext), start);
      llvm::Value* loadElementPtr = Builder->CreateGEP(elementType, dataPtr, gepIndices, "ptrToDataElement");
      llvm::Type* intType = llvm::Type::getIntNTy(*TheContext, bytesize << 3);
      llvm::Value* element = Builder->CreateLoad(intType, loadElementPtr, "loadedElement");
      gepIndices[0] = llvm::ConstantInt::get(llvm::Type::getInt64Ty(*TheContext), 0);
      llvm::Value* storeElementPtr = Builder->CreateGEP(elementType, Alloca, gepIndices, "ptrToStoreElement");
      Builder->CreateStore(element, storeElementPtr);
      #endif
    }
    else if (nd.getType().isBitVector()) {
      // bitvector variables
      std::vector<llvm::Value *> gepIndices(1);
      size_t bvsize = nd.getType().getBitVectorSize();
      size_t bytesize = bvSize2byteSize(bvsize);
      std::string vname = getNodeName(nd);
      // allocation
      llvm::AllocaInst *Alloca = CreateEntryBlockAlloca(TargetFunction, vname, llvm::Type::getIntNTy(*TheContext, bytesize << 3));
      varLLVMAllocas[nd] = Alloca;
      // initialization from seed
      auto pospair = varPosMap[vname];
      size_t start = pospair.first, len = pospair.second;
      assert(len == bytesize);
      #ifdef ENABLE_LLVM11
      llvm::Value *AllocaElement = Builder->CreateBitCast(Alloca, llvm::PointerType::getUnqual(elementType));
      // move byte one by one
      // 1234(bv) -> 4321(buffer)
      for (size_t i = 0; i < bytesize; ++i){
        gepIndices[0] = llvm::ConstantInt::get(llvm::Type::getInt64Ty(*TheContext), start + i);
        llvm::Value* loadElementPtr = Builder->CreateGEP(elementType, dataPtr, gepIndices, "ptrToDataElement");
        llvm::Value* element = Builder->CreateLoad(elementType, loadElementPtr, "loadedElement");
        gepIndices[0] = llvm::ConstantInt::get(llvm::Type::getInt64Ty(*TheContext), bytesize - 1 - i);
        llvm::Value* storeElementPtr = Builder->CreateGEP(elementType, AllocaElement, gepIndices, "ptrToStoreElement");
        Builder->CreateStore(element, storeElementPtr);
      }
      #else
      gepIndices[0] = llvm::ConstantInt::get(llvm::Type::getInt64Ty(*TheContext), start);
      llvm::Value* loadElementPtr = Builder->CreateGEP(elementType, dataPtr, gepIndices, "ptrToDataElement");
      llvm::Type* intType = llvm::Type::getIntNTy(*TheContext, bytesize << 3);
      llvm::Value* element = Builder->CreateLoad(intType, loadElementPtr, "loadedElement");
      gepIndices[0] = llvm::ConstantInt::get(llvm::Type::getInt64Ty(*TheContext), 0);
      llvm::Value* storeElementPtr = Builder->CreateGEP(elementType, Alloca, gepIndices, "ptrToStoreElement");
      Builder->CreateStore(element, storeElementPtr);
      #endif
    }
    else if (nd.getType().isArray()) {
      // array variables
      std::vector<llvm::Value *> gepIndices(1);
      std::string aname = getNodeName(nd);
      uint32_t arrayfullsize = arraySizeMap[aname];
      assert(nd.getType().getArrayConstituentType().isBitVector());
      size_t elementsize = nd.getType().getArrayConstituentType().getBitVectorSize();
      size_t elementbytesize = bvSize2byteSize(elementsize);
      llvm::Type* I = llvm::IntegerType::getIntNTy(*TheContext, elementbytesize << 3);
      llvm::ArrayType* arrayType = llvm::ArrayType::get(I, arrayfullsize);
      // allocation
      llvm::AllocaInst *Alloca = CreateEntryBlockAlloca(TargetFunction, aname, arrayType);
      varLLVMAllocas[nd] = Alloca;
      // initialization from seed, remember to add constant elements
      auto pospair = varPosMap[aname];
      size_t start = pospair.first, arraySeedLen = pospair.second;
      size_t seedIndexFromStart = 0;
      for (uint32_t i = 0; i < arrayfullsize; ++i){
        // constant element
        if (arrayConstMap.find(aname) != arrayConstMap.end() && arrayConstMap[aname].find(i) != arrayConstMap[aname].end()){
          uint64_t constValue = arrayConstMap[aname][i];
          #ifdef ENABLE_LLVM11
          llvm::Value *AllocaElement = Builder->CreateBitCast(Alloca, llvm::PointerType::getUnqual(elementType));
          // move byte one by one
          // 1234(bv) -> 4321(buffer)
          for (size_t j = 0; j < elementbytesize; ++j){
            gepIndices[0] = llvm::ConstantInt::get(llvm::Type::getInt64Ty(*TheContext), i * elementbytesize + elementbytesize - 1 - j);
            llvm::Value* storeElementPtr = Builder->CreateGEP(elementType, AllocaElement, gepIndices, "ptrToStoreElement");
            uint8_t constByte = (constValue >> (j << 3)) & 0xff;
            llvm::Value* element = llvm::ConstantInt::get(llvm::Type::getInt64Ty(*TheContext), constByte);
            Builder->CreateStore(element, storeElementPtr);
          }
          #else
          gepIndices[0] = llvm::ConstantInt::get(llvm::Type::getInt64Ty(*TheContext), i);
          llvm::Value* storeElementPtr = Builder->CreateGEP(I, Alloca, gepIndices, "ptrToStoreElement");
          llvm::Value* element = llvm::ConstantInt::get(I, constValue);
          Builder->CreateStore(element, storeElementPtr);
          #endif
          continue;
        }
        // non-constant element
        #ifdef ENABLE_LLVM11
        llvm::Value *AllocaElement = Builder->CreateBitCast(Alloca, llvm::PointerType::getUnqual(elementType));
        // move byte one by one
        // 1234(bv) -> 4321(buffer)
        for (size_t j = 0; j < elementbytesize; ++j){
          gepIndices[0] = llvm::ConstantInt::get(llvm::Type::getInt64Ty(*TheContext), start + seedIndexFromStart + j);
          llvm::Value* loadElementPtr = Builder->CreateGEP(elementType, dataPtr, gepIndices, "ptrToDataElement");
          llvm::Value* element = Builder->CreateLoad(elementType, loadElementPtr, "loadedElement");
          gepIndices[0] = llvm::ConstantInt::get(llvm::Type::getInt64Ty(*TheContext), i * elementbytesize + elementbytesize - 1 - j);
          llvm::Value* storeElementPtr = Builder->CreateGEP(elementType, AllocaElement, gepIndices, "ptrToStoreElement");
          Builder->CreateStore(element, storeElementPtr);
        }
        seedIndexFromStart += elementbytesize;
        #else
        gepIndices[0] = llvm::ConstantInt::get(llvm::Type::getInt64Ty(*TheContext), start + seedIndexFromStart);
        llvm::Value* loadElementPtr = Builder->CreateGEP(elementType, dataPtr, gepIndices, "ptrToDataElement");
        llvm::Value* element = Builder->CreateLoad(I, loadElementPtr, "loadedElement");
        gepIndices[0] = llvm::ConstantInt::get(llvm::Type::getInt64Ty(*TheContext), i);
        llvm::Value* storeElementPtr = Builder->CreateGEP(I, Alloca, gepIndices, "ptrToStoreElement");
        Builder->CreateStore(element, storeElementPtr);
        seedIndexFromStart += elementbytesize;
        #endif
        assert(seedIndexFromStart <= arraySeedLen);
      }
    }
    else if (nd.getType().isFloatingPoint()) {
      // floating point variables
      std::vector<llvm::Value *> gepIndices(1);
      std::string vname = getNodeName(nd);
      auto exponentSize = nd.getType().getFloatingPointExponentSize();
      auto significandSize = nd.getType().getFloatingPointSignificandSize();
      auto bitSize = exponentSize + significandSize;
      auto bytesize = bvSize2byteSize(bitSize);
      assert(exponentSize == 8 || exponentSize == 11);
      assert(significandSize == 24 || significandSize == 53);
      assert(bitSize == 32 || bitSize == 64);
      llvm::Type* F = nullptr;
      if (bitSize == 32){
        F = llvm::Type::getFloatTy(*TheContext);
      }
      else if (bitSize == 64){
        F = llvm::Type::getDoubleTy(*TheContext);
      }
      else {
        BOOST_THROW_EXCEPTION(std::runtime_error("codegen vars implementation incomplete"));
        exit(1);
      }
      assert(F != nullptr);
      // allocation
      llvm::AllocaInst *Alloca = CreateEntryBlockAlloca(TargetFunction, vname, F);
      varLLVMAllocas[nd] = Alloca;
      // initialization from seed
      auto pospair = varPosMap[vname];
      size_t start = pospair.first, len = pospair.second;
      assert(len == bytesize);
      #ifdef ENABLE_LLVM11
      llvm::Value *AllocaElement = Builder->CreateBitCast(Alloca, llvm::PointerType::getUnqual(elementType));
      // move byte one by one
      // 1234(bv) -> 4321(buffer)
      for (size_t i = 0; i < bytesize; ++i){
        gepIndices[0] = llvm::ConstantInt::get(llvm::Type::getInt64Ty(*TheContext), start + i);
        llvm::Value* loadElementPtr = Builder->CreateGEP(elementType, dataPtr, gepIndices, "ptrToDataElement");
        llvm::Value* element = Builder->CreateLoad(elementType, loadElementPtr, "loadedElement");
        gepIndices[0] = llvm::ConstantInt::get(llvm::Type::getInt64Ty(*TheContext), bytesize - 1 - i);
        llvm::Value* storeElementPtr = Builder->CreateGEP(elementType, AllocaElement, gepIndices, "ptrToStoreElement");
        Builder->CreateStore(element, storeElementPtr);
      }
      #else
      gepIndices[0] = llvm::ConstantInt::get(llvm::Type::getInt64Ty(*TheContext), start);
      llvm::Value* loadElementPtr = Builder->CreateGEP(elementType, dataPtr, gepIndices, "ptrToDataElement");
      llvm::Value* element = Builder->CreateLoad(F, loadElementPtr, "loadedElement");
      gepIndices[0] = llvm::ConstantInt::get(llvm::Type::getInt64Ty(*TheContext), 0);
      llvm::Value* storeElementPtr = Builder->CreateGEP(elementType, Alloca, gepIndices, "ptrToStoreElement");
      Builder->CreateStore(element, storeElementPtr);
      #endif
    }
    else {
      BOOST_THROW_EXCEPTION(std::runtime_error("codegen vars implementation incomplete"));
      exit(1);
    }
  }
}
static float FloatingPointTofloat(FloatingPoint fp){
  assert(fp.getExponent().getSize() == 9 && fp.getSignificand().getSize() == 24);
  int e = 0;
  double m = 0.0;
  for (size_t i = 0; i < 9; ++i){
    if ((fp.getExponent().getValue().getUnsignedLong() >> (8 - i)) & 1){
      if (i == 0){
        e += - (1 << 8);
      }
      else{
        e += 1 << (8 - i);
      }
    }
  }
  for (int i = 0; i < 24; ++i){
    if ((fp.getSignificand().getValue().getUnsignedLong() >> (23 - i)) & 1){
      m += pow(2, -i);
    }
  }
  assert(m >= 1.0 && m < 2.0);
  if (fp.isNaN())
    return std::numeric_limits<float>::quiet_NaN();
  if (fp.isInfinite()){
    float inf = std::numeric_limits<float>::infinity();
    if (!fp.getSign())
      return inf;
    u_int32_t inf_bv = *(u_int32_t*)&inf;
    assert(inf_bv == 0x7f800000);
    inf_bv = 0xff800000;
    return *(float*)&inf_bv;
  }
  if (fp.isZero() && fp.getSign())
    return -0.0;
  if (fp.isZero() && !fp.getSign())
    return 0.0;
  if (fp.isNormal())
    return (fp.getSign()? -1 : 1) * m * pow(2, e);
  if (fp.isSubnormal())
    return (fp.getSign()? -1 : 1) * m * pow(2, e);
  assert(false);
  return m * pow(2, e);
}
static double FloatingPointTodouble(FloatingPoint fp){
  assert(fp.getExponent().getSize() == 12 && fp.getSignificand().getSize() == 53);
  int e = 0;
  double m = 0.0;
  for (size_t i = 0; i < 12; ++i){
    if ((fp.getExponent().getValue().getUnsignedLong() >> (11 - i)) & 1){
      if (i == 0){
        e += - (1 << 11);
      }
      else{
        e += 1 << (11 - i);
      }
    }
  }
  for (int i = 0; i < 53; ++i){
    if ((fp.getSignificand().getValue().getUnsignedLong() >> (52 - i)) & 1){
      m += pow(2, -i);
    }
  }
  assert(m >= 1.0 && m < 2.0);
  if (fp.isNaN())
    return std::numeric_limits<double>::quiet_NaN();
  if (fp.isInfinite()){
    double inf = std::numeric_limits<double>::infinity();
    if (!fp.getSign())
      return inf;
    u_int64_t inf_bv = *(u_int64_t*)&inf;
    assert(inf_bv == 0x7ff0000000000000);
    inf_bv = 0xfff0000000000000;
    return *(double*)&inf_bv;
  }
  if (fp.isZero() && fp.getSign())
    return -0.0;
  if (fp.isZero() && !fp.getSign())
    return 0.0;
  if (fp.isNormal())
    return (fp.getSign()? -1 : 1) * m * pow(2, e);
  if (fp.isSubnormal())
    return (fp.getSign()? -1 : 1) * m * pow(2, e);
  assert(false);
  return m * pow(2, e);
}
static double RationalTodouble(Rational r){
  auto rat = r;
  int64_t num = rat.getNumerator().getLong();
  int64_t den = rat.getDenominator().getLong();
  assert(den != 0);
  double fvalue = (double)num / (double)den;
  return fvalue;
}
static uint64_t floatToBV(float f){
  uint32_t *p = (uint32_t*)&f;
  uint64_t extended = *p;
  return extended;
}
static uint64_t doubleToBV(double d){
  uint64_t *p = (uint64_t*)&d;
  return *p;
}
static float BVToFloat(uint64_t bv){
  uint32_t truncated = bv;
  return *(float*)&truncated;
}
static double BVToDouble(uint64_t bv){
  return *(double*)&bv;
}

llvm::Value* AUFBVJitGenerator::FPExtOrFPTrunc(llvm::Value* v, llvm::Type* toType, std::string name){
  llvm::Type* fromType = v->getType();
  if (fromType == toType)
    return v;
  if (fromType->isFloatTy() && toType->isDoubleTy())
    return Builder->CreateFPExt(v, toType, name);
  if (fromType->isDoubleTy() && toType->isFloatTy())
    return Builder->CreateFPTrunc(v, toType, name);
  assert(false);
  return nullptr;
}

llvm::Value* AUFBVJitGenerator::FPAndConstCmp(llvm::Value* v, double cv, llvm::CmpInst::Predicate pred, std::string name){
  llvm::Type* toType = v->getType();
  assert(toType->isFloatTy() || toType->isDoubleTy());
  llvm::Value* cv_ = nullptr;
  if (toType->isFloatTy()){
    float cvf = cv;
    cv_ = llvm::ConstantFP::get(*TheContext, llvm::APFloat(cvf));
  }
  else if (toType->isDoubleTy()){
    double cvd = cv;
    cv_ = llvm::ConstantFP::get(*TheContext, llvm::APFloat(cvd));
  }
  else{
    assert(false);
  }
  switch (pred)
  {
    case llvm::CmpInst::Predicate::FCMP_OEQ:
      return Builder->CreateFCmpOEQ(v, cv_, name);
    case llvm::CmpInst::Predicate::FCMP_OGT:
      return Builder->CreateFCmpOGT(v, cv_, name);
    case llvm::CmpInst::Predicate::FCMP_OGE:
      return Builder->CreateFCmpOGE(v, cv_, name);
    case llvm::CmpInst::Predicate::FCMP_OLT:
      return Builder->CreateFCmpOLT(v, cv_, name);
    case llvm::CmpInst::Predicate::FCMP_OLE:
      return Builder->CreateFCmpOLE(v, cv_, name);
    case llvm::CmpInst::Predicate::FCMP_ONE:
      return Builder->CreateFCmpONE(v, cv_, name);
    default:
      assert(false);
  }
}

llvm::Value *AUFBVJitGenerator::codegenRecursive(Node const& node, bool reverse, bool tempDump){
  // If the node is computed before, return the value directly
  if (tempVarLLVMValues.find(node) != tempVarLLVMValues.end()){
    return tempVarLLVMValues[node];
  }
  Kind k = node.getKind();
  // Incorporate NOT to inner expression (>, >=, <, <=): no NOT EQUAL kind
  if (k == kind::NOT){
    if (node[0].getKind() != kind::EQUAL && node[0].getKind() != kind::FLOATINGPOINT_EQ){
      return codegenRecursive(node[0], true);
    }
  }
  if (reverse){
    assert(k == kind::GT || k == kind::GEQ || k == kind::LT || k == kind::LEQ || k == kind::BITVECTOR_SGT || k == kind::BITVECTOR_UGT || k == kind::BITVECTOR_SGE || k == kind::BITVECTOR_UGE || k == kind::BITVECTOR_SLT || k == kind::BITVECTOR_ULT || k == kind::BITVECTOR_SLE || k == kind::BITVECTOR_ULE || k == kind::FLOATINGPOINT_GT || k == kind::FLOATINGPOINT_GEQ || k == kind::FLOATINGPOINT_LT || k == kind::FLOATINGPOINT_LEQ || k == kind::APPLY_UF
    || k == kind::FLOATINGPOINT_ISN || k == kind::FLOATINGPOINT_ISSN || k == kind::FLOATINGPOINT_ISZ || k == kind::FLOATINGPOINT_ISINF || k == kind::FLOATINGPOINT_ISNAN || k == kind::FLOATINGPOINT_ISNEG || k == kind::FLOATINGPOINT_ISPOS);
    switch (k){
      case kind::GT:
        k = kind::LEQ;
        break;
      case kind::GEQ:
        k = kind::LT;
        break;
      case kind::LT:
        k = kind::GEQ;
        break;
      case kind::LEQ:
        k = kind::GT;
        break;
      case kind::BITVECTOR_SGT:
        k = kind::BITVECTOR_SLE;
        break;
      case kind::BITVECTOR_UGT:
        k = kind::BITVECTOR_ULE;
        break;
      case kind::BITVECTOR_SGE:
        k = kind::BITVECTOR_SLT;
        break;
      case kind::BITVECTOR_UGE:
        k = kind::BITVECTOR_ULT;
        break;
      case kind::BITVECTOR_SLT:
        k = kind::BITVECTOR_SGE;
        break;
      case kind::BITVECTOR_ULT:
        k = kind::BITVECTOR_UGE;
        break;
      case kind::BITVECTOR_SLE:
        k = kind::BITVECTOR_SGT;
        break;
      case kind::BITVECTOR_ULE:
        k = kind::BITVECTOR_UGT;
        break;
      case kind::FLOATINGPOINT_LEQ:
        k = kind::FLOATINGPOINT_GT;
        break;
      case kind::FLOATINGPOINT_LT:
        k = kind::FLOATINGPOINT_GEQ;
        break;
      case kind::FLOATINGPOINT_GEQ:
        k = kind::FLOATINGPOINT_LT;
        break;
      case kind::FLOATINGPOINT_GT:
        k = kind::FLOATINGPOINT_LEQ;
        break;
      case kind::APPLY_UF:
        break;
      case kind::FLOATINGPOINT_ISN:
      case kind::FLOATINGPOINT_ISSN:
      case kind::FLOATINGPOINT_ISZ:
      case kind::FLOATINGPOINT_ISINF:
      case kind::FLOATINGPOINT_ISNAN:
      case kind::FLOATINGPOINT_ISNEG:
      case kind::FLOATINGPOINT_ISPOS:
        break;
      default:
        assert(false);
    }
  }
  // Main codegen
  llvm::Value *ret = nullptr;
  switch (k) {
    // Constants
    case kind::CONST_RATIONAL:{
      if (node.getConst<Rational>().isIntegral()) {
        if (node.getConst<Rational>().sgn() < 0)
          ret = llvm::ConstantInt::get(*TheContext, llvm::APInt(64, node.getConst<Rational>().getNumerator().getUnsignedLong(), true));
        else
          ret = llvm::ConstantInt::get(*TheContext, llvm::APInt(64, node.getConst<Rational>().getNumerator().getUnsignedLong(), false));

      } else {
        BOOST_THROW_EXCEPTION(std::runtime_error("codegenRecursive implementation incomplete for kind::CONST_RATIONAL"));
        exit(1);
      }
      break;
    }
    case kind::CONST_BITVECTOR:{
      size_t bvsize = node.getConst<BitVector>().getSize();
      size_t roundedBitsize = bvSize2byteSize(bvsize) << 3;
      ret = llvm::ConstantInt::get(*TheContext, llvm::APInt(roundedBitsize, node.getConst<BitVector>().getValue().getUnsignedLong()));
      break;
    }
    // Variables
    case kind::VARIABLE:{
      // derived variables
      if (derived_vars.find(node) != derived_vars.end()){
        // FIXME: value reuse
        ret = codegenRecursive(derived_vars[node]);
        break;
      }
      assert(varLLVMAllocas.find(node) != varLLVMAllocas.end());
      // other variables
      if (node.getType().isInteger()){
        // integer variables
        ret = Builder->CreateLoad(llvm::Type::getInt32Ty(*TheContext), varLLVMAllocas[node], getNodeName(node));
      }
      else if (node.getType().isBitVector()){
        // bitvector variables
        size_t bvsize = node.getType().getBitVectorSize();
        size_t roundedBitsize = bvSize2byteSize(bvsize) << 3;
        ret = Builder->CreateLoad(llvm::Type::getIntNTy(*TheContext, roundedBitsize), varLLVMAllocas[node], getNodeName(node));
      }
      else if (node.getType().isArray()){
        // array variables
        // FIXME: return array pointer?
        ret = varLLVMAllocas[node];
      }
      else if (node.getType().isFloatingPoint()){
        // floating point variables
        auto exponentSize = node.getType().getFloatingPointExponentSize();
        auto significandSize = node.getType().getFloatingPointSignificandSize();
        auto bitSize = exponentSize + significandSize;
        auto bytesize = bvSize2byteSize(bitSize);
        assert(exponentSize == 8 || exponentSize == 11);
        assert(significandSize == 24 || significandSize == 53);
        assert(bitSize == 32 || bitSize == 64);
        if (bitSize == 32){
          ret = Builder->CreateLoad(llvm::Type::getFloatTy(*TheContext), varLLVMAllocas[node], getNodeName(node));
        }
        else if (bitSize == 64){
          ret = Builder->CreateLoad(llvm::Type::getDoubleTy(*TheContext), varLLVMAllocas[node], getNodeName(node));
        }
        else {
          BOOST_THROW_EXCEPTION(std::runtime_error("codegenRecursive implementation incomplete for kind::VARIABLE (floating point)"));
          exit(1);
        }
      }
      else {
        BOOST_THROW_EXCEPTION(std::runtime_error("codegenRecursive implementation incomplete for kind::VARIABLE"));
        exit(1);
      }
      break;
    }
    // Predicates
    case kind::NOT:{
      if (node[0].getKind() == kind::EQUAL){
        llvm::Value* lhs = codegenRecursive(node[0][0]);
        llvm::Value* rhs = codegenRecursive(node[0][1]);
        llvm::Value* dlhs, *drhs;
        assert(node[0][0].getType().isBitVector() || node[0][0].getType().isFloatingPoint());
        assert(node[0][0].getType() == node[0][1].getType());
        if (node[0][0].getType().isBitVector()){
          dlhs = Builder->CreateUIToFP(lhs, llvm::Type::getDoubleTy(*TheContext), "dlhs");
          drhs = Builder->CreateUIToFP(rhs, llvm::Type::getDoubleTy(*TheContext), "drhs");
        }
        else if (node[0][0].getType().isFloatingPoint()){
          dlhs = FPExtOrFPTrunc(lhs, llvm::Type::getDoubleTy(*TheContext), "dlhs");
          drhs = FPExtOrFPTrunc(rhs, llvm::Type::getDoubleTy(*TheContext), "drhs");
        }
        else{
          BOOST_THROW_EXCEPTION(std::runtime_error("codegenRecursive implementation incomplete for kind::NOT"));
          exit(1);
        }
        ret = neqLoss(dlhs, drhs);
        break;
      }
      else if (node[0].getKind() == kind::FLOATINGPOINT_EQ){
        llvm::Value* lhs = codegenRecursive(node[0][0]);
        llvm::Value* rhs = codegenRecursive(node[0][1]);
        llvm::Value* dlhs, *drhs;
        assert(node[0][0].getType().isFloatingPoint() && node[0][1].getType().isFloatingPoint());
        dlhs = FPExtOrFPTrunc(lhs, llvm::Type::getDoubleTy(*TheContext), "dlhs");
        drhs = FPExtOrFPTrunc(rhs, llvm::Type::getDoubleTy(*TheContext), "drhs");
        ret = neqLoss(dlhs, drhs);
        break;
      }
      else {
        // Other kinds of predicates are incorporated
        assert(false);
      }
    }
    case kind::FLOATINGPOINT_EQ:
    case kind::EQUAL: {
      llvm::Value* lhs = codegenRecursive(node[0]);
      llvm::Value* rhs = codegenRecursive(node[1]);
      llvm::Value* dlhs, *drhs;
      if (k == kind::EQUAL){
        if (node[0].getType().isBitVector()){
          assert(node[0].getType() == node[1].getType());
          dlhs = Builder->CreateUIToFP(lhs, llvm::Type::getDoubleTy(*TheContext), "dlhs");
          drhs = Builder->CreateUIToFP(rhs, llvm::Type::getDoubleTy(*TheContext), "drhs");
        }
        else if (node[0].getType().isFloatingPoint()){
          assert(node[0].getType() == node[1].getType());
          dlhs = FPExtOrFPTrunc(lhs, llvm::Type::getDoubleTy(*TheContext), "dlhs");
          drhs = FPExtOrFPTrunc(rhs, llvm::Type::getDoubleTy(*TheContext), "drhs");
        }
        else{
          BOOST_THROW_EXCEPTION(std::runtime_error("codegenRecursive implementation incomplete for kind::EQUAL"));
          exit(1);
        }
      }
      else if (k == kind::FLOATINGPOINT_EQ){
        dlhs = FPExtOrFPTrunc(lhs, llvm::Type::getDoubleTy(*TheContext), "dlhs");
        drhs = FPExtOrFPTrunc(rhs, llvm::Type::getDoubleTy(*TheContext), "drhs");
      }
      else{
        BOOST_THROW_EXCEPTION(std::runtime_error("codegenRecursive implementation incomplete for kind::EQUAL/FLOATINGPOINT_EQ"));
      }
      ret = eqLoss(dlhs, drhs);
      break;
    }
    case kind::BITVECTOR_NOT: {
      llvm::Value* child = codegenRecursive(node[0]);
      llvm::Value* notchild = Builder->CreateNot(child, "notchild");
      ret = notchild;
      break;
    }
    case kind::BITVECTOR_NEG: {
      llvm::Value* child = codegenRecursive(node[0]);
      llvm::Value* negchild = Builder->CreateNeg(child, "negchild");
      ret = negchild;
      break;
    }
    case kind::GT:
    case kind::BITVECTOR_UGT:
    case kind::BITVECTOR_SGT:
    case kind::FLOATINGPOINT_GT:{
      llvm::Value* lhs = codegenRecursive(node[0]);
      llvm::Value* rhs = codegenRecursive(node[1]);
      llvm::Value* dlhs, *drhs;
      if (k == kind::BITVECTOR_SGT || k == kind::GT){
        dlhs = Builder->CreateSIToFP(lhs, llvm::Type::getDoubleTy(*TheContext), "dlhs");
        drhs = Builder->CreateSIToFP(rhs, llvm::Type::getDoubleTy(*TheContext), "drhs");
      }
      else if (k == kind::BITVECTOR_UGT){
        dlhs = Builder->CreateUIToFP(lhs, llvm::Type::getDoubleTy(*TheContext), "dlhs");
        drhs = Builder->CreateUIToFP(rhs, llvm::Type::getDoubleTy(*TheContext), "drhs");
      }
      else if (k == kind::FLOATINGPOINT_GT){
        dlhs = FPExtOrFPTrunc(lhs, llvm::Type::getDoubleTy(*TheContext), "dlhs");
        drhs = FPExtOrFPTrunc(rhs, llvm::Type::getDoubleTy(*TheContext), "drhs");
      }
      else{
        BOOST_THROW_EXCEPTION(std::runtime_error("codegenRecursive implementation incomplete for kind::GT/BITVECTOR_SGT/BITVECTOR_UGT"));
      }
      ret = gtLoss(dlhs, drhs);
      break;
    }
    case kind::GEQ:
    case kind::BITVECTOR_SGE:
    case kind::BITVECTOR_UGE:
    case kind::FLOATINGPOINT_GEQ:{
      llvm::Value* lhs = codegenRecursive(node[0]);
      llvm::Value* rhs = codegenRecursive(node[1]);
      llvm::Value* dlhs, *drhs;
      if (k == kind::BITVECTOR_SGE || k == kind::GEQ){
        dlhs = Builder->CreateSIToFP(lhs, llvm::Type::getDoubleTy(*TheContext), "dlhs");
        drhs = Builder->CreateSIToFP(rhs, llvm::Type::getDoubleTy(*TheContext), "drhs");
      }
      else if (k == kind::BITVECTOR_UGE){
        dlhs = Builder->CreateUIToFP(lhs, llvm::Type::getDoubleTy(*TheContext), "dlhs");
        drhs = Builder->CreateUIToFP(rhs, llvm::Type::getDoubleTy(*TheContext), "drhs");
      }
      else if (k == kind::FLOATINGPOINT_GEQ){
        dlhs = FPExtOrFPTrunc(lhs, llvm::Type::getDoubleTy(*TheContext), "dlhs");
        drhs = FPExtOrFPTrunc(rhs, llvm::Type::getDoubleTy(*TheContext), "drhs");
      }
      else{
        BOOST_THROW_EXCEPTION(std::runtime_error("codegenRecursive implementation incomplete for kind::GEQ/BITVECTOR_SGE/BITVECTOR_UGE"));
      }
      ret = geqLoss(dlhs, drhs);
      break;
    }
    case kind::LT:
    case kind::BITVECTOR_SLT:
    case kind::BITVECTOR_ULT:
    case kind::FLOATINGPOINT_LT:{
      llvm::Value* lhs = codegenRecursive(node[0]);
      llvm::Value* rhs = codegenRecursive(node[1]);
      llvm::Value* dlhs, *drhs;
      if (k == kind::BITVECTOR_SLT || k == kind::LT){
        dlhs = Builder->CreateSIToFP(lhs, llvm::Type::getDoubleTy(*TheContext), "dlhs");
        drhs = Builder->CreateSIToFP(rhs, llvm::Type::getDoubleTy(*TheContext), "drhs");
      }
      else if (k == kind::BITVECTOR_ULT){
        dlhs = Builder->CreateUIToFP(lhs, llvm::Type::getDoubleTy(*TheContext), "dlhs");
        drhs = Builder->CreateUIToFP(rhs, llvm::Type::getDoubleTy(*TheContext), "drhs");
      }
      else if (k == kind::FLOATINGPOINT_LT){
        dlhs = FPExtOrFPTrunc(lhs, llvm::Type::getDoubleTy(*TheContext), "dlhs");
        drhs = FPExtOrFPTrunc(rhs, llvm::Type::getDoubleTy(*TheContext), "drhs");
      }
      else {
        BOOST_THROW_EXCEPTION(std::runtime_error("codegenRecursive implementation incomplete for kind::LT/BITVECTOR_SLT/BITVECTOR_ULT"));
      }
      ret = ltLoss(dlhs, drhs);
      break;
    }
    case kind::LEQ:
    case kind::BITVECTOR_ULE:
    case kind::BITVECTOR_SLE:
    case kind::FLOATINGPOINT_LEQ:{
      llvm::Value* lhs = codegenRecursive(node[0]);
      llvm::Value* rhs = codegenRecursive(node[1]);
      llvm::Value* dlhs, *drhs;
      if (k == kind::BITVECTOR_SLE || k == kind::LEQ){
        dlhs = Builder->CreateSIToFP(lhs, llvm::Type::getDoubleTy(*TheContext), "dlhs");
        drhs = Builder->CreateSIToFP(rhs, llvm::Type::getDoubleTy(*TheContext), "drhs");
      }
      else if (k == kind::BITVECTOR_ULE){
        dlhs = Builder->CreateUIToFP(lhs, llvm::Type::getDoubleTy(*TheContext), "dlhs");
        drhs = Builder->CreateUIToFP(rhs, llvm::Type::getDoubleTy(*TheContext), "drhs");
      }
      else if (k == kind::FLOATINGPOINT_LEQ){
        dlhs = FPExtOrFPTrunc(lhs, llvm::Type::getDoubleTy(*TheContext), "dlhs");
        drhs = FPExtOrFPTrunc(rhs, llvm::Type::getDoubleTy(*TheContext), "drhs");
      }
      else {
        BOOST_THROW_EXCEPTION(std::runtime_error("codegenRecursive implementation incomplete for kind::LEQ/BITVECTOR_SLE/BITVECTOR_ULE"));
      }
      ret = leqLoss(dlhs, drhs);
      break;
    }
    case kind::OR:{
      // logic OR?
      // ret = fmin(loss1, loss2, ...)
      assert(node.getNumChildren() >= 2);
      llvm::Value* first = codegenRecursive(node[0]);
      llvm::Value* second = codegenRecursive(node[1]);
      std::vector<llvm::Value *> fmin_args(2);
      fmin_args[0] = first;
      fmin_args[1] = second;
      llvm::Value* v = Builder->CreateCall(functionMap["fmin"], fmin_args, "lor");
      for (size_t it = 2; it < node.getNumChildren(); ++it) {
        llvm::Value* child = codegenRecursive(node[it]);
        fmin_args[0] = v;
        fmin_args[1] = child;
        v = Builder->CreateCall(functionMap["fmin"], fmin_args, "lor");
      }
      ret = v;
      break;
    }
    case kind::AND:{
      // logic AND?
      // ret = loss1 + loss2 + ...
      BOOST_THROW_EXCEPTION(std::runtime_error("codegenRecursive implementation incomplete for kind::AND"));
      assert(false);
      assert(node.getNumChildren() >= 2);
      llvm::Value* first = codegenRecursive(node[0]);
      llvm::Value* second = codegenRecursive(node[1]);
      llvm::Value* v = Builder->CreateAdd(first, second, "land");
      for (size_t it = 2; it < node.getNumChildren(); ++it) {
        llvm::Value* child = codegenRecursive(node[it]);
        v = Builder->CreateAdd(v, child, "land");
      }
      ret = v;
      break;
    }
    case kind::FLOATINGPOINT_ISN:{
      assert(node.getNumChildren() == 1);
      ret = isNLoss(node[0], reverse);
      break;
    }
    case kind::FLOATINGPOINT_ISSN:{
      assert(node.getNumChildren() == 1);
      ret = isSNLoss(node[0], reverse);
      break;
    }
    case kind::FLOATINGPOINT_ISZ:{
      assert(node.getNumChildren() == 1);
      ret = isZLoss(node[0], reverse);
      break;
    }
    case kind::FLOATINGPOINT_ISINF:{
      assert(node.getNumChildren() == 1);
      ret = isInfLoss(node[0], reverse);
      break;
    }
    case kind::FLOATINGPOINT_ISNAN:{
      assert(node.getNumChildren() == 1);
      ret = isNanLoss(node[0], reverse);
      break;
    }
    case kind::FLOATINGPOINT_ISNEG:{
      assert(node.getNumChildren() == 1);
      ret = isNegLoss(node[0], reverse);
      break;
    }
    case kind::FLOATINGPOINT_ISPOS:{
      assert(node.getNumChildren() == 1);
      ret = isPosLoss(node[0], reverse);
      break;
    }
    // Arithmetic
    case kind::APPLY_UF: {
      std::string funcName = node.getOperator().toString();
      if (specialPredicates.count(funcName) > 0){
        ret = specialPredicateLoss(node, reverse);
        break;
      }
      assert(functionMap.find(funcName) != functionMap.end());
      llvm::Function* func = functionMap[funcName];
      std::vector<llvm::Value *> args(node.getNumChildren());
      for (size_t cid = 0; cid < node.getNumChildren(); ++cid) {
        args[cid] = codegenRecursive(node[cid]);
      }
      // save oracle information
      uint64_t oracleId;
      if (oracleIdMap.find(funcName) != oracleIdMap.end()){
        oracleId = oracleIdMap[funcName];
      }
      else{
        oracleId = oracleIdCnt;
        oracleIdMap[funcName] = oracleId;
        if (oracleIdReverseMap.find(oracleId) == oracleIdReverseMap.end()){
          oracleIdReverseMap[oracleId] = funcName;
        }
        oracleIdReverseMap[oracleId] = funcName;
        oracleIdCnt++;
        oracleIdToLen[oracleId] = node.getNumChildren() + 1; // +1 for return value
      }
      storeOracleInfo(Node::null(), llvm::ConstantInt::get(*TheContext, llvm::APInt(64, oracleId)));
      // save oracle information: args as bitvector
      for (size_t cid = 0; cid < node.getNumChildren(); ++cid){
        storeOracleInfo(node[cid], args[cid]);
      }
      llvm::Value* calltmp = Builder->CreateCall(func, args, "calltmp");
      // save oracle information: return value
      storeOracleInfo(node, calltmp);
      if (calltmp->getType()->isIntegerTy(1)){
        // if the result is boolean, this is the top loss level
        if (reverse){
          // 1 -> loss 1.0, 0 -> loss 0.0
          llvm::Value* loss = Builder->CreateUIToFP(calltmp, llvm::Type::getDoubleTy(*TheContext), "loss");
          ret = loss;
          break;
        }
        else{
          // 1 -> loss 0.0, 0 -> loss 1.0
          // FIXME: very simple loss: 1.0 - (double)calltmp
          llvm::Value* loss = Builder->CreateUIToFP(calltmp, llvm::Type::getDoubleTy(*TheContext), "loss");
          llvm::Value* loss1 = Builder->CreateFSub(llvm::ConstantFP::get(*TheContext, llvm::APFloat(1.0)), loss, "loss1");
          ret = loss1;
          break;
        }
      }
      ret = calltmp;
      break;
    }
    case kind::BITVECTOR_PLUS:
    case kind::PLUS:{
      assert(node.getNumChildren() >= 2);
      llvm::Value* first = codegenRecursive(node[0]);
      llvm::Value* second = codegenRecursive(node[1]);
      llvm::Value* sum = Builder->CreateAdd(first, second, "plus");
      for (size_t it = 2; it < node.getNumChildren(); ++it) {
        llvm::Value* child = codegenRecursive(node[it]);
        sum = Builder->CreateAdd(sum, child, "plus");
      }
      ret = sum;
      break;
    }
    case kind::MINUS:{
      assert(node.getNumChildren() == 2);
      llvm::Value* first = codegenRecursive(node[0]);
      llvm::Value* second = codegenRecursive(node[1]);
      llvm::Value* sub = Builder->CreateSub(first, second, "sub");
      ret = sub;
      break;
    }
    case kind::BITVECTOR_MULT:
    case kind::MULT:{
      assert(node.getNumChildren() >= 2);
      llvm::Value* first = codegenRecursive(node[0]);
      llvm::Value* second = codegenRecursive(node[1]);
      llvm::Value* mul = Builder->CreateMul(first, second, "mul");
      for (size_t it = 2; it < node.getNumChildren(); ++it) {
        llvm::Value* child = codegenRecursive(node[it]);
        mul = Builder->CreateMul(mul, child, "mul");
      }
      ret = mul;
      break;
    }
    case kind::DIVISION:{
      assert(node.getNumChildren() == 2);
      llvm::Value* first = codegenRecursive(node[0]);
      llvm::Value* second = codegenRecursive(node[1]);
      llvm::Value* div = Builder->CreateUDiv(first, second, "udiv");
      ret = div;
      break;
    }
    case kind::BITVECTOR_UREM:{
      // unsigned remainder from truncating division of two bit-vectors (defined to be equal to the dividend, if divisor is 0)
      assert(node.getNumChildren() == 2);
      llvm::Value* first = codegenRecursive(node[0]);
      llvm::Value* second = codegenRecursive(node[1]);
      llvm::Value* urem = Builder->CreateURem(first, second, "urem");
      ret = urem;
      break;
    }
    case kind::BITVECTOR_SMOD:{
      // 2's complement signed remainder (sign follows divisor)
      assert(node.getNumChildren() == 2);
      llvm::Value* first = codegenRecursive(node[0]);
      llvm::Value* second = codegenRecursive(node[1]);
      llvm::Value* smod = Builder->CreateSRem(first, second, "smod");
      ret = smod;
      break;
    }
    case kind::BITVECTOR_SIGN_EXTEND:{
      assert(node.getNumChildren() == 1);
      llvm::Value* child = codegenRecursive(node[0]);
      unsigned int childWidth = node[0].getType().getBitVectorSize();
      unsigned int width = node.getType().getBitVectorSize();
      assert(width > childWidth);
      llvm::Value* sext = Builder->CreateSExt(child, llvm::Type::getIntNTy(*TheContext, width), "sext");
      ret = sext;
      break;
    }
    case kind::BITVECTOR_ZERO_EXTEND:{
      assert(node.getNumChildren() == 1);
      llvm::Value* child = codegenRecursive(node[0]);
      unsigned int childWidth = node[0].getType().getBitVectorSize();
      unsigned int width = node.getType().getBitVectorSize();
      assert(width > childWidth);
      llvm::Value* zext = Builder->CreateZExt(child, llvm::Type::getIntNTy(*TheContext, width), "zext");
      ret = zext;
      break;
    }
    case kind::BITVECTOR_EXTRACT: {
      assert(node.getNumChildren()==1);
      unsigned int high = theory::bv::utils::getExtractHigh(node);
      unsigned int low = theory::bv::utils::getExtractLow(node);
      unsigned int len = high - low + 1;
      assert(high >= low);
      llvm::Value* child = codegenRecursive(node[0]);
      if (low == 0){
        llvm::Value* trunc = Builder->CreateTrunc(child, llvm::Type::getIntNTy(*TheContext, len), "trunc");
        ret = trunc;
        break;
      }
      llvm::Value* lshr = Builder->CreateLShr(child, low, "lshr");
      llvm::Value* trunc = Builder->CreateTrunc(lshr, llvm::Type::getIntNTy(*TheContext, len), "trunc");
      ret = trunc;
      break;
    }
    case kind::BITVECTOR_CONCAT: {
      if (concatIsLSHR(node)){
        assert(node.getNumChildren() == 2);
        size_t bvsize0 = node[0].getType().getBitVectorSize();
        size_t bvsize1 = node[1].getType().getBitVectorSize();
        assert(bvsize1 + bvsize0 <= sizeof(size_t) * 8);
        // FIXME: maybe buggy: must be extract?
        unsigned int high = theory::bv::utils::getExtractHigh(node[1]);
        unsigned int low = theory::bv::utils::getExtractLow(node[1]);
        assert(node[1].getNumChildren() == 1);
        assert(high >= low);
        llvm::Value* child = codegenRecursive(node[1][0]);
        size_t childSize = node[1][0].getType().getBitVectorSize();
        llvm::Value* lshr = Builder->CreateLShr(child, low, "lshr");
        if (childSize < bvsize0 + bvsize1){
          // extend the result
          llvm::Value* zext = Builder->CreateZExt(lshr, llvm::Type::getIntNTy(*TheContext, bvsize0 + bvsize1), "zext");
          ret = zext;
          break;
        }
        else if (childSize > bvsize0 + bvsize1){
          // truncate the result to bvsize0 + bvsize1
          llvm::Value* trunc = Builder->CreateTrunc(lshr, llvm::Type::getIntNTy(*TheContext, bvsize0 + bvsize1), "trunc");
          ret = trunc;
          break;
        }
        else {
          ret = lshr;
          break;
        }
      }
      else if (node.getNumChildren() == 2) {
	      ret = codegenBvConcat2(node);
      }
      else {
	      ret = codegenBvConcat(node);
      }
      break;
    }
    case kind::SELECT: {
      assert(node.getNumChildren() == 2);
      llvm::Value* child = codegenRecursive(node[0]);
      llvm::Value* index = codegenRecursive(node[1]);
      std::vector<llvm::Value *> gepIndices(1);
      gepIndices[0] = index;
      assert(node[0].getType().getArrayConstituentType().isBitVector());
      size_t elementsize = node[0].getType().getArrayConstituentType().getBitVectorSize();
      llvm::Type* elementType = llvm::Type::getIntNTy(*TheContext, elementsize);
      child = Builder->CreateBitCast(child, llvm::PointerType::getUnqual(elementType));
      llvm::Value* ptr = Builder->CreateGEP(elementType, child, gepIndices, "selectptr");
      llvm::Value* select = Builder->CreateLoad(elementType, ptr, "select");
      ret = select;
      break;
    }
    case kind::BITVECTOR_XOR: {
      assert(node.getNumChildren() == 2);
      llvm::Value* first = codegenRecursive(node[0]);
      llvm::Value* second = codegenRecursive(node[1]);
      llvm::Value* xor_ = Builder->CreateXor(first, second, "bvxor");
      ret = xor_;
      break;
    }
    case kind::BITVECTOR_OR: {
      assert(node.getNumChildren() == 2);
      llvm::Value* first = codegenRecursive(node[0]);
      llvm::Value* second = codegenRecursive(node[1]);
      llvm::Value* or_ = Builder->CreateOr(first, second, "bvor");
      ret = or_;
      break;
    }
    case kind::BITVECTOR_AND: {
      assert(node.getNumChildren() == 2);
      llvm::Value* first = codegenRecursive(node[0]);
      llvm::Value* second = codegenRecursive(node[1]);
      llvm::Value* and_ = Builder->CreateAnd(first, second, "bvand");
      ret = and_;
      break;
    }
    case kind::CONST_FLOATINGPOINT:{
      // get the value
      FloatingPoint const& fp = node.getConst<FloatingPoint>();
      auto exp_size = node.getType().getFloatingPointExponentSize();
      auto sig_size = node.getType().getFloatingPointSignificandSize();
      auto fp_width = exp_size + sig_size;
      assert(fp_width == 32 || fp_width == 64);
      if (fp_width == 32){
        float f = FloatingPointTofloat(fp);
        ret = llvm::ConstantFP::get(*TheContext, llvm::APFloat(f));
      }
      else if (fp_width == 64){
        double d = FloatingPointTodouble(fp);
        ret = llvm::ConstantFP::get(*TheContext, llvm::APFloat(d));
      }
      else {
        BOOST_THROW_EXCEPTION(std::runtime_error("codegenRecursive implementation incomplete for kind::CONST_FLOATINGPOINT"));
        exit(1);
      }
      break;
    }
    case kind::FLOATINGPOINT_TO_FP_IEEE_BITVECTOR:{
      assert(node.getNumChildren() == 1);
      llvm::Value* bv = codegenRecursive(node[0]);
      assert(node[0].getType().isBitVector());
      unsigned int bvsize = node[0].getType().getBitVectorSize();
      assert(bvsize == 32 || bvsize == 64);
      llvm::Type* type = nullptr;
      if (bvsize == 32){
        type = llvm::Type::getFloatTy(*TheContext);
      }
      else if (bvsize == 64){
        type = llvm::Type::getDoubleTy(*TheContext);
      }
      assert(type != nullptr);
      llvm::Value* v = Builder->CreateBitCast(bv, type);
      ret = v;
      break;
    }
    case kind::FLOATINGPOINT_TO_FP_GENERIC:{
      // ((_ to_fp 11 53) a): bit re-interpretation
      // ((_ to_fp 11 53) RNE a): value to floating-point
      assert(node.getNumChildren() == 1 || node.getNumChildren() == 2);
      if (node.getNumChildren() == 1){
        Node value_nd = node[0];
        assert(value_nd.getType().isBitVector());
        llvm::Value* child = codegenRecursive(value_nd);
        unsigned int bvsize = value_nd.getType().getBitVectorSize();
        assert(bvsize == 32 || bvsize == 64);
        unsigned int exp_size = node.getType().getFloatingPointExponentSize();
        unsigned int sig_size = node.getType().getFloatingPointSignificandSize();
        assert((exp_size == 8 && sig_size == 24) || (exp_size == 11 && sig_size == 53));
        unsigned int dst_width = exp_size + sig_size;
        assert(bvsize == dst_width);
        llvm::Type* type = nullptr;
        if (dst_width == 32){
          type = llvm::Type::getFloatTy(*TheContext);
        }
        else if (dst_width == 64){
          type = llvm::Type::getDoubleTy(*TheContext);
        }
        assert(type != nullptr);
        llvm::Value* v = Builder->CreateBitCast(child, type);
        ret = v;
      }
      else if (node.getNumChildren() == 2){
        // rounding mode
        Node value_nd = node[1];
        assert(node[0].getKind() == kind::CONST_ROUNDINGMODE);
        if (value_nd.getType().isBitVector()){
          llvm::Value* bv = codegenRecursive(value_nd);
          unsigned int bvsize = value_nd.getType().getBitVectorSize();
          auto exp_size = node.getType().getFloatingPointExponentSize();
          auto sig_size = node.getType().getFloatingPointSignificandSize();
          assert((exp_size == 8 && sig_size == 24) || (exp_size == 11 && sig_size == 53));
          auto dst_width = exp_size + sig_size;
          llvm::Type* type = nullptr;
          if (dst_width == 32){
            type = llvm::Type::getFloatTy(*TheContext);
          }
          else if (dst_width == 64){
            type = llvm::Type::getDoubleTy(*TheContext);
          }
          assert(type != nullptr);
          llvm::Value* v = Builder->CreateUIToFP(bv, type);
          ret = v;
        }
        else if (value_nd.getType().isFloatingPoint()){
          llvm::Value* fp = codegenRecursive(value_nd);
          auto exp_size = node.getType().getFloatingPointExponentSize();
          auto sig_size = node.getType().getFloatingPointSignificandSize();
          assert((exp_size == 8 && sig_size == 24) || (exp_size == 11 && sig_size == 53));
          auto dst_width = exp_size + sig_size;
          llvm::Type* type = nullptr;
          if (dst_width == 32){
            type = llvm::Type::getFloatTy(*TheContext);
          }
          else if (dst_width == 64){
            type = llvm::Type::getDoubleTy(*TheContext);
          }
          assert(type != nullptr);
          llvm::Value* v = FPExtOrFPTrunc(fp, type);
          ret = v;
        }
        else if (value_nd.getKind() == kind::CONST_RATIONAL){
          Rational r = value_nd.getConst<Rational>();
          double d = RationalTodouble(r);
          #ifdef ENABLE_CBF_DEBUG
          llvm::errs() << "Floating-point constant (from rational): " << d << "\n";
          #endif
          if (node.getType().getFloatingPointExponentSize() == 8 && node.getType().getFloatingPointSignificandSize() == 24){
            float f = (float)d;
            ret = llvm::ConstantFP::get(*TheContext, llvm::APFloat(f));
          }
          else if (node.getType().getFloatingPointExponentSize() == 11 && node.getType().getFloatingPointSignificandSize() == 53){
            ret = llvm::ConstantFP::get(*TheContext, llvm::APFloat(d));
          }
          else {
            BOOST_THROW_EXCEPTION(std::runtime_error("codegenRecursive implementation incomplete for kind::FLOATINGPOINT_TO_FP_GENERIC"));
            exit(1);
          }
        }
      }
      else {
        BOOST_THROW_EXCEPTION(std::runtime_error("codegenRecursive implementation incomplete for kind::FLOATINGPOINT_TO_FP_GENERIC"));
        exit(1);
      }
      break;
    }
    case kind::FLOATINGPOINT_TO_FP_FLOATINGPOINT:{
      assert(false);
      assert(node.getNumChildren() == 1);
      assert(node.getType().isFloatingPoint() && node[0].getType().isFloatingPoint());
      unsigned int src_width = node[0].getType().getFloatingPointExponentSize() + node[0].getType().getFloatingPointSignificandSize();
      unsigned int dst_width = node.getType().getFloatingPointExponentSize() + node.getType().getFloatingPointSignificandSize();
      llvm::Value* fp = codegenRecursive(node[0]);
      if (src_width < dst_width){
        assert(src_width == 32 && dst_width == 64);
        // extend
        llvm::Value* v = Builder->CreateFPExt(fp, llvm::Type::getDoubleTy(*TheContext));
        ret = v;
      }
      else if (src_width > dst_width){
        assert(src_width == 64 && dst_width == 32);
        // truncate
        llvm::Value* v = Builder->CreateFPTrunc(fp, llvm::Type::getFloatTy(*TheContext));
        ret = v;
      }
      else {
        assert(src_width == 32 || src_width == 64);
        // same width
        ret = fp;
      }
      break;
    }
    case kind::FLOATINGPOINT_TO_UBV:{
      assert(node.getNumChildren() == 2);
      assert(node.getType().isBitVector());
      assert(node[1].getType().isFloatingPoint());
      llvm::Value* fp = codegenRecursive(node[1]);
      unsigned int fp_width = node[1].getType().getFloatingPointExponentSize() + node[1].getType().getFloatingPointSignificandSize();
      assert(fp_width == 32 || fp_width == 64);
      unsigned int bv_width = node.getType().getBitVectorSize();
      assert(bv_width == 32 || bv_width == 64);
      llvm::Value* v = nullptr;
      if (bv_width == 32){
        v = Builder->CreateFPToUI(fp, llvm::Type::getInt32Ty(*TheContext));
      }
      else if (bv_width == 64){
        v = Builder->CreateFPToUI(fp, llvm::Type::getInt64Ty(*TheContext));
      }
      assert(v != nullptr);
      ret = v;
      break;
    }
    case kind::FLOATINGPOINT_TO_SBV:{
      assert(node.getNumChildren() == 2);
      assert(node.getType().isBitVector());
      assert(node[1].getType().isFloatingPoint());
      llvm::Value* fp = codegenRecursive(node[1]);
      unsigned int fp_width = node[1].getType().getFloatingPointExponentSize() + node[1].getType().getFloatingPointSignificandSize();
      assert(fp_width == 32 || fp_width == 64);
      unsigned int bv_width = node.getType().getBitVectorSize();
      assert(bv_width == 32 || bv_width == 64);
      llvm::Value* v = nullptr;
      if (bv_width == 32){
        v = Builder->CreateFPToSI(fp, llvm::Type::getInt32Ty(*TheContext));
      }
      else if (bv_width == 64){
        v = Builder->CreateFPToSI(fp, llvm::Type::getInt64Ty(*TheContext));
      }
      assert(v != nullptr);
      ret = v;
      break;
    }
    case kind::FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR:{
      assert(node.getNumChildren() == 2);
      assert(node[1].getType().isBitVector());
      llvm::Value* bv = codegenRecursive(node[1]);
      unsigned int bvsize = node[1].getType().getBitVectorSize();
      assert(bvsize == 32 || bvsize == 64);
      unsigned int dst_width = node.getType().getFloatingPointExponentSize() + node.getType().getFloatingPointSignificandSize();
      assert(dst_width == bvsize);
      llvm::Type* type = nullptr;
      if (dst_width == 32){
        type = llvm::Type::getFloatTy(*TheContext);
      }
      else if (dst_width == 64){
        type = llvm::Type::getDoubleTy(*TheContext);
      }
      assert(type != nullptr);
      llvm::Value* v = Builder->CreateUIToFP(bv, type);
      ret = v;
      break;
    }
    case kind::FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR:{
      assert(node.getNumChildren() == 2);
      assert(node[1].getType().isBitVector());
      llvm::Value* bv = codegenRecursive(node[1]);
      unsigned int bvsize = node[1].getType().getBitVectorSize();
      assert(bvsize == 32 || bvsize == 64);
      unsigned int dst_width = node.getType().getFloatingPointExponentSize() + node.getType().getFloatingPointSignificandSize();
      assert(dst_width == bvsize);
      llvm::Type* type = nullptr;
      if (dst_width == 32){
        type = llvm::Type::getFloatTy(*TheContext);
      }
      else if (dst_width == 64){
        type = llvm::Type::getDoubleTy(*TheContext);
      }
      assert(type != nullptr);
      llvm::Value* v = Builder->CreateSIToFP(bv, type);
      ret = v;
      break;
    }
    case kind::FLOATINGPOINT_SQRT:{
      assert(node.getNumChildren() == 2);
      llvm::Value* child = codegenRecursive(node[1]);
      assert(child->getType()->isFloatTy() || child->getType()->isDoubleTy());
      if (child->getType()->isFloatTy()){
        child = Builder->CreateFPExt(child, llvm::Type::getDoubleTy(*TheContext), "fpext");
      }
      llvm::Value* sqrt = Builder->CreateCall(functionMap["sqrt"], child, "sqrt");
      if (node.getType().getFloatingPointExponentSize() == 8 && node.getType().getFloatingPointSignificandSize() == 24){
        sqrt = Builder->CreateFPTrunc(sqrt, llvm::Type::getFloatTy(*TheContext), "fptrunc");
      }
      ret = sqrt;
      break;
    }
    case kind::FLOATINGPOINT_ABS:{
      assert(node.getNumChildren() == 2);
      llvm::Value* child = codegenRecursive(node[1]);
      assert(child->getType()->isFloatTy() || child->getType()->isDoubleTy());
      if (child->getType()->isFloatTy()){
        child = Builder->CreateFPExt(child, llvm::Type::getDoubleTy(*TheContext), "fpext");
      }
      llvm::Value* abs = Builder->CreateCall(functionMap["fabs"], child, "fabs");
      if (node.getType().getFloatingPointExponentSize() == 8 && node.getType().getFloatingPointSignificandSize() == 24){
        abs = Builder->CreateFPTrunc(abs, llvm::Type::getFloatTy(*TheContext), "fptrunc");
      }
      ret = abs;
      break;
    }
    case kind::FLOATINGPOINT_PLUS:{
      assert(node.getNumChildren() == 3);
      llvm::Value* first = codegenRecursive(node[1]);
      llvm::Value* second = codegenRecursive(node[2]);
      llvm::Value* add = Builder->CreateFAdd(first, second, "fadd");
      ret = add;
      break;
    }
    case kind::FLOATINGPOINT_SUB:{
      assert(node.getNumChildren() == 3);
      llvm::Value* first = codegenRecursive(node[1]);
      llvm::Value* second = codegenRecursive(node[2]);
      llvm::Value* sub = Builder->CreateFSub(first, second, "fsub");
      ret = sub;
      break;
    }
    case kind::FLOATINGPOINT_MULT:{
      assert(node.getNumChildren() == 3);
      llvm::Value* first = codegenRecursive(node[1]);
      llvm::Value* second = codegenRecursive(node[2]);
      llvm::Value* mul = Builder->CreateFMul(first, second, "fmul");
      ret = mul;
      break;
    }
    case kind::FLOATINGPOINT_DIV:{
      assert(node.getNumChildren() == 3);
      llvm::Value* first = codegenRecursive(node[1]);
      llvm::Value* second = codegenRecursive(node[2]);
      llvm::Value* div = Builder->CreateFDiv(first, second, "fdiv");
      ret = div;
      break;
    }
    case kind::FLOATINGPOINT_NEG:{
      assert(node.getNumChildren() == 1);
      llvm::Value* child = codegenRecursive(node[0]);
      llvm::Value* neg = Builder->CreateFNeg(child, "fneg");
      ret = neg;
      break;
    }
    case kind::FLOATINGPOINT_FP: {
      assert(node.getNumChildren() == 3);
      assert(node[0].getType().isBitVector() && node[1].getType().isBitVector() && node[2].getType().isBitVector());
      assert(node[0].isConst() && node[1].isConst() && node[2].isConst());
      unsigned int bvsize0 = node[0].getType().getBitVectorSize();
      unsigned int bvsize1 = node[1].getType().getBitVectorSize();
      unsigned int bvsize2 = node[2].getType().getBitVectorSize();
      unsigned int combined_size = bvsize0 + bvsize1 + bvsize2;
      assert((bvsize0 == 1 && bvsize1 == 8 && bvsize2 == 23) || (bvsize0 == 1 && bvsize1 == 11 && bvsize2 == 52));
      unsigned int exp_size = node.getType().getFloatingPointExponentSize();
      unsigned int sig_size = node.getType().getFloatingPointSignificandSize();
      assert((exp_size == 8 && sig_size == 24) || (exp_size == 11 && sig_size == 53));
      unsigned int dst_width = exp_size + sig_size;
      assert(dst_width == combined_size);
      BitVector concat = node[0].getConst<BitVector>().concat(node[1].getConst<BitVector>()).concat(node[2].getConst<BitVector>());
      uint64_t bv = concat.getValue().getUnsignedLong();
      if (dst_width == 32){
        float f = BVToFloat(bv);
        ret = llvm::ConstantFP::get(*TheContext, llvm::APFloat(f));
      }
      else if (dst_width == 64){
        double d = BVToDouble(bv);
        ret = llvm::ConstantFP::get(*TheContext, llvm::APFloat(d));
      }
      else {
        BOOST_THROW_EXCEPTION(std::runtime_error("codegenRecursive implementation incomplete for kind::FLOATINGPOINT_FP"));
        exit(1);
      }
      break;
    }
    default:{
      BOOST_THROW_EXCEPTION(std::runtime_error("Codegeneration for " + kind::kindToString(node.getKind()) + " NOT SUPPORTED"));
      exit(1);
      break;
    }
  }
  // cache the value for visited node
  assert(ret != nullptr);
  assert(tempVarLLVMValues.find(node) == tempVarLLVMValues.end());
  tempVarLLVMValues[node] = ret;
  return ret;
}
bool AUFBVJitGenerator::concatIsLSHR(Node const& nd){
  if (nd.getNumChildren() != 2) return false;
  // ret = 0 concat bv[len(bv)-1:l]
  if (nd[0].getKind() == kind::CONST_BITVECTOR || nd[1].getKind() == kind::BITVECTOR_EXTRACT) {
      unsigned long value = nd[0].getConst<BitVector>().getValue().getUnsignedLong();
      unsigned int high = theory::bv::utils::getExtractHigh(nd[1]);
      assert(nd[1][0].getType().isBitVector());
      size_t bvsize = nd[1][0].getType().getBitVectorSize();
      if (value == 0 && high == bvsize - 1) return true;
  }
  return false;
}
llvm::Value* AUFBVJitGenerator::codegenBvConcat2(Node const& nd) {
  size_t bvsize0 = nd[0].getType().getBitVectorSize();
  size_t bvsize1 = nd[1].getType().getBitVectorSize();
  assert(bvsize1 + bvsize0 <= sizeof(size_t) * 8);
  llvm::Value* v0 = codegenRecursive(nd[0]);
  llvm::Value* v1 = codegenRecursive(nd[1]);
  llvm::Value* v2 = Builder->CreateZExt(v0, llvm::Type::getIntNTy(*TheContext, bvsize1 + bvsize0));
  llvm::Value* v3 = Builder->CreateShl(v2, bvsize1);
  llvm::Value* v4 = Builder->CreateZExt(v1, llvm::Type::getIntNTy(*TheContext, bvsize1 + bvsize0));
  llvm::Value* v5 = Builder->CreateOr(v3, v4);
  return v5;
}
llvm::Value* AUFBVJitGenerator::codegenBvConcat(Node const& nd) {
  size_t numChildren = nd.getNumChildren();
  assert (numChildren > 2);
  std::vector<size_t> size_vector;
  size_t size_sum = 0;
  for (size_t i = 0; i < numChildren; ++i){
    size_t bv_size = nd[i].getType().getBitVectorSize();
    size_sum += bv_size;
    size_vector.push_back(bv_size);
  }
  assert(size_sum <= sizeof(size_t) * 8);
  llvm::Value* v0 = codegenRecursive(nd[0]);
  llvm::Value* v1 = codegenRecursive(nd[1]);
  llvm::Value* v2 = Builder->CreateZExt(v0, llvm::Type::getIntNTy(*TheContext, size_sum));
  llvm::Value* v9 = Builder->CreateZExt(v1, llvm::Type::getIntNTy(*TheContext, size_sum));
  llvm::Value* v3 = Builder->CreateShl(v2, size_vector[1]);
  llvm::Value* v4 = Builder->CreateOr(v3, v9);
  for (size_t i = 2; i < numChildren; ++i){
    llvm::Value* v5 = codegenRecursive(nd[i]);
    llvm::Value* v6 = Builder->CreateZExt(v5, llvm::Type::getIntNTy(*TheContext, size_sum));
    llvm::Value* v7 = Builder->CreateShl(v4, size_vector[i]);
    llvm::Value* v8 = Builder->CreateOr(v7, v6);
    v4 = v8;
  }
  return v4;
}

llvm::Value* AUFBVJitGenerator::ltLoss(llvm::Value* dlhs, llvm::Value* drhs){
  auto f = TheModule->getFunction("ltLoss");
  if (f == nullptr){
    // define the function
    llvm::FunctionType* ft = llvm::FunctionType::get(llvm::Type::getDoubleTy(*TheContext), {llvm::Type::getDoubleTy(*TheContext), llvm::Type::getDoubleTy(*TheContext)}, false);
    llvm::Function* ltLossFunction = llvm::Function::Create(ft, llvm::Function::ExternalLinkage, "ltLoss", TheModule.get());
    llvm::Function::arg_iterator args = ltLossFunction->arg_begin();
    llvm::Value* arg1 = &*args++;
    llvm::Value* arg2 = &*args++;
    arg1->setName("dlhs");
    arg2->setName("drhs");
    // dlhs < drhs: 0
    // dlhs == NaN || drhs == NaN: DBL_MAX
    // else: fmax(0, dlhs - drhs + EPSILON)
    llvm::BasicBlock* entry = llvm::BasicBlock::Create(*TheContext, "entry", ltLossFunction);
    // create a new builder
    llvm::IRBuilder<> TmpBuilder(entry);
    llvm::BasicBlock* case1 = llvm::BasicBlock::Create(*TheContext, "case1", ltLossFunction);
    llvm::BasicBlock* notcase1 = llvm::BasicBlock::Create(*TheContext, "notcase1", ltLossFunction);
    auto cmp1 = TmpBuilder.CreateFCmpOLT(arg1, arg2, "cmplt");
    TmpBuilder.CreateCondBr(cmp1, case1, notcase1);
    // case 1
    TmpBuilder.SetInsertPoint(case1);
    llvm::Value* loss1 = llvm::ConstantFP::get(*TheContext, llvm::APFloat(0.0));
    TmpBuilder.CreateRet(loss1);
    // not case 1
    TmpBuilder.SetInsertPoint(notcase1);
    auto cmp2 = TmpBuilder.CreateFCmpUNO(arg1, arg2, "cmpuno"); //  True if unordered: isnan(X) | isnan(Y)
    llvm::BasicBlock* case2 = llvm::BasicBlock::Create(*TheContext, "case2", ltLossFunction);
    llvm::BasicBlock* notcase2 = llvm::BasicBlock::Create(*TheContext, "notcase2", ltLossFunction);
    TmpBuilder.CreateCondBr(cmp2, case2, notcase2);
    // case 2
    TmpBuilder.SetInsertPoint(case2);
    llvm::Value* loss2 = llvm::ConstantFP::get(*TheContext, llvm::APFloat(DBL_MAX));
    TmpBuilder.CreateRet(loss2);
    // not case 2
    TmpBuilder.SetInsertPoint(notcase2);
    double EPSILON = 1e-6;
    llvm::Value* diff = TmpBuilder.CreateFSub(arg1, arg2, "diff");
    diff = TmpBuilder.CreateFAdd(diff, llvm::ConstantFP::get(*TheContext, llvm::APFloat(EPSILON)), "diff");
    std::vector<llvm::Value *> fmax_args(2);
    fmax_args[0] = llvm::ConstantFP::get(*TheContext, llvm::APFloat(0.0));
    fmax_args[1] = diff;
    llvm::Value* loss = TmpBuilder.CreateCall(functionMap["fmax"], fmax_args, "loss");
    TmpBuilder.CreateRet(loss);
    addedGlobalVarSymbols.push_back("ltLoss");
    f = ltLossFunction;
  }
  assert(f != nullptr);
  std::vector<llvm::Value *> args(2);
  args[0] = dlhs;
  args[1] = drhs;
  return Builder->CreateCall(f, args, "ltLoss");
}

llvm::Value* AUFBVJitGenerator::leqLoss(llvm::Value* dlhs, llvm::Value* drhs){
  auto f = TheModule->getFunction("leqLoss");
  if (f == nullptr){
    // define the function
    llvm::FunctionType* ft = llvm::FunctionType::get(llvm::Type::getDoubleTy(*TheContext), {llvm::Type::getDoubleTy(*TheContext), llvm::Type::getDoubleTy(*TheContext)}, false);
    llvm::Function* leqLossFunction = llvm::Function::Create(ft, llvm::Function::ExternalLinkage, "leqLoss", TheModule.get());
    llvm::Function::arg_iterator args = leqLossFunction->arg_begin();
    llvm::Value* arg1 = &*args++;
    llvm::Value* arg2 = &*args++;
    arg1->setName("dlhs");
    arg2->setName("drhs");
    // dlhs <= drhs: 0
    // dlhs == NaN || drhs == NaN: DBL_MAX
    // else: fmax(0, dlhs - drhs)
    llvm::BasicBlock* entry = llvm::BasicBlock::Create(*TheContext, "entry", leqLossFunction);
    // create a new builder
    llvm::IRBuilder<> TmpBuilder(entry);
    llvm::BasicBlock* case1 = llvm::BasicBlock::Create(*TheContext, "case1", leqLossFunction);
    llvm::BasicBlock* notcase1 = llvm::BasicBlock::Create(*TheContext, "notcase1", leqLossFunction);
    auto cmp1 = TmpBuilder.CreateFCmpOLE(arg1, arg2, "cmpole");
    TmpBuilder.CreateCondBr(cmp1, case1, notcase1);
    // case 1
    TmpBuilder.SetInsertPoint(case1);
    llvm::Value* loss1 = llvm::ConstantFP::get(*TheContext, llvm::APFloat(0.0));
    TmpBuilder.CreateRet(loss1);
    // not case 1
    TmpBuilder.SetInsertPoint(notcase1);
    auto cmp2 = TmpBuilder.CreateFCmpUNO(arg1, arg2, "cmpuno"); //  True if unordered: isnan(X) | isnan(Y)
    llvm::BasicBlock* case2 = llvm::BasicBlock::Create(*TheContext, "case2", leqLossFunction);
    llvm::BasicBlock* notcase2 = llvm::BasicBlock::Create(*TheContext, "notcase2", leqLossFunction);
    TmpBuilder.CreateCondBr(cmp2, case2, notcase2);
    // case 2
    TmpBuilder.SetInsertPoint(case2);
    llvm::Value* loss2 = llvm::ConstantFP::get(*TheContext, llvm::APFloat(DBL_MAX));
    TmpBuilder.CreateRet(loss2);
    // not case 2
    TmpBuilder.SetInsertPoint(notcase2);
    llvm::Value* diff = TmpBuilder.CreateFSub(arg1, arg2, "diff");
    std::vector<llvm::Value *> fmax_args(2);
    fmax_args[0] = llvm::ConstantFP::get(*TheContext, llvm::APFloat(0.0));
    fmax_args[1] = diff;
    llvm::Value* loss = TmpBuilder.CreateCall(functionMap["fmax"], fmax_args, "loss");
    TmpBuilder.CreateRet(loss);
    addedGlobalVarSymbols.push_back("leqLoss");
    f = leqLossFunction;
  }
  assert(f != nullptr);
  std::vector<llvm::Value *> args(2);
  args[0] = dlhs;
  args[1] = drhs;
  return Builder->CreateCall(f, args, "leqLoss");
}

llvm::Value* AUFBVJitGenerator::gtLoss(llvm::Value* dlhs, llvm::Value* drhs){
  auto f = TheModule->getFunction("gtLoss");
  if (f == nullptr){
    // define the function
    llvm::FunctionType* ft = llvm::FunctionType::get(llvm::Type::getDoubleTy(*TheContext), {llvm::Type::getDoubleTy(*TheContext), llvm::Type::getDoubleTy(*TheContext)}, false);
    llvm::Function* gtLossFunction = llvm::Function::Create(ft, llvm::Function::ExternalLinkage, "gtLoss", TheModule.get());
    llvm::Function::arg_iterator args = gtLossFunction->arg_begin();
    llvm::Value* arg1 = &*args++;
    llvm::Value* arg2 = &*args++;
    arg1->setName("dlhs");
    arg2->setName("drhs");
    // dlhs > drhs: 0
    // dlhs == NaN || drhs == NaN: DBL_MAX
    // else: fmax(0, drhs - dlhs + EPSILON)
    llvm::BasicBlock* entry = llvm::BasicBlock::Create(*TheContext, "entry", gtLossFunction);
    // create a new builder
    llvm::IRBuilder<> TmpBuilder(entry);
    llvm::BasicBlock* case1 = llvm::BasicBlock::Create(*TheContext, "case1", gtLossFunction);
    llvm::BasicBlock* notcase1 = llvm::BasicBlock::Create(*TheContext, "notcase1", gtLossFunction);
    auto cmp1 = TmpBuilder.CreateFCmpOGT(arg1, arg2, "cmpgt");
    TmpBuilder.CreateCondBr(cmp1, case1, notcase1);
    // case 1
    TmpBuilder.SetInsertPoint(case1);
    llvm::Value* loss1 = llvm::ConstantFP::get(*TheContext, llvm::APFloat(0.0));
    TmpBuilder.CreateRet(loss1);
    // not case 1
    TmpBuilder.SetInsertPoint(notcase1);
    auto cmp2 = TmpBuilder.CreateFCmpUNO(arg1, arg2, "cmpuno"); //  True if unordered: isnan(X) | isnan(Y)
    llvm::BasicBlock* case2 = llvm::BasicBlock::Create(*TheContext, "case2", gtLossFunction);
    llvm::BasicBlock* notcase2 = llvm::BasicBlock::Create(*TheContext, "notcase2", gtLossFunction);
    TmpBuilder.CreateCondBr(cmp2, case2, notcase2);
    // case 2
    TmpBuilder.SetInsertPoint(case2);
    llvm::Value* loss2 = llvm::ConstantFP::get(*TheContext, llvm::APFloat(DBL_MAX));
    TmpBuilder.CreateRet(loss2);
    // not case 2
    TmpBuilder.SetInsertPoint(notcase2);
    double EPSILON = 1e-6;
    llvm::Value* diff = TmpBuilder.CreateFSub(arg2, arg1, "diff");
    diff = TmpBuilder.CreateFAdd(diff, llvm::ConstantFP::get(*TheContext, llvm::APFloat(EPSILON)), "diff");
    std::vector<llvm::Value *> fmax_args(2);
    fmax_args[0] = llvm::ConstantFP::get(*TheContext, llvm::APFloat(0.0));
    fmax_args[1] = diff;
    llvm::Value* loss = TmpBuilder.CreateCall(functionMap["fmax"], fmax_args, "loss");
    TmpBuilder.CreateRet(loss);
    addedGlobalVarSymbols.push_back("gtLoss");
    f = gtLossFunction;
  }
  assert(f != nullptr);
  std::vector<llvm::Value *> args(2);
  args[0] = dlhs;
  args[1] = drhs;
  return Builder->CreateCall(f, args, "gtLoss");
}

llvm::Value* AUFBVJitGenerator::geqLoss(llvm::Value* dlhs, llvm::Value* drhs){
  auto f = TheModule->getFunction("geqLoss");
  if (f == nullptr){
    // define the function
    llvm::FunctionType* ft = llvm::FunctionType::get(llvm::Type::getDoubleTy(*TheContext), {llvm::Type::getDoubleTy(*TheContext), llvm::Type::getDoubleTy(*TheContext)}, false);
    llvm::Function* geqLossFunction = llvm::Function::Create(ft, llvm::Function::ExternalLinkage, "geqLoss", TheModule.get());
    llvm::Function::arg_iterator args = geqLossFunction->arg_begin();
    llvm::Value* arg1 = &*args++;
    llvm::Value* arg2 = &*args++;
    arg1->setName("dlhs");
    arg2->setName("drhs");
    // dlhs >= drhs: 0
    // dlhs == NaN || drhs == NaN: DBL_MAX
    // else: fmax(0, drhs - dlhs)
    llvm::BasicBlock* entry = llvm::BasicBlock::Create(*TheContext, "entry", geqLossFunction);
    // create a new builder
    llvm::IRBuilder<> TmpBuilder(entry);
    llvm::BasicBlock* case1 = llvm::BasicBlock::Create(*TheContext, "case1", geqLossFunction);
    llvm::BasicBlock* notcase1 = llvm::BasicBlock::Create(*TheContext, "notcase1", geqLossFunction);
    auto cmp1 = TmpBuilder.CreateFCmpOGE(arg1, arg2, "cmpge");
    TmpBuilder.CreateCondBr(cmp1, case1, notcase1);
    // case 1
    TmpBuilder.SetInsertPoint(case1);
    llvm::Value* loss1 = llvm::ConstantFP::get(*TheContext, llvm::APFloat(0.0));
    TmpBuilder.CreateRet(loss1);
    // not case 1
    TmpBuilder.SetInsertPoint(notcase1);
    auto cmp2 = TmpBuilder.CreateFCmpUNO(arg1, arg2, "cmpuno"); //  True if unordered: isnan(X) | isnan(Y)
    llvm::BasicBlock* case2 = llvm::BasicBlock::Create(*TheContext, "case2", geqLossFunction);
    llvm::BasicBlock* notcase2 = llvm::BasicBlock::Create(*TheContext, "notcase2", geqLossFunction);
    TmpBuilder.CreateCondBr(cmp2, case2, notcase2);
    // case 2
    TmpBuilder.SetInsertPoint(case2);
    llvm::Value* loss2 = llvm::ConstantFP::get(*TheContext, llvm::APFloat(DBL_MAX));
    TmpBuilder.CreateRet(loss2);
    // not case 2
    TmpBuilder.SetInsertPoint(notcase2);
    llvm::Value* diff = TmpBuilder.CreateFSub(arg2, arg1, "diff");
    std::vector<llvm::Value *> fmax_args(2);
    fmax_args[0] = llvm::ConstantFP::get(*TheContext, llvm::APFloat(0.0));
    fmax_args[1] = diff;
    llvm::Value* loss = TmpBuilder.CreateCall(functionMap["fmax"], fmax_args, "loss");
    TmpBuilder.CreateRet(loss);
    addedGlobalVarSymbols.push_back("geqLoss");
    f = geqLossFunction;
  }
  assert(f != nullptr);
  std::vector<llvm::Value *> args(2);
  args[0] = dlhs;
  args[1] = drhs;
  return Builder->CreateCall(f, args, "geqLoss");
}

llvm::Value* AUFBVJitGenerator::eqLoss(llvm::Value* dlhs, llvm::Value* drhs){
  auto f = TheModule->getFunction("eqLoss");
  if (f == nullptr){
    // define the function
    llvm::FunctionType* ft = llvm::FunctionType::get(llvm::Type::getDoubleTy(*TheContext), {llvm::Type::getDoubleTy(*TheContext), llvm::Type::getDoubleTy(*TheContext)}, false);
    llvm::Function* eqLossFunction = llvm::Function::Create(ft, llvm::Function::ExternalLinkage, "eqLoss", TheModule.get());
    llvm::Function::arg_iterator args = eqLossFunction->arg_begin();
    llvm::Value* arg1 = &*args++;
    llvm::Value* arg2 = &*args++;
    arg1->setName("dlhs");
    arg2->setName("drhs");
    // dlhs == drhs: 0
    // dlhs == NaN || drhs == NaN: DBL_MAX
    // else: |dlhs - drhs|
    llvm::BasicBlock* entry = llvm::BasicBlock::Create(*TheContext, "entry", eqLossFunction);
    // create a new builder
    llvm::IRBuilder<> TmpBuilder(entry);
    llvm::BasicBlock* case1 = llvm::BasicBlock::Create(*TheContext, "case1", eqLossFunction);
    llvm::BasicBlock* notcase1 = llvm::BasicBlock::Create(*TheContext, "notcase1", eqLossFunction);
    auto cmp1 = TmpBuilder.CreateFCmpOEQ(arg1, arg2, "cmpeq");
    TmpBuilder.CreateCondBr(cmp1, case1, notcase1);
    // case 1
    TmpBuilder.SetInsertPoint(case1);
    llvm::Value* loss1 = llvm::ConstantFP::get(*TheContext, llvm::APFloat(0.0));
    TmpBuilder.CreateRet(loss1);
    // not case 1
    TmpBuilder.SetInsertPoint(notcase1);
    auto cmp2 = TmpBuilder.CreateFCmpUNO(arg1, arg2, "cmpuno"); //  True if unordered: isnan(X) | isnan(Y)
    llvm::BasicBlock* case2 = llvm::BasicBlock::Create(*TheContext, "case2", eqLossFunction);
    llvm::BasicBlock* notcase2 = llvm::BasicBlock::Create(*TheContext, "notcase2", eqLossFunction);
    TmpBuilder.CreateCondBr(cmp2, case2, notcase2);
    // case 2
    TmpBuilder.SetInsertPoint(case2);
    llvm::Value* loss2 = llvm::ConstantFP::get(*TheContext, llvm::APFloat(DBL_MAX));
    TmpBuilder.CreateRet(loss2);
    // not case 2
    TmpBuilder.SetInsertPoint(notcase2);
    llvm::Value* diff = TmpBuilder.CreateFSub(arg1, arg2, "diff");
    std::vector<llvm::Value *> fabs_args(1);
    fabs_args[0] = diff;
    llvm::Value* absdiff = TmpBuilder.CreateCall(functionMap["fabs"], fabs_args, "loss");
    TmpBuilder.CreateRet(absdiff);
    addedGlobalVarSymbols.push_back("eqLoss");
    f = eqLossFunction;
  }
  assert(f != nullptr);
  std::vector<llvm::Value *> args(2);
  args[0] = dlhs;
  args[1] = drhs;
  return Builder->CreateCall(f, args, "eqLoss");
}

llvm::Value* AUFBVJitGenerator::neqLoss(llvm::Value* dlhs, llvm::Value* drhs){
  auto f = TheModule->getFunction("neqLoss");
  if (f == nullptr){
    // define the function
    llvm::FunctionType* ft = llvm::FunctionType::get(llvm::Type::getDoubleTy(*TheContext), {llvm::Type::getDoubleTy(*TheContext), llvm::Type::getDoubleTy(*TheContext)}, false);
    llvm::Function* neqLossFunction = llvm::Function::Create(ft, llvm::Function::ExternalLinkage, "neqLoss", TheModule.get());
    llvm::Function::arg_iterator args = neqLossFunction->arg_begin();
    llvm::Value* arg1 = &*args++;
    llvm::Value* arg2 = &*args++;
    arg1->setName("dlhs");
    arg2->setName("drhs");
    // dlhs == drhs: 1
    // else: 0
    llvm::BasicBlock* entry = llvm::BasicBlock::Create(*TheContext, "entry", neqLossFunction);
    // create a new builder
    llvm::IRBuilder<> TmpBuilder(entry);
    llvm::BasicBlock* case1 = llvm::BasicBlock::Create(*TheContext, "case1", neqLossFunction);
    llvm::BasicBlock* notcase1 = llvm::BasicBlock::Create(*TheContext, "notcase1", neqLossFunction);
    auto cmp1 = TmpBuilder.CreateFCmpOEQ(arg1, arg2, "cmpeq");
    TmpBuilder.CreateCondBr(cmp1, case1, notcase1);
    // case 1
    TmpBuilder.SetInsertPoint(case1);
    llvm::Value* loss1 = llvm::ConstantFP::get(*TheContext, llvm::APFloat(1.0));
    TmpBuilder.CreateRet(loss1);
    // not case 1
    TmpBuilder.SetInsertPoint(notcase1);
    llvm::Value* loss2 = llvm::ConstantFP::get(*TheContext, llvm::APFloat(0.0));
    TmpBuilder.CreateRet(loss2);
    addedGlobalVarSymbols.push_back("neqLoss");
    f = neqLossFunction;
  }
  assert(f != nullptr);
  std::vector<llvm::Value *> args(2);
  args[0] = dlhs;
  args[1] = drhs;
  return Builder->CreateCall(f, args, "neqLoss");
}

llvm::Value* AUFBVJitGenerator::specialPredicateLoss(Node const& node, bool reverse){
  assert(node.getKind() == kind::APPLY_UF);
  std::string funcName = node.getOperator().toString();
  assert(specialPredicates.count(funcName) > 0);
  if (funcName == "isinf"){
    assert(node.getNumChildren() == 1);
    return isInfLoss(node[0], reverse);
  }
  else if (funcName == "isnan"){
    assert(node.getNumChildren() == 1);
    return isNanLoss(node[0], reverse);
  }
  else {
    BOOST_THROW_EXCEPTION(std::runtime_error("specialPredicateLoss implementation incomplete for " + funcName));
    exit(1);
  }
}
llvm::Value* AUFBVJitGenerator::isNanLoss(Node const& node, bool reverse){
  // IEEE 754 NaN bit representation: exponent = full 1, significand != 0
  // loss = (exponent with full 1 - exponent) + if significand == 0 then penalty value (default 1) else 0
  if (reverse){
    // loss == fmin (isInfLoss, isSNLoss, isNLoss)
    llvm::Value* loss1 = isInfLoss(node, false);
    llvm::Value* loss2 = isSNLoss(node, false);
    llvm::Value* loss3 = isNLoss(node, false);
    std::vector<llvm::Value *> fmin_args(2);
    fmin_args[0] = loss1;
    fmin_args[1] = loss2;
    llvm::Value* loss = Builder->CreateCall(functionMap["fmin"], fmin_args, "loss");
    fmin_args[0] = loss;
    fmin_args[1] = loss3;
    loss = Builder->CreateCall(functionMap["fmin"], fmin_args, "loss");
    return loss;
  }
  llvm::Value* child = codegenRecursive(node);
  assert(child->getType()->isFloatTy() || child->getType()->isDoubleTy());
  // get the bit representation
  llvm::Value* bitcast = nullptr;
  llvm::Value* exponent = nullptr;
  llvm::Value* significand = nullptr;
  llvm::Value* loss = nullptr;
  if (child->getType()->isFloatTy()){
    // float
    bitcast = Builder->CreateBitCast(child, llvm::Type::getInt32Ty(*TheContext));
    bitcast = Builder->CreateAnd(bitcast, 0x7FFFFFFF);
    exponent = Builder->CreateLShr(bitcast, 23);
    significand = Builder->CreateAnd(bitcast, 0x7FFFFF);
    double exponent_full_1 = 0xFF;
    double penalty = 1;
    // exponent with full 1 - exponent
    loss = Builder->CreateFSub(llvm::ConstantFP::get(*TheContext, llvm::APFloat(exponent_full_1)), Builder->CreateUIToFP(exponent, llvm::Type::getDoubleTy(*TheContext)), "loss");
    // if significand == 0 then penalty else 0
    llvm::Value* cmp = Builder->CreateICmpEQ(significand, llvm::ConstantInt::get(*TheContext, llvm::APInt(32, 0)), "cmp");
    llvm::Value* loss2 = Builder->CreateSelect(cmp, llvm::ConstantFP::get(*TheContext, llvm::APFloat(penalty)), llvm::ConstantFP::get(*TheContext, llvm::APFloat(0.0)), "loss");
    // full loss
    loss = Builder->CreateFAdd(loss, loss2, "loss");
  }
  else if (child->getType()->isDoubleTy()){
    // double
    bitcast = Builder->CreateBitCast(child, llvm::Type::getInt64Ty(*TheContext));
    bitcast = Builder->CreateAnd(bitcast, 0x7FFFFFFFFFFFFFFF);
    exponent = Builder->CreateLShr(bitcast, 52);
    significand = Builder->CreateAnd(bitcast, 0xFFFFFFFFFFFFF);
    double exponent_full_1 = 0x7FF;
    double penalty = 1;
    // exponent with full 1 - exponent
    loss = Builder->CreateFSub(llvm::ConstantFP::get(*TheContext, llvm::APFloat(exponent_full_1)), Builder->CreateUIToFP(exponent, llvm::Type::getDoubleTy(*TheContext)), "loss");
    // if significand == 0 then penalty else 0
    llvm::Value* cmp = Builder->CreateICmpEQ(significand, llvm::ConstantInt::get(*TheContext, llvm::APInt(64, 0)), "cmp");
    llvm::Value* loss2 = Builder->CreateSelect(cmp, llvm::ConstantFP::get(*TheContext, llvm::APFloat(penalty)), llvm::ConstantFP::get(*TheContext, llvm::APFloat(0.0)), "loss");
    // full loss
    loss = Builder->CreateFAdd(loss, loss2, "loss");
  }
  assert(loss != nullptr);
  return loss;
}
llvm::Value* AUFBVJitGenerator::isInfLoss(Node const& node, bool reverse){
  // IEEE 754 infinity bit representation: exponent = full 1, significand = 0
  // loss = (exponent with full 1 - exponent) + significand
  if (reverse){
    // loss == fmin (isNanLoss, isSNLoss, isNLoss)
    llvm::Value* loss1 = isNanLoss(node, false);
    llvm::Value* loss2 = isSNLoss(node, false);
    llvm::Value* loss3 = isNLoss(node, false);
    std::vector<llvm::Value *> fmin_args(2);
    fmin_args[0] = loss1;
    fmin_args[1] = loss2;
    llvm::Value* loss = Builder->CreateCall(functionMap["fmin"], fmin_args, "loss");
    fmin_args[0] = loss;
    fmin_args[1] = loss3;
    loss = Builder->CreateCall(functionMap["fmin"], fmin_args, "loss");
    return loss;
  }
  llvm::Value* child = codegenRecursive(node);
  assert(child->getType()->isFloatTy() || child->getType()->isDoubleTy());
  // get the bit representation
  llvm::Value* bitcast = nullptr;
  llvm::Value* exponent = nullptr;
  llvm::Value* significand = nullptr;
  llvm::Value* loss = nullptr;
  if (child->getType()->isFloatTy()){
    // float
    bitcast = Builder->CreateBitCast(child, llvm::Type::getInt32Ty(*TheContext));
    bitcast = Builder->CreateAnd(bitcast, 0x7FFFFFFF);
    exponent = Builder->CreateLShr(bitcast, 23);
    significand = Builder->CreateAnd(bitcast, 0x7FFFFF);
    double exponent_full_1 = 0xFF;
    // exponent with full 1 - exponent
    loss = Builder->CreateFSub(llvm::ConstantFP::get(*TheContext, llvm::APFloat(exponent_full_1)), Builder->CreateUIToFP(exponent, llvm::Type::getDoubleTy(*TheContext)), "loss");
    // significand
    loss = Builder->CreateFAdd(loss, Builder->CreateUIToFP(significand, llvm::Type::getDoubleTy(*TheContext)), "loss");
  }
  else if (child->getType()->isDoubleTy()){
    // double
    bitcast = Builder->CreateBitCast(child, llvm::Type::getInt64Ty(*TheContext));
    bitcast = Builder->CreateAnd(bitcast, 0x7FFFFFFFFFFFFFFF);
    exponent = Builder->CreateLShr(bitcast, 52);
    significand = Builder->CreateAnd(bitcast, 0xFFFFFFFFFFFFF);
    double exponent_full_1 = 0x7FF;
    // exponent with full 1 - exponent
    loss = Builder->CreateFSub(llvm::ConstantFP::get(*TheContext, llvm::APFloat(exponent_full_1)), Builder->CreateUIToFP(exponent, llvm::Type::getDoubleTy(*TheContext)), "loss");
    // significand
    loss = Builder->CreateFAdd(loss, Builder->CreateUIToFP(significand, llvm::Type::getDoubleTy(*TheContext)), "loss");
  }
  assert(loss != nullptr);
  return loss;
}
llvm::Value* AUFBVJitGenerator::isSNLoss(Node const& node, bool reverse){
  // IEEE 754 subnormal bit representation: exponent = 0, significand != 0
  // loss = exponent + if significand == 0 then penalty value (default 1) else 0
  if (reverse){
    // loss == fmin (isInfLoss, isNanLoss, isSLoss)
    llvm::Value* loss1 = isInfLoss(node, false);
    llvm::Value* loss2 = isNanLoss(node, false);
    llvm::Value* loss3 = isNLoss(node, false);
    std::vector<llvm::Value *> fmin_args(2);
    fmin_args[0] = loss1;
    fmin_args[1] = loss2;
    llvm::Value* loss = Builder->CreateCall(functionMap["fmin"], fmin_args, "loss");
    fmin_args[0] = loss;
    fmin_args[1] = loss3;
    loss = Builder->CreateCall(functionMap["fmin"], fmin_args, "loss");
    return loss;
  }
  llvm::Value* child = codegenRecursive(node);
  assert(child->getType()->isFloatTy() || child->getType()->isDoubleTy());
  // get the bit representation
  llvm::Value* bitcast = nullptr;
  llvm::Value* exponent = nullptr;
  llvm::Value* significand = nullptr;
  llvm::Value* loss = nullptr;
  if (child->getType()->isFloatTy()){
    // float
    bitcast = Builder->CreateBitCast(child, llvm::Type::getInt32Ty(*TheContext));
    bitcast = Builder->CreateAnd(bitcast, 0x7FFFFFFF);
    exponent = Builder->CreateLShr(bitcast, 23);
    significand = Builder->CreateAnd(bitcast, 0x7FFFFF);
    double penalty = 1;
    // if significand == 0 then penalty else 0
    llvm::Value* cmp = Builder->CreateICmpEQ(significand, llvm::ConstantInt::get(*TheContext, llvm::APInt(32, 0)), "cmp");
    llvm::Value* loss2 = Builder->CreateSelect(cmp, llvm::ConstantFP::get(*TheContext, llvm::APFloat(penalty)), llvm::ConstantFP::get(*TheContext, llvm::APFloat(0.0)), "loss");
    // full loss
    loss = Builder->CreateFAdd(Builder->CreateUIToFP(exponent, llvm::Type::getDoubleTy(*TheContext)), loss2, "loss");
  }
  else if (child->getType()->isDoubleTy()){
    // double
    bitcast = Builder->CreateBitCast(child, llvm::Type::getInt64Ty(*TheContext));
    bitcast = Builder->CreateAnd(bitcast, 0x7FFFFFFFFFFFFFFF);
    exponent = Builder->CreateLShr(bitcast, 52);
    significand = Builder->CreateAnd(bitcast, 0xFFFFFFFFFFFFF);
    double penalty = 1;
    // if significand == 0 then penalty else 0
    llvm::Value* cmp = Builder->CreateICmpEQ(significand, llvm::ConstantInt::get(*TheContext, llvm::APInt(64, 0)), "cmp");
    llvm::Value* loss2 = Builder->CreateSelect(cmp, llvm::ConstantFP::get(*TheContext, llvm::APFloat(penalty)), llvm::ConstantFP::get(*TheContext, llvm::APFloat(0.0)), "loss");
    // full loss
    loss = Builder->CreateFAdd(Builder->CreateUIToFP(exponent, llvm::Type::getDoubleTy(*TheContext)), loss2, "loss");
  }
  assert(loss != nullptr);
  return loss;
}
llvm::Value* AUFBVJitGenerator::isNLoss(Node const& node, bool reverse){
  // modify 1 bit is enough to make a number normal
  if (reverse){
    // loss == fmin (isInfLoss, isNanLoss, isSNLoss)
    llvm::Value* loss1 = isInfLoss(node, false);
    llvm::Value* loss2 = isNanLoss(node, false);
    llvm::Value* loss3 = isSNLoss(node, false);
    std::vector<llvm::Value *> fmin_args(2);
    fmin_args[0] = loss1;
    fmin_args[1] = loss2;
    llvm::Value* loss = Builder->CreateCall(functionMap["fmin"], fmin_args, "loss");
    fmin_args[0] = loss;
    fmin_args[1] = loss3;
    loss = Builder->CreateCall(functionMap["fmin"], fmin_args, "loss");
    return loss;
  }
  llvm::Value* child = codegenRecursive(node);
  assert(child->getType()->isFloatTy() || child->getType()->isDoubleTy());
  // get the bit representation
  llvm::Value* bitcast = nullptr;
  llvm::Value* exponent = nullptr;
  llvm::Value* significand = nullptr;
  llvm::Value* loss = nullptr;
  if (child->getType()->isFloatTy()){
    // float
    bitcast = Builder->CreateBitCast(child, llvm::Type::getInt32Ty(*TheContext));
    bitcast = Builder->CreateAnd(bitcast, 0x7FFFFFFF);
    exponent = Builder->CreateLShr(bitcast, 23);
    significand = Builder->CreateAnd(bitcast, 0x7FFFFF);
    double exponent_full_1 = 0xFF;
    double penalty = 1.0;
    // if exponent == exponent_full_1 then penalty else 0
    llvm::Value* cmp = Builder->CreateFCmpOEQ(Builder->CreateUIToFP(exponent, llvm::Type::getDoubleTy(*TheContext)), llvm::ConstantFP::get(*TheContext, llvm::APFloat(exponent_full_1)), "cmp");
    llvm::Value* loss2 = Builder->CreateSelect(cmp, llvm::ConstantFP::get(*TheContext, llvm::APFloat(penalty)), llvm::ConstantFP::get(*TheContext, llvm::APFloat(0.0)), "loss");
    // if exponent == 0 and significand != 0 then penalty else 0
    llvm::Value* cmp2 = Builder->CreateFCmpOEQ(Builder->CreateUIToFP(exponent, llvm::Type::getDoubleTy(*TheContext)), llvm::ConstantFP::get(*TheContext, llvm::APFloat(0.0)), "cmp");
    llvm::Value* cmp3 = Builder->CreateFCmpONE(Builder->CreateUIToFP(significand, llvm::Type::getDoubleTy(*TheContext)), llvm::ConstantFP::get(*TheContext, llvm::APFloat(0.0)), "cmp");
    llvm::Value* cmp4 = Builder->CreateAnd(cmp2, cmp3, "cmp");
    llvm::Value* loss3 = Builder->CreateSelect(cmp4, llvm::ConstantFP::get(*TheContext, llvm::APFloat(penalty)), llvm::ConstantFP::get(*TheContext, llvm::APFloat(0.0)), "loss");
    // full loss
    loss = Builder->CreateFAdd(loss2, loss3, "loss");
  }
  else if (child->getType()->isDoubleTy()){
    // double
    bitcast = Builder->CreateBitCast(child, llvm::Type::getInt64Ty(*TheContext));
    bitcast = Builder->CreateAnd(bitcast, 0x7FFFFFFFFFFFFFFF);
    exponent = Builder->CreateLShr(bitcast, 52);
    significand = Builder->CreateAnd(bitcast, 0xFFFFFFFFFFFFF);
    double exponent_full_1 = 0x7FF;
    double penalty = 1.0;
    // if exponent == exponent_full_1 then penalty else 0
    llvm::Value* cmp = Builder->CreateFCmpOEQ(Builder->CreateUIToFP(exponent, llvm::Type::getDoubleTy(*TheContext)), llvm::ConstantFP::get(*TheContext, llvm::APFloat(exponent_full_1)), "cmp");
    llvm::Value* loss2 = Builder->CreateSelect(cmp, llvm::ConstantFP::get(*TheContext, llvm::APFloat(penalty)), llvm::ConstantFP::get(*TheContext, llvm::APFloat(0.0)), "loss");
    // if exponent == 0 and significand != 0 then penalty else 0
    llvm::Value* cmp2 = Builder->CreateFCmpOEQ(Builder->CreateUIToFP(exponent, llvm::Type::getDoubleTy(*TheContext)), llvm::ConstantFP::get(*TheContext, llvm::APFloat(0.0)), "cmp");
    llvm::Value* cmp3 = Builder->CreateFCmpONE(Builder->CreateUIToFP(significand, llvm::Type::getDoubleTy(*TheContext)), llvm::ConstantFP::get(*TheContext, llvm::APFloat(0.0)), "cmp");
    llvm::Value* cmp4 = Builder->CreateAnd(cmp2, cmp3, "cmp");
    llvm::Value* loss3 = Builder->CreateSelect(cmp4, llvm::ConstantFP::get(*TheContext, llvm::APFloat(penalty)), llvm::ConstantFP::get(*TheContext, llvm::APFloat(0.0)), "loss");
    // full loss
    loss = Builder->CreateFAdd(loss2, loss3, "loss");
  }
  assert(loss != nullptr);
  return loss;
}
llvm::Value* AUFBVJitGenerator::isZLoss(Node const& node, bool reverse){
  if (reverse){
    // loss == 1 if child == 0 else 0
    llvm::Value* loss = nullptr;
    llvm::Value* child = codegenRecursive(node);
    assert(child->getType()->isFloatTy() || child->getType()->isDoubleTy());
    llvm::Value* cmp = FPAndConstCmp(child, 0.0, llvm::CmpInst::Predicate::FCMP_OEQ, "cmp");
    loss = Builder->CreateSelect(cmp, llvm::ConstantFP::get(*TheContext, llvm::APFloat(1.0)), llvm::ConstantFP::get(*TheContext, llvm::APFloat(0.0)), "loss");
    return loss;
  }
  // loss = abs(child)
  llvm::Value* child = codegenRecursive(node);
  assert(child->getType()->isFloatTy() || child->getType()->isDoubleTy());
  llvm::Value* loss = nullptr;
  std::vector<llvm::Value *> fabs_args(1);
  fabs_args[0] = child;
  loss = Builder->CreateCall(functionMap["fabs"], fabs_args, "loss");
  return loss;
}
llvm::Value* AUFBVJitGenerator::isPosLoss(Node const& node, bool reverse){
  if (reverse){
    // loss == child if child > 0 else 0
    llvm::Value* loss = nullptr;
    llvm::Value* child = codegenRecursive(node);
    assert(child->getType()->isFloatTy() || child->getType()->isDoubleTy());
    llvm::Value* cmp = FPAndConstCmp(child, 0.0, llvm::CmpInst::Predicate::FCMP_OGT, "cmp");
    loss = Builder->CreateSelect(cmp, child, llvm::ConstantFP::get(*TheContext, llvm::APFloat(0.0)), "loss");
  }
  // loss = -child + 1 if child <= 0 else 0
  llvm::Value* child = codegenRecursive(node);
  assert(child->getType()->isFloatTy() || child->getType()->isDoubleTy());
  llvm::Value* loss = nullptr;
  llvm::Value* neg = Builder->CreateFNeg(child, "neg");
  llvm::Value* cmp = FPAndConstCmp(child, 0.0, llvm::CmpInst::Predicate::FCMP_OLE, "cmp");
  llvm::Value* loss2 = Builder->CreateSelect(cmp, Builder->CreateFAdd(neg, llvm::ConstantFP::get(*TheContext, llvm::APFloat(1.0)), "loss"), llvm::ConstantFP::get(*TheContext, llvm::APFloat(0.0)), "loss");
  loss = loss2;
  return loss;
}
llvm::Value* AUFBVJitGenerator::isNegLoss(Node const& node, bool reverse){
  if (reverse){
    // loss == -child if child < 0 else 0
    llvm::Value* loss = nullptr;
    llvm::Value* child = codegenRecursive(node);
    assert(child->getType()->isFloatTy() || child->getType()->isDoubleTy());
    llvm::Value* cmp = FPAndConstCmp(child, 0.0, llvm::CmpInst::Predicate::FCMP_OLT, "cmp");
    loss = Builder->CreateSelect(cmp, Builder->CreateFNeg(child, "neg"), llvm::ConstantFP::get(*TheContext, llvm::APFloat(0.0)), "loss");
    return loss;
  }
  // loss = child+1 if child >= 0 else 0
  llvm::Value* child = codegenRecursive(node);
  assert(child->getType()->isFloatTy() || child->getType()->isDoubleTy());
  llvm::Value* loss = nullptr;
  llvm::Value* cmp = FPAndConstCmp(child, 0.0, llvm::CmpInst::Predicate::FCMP_OGE, "cmp");
  llvm::Value* loss2 = Builder->CreateSelect(cmp, Builder->CreateFAdd(child, llvm::ConstantFP::get(*TheContext, llvm::APFloat(1.0)), "loss"), llvm::ConstantFP::get(*TheContext, llvm::APFloat(0.0)), "loss");
  loss = loss2;
  return loss;
}

void AUFBVJitGenerator::readCrashInput() {
  // Must have a crash input/The solution must exist
  if (seedSize > 0){
    assert(solution.first != nullptr);
    uint8_t* data = solution.first.get();
    size_t len = solution.second;
    assert((data != nullptr) && (len > 0));
    uint8_t* buffptr = data;
    /*
    * Read the input from the seed
    */
    for (Node nd : varlist) {
      // skip the variables that can be derived from other variables
      if (derived_vars.find(nd) != derived_vars.end()) {
        continue;
      }
      if (nd.getType().isInteger()) {
        // integer variables
        std::string varname = getNodeName(nd);
        assert(varPosMap.find(varname) != varPosMap.end());
        auto pospair = varPosMap[varname];
        size_t start = pospair.first;
        size_t len = pospair.second;
        // start may not be aligned
        unsigned int value = 0;
        buffptr = data + start;
        for (size_t i = 0; i < len; ++i){
          value = value << 8;
          value += *((uint8_t*)(buffptr));
          buffptr++;
        }
        crashModel[nd] = NodeManager::currentNM()->mkConst(Rational(value));
      }
      else if (nd.getType().isBitVector()) {
        // bitvector variables
        std::string varname = getNodeName(nd);
        assert(varPosMap.find(varname) != varPosMap.end());
        auto pospair = varPosMap[varname];
        size_t start = pospair.first;
        size_t len = pospair.second;
        size_t bvByteSize = bvSize2byteSize(nd.getType().getBitVectorSize());
        assert(len == bvByteSize);
        assert(bvByteSize == 1 || bvByteSize == 2 || bvByteSize == 4 || bvByteSize == 8);
        // start may not be aligned
        uint64_t value = 0;
        buffptr = data + start;
        for (size_t i = 0; i < bvByteSize; ++i){
          value = value << 8;
          value += *((uint8_t*)(buffptr));
          buffptr++;
        }
        cvc5::Integer cvc5value(value);
        crashModel[nd] = theory::bv::utils::mkConst(nd.getType().getBitVectorSize(), cvc5value);
      }
      else if (nd.getType().isArray()) {
        // array variables
        std::string aname = getNodeName(nd);
        uint32_t arrayFullSize = arraySizeMap[aname];
        assert(arrayFullSize > 0);
        std::string varname = getNodeName(nd);
        assert(varPosMap.find(varname) != varPosMap.end());
        auto pospair = varPosMap[varname];
        size_t start = pospair.first;
        size_t arraySeedLen = pospair.second;
        size_t seedIndexFromStart = 0;
        size_t elementByteSize = bvSize2byteSize(nd.getType().getArrayConstituentType().getBitVectorSize());
        assert(elementByteSize == 1 || elementByteSize == 2 || elementByteSize == 4 || elementByteSize == 8);
        // prepare the array model
        if (arrayModels.find(aname) == arrayModels.end()){
          arrayModels[aname] = std::vector<uint64_t>();
        }
        arrayModels[aname].resize(arrayFullSize);
        for (uint32_t i = 0; i < arrayFullSize; ++i){
          uint64_t elementValue = 0;
          if (arrayConstMap.find(aname) != arrayConstMap.end() && arrayConstMap[aname].find(i) != arrayConstMap[aname].end()){
            // Constant element
            elementValue = arrayConstMap[aname][i];
          }
          else {
            // Non-constant element
            // start may not be aligned
            buffptr = data + start + seedIndexFromStart;
            assert(seedIndexFromStart + elementByteSize <= arraySeedLen);
            for (size_t j = 0; j < elementByteSize; ++j){
              elementValue = elementValue << 8;
              elementValue += *((uint8_t*)(buffptr));
              buffptr++;
            }
            seedIndexFromStart += elementByteSize;
          }
          // update the crash model
          Node ni = NodeManager::currentNM()->mkNode(kind::SELECT, nd, NodeManager::currentNM()->mkConst(BitVector(nd.getType().getArrayIndexType().getBitVectorSize(), i)));
          cvc5::Integer cvc5value(elementValue);
          crashModel[ni] = theory::bv::utils::mkConst(nd.getType().getArrayConstituentType().getBitVectorSize(), cvc5value);
          // update the array model
          arrayModels[aname][i] = elementValue;
        }
      }
      else if (nd.getType().isFloatingPoint()) {
        // floating-point variables
        std::string varname = getNodeName(nd);
        assert(varPosMap.find(varname) != varPosMap.end());
        auto pospair = varPosMap[varname];
        size_t start = pospair.first;
        size_t len = pospair.second;
        size_t fvalue_len = nd.getType().getFloatingPointExponentSize() + nd.getType().getFloatingPointSignificandSize();
        assert(fvalue_len == 32 || fvalue_len == 64);
        size_t fvalueByteSize = fvalue_len / 8;
        assert(len == fvalueByteSize);
        // start may not be aligned
        uint64_t value = 0;
        buffptr = data + start;
        for (size_t i = 0; i < fvalueByteSize; ++i){
          value = value << 8;
          value += *((uint8_t*)(buffptr));
          buffptr++;
        }
        if (nd.getType().isFloatingPoint(8, 24)){
          crashModel[nd] = NodeManager::currentNM()->mkConst(FloatingPoint(8, 24, BitVector(fvalue_len, value)));
        }
        else if (nd.getType().isFloatingPoint(11, 53)){
          crashModel[nd] = NodeManager::currentNM()->mkConst(FloatingPoint(11, 53, BitVector(fvalue_len, value)));
        }
        else {
          assert(false);
        }
      }
      else {
        BOOST_THROW_EXCEPTION(std::runtime_error("readCrashInput implementation incomplete: read the input from the seed"));
        exit(1);
      }
    }
    /*
    * Read the input from the seed ends
    */
  }

  /*
  * Derive the values of derived variables: derivation order is important
  */
  // Build the derived_vars_relation_graph
  // edge: v -> w, w is a precondition of v
  std::map<Node, std::vector<Node>> derived_vars_relation_graph;
  for (auto vi = derived_vars.begin(), ve = derived_vars.end(); vi!=ve; ++vi){
    // initialization
    Node nd = vi->first;
    assert(derived_vars_relation_graph.find(nd) == derived_vars_relation_graph.end());
    derived_vars_relation_graph[nd] = std::vector<Node>();
    // add edges
    Node vnd = vi->second;
    std::vector<Node> varnodes;
    get_all_varnodes(vnd, varnodes);
    for (Node vn : varnodes){
      if (derived_vars.find(vn) != derived_vars.end()){
        derived_vars_relation_graph[nd].push_back(vn);
      }
    }
  }
  // Reverse topsort
  std::vector<Node> evaluation_order;
  reverse_topsort(derived_vars_relation_graph, evaluation_order);
  assert(evaluation_order.size() == derived_vars.size());
  // Evaluate the derived variables in order
  for (unsigned int i = 0; i < evaluation_order.size(); ++i){
    Node nd = evaluation_order[i];
    Node vnd = derived_vars[nd];
    if (nd.getType().isInteger()){
      assert(false);
    }
    else if (nd.getType().isBitVector()){
      uint64_t value;
      if (!evaluate_bitvector(vnd, value)){
        BOOST_THROW_EXCEPTION(std::runtime_error("readCrashInput implementation incomplete: evaluate_bitvector"));
        exit(1);
      }
      cvc5::Integer cvc5value(value);
      crashModel[nd] = theory::bv::utils::mkConst(nd.getType().getBitVectorSize(), cvc5value);
    }
    else if (nd.getType().isFloatingPoint()){
      assert(nd.getType().isFloatingPoint(8, 24) || nd.getType().isFloatingPoint(11, 53));
      uint64_t value;
      if (!evaluate_bitvector(vnd, value)){
        BOOST_THROW_EXCEPTION(std::runtime_error("readCrashInput implementation incomplete: evaluate_floatingpoint"));
        exit(1);
      }
      if (nd.getType().isFloatingPoint(8, 24)){
        auto fvalue_len = nd.getType().getFloatingPointExponentSize() + nd.getType().getFloatingPointSignificandSize();
        assert(fvalue_len == 32);
        cvc5::BitVector fvalue_bv = BitVector(fvalue_len, value);
        crashModel[nd] = NodeManager::currentNM()->mkConst(FloatingPoint(8, 24, fvalue_bv));
      }
      else if (nd.getType().isFloatingPoint(11, 53)){
        auto fvalue_len = nd.getType().getFloatingPointExponentSize() + nd.getType().getFloatingPointSignificandSize();
        assert(fvalue_len == 64);
        cvc5::BitVector fvalue_bv = BitVector(fvalue_len, value);
        crashModel[nd] = NodeManager::currentNM()->mkConst(FloatingPoint(11, 53, fvalue_bv));
      }
      else {
        assert(false);
      }
    }
    else if (nd.getType().isArray()){
      assert(false);
    }
    else {
      BOOST_THROW_EXCEPTION(
          std::runtime_error("readCrashInput implementation incomplete: evaluate derived variables"));
      exit(1);
    }
  }
  /*
  * Derive the values of derived variables
  */
  return;
}
void AUFBVJitGenerator::learnOracleInfo(){
  oracleInfo.clear();
  for (auto &info : oracleKeyPoints){
    std::string oracleName = info.first;
    std::set<std::vector<uint64_t>> keyPoints = info.second;
    uint64_t oracleId = oracleIdMap[oracleName];
    assert(!oracleName.empty());
    // check function_declarations
    assert(function_declarations.find(oracleName) != function_declarations.end());
    assert(function_to_nodes.find(oracleName) != function_to_nodes.end());
    assert(function_to_nodes[oracleName].size() > 0);
    auto op = function_to_nodes[oracleName][0].getOperator();
    auto function_declaration_sizes = function_declarations[oracleName].first;
    auto function_declaration_is_float_vector = function_declarations[oracleName].second;
    assert(function_declaration_sizes.size() == function_declaration_is_float_vector.size());
    std::vector<std::vector<Node>> keyPointsArgNodes;
    for (auto &keyPoint: keyPoints){
      assert(keyPoint.size() == function_declaration_sizes.size());
      std::vector<Node> args;
      Node ret;
      for (unsigned int i = 0; i < keyPoint.size(); ++i){
        uint64_t size = function_declaration_sizes[(i+1)%keyPoint.size()];
        bool is_float = function_declaration_is_float_vector[(i+1)%keyPoint.size()];
        Node valueNode;
        if (is_float){
          assert(size == 32 || size == 64);
          if (size == 32){
            // float
            valueNode = NodeManager::currentNM()->mkConst(FloatingPoint(8, 24, BitVector(32, keyPoint[i])));
          }
          else {
            // double
            valueNode = NodeManager::currentNM()->mkConst(FloatingPoint(11, 53, BitVector(64, keyPoint[i])));
          }
        }
        else {
          // bit-vector
          cvc5::Integer cvc5value(keyPoint[i]);
          valueNode = theory::bv::utils::mkConst(size, cvc5value);
        }
        assert(!valueNode.isNull());
        if (i != keyPoint.size() - 1){
          args.push_back(valueNode);
        }
        else {
          ret = valueNode;
        }
      }
      assert(!ret.isNull());
      keyPointsArgNodes.push_back(args);
      args.insert(args.begin(), op);
      Node ufNode = NodeManager::currentNM()->mkNode(kind::APPLY_UF, args);
      Node eqNode = NodeManager::currentNM()->mkNode(kind::EQUAL, ufNode, ret);
      oracleInfo.insert(eqNode);
    }
    // add oracle arg constraints
    auto fnodes = function_to_nodes[oracleName];
    for (auto & fnode: fnodes){
      assert(fnode.getKind() == kind::APPLY_UF);
      std::vector<Node> constraints;
      for (auto & args: keyPointsArgNodes){
        assert(args.size() == fnode.getNumChildren());
        std::vector<Node> pointConstraints;
        for (unsigned int i = 0; i < args.size(); ++i){
          Node arg = fnode[i];
          Node argValue = args[i];
          Node eqNode = NodeManager::currentNM()->mkNode(kind::EQUAL, arg, argValue);
          pointConstraints.push_back(eqNode);
        }
        Node pointConstraint = NodeManager::currentNM()->mkAnd(pointConstraints);
        constraints.push_back(pointConstraint);
      }
      Node constraint = NodeManager::currentNM()->mkOr(constraints);
      oracleInfo.insert(constraint);
    }
  }
  #ifdef ENABLE_CBF_DEBUG
  // print oracleInfo
  for (auto &info: oracleInfo){
    llvm::errs() << "Oracle Info: " << info.toString() << "\n";
  }
  #endif
  return;
}
/*
* Core interfaces ends
*/

/*
* JIT interfaces
*/
void AUFBVJitGenerator::addSpecialFunctionsDeclarations() {
  return;
}

void AUFBVJitGenerator::InitializeModuleAndPassManager() {
  // Create a new module for target functions
  assert(TheContext != nullptr);
  if (!Builder){
  #ifdef ENABLE_LLVM11
    Builder = std::make_unique<llvm::IRBuilder<>>(*TheContext);
  #else
    Builder = std::make_unique<llvm::IRBuilder<>>(*TheContext);
  #endif
  }
  std::string module_name = "aufbv-jit";
  TheModule = std::make_unique<llvm::Module>(module_name, *TheContext);
  TheModule->setDataLayout(TheJIT->getDataLayout());

  // Create a new pass manager attached to it
  TheFPM = std::make_unique<llvm::legacy::FunctionPassManager>(TheModule.get());
  // TODO: Optimization for FPM
  // // Promote allocas to registers.
  // TheFPM->add(llvm::createPromoteMemoryToRegisterPass());
  // // Do simple "peephole" optimizations and bit-twiddling optzns.
  // TheFPM->add(llvm::createInstructionCombiningPass());
  // // Reassociate expressions.
  // TheFPM->add(llvm::createReassociatePass());
  // // Eliminate Common SubExpressions.
  // TheFPM->add(llvm::createGVNPass());
  // // Simplify the control flow graph (deleting unreachable blocks, etc).
  // TheFPM->add(llvm::createCFGSimplificationPass());
  // TheFPM->doInitialization();

  /*
  * Add external function declarations
  */
  // fmax: double fmax(double, double)
  std::vector<llvm::Type*> fmaxArgs(2, llvm::Type::getDoubleTy(*TheContext));
  llvm::FunctionType *fmaxType = llvm::FunctionType::get(llvm::Type::getDoubleTy(*TheContext), fmaxArgs, false);
  llvm::Function *fmaxF = llvm::Function::Create(fmaxType, llvm::Function::ExternalLinkage, "fmax", TheModule.get());
  functionMap["fmax"] = fmaxF;
  // fmin: double fmin(double, double)
  std::vector<llvm::Type*> fminArgs(2, llvm::Type::getDoubleTy(*TheContext));
  llvm::FunctionType *fminType = llvm::FunctionType::get(llvm::Type::getDoubleTy(*TheContext), fminArgs, false);
  llvm::Function *fminF = llvm::Function::Create(fminType, llvm::Function::ExternalLinkage, "fmin", TheModule.get());
  functionMap["fmin"] = fminF;
  // fabs: double fabs(double)
  std::vector<llvm::Type*> fabsArgs(1, llvm::Type::getDoubleTy(*TheContext));
  llvm::FunctionType *fabsType = llvm::FunctionType::get(llvm::Type::getDoubleTy(*TheContext), fabsArgs, false);
  llvm::Function *fabsF = llvm::Function::Create(fabsType, llvm::Function::ExternalLinkage, "fabs", TheModule.get());
  functionMap["fabs"] = fabsF;
  // sqrt: double sqrt(double)
  std::vector<llvm::Type*> sqrtArgs(1, llvm::Type::getDoubleTy(*TheContext));
  llvm::FunctionType *sqrtType = llvm::FunctionType::get(llvm::Type::getDoubleTy(*TheContext), sqrtArgs, false);
  llvm::Function *sqrtF = llvm::Function::Create(sqrtType, llvm::Function::ExternalLinkage, "sqrt", TheModule.get());
  functionMap["sqrt"] = sqrtF;

  addSpecialFunctionsDeclarations();
  /*
  * Add external function declarations ends
  */
}
void AUFBVJitGenerator::InitializeTargetFunctionInModule(std::string funcname) {
  // Target function prototype: bool target(uint8_t *data, size_t size, double *losses, size_t loss_cnt, uint64_t * oracle_info)
  std::vector<llvm::Type*> argTypes(5);
  argTypes[0] = llvm::Type::getInt8PtrTy(*TheContext);
  argTypes[1] = llvm::Type::getInt64Ty(*TheContext);
  argTypes[2] = llvm::Type::getDoublePtrTy(*TheContext);
  argTypes[3] = llvm::Type::getInt64Ty(*TheContext);
  argTypes[4] = llvm::Type::getInt64PtrTy(*TheContext);
  llvm::FunctionType *FT = llvm::FunctionType::get(llvm::Type::getInt1Ty(*TheContext), argTypes, false);
  llvm::Function *F = llvm::Function::Create(FT, llvm::Function::ExternalLinkage, funcname, TheModule.get());
  TargetFunction = F;
  EntryBB = nullptr;
  ThenBB = nullptr;
  ElseBB = nullptr;
  // Set names for all arguments.
  llvm::Function::arg_iterator args = TargetFunction->arg_begin();
  llvm::Value* arg1 = &*args++;
  llvm::Value* arg2 = &*args++;
  llvm::Value* arg3 = &*args++;
  llvm::Value* arg4 = &*args++;
  llvm::Value* arg5 = &*args++;
  arg1->setName("data");
  arg2->setName("size");
  arg3->setName("losses");
  arg4->setName("loss_cnt");
  arg5->setName("oracle_info");
  return;
}
void AUFBVJitGenerator::ClearModuleAndPassManager() {
  Builder.reset(nullptr);
  TheModule.reset(nullptr);
  TheFPM.reset(nullptr);
  TargetFunction = nullptr;
  EntryBB = nullptr;
  ThenBB = nullptr;
  ElseBB = nullptr;
}
/*
* JIT interfaces ends
*/

/*
* Miscellaneous helper functions
*/
std::string AUFBVJitGenerator::getNodeName(Node const& node) const {
  std::ostringstream oss;
  node.toStream(oss);
  return oss.str();
}
size_t AUFBVJitGenerator::bvSize2byteSize(size_t bvsize) {
  if (0 < bvsize && bvsize <= 8) {
    return 1;
  } else if (8 < bvsize && bvsize <= 16) {
    return 2;
  } else if (16 < bvsize && bvsize <= 32) {
    return 4;
  } else if (32 < bvsize && bvsize <= 64) {
    return 8;
  } else {
    BOOST_THROW_EXCEPTION(std::runtime_error("Unsupported bvsize"));
    exit(1);
  }
}
void AUFBVJitGenerator::get_all_varnames(Node const& node, std::vector<std::string>& dest){
  if (node.getKind() == kind::VARIABLE){
    std::string varname = getNodeName(node);
    dest.push_back(varname);
  }
  else {
    for (size_t i = 0; i < node.getNumChildren(); ++i){
      get_all_varnames(node[i], dest);
    }
  }
}
void AUFBVJitGenerator::get_all_varnodes(Node const& node, std::vector<Node>& dest){
  if (node.getKind() == kind::VARIABLE){
    dest.push_back(node);
  }
  else {
    for (size_t i = 0; i < node.getNumChildren(); ++i){
      get_all_varnodes(node[i], dest);
    }
  }
}
void AUFBVJitGenerator::get_all_kinds(Node const& node, std::set<Kind>& dest){
  dest.insert(node.getKind());
  for (size_t i = 0; i < node.getNumChildren(); ++i){
    get_all_kinds(node[i], dest);
  }
}
bool AUFBVJitGenerator::evaluate_bitvector(Node const& nd, uint64_t& v){
  Kind k = nd.getKind();
  switch (k) {
    // Constants
    case kind::CONST_BITVECTOR: {
      v = nd.getConst<BitVector>().getValue().getUnsignedLong();
      return true;
    }
    // Variables
    case kind::VARIABLE: {
      if (crashModel.find(nd) != crashModel.end()) {
        if (nd.getType().isBitVector()){
          v = crashModel[nd].getConst<BitVector>().getValue().getUnsignedLong();
        }
        else if (nd.getType().isFloatingPoint()) {
          auto fp = crashModel[nd].getConst<FloatingPoint>();
          auto fvalue_len = nd.getType().getFloatingPointExponentSize() + nd.getType().getFloatingPointSignificandSize();
          assert(fvalue_len == 32 || fvalue_len == 64);
          if (fvalue_len == 32){
            float fvalue = FloatingPointTofloat(fp);
            v = floatToBV(fvalue);
          }
          else if (fvalue_len == 64){
            double fvalue = FloatingPointTodouble(fp);
            v = doubleToBV(fvalue);
          }
          else
            assert(false);
        }
        else
          assert(false);
        return true;
      }
      else {
        v = 0;
        return false;
      }
    }
    // Arithmetic
    case kind::APPLY_UF: {
      #ifdef CVC4_USE_SYMFPU
      assert(false);
      #endif
      std::string funcname = nd.getOperator().toString();
      // find the runtime address of the function
      #ifdef ENABLE_LLVM11
      auto ExprSymbol = ExitOnErr(TheJIT->lookup(funcname));
      #else
      llvm::JITEvaluatedSymbol ExprSymbol = ExitOnErr(TheJIT->lookup(funcname));
      #endif
      assert(ExprSymbol && "Function not found");
      #ifdef ENABLE_LLVM11
      auto func = ExprSymbol.getAddress();
      #else
      auto func = ExprSymbol.getAddress();
      #endif
      // prepare the arguments
      std::vector<uint64_t> args;
      size_t argc = nd.getNumChildren();
      assert(argc >= 1 && argc <= 8);
      for (size_t i = 0; i < nd.getNumChildren(); ++i) {
        uint64_t value = 0;
        if (!evaluate_bitvector(nd[i], value)){
          v = 0;
          return false;
        }
        args.push_back(value);
      }
      // call the function with args
      uint64_t retValue = 0;
      uint64_t mask = getMask(nd.getType().getBitVectorSize());
      retValue = evaluateExFunc((void*)func, function_declarations[funcname].first, function_declarations[funcname].second, args);
      v = retValue & mask;
      return true;
    }
    case kind::BITVECTOR_NOT: {
      assert(nd.getNumChildren() == 1);
      assert(nd[0].getType().isBitVector());
      size_t bvsize = nd[0].getType().getBitVectorSize();
      uint64_t v0 = 0;
      if (!evaluate_bitvector(nd[0], v0)){
        v = 0;
        return false;
      }
      uint64_t tv = ~v0;
      uint64_t mask = getMask(bvsize);
      v = tv & mask;
      return true;
    }
    case kind::BITVECTOR_NEG: {
      assert(nd.getNumChildren() == 1);
      assert(nd[0].getType().isBitVector());
      size_t bvsize = nd[0].getType().getBitVectorSize();
      uint64_t v0 = 0;
      if (!evaluate_bitvector(nd[0], v0)){
        v = 0;
        return false;
      }
      uint64_t tv = -v0;
      uint64_t mask = getMask(bvsize);
      v = tv & mask;
      return true;
    }
    case kind::BITVECTOR_PLUS: {
      assert(nd.getNumChildren() >= 2);
      assert(nd[0].getType().isBitVector());
      size_t bvsize = nd[0].getType().getBitVectorSize();
      uint64_t tv = 0;
      for (size_t i = 0; i < nd.getNumChildren(); ++i){
        assert(nd[i].getType().isBitVector());
        assert(nd[i].getType().getBitVectorSize() == bvsize);
        uint64_t v0 = 0;
        if (!evaluate_bitvector(nd[i], v0)){
          v = 0;
          return false;
        }
        tv += v0;
      }
      // prune to bvsize
      uint64_t mask = getMask(bvsize);
      v = tv & mask;
      return true;
    }
    case kind::BITVECTOR_MULT: {
      assert(nd.getNumChildren() >= 2);
      assert(nd[0].getType().isBitVector());
      size_t bvsize = nd[0].getType().getBitVectorSize();
      uint64_t tv = 1;
      for (size_t i = 0; i < nd.getNumChildren(); ++i){
        assert(nd[i].getType().isBitVector());
        assert(nd[i].getType().getBitVectorSize() == bvsize);
        uint64_t v0 = 0;
        if (!evaluate_bitvector(nd[i], v0)){
          v = 0;
          return false;
        }
        tv *= v0;
      }
      // prune to bvsize
      uint64_t mask = getMask(bvsize);
      v = tv & mask;
      return true;
    }
    case kind::BITVECTOR_SIGN_EXTEND: {
      assert(nd.getNumChildren() == 1);
      assert(nd[0].getType().isBitVector());
      size_t bvsize = nd[0].getType().getBitVectorSize();
      size_t resultsize = nd.getType().getBitVectorSize();
      uint64_t v0 = 0;
      if (!evaluate_bitvector(nd[0], v0)){
        v = 0;
        return false;
      }
      uint64_t tv = v0;
      uint64_t mask = getMask(bvsize);
      tv = tv & mask;
      uint64_t sign = (tv >> (bvsize - 1)) & 1;
      if (sign == 1) {
        uint64_t mask2 = getMask(resultsize - bvsize);
        tv = tv | (mask2 << bvsize);
      }
      v = tv;
      return true;
    }
    case kind::BITVECTOR_EXTRACT: {
      assert(nd.getNumChildren() == 1);
      assert(nd[0].getType().isBitVector());
      size_t bvsize = nd[0].getType().getBitVectorSize();
      unsigned int high = theory::bv::utils::getExtractHigh(nd);
      unsigned int low = theory::bv::utils::getExtractLow(nd);
      uint64_t v0 = 0;
      if (!evaluate_bitvector(nd[0], v0)){
        v = 0;
        return false;
      }
      uint64_t tv = v0;
      uint64_t mask = getMask(bvsize);
      tv = tv & mask;
      uint64_t mask2 = getMask(high - low + 1);
      tv = (tv >> low) & mask2;
      v = tv;
      return true;
    }
    case kind::BITVECTOR_CONCAT:{
      assert(nd.getNumChildren() >= 2);
      assert(nd.getType().getBitVectorSize() <= 64);
      if (nd.getNumChildren() == 2) {
        assert(nd[0].getType().isBitVector() && nd[1].getType().isBitVector());
        size_t bvsize0 = nd[0].getType().getBitVectorSize();
        size_t bvsize1 = nd[1].getType().getBitVectorSize();
        uint64_t v0 = 0, v1 = 0;
        if (!evaluate_bitvector(nd[0], v0) || !evaluate_bitvector(nd[1], v1)){
          v = 0;
          return false;
        }
        uint64_t tv = v0;
        uint64_t mask = getMask(bvsize0);
        tv = tv & mask;
        uint64_t masked_v1 = v1;
        uint64_t mask2 = getMask(bvsize1);
        masked_v1 = masked_v1 & mask2;
        tv = tv << bvsize1;
        tv = tv | masked_v1;
        v = tv;
        return true;
      }
      else {
        size_t numn = nd.getNumChildren();
        assert (numn > 2);
        std::vector<size_t> size_vector;
        size_t size_sum = 0;
        size_t offset = 0;
        for (size_t i = 0; i < numn; ++i){
          size_t bv_size = nd[i].getType().getBitVectorSize();
          size_sum += bv_size;
          size_vector.push_back(bv_size);
        }
        offset = size_sum;
        assert(size_sum <= 64);
        uint64_t tv = 0;
        for (size_t i = 0; i < numn; ++i){
          uint64_t v0 = 0;
          if (!evaluate_bitvector(nd[i], v0)){
            v = 0;
            return false;
          }
          uint64_t mask = getMask(size_vector[i]);
          v0 = v0 & mask;
          tv = tv | (v0 << (offset - size_vector[i]));
          offset -= size_vector[i];
        }
        v = tv;
        return true;
      }
    }
    case kind::SELECT: {
      assert(nd.getNumChildren() == 2);
      assert(nd[0].getType().isArray());
      assert(nd[1].getType().isBitVector());
      assert(nd[1].isConst());
      std::string aname = getNodeName(nd[0]);
      uint64_t index = nd[1].getConst<BitVector>().getValue().getUnsignedLong();
      if (arrayConstMap.find(aname) != arrayConstMap.end() && arrayConstMap[aname].find(index) != arrayConstMap[aname].end()){
        // Constant element
        v = arrayConstMap[aname][index];
        return true;
      }
      else {
        // Non-constant element
        if (crashModel.find(nd) != crashModel.end()){
          assert(arrayModels.find(aname) != arrayModels.end() && arrayModels[aname].size() > index);
          v = arrayModels[aname][index];
          return true;
        }
        else {
          v = 0;
          return false;
        }
      }
    }
    case kind::BITVECTOR_XOR: {
      assert(nd.getNumChildren() == 2);
      assert(nd[0].getType().isBitVector() && nd[1].getType().isBitVector());
      assert(nd[0].getType().getBitVectorSize() == nd[1].getType().getBitVectorSize());
      size_t bvsize = nd[0].getType().getBitVectorSize();
      uint64_t v0 = 0, v1 = 0;
      if (!evaluate_bitvector(nd[0], v0) || !evaluate_bitvector(nd[1], v1)){
        v = 0;
        return false;
      }
      uint64_t tv = v0 ^ v1;
      uint64_t mask = getMask(bvsize);
      v = tv & mask;
      return true;
    }
    case kind::BITVECTOR_OR: {
      assert(nd.getNumChildren() == 2);
      assert(nd[0].getType().isBitVector() && nd[1].getType().isBitVector());
      assert(nd[0].getType().getBitVectorSize() == nd[1].getType().getBitVectorSize());
      size_t bvsize = nd[0].getType().getBitVectorSize();
      uint64_t v0 = 0, v1 = 0;
      if (!evaluate_bitvector(nd[0], v0) || !evaluate_bitvector(nd[1], v1)){
        v = 0;
        return false;
      }
      uint64_t tv = v0 | v1;
      uint64_t mask = getMask(bvsize);
      v = tv & mask;
      return true;
    }
    case kind::BITVECTOR_AND: {
      assert(nd.getNumChildren() == 2);
      assert(nd[0].getType().isBitVector() && nd[1].getType().isBitVector());
      assert(nd[0].getType().getBitVectorSize() == nd[1].getType().getBitVectorSize());
      size_t bvsize = nd[0].getType().getBitVectorSize();
      uint64_t v0 = 0, v1 = 0;
      if (!evaluate_bitvector(nd[0], v0) || !evaluate_bitvector(nd[1], v1)){
        v = 0;
        return false;
      }
      uint64_t tv = v0 & v1;
      uint64_t mask = getMask(bvsize);
      v = tv & mask;
      return true;
    }
    // floating-point
    case kind::CONST_FLOATINGPOINT:{
      assert(nd.getType().isFloatingPoint());
      if (nd.getType().isFloatingPoint(8, 24)){
        auto fvalue_len = nd.getType().getFloatingPointExponentSize() + nd.getType().getFloatingPointSignificandSize();
        assert(fvalue_len == 32);
        float fvalue = FloatingPointTofloat(nd.getConst<FloatingPoint>());
        v = floatToBV(fvalue);
        return true;
      }
      else if (nd.getType().isFloatingPoint(11, 53)){
        auto fvalue_len = nd.getType().getFloatingPointExponentSize() + nd.getType().getFloatingPointSignificandSize();
        assert(fvalue_len == 64);
        double fvalue = FloatingPointTodouble(nd.getConst<FloatingPoint>());
        v = doubleToBV(fvalue);
        return true;
      }
      else {
        assert(false);
      }
    }
    case kind::FLOATINGPOINT_TO_FP_IEEE_BITVECTOR:{
      assert(nd.getNumChildren() == 1);
      assert(nd[0].getType().isBitVector());
      unsigned int bvsize = nd[0].getType().getBitVectorSize();
      uint64_t v0 = 0;
      if (!evaluate_bitvector(nd[0], v0)){
        v = 0;
        return false;
      }
      if (nd.getType().isFloatingPoint(8, 24)){
        assert(bvsize == 32);
        v = v0;
        return true;
      }
      else if (nd.getType().isFloatingPoint(11, 53)){
        assert(bvsize == 64);
        v = v0;
        return true;
      }
      else {
        assert(false);
      }
    }
    case kind::FLOATINGPOINT_TO_FP_GENERIC:{
      // ((_ to_fp 11 53) a)
      // ((_ to_fp 11 53) RNE a)
      assert(nd.getNumChildren() == 1 || nd.getNumChildren() == 2);
      if (nd.getNumChildren() == 1){
        Node value_nd = nd[0];
        assert(value_nd.getType().isBitVector());
        unsigned int bvsize = value_nd.getType().getBitVectorSize();
        assert(bvsize == 32 || bvsize == 64);
        unsigned int exp_size = nd.getType().getFloatingPointExponentSize();
        unsigned int sig_size = nd.getType().getFloatingPointSignificandSize();
        assert((exp_size == 8 && sig_size == 24) || (exp_size == 11 && sig_size == 53));
        unsigned int dst_width = exp_size + sig_size;
        assert(bvsize == dst_width);
        uint64_t v0 = 0;
        if (!evaluate_bitvector(value_nd, v0)){
          v = 0;
          return false;
        }
        if (dst_width == 32){
          assert(bvsize == 32);
          v = v0;
          return true;
        }
        else if (dst_width == 64){
          assert(bvsize == 64);
          v = v0;
          return true;
        }
        else {
          assert(false);
        }
      }
      else if (nd.getNumChildren() == 2){
        Node value_nd = nd[1];
        // Node rm = nd[0];
        assert(nd[0].getKind() == kind::CONST_ROUNDINGMODE);
        if (value_nd.getType().isBitVector()){
          unsigned int bvsize = value_nd.getType().getBitVectorSize();
          unsigned int exp_size = nd.getType().getFloatingPointExponentSize();
          unsigned int sig_size = nd.getType().getFloatingPointSignificandSize();
          assert((exp_size == 8 && sig_size == 24) || (exp_size == 11 && sig_size == 53));
          unsigned int dst_width = exp_size + sig_size;
          uint64_t v0 = 0;
          if (!evaluate_bitvector(value_nd, v0)){
            v = 0;
            return false;
          }
          if (dst_width == 32){
            float fvalue = (float)v0;
            v = floatToBV(fvalue);
            return true;
          }
          else if (dst_width == 64){
            double fvalue = (double)v0;
            v = doubleToBV(fvalue);
            return true;
          }
          else {
            assert(false);
          }
        }
        else if (value_nd.getType().isFloatingPoint()){
          unsigned int exp_size = value_nd.getType().getFloatingPointExponentSize();
          unsigned int sig_size = value_nd.getType().getFloatingPointSignificandSize();
          assert((exp_size == 8 && sig_size == 24) || (exp_size == 11 && sig_size == 53));
          unsigned int value_width = exp_size + sig_size;
          uint64_t v0 = 0;
          if (!evaluate_bitvector(value_nd, v0)){
            v = 0;
            return false;
          }
          if (nd.getType().isFloatingPoint(8, 24)){
            if (value_width == 32){
              float fvalue = BVToFloat(v0);
              v = floatToBV(fvalue);
              return true;
            }
            else if (value_width == 64){
              double fvalue = BVToDouble(v0);
              v = floatToBV((float)fvalue);
              return true;
            }
            else {
              assert(false);
            }
          }
          else if (nd.getType().isFloatingPoint(11, 53)){
            if (value_width == 32){
              float fvalue = BVToFloat(v0);
              v = doubleToBV((double)fvalue);
              return true;
            }
            else if (value_width == 64){
              double fvalue = BVToDouble(v0);
              v = doubleToBV(fvalue);
              return true;
            }
            else {
              assert(false);
            }
          }
          else {
            assert(false);
          }
        }
        else if (value_nd.getKind() == kind::CONST_RATIONAL){
          auto rat = value_nd.getConst<Rational>();
          double fvalue = RationalTodouble(rat);
          #ifdef ENABLE_CBF_DEBUG
          llvm::errs() << "Floating-point constant (from rational): " << fvalue << "\n";
          #endif
          if (nd.getType().isFloatingPoint(8, 24)){
            float f = (float)fvalue;
            v = floatToBV(f);
            return true;
          }
          else if (nd.getType().isFloatingPoint(11, 53)){
            double f = fvalue;
            v = doubleToBV(f);
            return true;
          }
          else {
            assert(false);
          }
        }
        else {
          llvm::errs() << "Unsupported kind: " << kind::kindToString(value_nd.getKind()) << "\n";
          assert(false);
        }
      }
      assert(false);
    }
    case kind::FLOATINGPOINT_TO_FP_FLOATINGPOINT:{
      assert(false);
    }
    case kind::FLOATINGPOINT_TO_UBV:{
      assert(nd.getNumChildren() == 2);
      assert(nd.getType().isBitVector());
      assert(nd[1].getType().isFloatingPoint());
      uint64_t v0 = 0;
      if (!evaluate_bitvector(nd[1], v0)){
        v = 0;
        return false;
      }
      unsigned int fp_width = nd[1].getType().getFloatingPointExponentSize() + nd[1].getType().getFloatingPointSignificandSize();
      unsigned int bv_width = nd.getType().getBitVectorSize();
      assert((fp_width == 32 && bv_width == 32) || (fp_width == 64 && bv_width == 64));
      if (fp_width == 32){
        float f = BVToFloat(v0);
        // fp to ui
        v = (uint32_t)f;
        return true;
      }
      else if (fp_width == 64){
        double d = BVToDouble(v0);
        // fp to ui
        v = (uint64_t)d;
        return true;
      }
      else {
        assert(false);
      }
      break;
    }
    case kind::FLOATINGPOINT_TO_SBV:{
      assert(nd.getNumChildren() == 2);
      assert(nd.getType().isBitVector());
      assert(nd[1].getType().isFloatingPoint());
      uint64_t v0 = 0;
      if (!evaluate_bitvector(nd[1], v0)){
        v = 0;
        return false;
      }
      unsigned int fp_width = nd[1].getType().getFloatingPointExponentSize() + nd[1].getType().getFloatingPointSignificandSize();
      unsigned int bv_width = nd.getType().getBitVectorSize();
      assert((fp_width == 32 && bv_width == 32) || (fp_width == 64 && bv_width == 64));
      if (fp_width == 32){
        float f = BVToFloat(v0);
        // fp to si
        v = (int32_t)f;
        return true;
      }
      else if (fp_width == 64){
        double d = BVToDouble(v0);
        // fp to si
        v = (int64_t)d;
        return true;
      }
      else {
        assert(false);
      }
      break;
    }
    case kind::FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR:{
      assert(nd.getNumChildren() == 2);
      assert(nd[1].getType().isBitVector());
      unsigned int bvsize = nd[1].getType().getBitVectorSize();
      assert(bvsize == 32 || bvsize == 64);
      unsigned int dst_width = nd.getType().getFloatingPointExponentSize() + nd.getType().getFloatingPointSignificandSize();
      assert(dst_width == bvsize);
      uint64_t v0 = 0;
      if (!evaluate_bitvector(nd[1], v0)){
        v = 0;
        return false;
      }
      if (bvsize == 32){
        uint32_t uv32 = v0;
        float f = (float)uv32;
        v = floatToBV(f);
        return true;
      }
      else if (bvsize == 64){
        uint64_t uv64 = v0;
        double f = (double)uv64;
        v = doubleToBV(f);
        return true;
      }
      else {
        assert(false);
      }
    }
    case kind::FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR:{
      assert(nd.getNumChildren() == 2);
      assert(nd[1].getType().isBitVector());
      unsigned int bvsize = nd[1].getType().getBitVectorSize();
      assert(bvsize == 32 || bvsize == 64);
      unsigned int dst_width = nd.getType().getFloatingPointExponentSize() + nd.getType().getFloatingPointSignificandSize();
      assert(dst_width == bvsize);
      uint64_t v0 = 0;
      if (!evaluate_bitvector(nd[1], v0)){
        v = 0;
        return false;
      }
      if (bvsize == 32){
        uint32_t trunc_v = v0;
        int32_t sv32 = *((int32_t*)(&trunc_v));
        float f = (float)sv32;
        v = floatToBV(f);
        return true;
      }
      else if (bvsize == 64){
        uint64_t trunc_v = v0;
        int64_t sv64 = *((int64_t*)(&trunc_v));
        double f = (double)sv64;
        v = doubleToBV(f);
        return true;
      }
      else {
        assert(false);
      }
    }
    case kind::FLOATINGPOINT_SQRT:{
      assert(nd.getNumChildren() == 1);
      assert(nd[0].getType().isFloatingPoint());
      uint64_t v0 = 0;
      if (!evaluate_bitvector(nd[0], v0)){
        v = 0;
        return false;
      }
      auto fvalue_len = nd[0].getType().getFloatingPointExponentSize() + nd[0].getType().getFloatingPointSignificandSize();
      if (nd[0].getType().isFloatingPoint(8, 24)){
        assert(fvalue_len == 32);
        float f = BVToFloat(v0);
        float sqrt_f = sqrt(f);
        v = floatToBV(sqrt_f);
        return true;
      }
      else if (nd[0].getType().isFloatingPoint(11, 53)){
        assert(fvalue_len == 64);
        double f = BVToDouble(v0);
        double sqrt_f = sqrt(f);
        v = doubleToBV(sqrt_f);
        return true;
      }
      else {
        assert(false);
      }
    }
    case kind::FLOATINGPOINT_ABS:{
      assert(nd.getNumChildren() == 1);
      assert(nd[0].getType().isFloatingPoint());
      uint64_t v0 = 0;
      if (!evaluate_bitvector(nd[0], v0)){
        v = 0;
        return false;
      }
      auto fvalue_len = nd[0].getType().getFloatingPointExponentSize() + nd[0].getType().getFloatingPointSignificandSize();
      if (nd[0].getType().isFloatingPoint(8, 24)){
        assert(fvalue_len == 32);
        float f = BVToFloat(v0);
        float abs_f = fabs(f);
        v = floatToBV(abs_f);
        return true;
      }
      else if (nd[0].getType().isFloatingPoint(11, 53)){
        assert(fvalue_len == 64);
        double f = BVToDouble(v0);
        double abs_f = fabs(f);
        v = doubleToBV(abs_f);
        return true;
      }
      else {
        assert(false);
      }
    }
    case kind::FLOATINGPOINT_PLUS:{
      assert(nd.getNumChildren() == 3);
      assert(nd[1].getType().isFloatingPoint() && nd[2].getType().isFloatingPoint());
      assert(nd[1].getType().getFloatingPointExponentSize() == nd[2].getType().getFloatingPointExponentSize());
      assert(nd[1].getType().getFloatingPointSignificandSize() == nd[2].getType().getFloatingPointSignificandSize());
      uint64_t v1 = 0, v2 = 0;
      if (!evaluate_bitvector(nd[1], v1) || !evaluate_bitvector(nd[2], v2)){
        v = 0;
        return false;
      }
      auto fvalue_len = nd[1].getType().getFloatingPointExponentSize() + nd[1].getType().getFloatingPointSignificandSize();
      if (nd[1].getType().isFloatingPoint(8, 24)){
        assert(fvalue_len == 32);
        float f1 = BVToFloat(v1);
        float f2 = BVToFloat(v2);
        float add_f = f1 + f2;
        v = floatToBV(add_f);
        return true;
      }
      else if (nd[1].getType().isFloatingPoint(11, 53)){
        assert(fvalue_len == 64);
        double f1 = BVToDouble(v1);
        double f2 = BVToDouble(v2);
        double add_f = f1 + f2;
        v = doubleToBV(add_f);
        return true;
      }
      else {
        assert(false);
      }
    }
    case kind::FLOATINGPOINT_SUB:{
      assert(nd.getNumChildren() == 3);
      assert(nd[1].getType().isFloatingPoint() && nd[2].getType().isFloatingPoint());
      assert(nd[1].getType().getFloatingPointExponentSize() == nd[2].getType().getFloatingPointExponentSize());
      assert(nd[1].getType().getFloatingPointSignificandSize() == nd[2].getType().getFloatingPointSignificandSize());
      uint64_t v1 = 0, v2 = 0;
      if (!evaluate_bitvector(nd[1], v1) || !evaluate_bitvector(nd[2], v2)){
        v = 0;
        return false;
      }
      auto fvalue_len = nd[1].getType().getFloatingPointExponentSize() + nd[1].getType().getFloatingPointSignificandSize();
      if (nd[1].getType().isFloatingPoint(8, 24)){
        assert(fvalue_len == 32);
        float f1 = BVToFloat(v1);
        float f2 = BVToFloat(v2);
        float sub_f = f1 - f2;
        v = floatToBV(sub_f);
        return true;
      }
      else if (nd[1].getType().isFloatingPoint(11, 53)){
        assert(fvalue_len == 64);
        double f1 = BVToDouble(v1);
        double f2 = BVToDouble(v2);
        double sub_f = f1 - f2;
        v = doubleToBV(sub_f);
        return true;
      }
      else {
        assert(false);
      }
    }
    case kind::FLOATINGPOINT_MULT:{
      assert(nd.getNumChildren() == 3);
      assert(nd[1].getType().isFloatingPoint() && nd[2].getType().isFloatingPoint());
      assert(nd[1].getType().getFloatingPointExponentSize() == nd[2].getType().getFloatingPointExponentSize());
      assert(nd[1].getType().getFloatingPointSignificandSize() == nd[2].getType().getFloatingPointSignificandSize());
      uint64_t v1 = 0, v2 = 0;
      if (!evaluate_bitvector(nd[1], v1) || !evaluate_bitvector(nd[2], v2)){
        v = 0;
        return false;
      }
      auto fvalue_len = nd[1].getType().getFloatingPointExponentSize() + nd[1].getType().getFloatingPointSignificandSize();
      if (nd[1].getType().isFloatingPoint(8, 24)){
        assert(fvalue_len == 32);
        float f1 = BVToFloat(v1);
        float f2 = BVToFloat(v2);
        float mul_f = f1 * f2;
        v = floatToBV(mul_f);
        return true;
      }
      else if (nd[1].getType().isFloatingPoint(11, 53)){
        assert(fvalue_len == 64);
        double f1 = BVToDouble(v1);
        double f2 = BVToDouble(v2);
        double mul_f = f1 * f2;
        v = doubleToBV(mul_f);
        return true;
      }
      else {
        assert(false);
      }
    }
    case kind::FLOATINGPOINT_DIV:{
      assert(nd.getNumChildren() == 3);
      assert(nd[1].getType().isFloatingPoint() && nd[2].getType().isFloatingPoint());
      assert(nd[1].getType().getFloatingPointExponentSize() == nd[2].getType().getFloatingPointExponentSize());
      assert(nd[1].getType().getFloatingPointSignificandSize() == nd[2].getType().getFloatingPointSignificandSize());
      uint64_t v1 = 0, v2 = 0;
      if (!evaluate_bitvector(nd[1], v1) || !evaluate_bitvector(nd[2], v2)){
        v = 0;
        return false;
      }
      auto fvalue_len = nd[1].getType().getFloatingPointExponentSize() + nd[1].getType().getFloatingPointSignificandSize();
      if (nd[1].getType().isFloatingPoint(8, 24)){
        assert(fvalue_len == 32);
        float f1 = BVToFloat(v1);
        float f2 = BVToFloat(v2);
        float div_f = f1 / f2;
        v = floatToBV(div_f);
        return true;
      }
      else if (nd[1].getType().isFloatingPoint(11, 53)){
        assert(fvalue_len == 64);
        double f1 = BVToDouble(v1);
        double f2 = BVToDouble(v2);
        double div_f = f1 / f2;
        v = doubleToBV(div_f);
        return true;
      }
      else {
        assert(false);
      }
    }
    case kind::FLOATINGPOINT_NEG:{
      assert(nd.getNumChildren() == 1);
      assert(nd[0].getType().isFloatingPoint());
      uint64_t v0 = 0;
      if (!evaluate_bitvector(nd[0], v0)){
        v = 0;
        return false;
      }
      auto fvalue_len = nd[0].getType().getFloatingPointExponentSize() + nd[0].getType().getFloatingPointSignificandSize();
      if (nd[0].getType().isFloatingPoint(8, 24)){
        assert(fvalue_len == 32);
        float f = BVToFloat(v0);
        float neg_f = -f;
        v = floatToBV(neg_f);
        return true;
      }
      else if (nd[0].getType().isFloatingPoint(11, 53)){
        assert(fvalue_len == 64);
        double f = BVToDouble(v0);
        double neg_f = -f;
        v = doubleToBV(neg_f);
        return true;
      }
      else {
        assert(false);
      }
    }
    case kind::FLOATINGPOINT_FP:{
      assert(nd.getNumChildren() == 3);
      assert(nd[0].getType().isBitVector() && nd[1].getType().isBitVector() && nd[2].getType().isBitVector());
      assert(nd[0].isConst() && nd[1].isConst() && nd[2].isConst());
      unsigned int bvsize0 = nd[0].getType().getBitVectorSize();
      unsigned int bvsize1 = nd[1].getType().getBitVectorSize();
      unsigned int bvsize2 = nd[2].getType().getBitVectorSize();
      unsigned int combined_size = bvsize0 + bvsize1 + bvsize2;
      assert((bvsize0 == 1 && bvsize1 == 8 && bvsize2 == 23) || (bvsize0 == 1 && bvsize1 == 11 && bvsize2 == 52));
      unsigned int exp_size = nd.getType().getFloatingPointExponentSize();
      unsigned int sig_size = nd.getType().getFloatingPointSignificandSize();
      assert((exp_size == 8 && sig_size == 24) || (exp_size == 11 && sig_size == 53));
      unsigned int dst_width = exp_size + sig_size;
      assert(combined_size == dst_width);
      BitVector concat = nd[0].getConst<BitVector>().concat(nd[1].getConst<BitVector>()).concat(nd[2].getConst<BitVector>());
      v = concat.getValue().getUnsignedLong();
      return true;
    }
    default: {
      BOOST_THROW_EXCEPTION(std::runtime_error("evaluate_bitvector: " + kind::kindToString(nd.getKind()) + " NOT SUPPORTED"));
      exit(1);
      break;
    }
  }
  return false;
}
/*
* Miscellaneous helper functions ends
*/

/*
* Deprecated functions: only to keep the program compiled successfully
*/
void AUFBVJitGenerator::dumpPartialModel(std::map<Node, Node> nmap) {
  assert(false);
}
/*
* Deprecated functions ends
*/
}
}