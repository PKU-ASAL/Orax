#ifndef _FUZZER_CODEGEN_H_
#define _FUZZER_CODEGEN_H_

#include <list>
#include <vector>
#include <map>

#include "context/cdlist.h"
#include "context/context.h"
#include "expr/kind.h"
#include "expr/node.h"
#include "theory/theory.h"
#include "theory/uf/theory_uf.h"
#include "theory/uf/equality_engine.h"

/// The CodeGenerator class is for traversing an equality
/// expressions of THEORY_UF and generate corresponding
/// C code as fuzz target

namespace cvc5 {

namespace cgen {
class CodeGenerator {
 public:
  CodeGenerator(theory::uf::TheoryUF *ufTh);

  void dump(std::ostream& out);
  void applyIndent(std::ostream& out, size_t indent);
  void dumpHeaders(std::ostream& out);
  void dumpDeclarations(std::ostream& out);
  void dumpVarInputs(std::ostream& out);
  void dumpVarInputs_NoOpt(std::ostream& out);  
  void dumpTempVars(std::ostream& out);
  void dumpExprRecursive(std::ostream& out, Node const& node);
  void dumpCrashInput(std::ostream& out, size_t indent);

  void dumpPartialModel(std::map<Node, Node> );
  
  theory::NodeSet findApplyUF(Node const& nd) const;
  static std::string getSymbol(kind::Kind_t);
  void readCrashInput();
  void reset();

  std::string bvSizeToCType(size_t bvsize);
  size_t bvSize2byteSize(size_t bvsize);
  Node rewriteBVBitManipOps(Node const& node);
  void handleBvConcat2(std::ostream&, Node const& node);
  
  inline bool hasInputVars() {
    return (varlist.size());
  }

  std::string getNodeName(Node const&) const;
  bool isValidIdName(std::string) const;
  std::string getAndStoreCorrectId(Node const&);

  inline std::map<Node, Node> getCrashModel() { return crashModel; }

 private:
  inline std::string newVarNext();
  inline std::string newTempVarNext();

  theory::uf::TheoryUF* ufTheoryPtr;
  theory::eq::EqualityEngine* ee;
  int numVars;
  int numTempVars;
  size_t buffSize;

  // TODO: create a single map for all variable list
  theory::NodeSet varlist;
  // theory::NodeSet constAssgnList;
  std::map<Node, std::string> tempVarMap;

  std::vector<Node> modelVars;
  std::map<Node, Node> crashModel;
  std::map<std::string, std::string> idCorrections;
};
}  // namespace cgen
}  // namespace cvc5
#endif
