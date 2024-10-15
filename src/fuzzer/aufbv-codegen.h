#ifndef _FUZZER_AUFBV_CODEGEN_H_
#define _FUZZER_AUFBV_CODEGEN_H_

#include <list>
#include <vector>
#include <map>
#include <set>

#include "context/cdlist.h"
#include "context/context.h"
#include "expr/kind.h"
#include "expr/node.h"
#include "theory/theory.h"
#include "theory/uf/theory_uf.h"
#include "theory/uf/equality_engine.h"

/// The CodeGenerator class is for traversing an equality
/// expressions of THEORY and generate corresponding
/// C code as fuzz target

namespace cvc5 {
// extern bool fuzzSolveFirst;

namespace cgen {
class AUFBVCodeGenerator {
public:
  // AUFBVCodeGenerator(theory::uf::TheoryUF *ufTh);
  AUFBVCodeGenerator(theory::Theory *Th);
  // AUFBVCodeGenerator();

  void dump(std::ostream& out);
  void applyIndent(std::ostream& out, size_t indent);
  void dumpMain(std::ostream& out);
  void dumpHeaders(std::ostream& out);
  void dumpDeclarations(std::ostream& out);
  void dumpVarInputs(std::ostream& out);
  void dumpVarInputs_NoOpt(std::ostream& out);
  void dumpTempVars(std::ostream& out);
  void dumpExprRecursive(std::ostream& out, Node const& node, bool reverse=false, bool tempDump=false);
  void dumpType(std::ostream& out, Node const& node);
//   void dumpCrashInput(std::ostream& out, size_t indent);
  void checkReused();
  void visitExpr(Node const& node);

  void dumpPartialModel(std::map<Node, Node>);

//   theory::NodeSet findApplyUF(Node const& nd) const;
  static std::string getSymbol(kind::Kind_t);
  void readCrashInput();
  void reset();

  std::string bvSizeToCType(size_t bvsize);
  size_t bvSize2byteSize(size_t bvsize);
  Node rewriteBVBitManipOps(Node const& node);
  void handleBvConcat2(std::ostream&, Node const& node);
  void handleBvConcat(std::ostream&, Node const& node);
  bool concatIsLSHR(Node const& nd);

  inline bool hasInputVars() {
    return (varlist.size());
  }

  std::string getNodeName(Node const&) const;
  bool isValidIdName(std::string) const;
  std::string getAndStoreCorrectId(Node const&);
  bool hasExternal();

  inline std::map<Node, Node> getCrashModel() { return crashModel; }

  void add_edge_recursive(Node const& node, Node const& parent);
  void build_graph(std::map<Node, std::string>& tempVarMap);
  void reverse_topsort();
private:
//   inline std::string newVarNext();
  inline std::string newTempVarNext();
  bool hasExternalRecursive(Node const& nd);

//   theory::uf::TheoryUF* ufTheoryPtr;
  theory::Theory* theoryPtr;

  theory::eq::EqualityEngine* ee;
  int numVars;
  int numTempVars;
  size_t buffSize;

//   // TODO: create a single map for all variable list
  theory::NodeSet varlist;
//   // theory::NodeSet constAssgnList;
  std::map<Node, std::string> tempVarMap;
  std::map<std::string, uint32_t> arraySizeMap;

  std::vector<Node> modelVars;
  std::map<Node, Node> crashModel;
  std::map<Node, std::vector<uint64_t>> arrayModel;
  std::map<std::string, std::string> idCorrections;

  // orax
  std::set<Node> cached;
  std::set<Node> reused;
  std::map<Node, std::vector<Node>> reused_node_graph;
  std::vector<Node> reversed_topological_order;
};
}  // namespace cgen
}  // namespace cvc5
#endif
