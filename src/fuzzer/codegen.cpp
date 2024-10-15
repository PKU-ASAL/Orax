
#include "fuzzer/codegen.h"

#include <sys/stat.h>

#include <boost/throw_exception.hpp>
#include <fstream>

#include "expr/type_node.h"
#include "include/termcolor.hpp"
#include "options/theory_options.h"
#include "theory/bv/theory_bv_rewrite_rules_constant_evaluation.h"
#include "theory/bv/theory_bv_rewrite_rules_normalization.h"
#include "theory/bv/theory_bv_utils.h"
#include "expr/node_traversal.h"
#include "assert.h"

namespace cvc5 {
namespace cgen {

CodeGenerator::CodeGenerator(theory::uf::TheoryUF *ufTh) : ufTheoryPtr(ufTh),
							   numVars(0),  buffSize(0),
							   varlist() {

  ee = ufTheoryPtr->getEqualityEngine();
}

void CodeGenerator::reset() {
  varlist.clear();
  crashModel.clear();
  tempVarMap.clear();
  modelVars.clear();
  idCorrections.clear();
  numVars = 0;
  numTempVars = 0;
  buffSize = 0;
}

void CodeGenerator::dump(std::ostream& out) {

  reset();
  std::stringstream ss;
  theory::NodeSet learntConflicts = ufTheoryPtr->getLearntConflicts();
  size_t i = 1;

  Trace("fuzzer-codegen") << "Generating fuzz target program..." << std::endl;

  dumpHeaders(out);
  out << std::endl;
  out << "double target(uint8_t *data, size_t size) {" << std::endl;

  // append conflict learned from solvers
  for (auto child_it = learntConflicts.begin();
       child_it != learntConflicts.end(); ++child_it) {

    Node cnode = Node(*child_it);
    ss << "loss += ";
    dumpExprRecursive(ss, cnode);
    ss << ";";
    ss << std::endl;
    ++i;
  }

  auto thi = ufTheoryPtr->facts_begin();
  auto the = ufTheoryPtr->facts_end();
  theory::NodeSet paramList;

  for (;thi != the;++thi) {
    Node tnode = Node(*thi);

    if (learntConflicts.find(tnode) == learntConflicts.end()) {
      theory::NodeSet ns = findApplyUF(tnode);
      if (ns.size() != 0) {
        // dump the IF-conditions
        ss << "loss += ";
        dumpExprRecursive(ss, tnode);
        ss << ";";
        ss << std::endl;
        ++i;
      }
    }

  }

  dumpDeclarations(out);
  std::stringstream vinputSS;
  dumpVarInputs(vinputSS);

  applyIndent(out, 2);
  // out << "assert(bufflen >= " << buffSize << ");" << std::endl;
  out << "if(bufflen < " << buffSize << ") return __DBL_MAX__;" << std::endl;


  out << vinputSS.str();
  dumpTempVars(out);

  std::string line;
  while(std::getline(ss, line)) {
    out << std::string(2, ' ') << line << std::endl;
  }

  // i = i + 1;
  // out << std::string(i, ' ') << "{" << std::endl;
  // dumpCrashInput(out, i + 2);
  // out << std::string(i + 2, ' ') << "assert(0);" << std::endl;
  // out << std::string(i, ' ') << "}" << std::endl;
  // out << std::string(4, ' ') << "}" << std::endl;
  // out << std::string(2, ' ') << "return 0;" << std::endl << "}";
  out << std::string(2, ' ') << "return loss;" << std::endl;
  out << std::endl;
  out << "}" << std::endl << std::endl;
  out << "size_t TARGET_DATA_MIN_LEN = " << buffSize << ";" << std::endl;
}

std::string CodeGenerator::bvSizeToCType(size_t bvsize) {
  if (0 < bvsize && bvsize <= 8) {
    return "uint8_t";
  } else if (8 < bvsize && bvsize <= 16) {
    return "uint16_t";
  } else if (16 < bvsize && bvsize <= 32) {
    return "uint32_t";
  } else if (32 < bvsize && bvsize <= 64) {
    return "uint64_t";
  } else {
    BOOST_THROW_EXCEPTION(std::runtime_error("Unsupported bvsize"));
    exit(1);
  }
}

size_t CodeGenerator::bvSize2byteSize(size_t bvsize) {
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

void CodeGenerator::dumpPartialModel(std::map<Node, Node> nmap) {

  FILE* fp = fopen("partmodel.bin", "wb");

  // for each variable dump the value
  for (Node nd : modelVars) {
    if (nd.getType().isInteger()) {
      int32_t temp = (nmap[nd]).getConst<Rational>().getNumerator().getSignedInt();
      fwrite(&temp, sizeof(temp), 1, fp);
    }
    else if (nd.getType().isBitVector()) {
      // check the size of the bitvector element
      size_t bvsize = bvSize2byteSize(nd.getType().getBitVectorSize());
      uint32_t value =  (nmap[nd]).getConst<BitVector>().getValue().getUnsignedInt();

      if (bvsize == 1) {
        uint8_t tvalue = (uint8_t)value;
	fwrite(&tvalue, sizeof(tvalue), 1, fp);
      } else if (bvsize == 2) {
        uint16_t tvalue = (uint16_t)value;
	fwrite(&tvalue, sizeof(tvalue), 1, fp);
      } else if (bvsize == 4) {
        uint32_t tvalue = (uint32_t)value;
	fwrite(&tvalue, sizeof(tvalue), 1, fp);
      }
      else {
        BOOST_THROW_EXCEPTION(std::runtime_error("Unsupported bvsize"));
        exit(1);
      }
    }

  }

  fclose(fp);
}

void CodeGenerator::readCrashInput() {
  struct stat fileStats;
  size_t fileSize = 0;

  // if (stat("model.bin", &fileStats) == 0)
  if (stat("solution.txt", &fileStats) == 0)
    fileSize = fileStats.st_size;
  else {
    std::cerr << "File stats error occured" << std::endl;
    exit(1);
  }

  // open file and read into buffer
  // std::ifstream model("model.bin", std::ios::in | std::ios::binary);
  std::ifstream model("solution.txt", std::ios::in);
  if (!model) {
    std::cerr << "Error opening model" << std::endl;
    exit(1);
  }

  std::string line;
  getline(model, line);
  assert(line.find("sat") != std::string::npos);
  getline(model, line);
  size_t len = std::stoi(line);

  std::vector<uint8_t> buffer(len);
  for (size_t byteId = 0; byteId < fileSize; ++byteId) model >> buffer[byteId];

  // reading integer data variable values from model
  // TODO: support other data types

  uint8_t* buffptr = buffer.data();
  for (Node nd : modelVars) {
    if (nd.getType().isInteger()) {
      int temp = *((int*)buffptr);
      crashModel[nd] = NodeManager::currentNM()->mkConst(Rational(temp));
      buffptr += sizeof(int);
    }
    else if (nd.getType().isBitVector()) {
      // check the size of the bitvector element
      size_t bvsize = bvSize2byteSize(nd.getType().getBitVectorSize());
      unsigned int value = 0;

      if (bvsize == 1) {
        value = *((uint8_t*)buffptr);
        buffptr += sizeof(uint8_t);
      } else if (bvsize == 2) {
        value = *((uint16_t*)buffptr);
        buffptr += sizeof(uint16_t);
      } else if (bvsize == 4) {
        value = *((uint32_t*)buffptr);
        buffptr += sizeof(uint32_t);
      } else if (bvsize == 8) {
        value = *((uint64_t*)buffptr);
        buffptr += sizeof(uint64_t);
      } else {
        BOOST_THROW_EXCEPTION(std::runtime_error("Unsupported bvsize"));
        exit(1);
      }

      crashModel[nd] = theory::bv::utils::mkConst(nd.getType().getBitVectorSize(), value);
    }
  }

  model.close();
}

void CodeGenerator::dumpCrashInput(std::ostream& out, size_t indent) {
  if (varlist.size() == 0) return;

  applyIndent(out, indent);
  out << "FILE* fp = fopen(\"model.bin\", \"wb\");" << std::endl;

  // for each variable dump the value
  for (Node nd : modelVars) {
    std::string nodeIdName = getNodeName(nd);
    if (!isValidIdName(nodeIdName)) nodeIdName = idCorrections[nodeIdName];

    applyIndent(out, indent);
    out << "fwrite(&" << nodeIdName << ", sizeof(" << nodeIdName << "), 1, fp);"
        << std::endl;
  }


  applyIndent(out, indent);
  out << "fclose(fp);" << std::endl;
}

void CodeGenerator::dumpDeclarations(std::ostream& out) {

  // buffer pointer to be allocated by HonggFuzz
  applyIndent(out, 2);
  out << "size_t bufflen = size;" << std::endl;
  // applyIndent(out, 2);
  // out << "__AFL_INIT();" << std::endl;
  applyIndent(out, 2);
  out << "uint8_t *buff = data;" << std::endl;
  applyIndent(out, 2);
  out << "double EPSILON = 1e-3;" << std::endl;
  applyIndent(out, 2);
  out << "double UNEQUAL_GAP = 1e-6;" << std::endl;

  applyIndent(out, 2);
  out << "double loss = 0;" << std::endl;
  out << std::endl;

  if (varlist.size() == 0)
    return;

  applyIndent(out, 1);
  out << "// variable declarations" << std::endl;
  for (Node nd : varlist) {
    if (nd.getType().isInteger()) {
      out << std::string(2, ' ') << "int " << getAndStoreCorrectId(nd);
    }
    else if (nd.getType().isBitVector()) {
      size_t bvsize = nd.getType().getBitVectorSize();
      size_t uintsize = bvSize2byteSize(bvsize);
      out << std::string(2, ' ') << bvSizeToCType(bvsize) << " " << getAndStoreCorrectId(nd);
      buffSize += uintsize;
    }
    else {
      BOOST_THROW_EXCEPTION(
          std::runtime_error("Variable declaration error : Unknown type"));
      exit(1);
    }

    out << ";" << std::endl;
  }

  out << std::endl;
}

void CodeGenerator::applyIndent(std::ostream& out, size_t indent) {
  out << std::string(indent, ' ');
}


void CodeGenerator::dumpVarInputs(std::ostream& out) {

  if (options::noOpt()) {
    dumpVarInputs_NoOpt(out);
    return;
  }

  out << std::string(2, ' ') << "uint8_t* buffptr = buff;\n" << std::endl;

  if (varlist.size() == 0) return;

  buffSize = 0;
  std::map<Node, Node> eqc;
  for (Node nd : varlist) {
    if (nd.getType().isInteger()) {
      Node tnode;
      if (ee->hasTerm(nd)) tnode = ee->getRepresentative(nd);
      applyIndent(out, 2);

      if (ee->hasTerm(nd) && tnode.getKind() == kind::VARIABLE && tnode != nd) {
        if (varlist.find(tnode) != varlist.end()) {
          eqc[nd] = tnode;
        }
        else {
          out << getAndStoreCorrectId(nd) << " = *((int*)buffptr);" << std::endl;
          applyIndent(out, 2);
          out << "buffptr += (sizeof(int) / sizeof(uint8_t));" << std::endl;
          buffSize += sizeof(int);
          modelVars.push_back(nd);
        }
      }
      else if (ee->hasTerm(nd) && tnode.getKind() == kind::CONST_RATIONAL)
        out << getAndStoreCorrectId(nd) << " = " << tnode << ";" << std::endl;
      else {
        out << getAndStoreCorrectId(nd) << " = *((int*)buffptr);" << std::endl;
        applyIndent(out, 2);
        out << "buffptr += (sizeof(int) / sizeof(uint8_t));" << std::endl;
        buffSize += sizeof(int);
        modelVars.push_back(nd);
      }

      out << std::endl;
    }
    else if (nd.getType().isBitVector()) {
      Node tnode;
      if (ee->hasTerm(nd)) tnode = ee->getRepresentative(nd);
      applyIndent(out, 2);

      if (ee->hasTerm(nd) && tnode.getKind() == kind::VARIABLE && tnode != nd) {
        if (varlist.find(tnode) != varlist.end()) {
          eqc[nd] = tnode;
        }
        else {
          size_t bvsize = nd.getType().getBitVectorSize();
          size_t uintsize = bvSize2byteSize(bvsize);
          out << getAndStoreCorrectId(nd) << " = *((" << bvSizeToCType(bvsize)
              << "*) buffptr);" << std::endl;
          applyIndent(out, 2);
          out << "buffptr += " << uintsize << ";" << std::endl;

          buffSize += uintsize;
          modelVars.push_back(nd);
        }
      }
      else if (ee->hasTerm(nd) && tnode.getKind() == kind::CONST_BITVECTOR)
        out << getAndStoreCorrectId(nd) << " = " << tnode.getConst<BitVector>().getValue()
            << ";" << std::endl;
      else {
        size_t bvsize = nd.getType().getBitVectorSize();
        size_t uintsize = bvSize2byteSize(bvsize);
        out << getAndStoreCorrectId(nd) << " = *((" << bvSizeToCType(bvsize)
            << "*) buffptr);" << std::endl;
        applyIndent(out, 2);
        out << "buffptr += " << uintsize << ";" << std::endl;

        buffSize += uintsize;
        modelVars.push_back(nd);
      }

      out << std::endl;

    }

    else {
      out << std::endl << "// Error : unknown type" << std::endl;
      BOOST_THROW_EXCEPTION(
          std::runtime_error("Bitvector codegen implementation incomplete"));
      exit(1);
    }

  }

  for (auto eqp : eqc) {
    applyIndent(out, 2);
    out << getAndStoreCorrectId(eqp.first) << " = "
	<< getAndStoreCorrectId(eqp.second) << ";" << std::endl;
  }

  out << std::endl;
}

void CodeGenerator::dumpVarInputs_NoOpt(std::ostream& out) {

  out << "uint8_t* buffptr = buff;\n" << std::endl;

  if (varlist.size() == 0) return;

  buffSize = 0;
  std::map<Node, Node> eqc;
  for (Node nd : varlist) {
    if (nd.getType().isInteger()) {
      applyIndent(out, 4);

      out << getAndStoreCorrectId(nd) << " = *((int*)buffptr);" << std::endl;
      applyIndent(out, 4);
      out << "buffptr += (sizeof(int) / sizeof(uint8_t));" << std::endl;
      buffSize += sizeof(int);
      modelVars.push_back(nd);

      out << std::endl;
    }
    else if (nd.getType().isBitVector()) {
      applyIndent(out, 4);

      size_t bvsize = nd.getType().getBitVectorSize();
      size_t uintsize = bvSize2byteSize(bvsize);
      out << getAndStoreCorrectId(nd) << " = *((" << bvSizeToCType(bvsize)
	  << "*) buffptr);" << std::endl;

      applyIndent(out, 4);
      out << "buffptr += " << uintsize << ";" << std::endl;

      buffSize += uintsize;
      modelVars.push_back(nd);
      out << std::endl;
    }

    else {
      out << std::endl << "// Error : unknown type" << std::endl;
      BOOST_THROW_EXCEPTION(
          std::runtime_error("Bitvector codegen implementation incomplete"));
      exit(1);
    }

  }

  out << std::endl;
}


void CodeGenerator::dumpTempVars(std::ostream& out) {

  if (tempVarMap.size() == 0) return;
  BOOST_THROW_EXCEPTION(std::runtime_error("Dump temp not supported for now"));

  applyIndent(out, 2);
  out << "// temp variable definitions" << std::endl;
  for (std::pair<Node, std::string> nd : tempVarMap) {
    if (nd.first.getKind() == kind::BITVECTOR_EXTRACT &&
        theory::bv::utils::getExtractLow(nd.first) == 0 &&
        nd.first[0].getKind() == kind::VARIABLE) {
      size_t hi = theory::bv::utils::getExtractHigh(nd.first);
      std::string ctype = bvSizeToCType(hi + 1);
      unsigned int mask = (1U << (hi + 1)) - 1;
      applyIndent(out, 2);
      out << ctype << " " << nd.second << " = ";
      out << " & " << mask << ";" << std::endl;
    } else {
      std::cerr << termcolor::red
                << "** Doesn't support BV_EXTRACT on expressions"
                << termcolor::reset << std::endl;
      exit(EXIT_FAILURE);
    }
  }
  out << std::endl;
}

theory::NodeSet CodeGenerator::findApplyUF(const Node &nd) const{

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

std::string CodeGenerator::newVarNext() {
  numVars += 1;
  return "__input_" + std::to_string(numVars);
}

std::string CodeGenerator::newTempVarNext() {
  numTempVars += 1;
  return "__temp_" + std::to_string(numTempVars);
}

void CodeGenerator::dumpHeaders(std::ostream& out) {
  // FIXME : add file check
  out << "#include \"" << options::targetHeader() << "\"" << std::endl;
  out << "#include <limits.h>" << std::endl;
  out << "#include <math.h>" << std::endl;
  out << "#include <assert.h>" << std::endl;
  // out <<"\n__AFL_FUZZ_INIT();\n" << std::endl;
  // out << "#pragma clang optimize off" << std::endl;
  // out << "#pragma GCC   optimize(\"O0\")" << std::endl;
}


void CodeGenerator::dumpExprRecursive(std::ostream& out, Node const& node) {
  Node rwNode;

  switch (node.getKind()) {

    case kind::CONST_RATIONAL:
      if (node.getConst<Rational>().isIntegral()) {
        bool neg = node.getConst<Rational>().sgn() == -1;
        if (neg) out << "(";
        out << node.getConst<Rational>();
        if (neg) out << ")";
      } else {
        BOOST_THROW_EXCEPTION(std::runtime_error("Implementation incomplete"));
        exit(1);
      }
      break;

    case kind::CONST_BITVECTOR:
      out << "(" << node.getConst<BitVector>().getValue() << ")";
      break;

    case kind::VARIABLE:
      if (varlist.end() == varlist.find(node)) varlist.insert(node);
      out << getAndStoreCorrectId(node);
      break;

    case kind::NOT:
      // out << getSymbol(node.getKind()) << "(";
      // dumpExprRecursive(out, node[0]);
      // out << ")";
      // break;
      Assert(node[0].getKind() == kind::EQUAL);
      out << "fmax(0, UNEQUAL_GAP - ";
      out << "abs(";
      dumpExprRecursive(out, node[0][0]);
      out << " - ";
      dumpExprRecursive(out, node[0][1]);
      out << ")";
      out << ")";
      break;

    case kind::EQUAL:
      out << "abs(";
      dumpExprRecursive(out, node[0]);
      out << " - ";
      dumpExprRecursive(out, node[1]);
      out << ")";
      break;

    case kind::OR:
    case kind::AND:
    case kind::MULT:
    case kind::BITVECTOR_MULT:
      out << "(";
      for (size_t it = 0; it < node.getNumChildren(); ++it) {
        dumpExprRecursive(out, node[it]);
        if (it < node.getNumChildren() - 1)
	        out << " " << getSymbol(node.getKind()) << " ";
      }

      out << ")";
      break;

    case kind::APPLY_UF:
      out << node.getOperator();
      out << "(";
      for (size_t cid = 0; cid < node.getNumChildren(); ++cid) {
        CodeGenerator::dumpExprRecursive(out, node[cid]);
        if (cid < node.getNumChildren() - 1) out << ", ";
      }
      out << ")";
      break;

    case kind::BITVECTOR_NOT:
      out << "!";
      dumpExprRecursive(out, node[0]);
      break;

    case kind::BITVECTOR_NEG:
      out << "-";
      dumpExprRecursive(out, node[0]);
      break;

    case kind::LT:
    case kind::BITVECTOR_SLT:
    case kind::BITVECTOR_ULT:
      out << "fmax(0,";
      dumpExprRecursive(out, node[0]);
      out << " - ";
      dumpExprRecursive(out, node[1]);
      out << " + EPSILON";
      out << ")";
      break;

    case kind::LEQ:
    case kind::BITVECTOR_ULE:
    case kind::BITVECTOR_SLE:
      out << "fmax(0,";
      dumpExprRecursive(out, node[0]);
      out << " - ";
      dumpExprRecursive(out, node[1]);
      out << ")";
      break;

    case kind::GT:
    case kind::BITVECTOR_UGT:
    case kind::BITVECTOR_SGT:
      out << "fmax(0,";
      dumpExprRecursive(out, node[1]);
      out << " - ";
      dumpExprRecursive(out, node[0]);
      out << " + EPSILON";
      out << ")";
      break;

    case kind::GEQ:
    case kind::BITVECTOR_SGE:
    case kind::BITVECTOR_UGE:
      out << "fmax(0,";
      dumpExprRecursive(out, node[1]);
      out << " - ";
      dumpExprRecursive(out, node[0]);
      out << ")";
      break;

    case kind::MINUS:
    case kind::DIVISION:
    case kind::PLUS:
    case kind::BITVECTOR_PLUS:
      dumpExprRecursive(out, node[0]);
      out << " " << getSymbol(node.getKind()) << " ";
      dumpExprRecursive(out, node[1]);
      break;

    case kind::BITVECTOR_SIGN_EXTEND:
      dumpExprRecursive(out, node[0]);
      break;

    case kind::BITVECTOR_EXTRACT:
      // TODO: apply node re-write rules to optimize the expression further
      rwNode = rewriteBVBitManipOps(node);
      if (node == rwNode) {
        if (tempVarMap.find(node) == tempVarMap.end())
          tempVarMap[node] = newTempVarNext();

        dumpExprRecursive(out, node[0]);
      } else
        dumpExprRecursive(out, rwNode);

      break;

    case kind::BITVECTOR_CONCAT:
      if (node.getNumChildren() == 2) {
	      handleBvConcat2(out, node);
      }
      else
        BOOST_THROW_EXCEPTION(std::runtime_error(
          "Codegeneration for BvConcat with more than two children NOT SUPPORTED"));
      break;

    default:
      BOOST_THROW_EXCEPTION(std::runtime_error(
          "Codegeneration for " + kind::kindToString(node.getKind()) +
          " NOT SUPPORTED"));
      break;
  }
}

std::string CodeGenerator::getNodeName(Node const& node) const {
  std::ostringstream oss;
  node.toStream(oss);
  return oss.str();
}

/*
 *  Taken from geeksforgeeks :
 *  https://www.geeksforgeeks.org/check-whether-the-given-string-is-a-valid-identifier/
 */
bool CodeGenerator::isValidIdName(std::string str) const {
  // If first character is invalid
  if (!((str[0] >= 'a' && str[0] <= 'z') || (str[0] >= 'A' && str[0] <= 'Z') ||
        str[0] == '_'))
    return false;

  // Traverse the string for the rest of the characters
  for (size_t i = 1; i < str.length(); i++) {
    if (!((str[i] >= 'a' && str[i] <= 'z') ||
          (str[i] >= 'A' && str[i] <= 'Z') ||
          (str[i] >= '0' && str[i] <= '9') || str[i] == '_'))
      return false;
  }

  // String is a valid identifier
  return true;
}

std::string CodeGenerator::getAndStoreCorrectId(Node const& node) {
  std::string nodeIdName = getNodeName(node);
  if (isValidIdName(nodeIdName)) return nodeIdName;

  if (idCorrections.find(nodeIdName) == idCorrections.end())
    idCorrections[nodeIdName] = newTempVarNext();

  return idCorrections[nodeIdName];
}

std::string CodeGenerator::getSymbol(kind::Kind_t ktype) {
  switch (ktype) {
    case kind::LT:
    case kind::BITVECTOR_SLT:
    case kind::BITVECTOR_ULT:
      return "<";
      break;

    case kind::LEQ:
    case kind::BITVECTOR_ULE:
    case kind::BITVECTOR_SLE:
      return "<=";
      break;

    case kind::GT:
    case kind::BITVECTOR_UGT:
    case kind::BITVECTOR_SGT:
      return ">";
      break;

    case kind::GEQ:
    case kind::BITVECTOR_SGE:
    case kind::BITVECTOR_UGE:
      return ">=";
      break;

    case kind::EQUAL:
      return "==";
      break;

    case kind::AND:
      return "&&";
      break;

    case kind::NOT:
    case kind::BITVECTOR_NOT:
      return "!";
      break;

    case kind::MINUS:
      return "-";
      break;

    case kind::DIVISION:
      return "/";
      break;

    case kind::PLUS:
    case kind::BITVECTOR_PLUS:
      return "+";
      break;

    case kind::MULT:
    case kind::BITVECTOR_MULT:
      return "*";
      break;

    case kind::BITVECTOR_ASHR:
      return ">>";
      break;


    default:
      BOOST_THROW_EXCEPTION(std::runtime_error(
          "Codegeneration for " + std::string(kind::toString(ktype)) +
          " NOT SUPPORTED"));
      break;
  }
}

Node CodeGenerator::rewriteBVBitManipOps(Node const& node) {
  if (theory::bv::RewriteRule<theory::bv::ExtractArith>::applies(node))
    return theory::bv::RewriteRule<theory::bv::ExtractArith>::run<false>(node);

  else if (theory::bv::RewriteRule<theory::bv::ExtractArith2>::applies(node)) {
    // lets throw an error for this now
    std::cerr << "ABORTING : only support extract of type [[e]](i : 0)"
              << std::endl;
    exit(EXIT_FAILURE);
  }

  if (theory::bv::RewriteRule<theory::bv::EvalExtract>::applies(node))
    return theory::bv::RewriteRule<theory::bv::EvalExtract>::run<false>(node);

  return node;
}

void CodeGenerator::handleBvConcat2(std::ostream& out, Node const& nd) {
  size_t bvsize0 = nd[0].getType().getBitVectorSize();
  size_t bvsize1 = nd[1].getType().getBitVectorSize();

  Assert (bvsize1 + bvsize0 <= sizeof(size_t) * 8);
  out << "((" << nd[0] << " << " << bvsize1 << ") | " << nd[1].getConst<BitVector>().getValue() << ")";
}



}  // namespace cgen
}  // namespace cvc5
