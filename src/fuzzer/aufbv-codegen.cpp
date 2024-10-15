#include "fuzzer/aufbv-codegen.h"

#include <sys/stat.h>

#include <boost/throw_exception.hpp>
#include <fstream>
#include <set>
#include <stack>

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

AUFBVCodeGenerator::AUFBVCodeGenerator(theory::Theory *Th): theoryPtr(Th), numVars(0), buffSize(0), varlist() {
  ee = theoryPtr->getEqualityEngine();
}

void AUFBVCodeGenerator::reset() {
  varlist.clear();
  crashModel.clear();
  tempVarMap.clear();
  modelVars.clear();
  idCorrections.clear();
  numVars = 0;
  numTempVars = 0;
  buffSize = 0;
  arraySizeMap.clear();
  arrayModel.clear();
  cached.clear();
  reused.clear();
}

void AUFBVCodeGenerator::dump(std::ostream& out) {

  reset();
  std::stringstream ss;
  size_t i = 1;
  Trace("fuzzer-codegen") << "Generating fuzz target program..." << std::endl;
  dumpHeaders(out);
  out << std::endl;
  out << "double target(uint8_t *data, size_t size) {" << std::endl;

  auto thi = theoryPtr->facts_begin();
  auto the = theoryPtr->facts_end();
  checkReused();
  for (;thi != the;++thi) {
    Node tnode = Node(*thi);
    ss << "loss += ";
    dumpExprRecursive(ss, tnode);
    ss << ";";
    ss << std::endl;
    ++i;
  }
  // temp needs to be before crash input
  std::stringstream tempss;
  dumpTempVars(tempss);

  dumpDeclarations(out);
  std::stringstream vinputSS;
  dumpVarInputs(vinputSS);

  applyIndent(out, 2);
  out << "if(bufflen < " << buffSize << ") return __DBL_MAX__;" << std::endl;

  out << vinputSS.str();
  out << tempss.str();

  std::string line;
  while(std::getline(ss, line)) {
    out << std::string(2, ' ') << line << std::endl;
  }

  out << std::string(2, ' ') << "return loss;" << std::endl;
  out << std::endl;
  out << "}" << std::endl << std::endl;
  out << "size_t TARGET_DATA_MIN_LEN = " << buffSize << ";" << std::endl << std::endl;
  dumpMain(out);
}

void AUFBVCodeGenerator::dumpMain(std::ostream& out){
  out << "int main(int argc, const char *argv[])" << std::endl;
  out << "{" << std::endl;
  out << std::string(2, ' ') << "if(argc != 2)" << std::endl;
  out << std::string(2, ' ') << "{" << std::endl;
  out << std::string(4, ' ') << "return 1;" << std::endl;
  out << std::string(2, ' ') << "}" << std::endl;
  out << std::string(2, ' ') << "size_t size = strlen(argv[1]);" << std::endl;
  out << std::string(2, ' ') << "double EPSILON = 1e-12;" << std::endl;
  out << std::string(2, ' ') << "double loss = target(argv[1], size);" << std::endl;
  out << std::string(2, ' ') << "if (fabs(loss) > EPSILON)" << std::endl;
  out << std::string(4, ' ') << "return 1;" << std::endl;
  out << std::string(2, ' ') << "return 0;" << std::endl;
  out << "}" << std::endl;
}

std::string AUFBVCodeGenerator::bvSizeToCType(size_t bvsize) {
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

size_t AUFBVCodeGenerator::bvSize2byteSize(size_t bvsize) {
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

void AUFBVCodeGenerator::dumpPartialModel(std::map<Node, Node> nmap) {
  // TODO: support dumpPartialModel
  assert(false);
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
    else if (nd.getType().isArray()) {
      std::string aname = getAndStoreCorrectId(nd);
      uint32_t arraysize = arraySizeMap[aname];
      assert(arraysize >= 0);
      uint64_t value = 0;
      for (uint32_t i = 0; i <= arraysize; ++i){
        size_t elementsize = nd.getType().getArrayConstituentType().getBitVectorSize();
        size_t uintsize = bvSize2byteSize(elementsize);
        value = arrayModel[nd][i];
        if (uintsize == 1) {
          uint8_t tvalue = (uint8_t)value;
          fwrite(&tvalue, sizeof(tvalue), 1, fp);
        } else if (uintsize == 2) {
          uint16_t tvalue = (uint16_t)value;
          fwrite(&tvalue, sizeof(tvalue), 1, fp);
        } else if (uintsize == 4) {
          uint32_t tvalue = (uint32_t)value;
          fwrite(&tvalue, sizeof(tvalue), 1, fp);
        } else if (uintsize == 8) {
          uint64_t tvalue = (uint64_t)value;
          fwrite(&tvalue, sizeof(tvalue), 1, fp);
        } else {
          BOOST_THROW_EXCEPTION(std::runtime_error("Unsupported bvsize"));
          exit(1);
        }
      }
    }
  }

  fclose(fp);
}

static char* readfile(FILE* fp){
  int filesize;
  std::string data = "";
  fseek(fp, 0, SEEK_END);
  filesize = ftell(fp);
  char* file_contents = (char*)(malloc(filesize+1));
  fseek(fp, 0, SEEK_SET);
  auto _ = fread(file_contents, filesize, 1, fp);
  file_contents[filesize] = '\0';
  return file_contents;
}

void AUFBVCodeGenerator::readCrashInput() {
  struct stat fileStats;
  size_t fileSize = 0;

  // if (stat("model.bin", &fileStats) == 0)
  if (stat("solution.bin", &fileStats) == 0)
    fileSize = fileStats.st_size;
  else {
    std::cerr << "File stats error occured" << std::endl;
    exit(1);
  }

  FILE* fp = std::fopen("solution.bin", "rb");
  char* model = readfile(fp);
  if (!model) {
    std::cerr << "Error opening model!" << std::endl;
    exit(1);
  }
  size_t len = fileSize;
  fclose(fp);

  std::vector<uint8_t> buffer(len);
  for (size_t byteId = 0; byteId < len; ++byteId){
    buffer[byteId] = (uint8_t)(model[byteId]);
  }
  if (model) free(model);

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
      uint64_t value = 0;

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
    else if (nd.getType().isArray()) {
      std::string aname = getAndStoreCorrectId(nd);
      uint32_t arraysize = arraySizeMap[aname];
      assert(arraysize >= 0);
      uint64_t value = 0;
      for (uint32_t i = 0; i <= arraysize; ++i){
        size_t elementsize = nd.getType().getArrayConstituentType().getBitVectorSize();
        size_t uintsize = bvSize2byteSize(elementsize);
        if (uintsize == 1) {
          value = *((uint8_t*)buffptr);
          buffptr += sizeof(uint8_t);
        } else if (uintsize == 2) {
          value = *((uint16_t*)buffptr);
          buffptr += sizeof(uint16_t);
        } else if (uintsize == 4) {
          value = *((uint32_t*)buffptr);
          buffptr += sizeof(uint32_t);
        } else if (uintsize == 8) {
          value = *((uint64_t*)buffptr);
          buffptr += sizeof(uint64_t);
        } else {
          BOOST_THROW_EXCEPTION(std::runtime_error("Unsupported bvsize"));
          exit(1);
        }
        Node ni = NodeManager::currentNM()->mkNode(kind::SELECT, nd, NodeManager::currentNM()->mkConst(BitVector(nd.getType().getArrayIndexType().getBitVectorSize(), i)));
        crashModel[ni] = theory::bv::utils::mkConst(elementsize, value);
        if (arrayModel.find(nd) == arrayModel.end()){
          arrayModel[nd] = std::vector<uint64_t>();
        }
        arrayModel[nd].push_back(value);
        assert(arrayModel[nd][i] == value);
      }
    }
  }
}

void AUFBVCodeGenerator::dumpDeclarations(std::ostream& out) {
  // buffer pointer to be allocated by HonggFuzz
  applyIndent(out, 2);
  out << "size_t bufflen = size;" << std::endl;
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
    }
    else if (nd.getType().isArray()){
      size_t elementsize = nd.getType().getArrayConstituentType().getBitVectorSize();
      size_t arraysize = arraySizeMap[getAndStoreCorrectId(nd)];
      assert(arraysize >= 0);
      arraysize += 1;
      out << std::string(2, ' ') << bvSizeToCType(elementsize) << " " << getAndStoreCorrectId(nd) << "[" << arraysize << "]";
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

void AUFBVCodeGenerator::applyIndent(std::ostream& out, size_t indent) {
  out << std::string(indent, ' ');
}


void AUFBVCodeGenerator::dumpVarInputs(std::ostream& out) {
  dumpVarInputs_NoOpt(out);
  return;

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

void AUFBVCodeGenerator::dumpVarInputs_NoOpt(std::ostream& out) {

  applyIndent(out, 2);
  out << "uint8_t* buffptr = buff;\n" << std::endl;

  if (varlist.size() == 0) return;

  buffSize = 0;
  std::map<Node, Node> eqc;
  for (Node nd : varlist) {
    if (nd.getType().isInteger()) {
      applyIndent(out, 2);

      out << getAndStoreCorrectId(nd) << " = *((int*)buffptr);" << std::endl;
      applyIndent(out, 2);
      out << "buffptr += (sizeof(int) / sizeof(uint8_t));" << std::endl;
      buffSize += sizeof(int);
      modelVars.push_back(nd);

      out << std::endl;
    }
    else if (nd.getType().isBitVector()) {
      applyIndent(out, 2);

      size_t bvsize = nd.getType().getBitVectorSize();
      size_t uintsize = bvSize2byteSize(bvsize);
      out << getAndStoreCorrectId(nd) << " = *((" << bvSizeToCType(bvsize)
	  << "*) buffptr);" << std::endl;

      applyIndent(out, 2);
      out << "buffptr += " << uintsize << ";" << std::endl;

      buffSize += uintsize;
      modelVars.push_back(nd);
      out << std::endl;
    }
    else if (nd.getType().isArray()) {
      std::string aname = getAndStoreCorrectId(nd);
      uint32_t arraysize = arraySizeMap[aname];
      assert(arraysize >= 0);
      for (uint32_t i = 0; i <= arraysize; ++i){
        applyIndent(out, 2);
        size_t elementsize = nd.getType().getArrayConstituentType().getBitVectorSize();
        size_t uintsize = bvSize2byteSize(elementsize);
        out << aname << "[" << i << "] = *((" << bvSizeToCType(elementsize)
      << "*) buffptr);" << std::endl;
        applyIndent(out, 2);
        out << "buffptr += " << uintsize << ";" << std::endl;
        buffSize += uintsize;
      }
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

void AUFBVCodeGenerator::add_edge_recursive(Node const& node, Node const& parent) {
  if (reused.find(node) != reused.end()) {
    if (reused_node_graph.find(parent) == reused_node_graph.end()) {
      reused_node_graph[parent] = std::vector<Node>();
    }
    if (std::find(reused_node_graph[parent].begin(), reused_node_graph[parent].end(), node) == reused_node_graph[parent].end()){
      reused_node_graph[parent].push_back(node);
      for (unsigned int i = 0; i < node.getNumChildren(); ++i) {
        add_edge_recursive(node[i], node);
      }
    }
    else
      return;
  }
  else {
    for (unsigned int i = 0; i < node.getNumChildren(); ++i) {
      add_edge_recursive(node[i], parent);
    }
  }

}

void AUFBVCodeGenerator::build_graph(std::map<Node, std::string>& tempVarMap) {
  reused_node_graph.clear();
  for (auto it = tempVarMap.begin(); it != tempVarMap.end(); ++it) {
    Node n = it->first;
    assert(reused_node_graph.find(n) == reused_node_graph.end());
    reused_node_graph[n] = std::vector<Node>();
  }
  for (auto it = tempVarMap.begin(); it != tempVarMap.end(); ++it) {
    Node n = it->first;
    for (unsigned int i = 0; i < n.getNumChildren(); ++i) {
      add_edge_recursive(n[i], n);
    }
  }
}

void AUFBVCodeGenerator::reverse_topsort(){
  std::set<Node> visited;
  std::stack<Node> s;
  for (auto it = reused_node_graph.begin(); it != reused_node_graph.end(); ++it) {
    Node n = it->first;
    if (visited.find(n) == visited.end()) {
      visited.insert(n);
      s.push(n);
      while (!s.empty()) {
        Node v = s.top();
        bool all_visited = true;
        for (unsigned int i = 0; i < reused_node_graph[v].size(); ++i) {
          Node w = reused_node_graph[v][i];
          if (visited.find(w) == visited.end()) {
            visited.insert(w);
            s.push(w);
            all_visited = false;
          }
        }
        if (all_visited) {
          s.pop();
          reversed_topological_order.push_back(v);
        }
      }
    }
  }
}

void AUFBVCodeGenerator::dumpTempVars(std::ostream& out) {
  if (tempVarMap.size() == 0) return;
  applyIndent(out, 2);
  out << "// temp variable definitions" << std::endl;
  build_graph(tempVarMap);
  reversed_topological_order.clear();
  reverse_topsort();
  assert(reversed_topological_order.size() == tempVarMap.size());
  for (unsigned int i = 0; i < reversed_topological_order.size(); ++i) {
    applyIndent(out, 2);
    size_t bvsize = reversed_topological_order[i].getType().getBitVectorSize();
    size_t uintsize = bvSize2byteSize(bvsize);
    out << bvSizeToCType(bvsize) << " ";
    out << tempVarMap[reversed_topological_order[i]] << " = ";
    dumpExprRecursive(out, reversed_topological_order[i], false, true);
    out << ";" << std::endl;
  }
  out << std::endl;
}

std::string AUFBVCodeGenerator::newTempVarNext() {
  numTempVars += 1;
  return "__temp_" + std::to_string(numTempVars);
}

void AUFBVCodeGenerator::dumpHeaders(std::ostream& out) {
  // FIXME : add file check
  if (options::targetHeader() != "") {
    out << "#include \"" << options::targetHeader() << "\"" << std::endl;
  }
  out << "#include <limits.h>" << std::endl;
  out << "#include <math.h>" << std::endl;
  out << "#include <assert.h>" << std::endl;
  out << "#include <string.h>" << std::endl;
  out << "#include <stdint.h>" << std::endl;
}

void AUFBVCodeGenerator::visitExpr(Node const& node){
  if (cached.find(node) != cached.end()){
    if (node.getKind() == kind::CONST_RATIONAL or node.getKind() == kind::CONST_BITVECTOR or node.getKind() == kind::VARIABLE)
      return;
    reused.insert(node);
    return;
  }
  cached.insert(node);
  // update varlist
  if (node.getKind() == kind::VARIABLE){
    if (varlist.end() == varlist.find(node)) varlist.insert(node);
  }
  for(unsigned int i = 0; i < node.getNumChildren(); ++i){
    visitExpr(node[i]);
  }
  return;
}

void AUFBVCodeGenerator::checkReused(){
  cached.clear();
  reused.clear();
  auto thi = theoryPtr->facts_begin();
  auto the = theoryPtr->facts_end();
  for (; thi != the; ++thi){
    visitExpr(*thi);
  }
  for (auto n: reused){
    tempVarMap[n] = newTempVarNext();
  }
  return;
}

void AUFBVCodeGenerator::dumpExprRecursive(std::ostream& out, Node const& node, bool reverse /* false */, bool tempDump /* false */) {
  if (tempDump){
    assert(!reverse);
  }
  else {
    if (reused.find(node) != reused.end()){
      if (!reverse){
        out << tempVarMap[node];
      }
      else {
        out << "(!" << tempVarMap[node] << ")";
      }
      return;
    }
  }
  Node rwNode;
  Kind k = node.getKind();
  // orax
  if (k == kind::NOT){
    if (node[0].getKind() != kind::EQUAL){
      dumpExprRecursive(out, node[0], true);
      return;
    }
  }
  if (reverse){
    assert(k == kind::LT || k == kind::BITVECTOR_SLT || k == kind::BITVECTOR_ULT || k == kind::LEQ || k == kind::BITVECTOR_ULE || k == kind::BITVECTOR_SLE || k == kind::GT || k == kind::BITVECTOR_UGT || k == kind::BITVECTOR_SGT || k == kind::GEQ || k == kind::BITVECTOR_SGE || k == kind::BITVECTOR_UGE);
    if (k == kind::LT)
      k = kind::GEQ;
    else if (k == kind::LEQ)
      k = kind::GT;
    else if (k == kind::GT)
      k = kind::LEQ;
    else if (k == kind::GEQ)
      k = kind::LT;
    else if (k == kind::BITVECTOR_SLT)
      k = kind::BITVECTOR_SGE;
    else if (k == kind::BITVECTOR_SLE)
      k = kind::BITVECTOR_SGT;
    else if (k == kind::BITVECTOR_SGT)
      k = kind::BITVECTOR_SLE;
    else if (k == kind::BITVECTOR_SGE)
      k = kind::BITVECTOR_SLT;
    else if (k == kind::BITVECTOR_ULT)
      k = kind::BITVECTOR_UGE;
    else if (k == kind::BITVECTOR_ULE)
      k = kind::BITVECTOR_UGT;
    else if (k == kind::BITVECTOR_UGT)
      k = kind::BITVECTOR_ULE;
    else if (k == kind::BITVECTOR_UGE)
      k = kind::BITVECTOR_ULT;
  }
  // orax
  switch (k) {
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
      out << "(";
      dumpType(out, node);
      out << node.getConst<BitVector>().getValue() << ")";
      break;

    case kind::VARIABLE:
      if (varlist.end() == varlist.find(node)) varlist.insert(node);
      out << getAndStoreCorrectId(node);
      break;

    case kind::NOT:
      if (node[0].getKind() == kind::EQUAL){
        out << "fmax(0, UNEQUAL_GAP - ";
        out << "fabs(";
        out << "(double)";
        dumpExprRecursive(out, node[0][0]);
        out << " - ";
        out << "(double)";
        dumpExprRecursive(out, node[0][1]);
        out << ")";
        out << ")";
        break;
      }
      else
        Assert(false);

    case kind::EQUAL:
      out << "fabs(";
      out << "(double)";
      dumpExprRecursive(out, node[0]);
      out << " - ";
      out << "(double)";
      dumpExprRecursive(out, node[1]);
      out << ")";
      break;

    case kind::BITVECTOR_MULT:
      dumpType(out, node);
    case kind::OR:
    case kind::AND:
    case kind::MULT:
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
        AUFBVCodeGenerator::dumpExprRecursive(out, node[cid]);
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
      out << "(double)";
      dumpExprRecursive(out, node[0]);
      out << " - ";
      out << "(double)";
      dumpExprRecursive(out, node[1]);
      out << " + EPSILON";
      out << ")";
      break;

    case kind::LEQ:
    case kind::BITVECTOR_ULE:
    case kind::BITVECTOR_SLE:
      out << "fmax(0,";
      out << "(double)";
      dumpExprRecursive(out, node[0]);
      out << " - ";
      out << "(double)";
      dumpExprRecursive(out, node[1]);
      out << ")";
      break;

    case kind::GT:
    case kind::BITVECTOR_UGT:
    case kind::BITVECTOR_SGT:
      out << "fmax(0,";
      out << "(double)";
      dumpExprRecursive(out, node[1]);
      out << " - ";
      out << "(double)";
      dumpExprRecursive(out, node[0]);
      out << " + EPSILON";
      out << ")";
      break;

    case kind::GEQ:
    case kind::BITVECTOR_SGE:
    case kind::BITVECTOR_UGE:
      out << "fmax(0,";
      out << "(double)";
      dumpExprRecursive(out, node[1]);
      out << " - ";
      out << "(double)";
      dumpExprRecursive(out, node[0]);
      out << ")";
      break;

    case kind::MINUS:
    case kind::DIVISION:
      assert(node.getNumChildren() == 2);
      out << "(";
      dumpExprRecursive(out, node[0]);
      out << " " << getSymbol(node.getKind()) << " ";
      dumpExprRecursive(out, node[1]);
      out << ")";
      break;
    case kind::BITVECTOR_PLUS:
      dumpType(out, node);
    case kind::PLUS:
      out << "(";
        for (size_t it = 0; it < node.getNumChildren(); ++it) {
          dumpExprRecursive(out, node[it]);
          if (it < node.getNumChildren() - 1)
            out << " " << getSymbol(node.getKind()) << " ";
        }
      out << ")";
      break;

    case kind::BITVECTOR_SIGN_EXTEND:
      dumpExprRecursive(out, node[0]);
      break;

    case kind::BITVECTOR_EXTRACT: {
      // TODO: apply node re-write rules to optimize the expression further
      // orax
      assert(node.getNumChildren()==1);
      // FIXME: maybe buggy
      unsigned int high = theory::bv::utils::getExtractHigh(node);
      unsigned int low = theory::bv::utils::getExtractLow(node);
      std::string mask = "0b";
      for (unsigned int i = low; i <= high; i++)
        mask += "1";
      out << "(";
      if (low == 0){
        dumpExprRecursive(out, node[0]);
        out << " & " << mask;
      }
      else {
        out << "(";
        dumpExprRecursive(out, node[0]);
        out << " >> " << low << ") & " << mask;
      }
      out << ")";
      break;
    }

    case kind::BITVECTOR_CONCAT: {
      if (concatIsLSHR(node)){
        unsigned int high = theory::bv::utils::getExtractHigh(node[1]);
        unsigned int low = theory::bv::utils::getExtractLow(node[1]);
        assert(node[1].getNumChildren() == 1);
        out << "(";
        dumpExprRecursive(out, node[1][0]);
        out << " >> ";
        out << low;
        out << ")";
        break;
      }
      if (node.getNumChildren() == 2) {
	      handleBvConcat2(out, node);
      }
      else {
	      handleBvConcat(out, node);
      }
      break;
    }

    case kind::SELECT: {
      assert(node.getNumChildren() == 2);
      dumpExprRecursive(out, node[0]);
      out << "[";
      uint32_t ni = node[1].getConst<BitVector>().getValue().toUnsignedInt();
      std::string aname = getAndStoreCorrectId(node[0]);
      if (arraySizeMap.find(aname) == arraySizeMap.end())
        arraySizeMap[aname] = ni;
      else {
        if (arraySizeMap[aname] < ni)
          arraySizeMap[aname] = ni;
      }
      out << ni;
      out << "]";
      break;
    }

    case kind::BITVECTOR_XOR: {
      assert(node.getNumChildren() == 2);
      out << "(";
      dumpExprRecursive(out, node[0]);
      out << "^";
      dumpExprRecursive(out, node[1]);
      out << ")";
      break;
    }

    case kind::BITVECTOR_OR: {
      assert(node.getNumChildren() == 2);
      out << "(";
      dumpExprRecursive(out, node[0]);
      out << "|";
      dumpExprRecursive(out, node[1]);
      out << ")";
      break;
    }

    case kind::BITVECTOR_AND: {
      assert(node.getNumChildren() == 2);
      out << "(";
      dumpExprRecursive(out, node[0]);
      out << "&";
      dumpExprRecursive(out, node[1]);
      out << ")";
      break;
    }

    default:
      BOOST_THROW_EXCEPTION(std::runtime_error(
          "Codegeneration for " + kind::kindToString(node.getKind()) +
          " NOT SUPPORTED"));
      exit(1);
      break;
  }
}

void AUFBVCodeGenerator::dumpType(std::ostream& out, Node const& node){
  TypeNode type = node.getType();
  out << "(";
  if (type.isInteger()){
    out << "int";
  }
  else if (type.isBitVector()){
    out << bvSizeToCType(type.getBitVectorSize());
  }
  else {
    BOOST_THROW_EXCEPTION(std::runtime_error(type.getName() +
          " NOT SUPPORTED"));
    exit(1);
  }
  out << ")";
}

std::string AUFBVCodeGenerator::getNodeName(Node const& node) const {
  std::ostringstream oss;
  node.toStream(oss);
  return oss.str();
}

/*
 *  Taken from geeksforgeeks :
 *  https://www.geeksforgeeks.org/check-whether-the-given-string-is-a-valid-identifier/
 */
bool AUFBVCodeGenerator::isValidIdName(std::string str) const {
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

std::string AUFBVCodeGenerator::getAndStoreCorrectId(Node const& node) {
  std::string nodeIdName = getNodeName(node);
  if (isValidIdName(nodeIdName)) return nodeIdName;

  if (idCorrections.find(nodeIdName) == idCorrections.end())
    idCorrections[nodeIdName] = newTempVarNext();

  return idCorrections[nodeIdName];
}

std::string AUFBVCodeGenerator::getSymbol(kind::Kind_t ktype) {
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

    case kind::BITVECTOR_XOR:
      return "^";
      break;

    default:
      BOOST_THROW_EXCEPTION(std::runtime_error(
          "Codegeneration for " + std::string(kind::toString(ktype)) +
          " NOT SUPPORTED"));
      exit(1);
      break;
  }
}

Node AUFBVCodeGenerator::rewriteBVBitManipOps(Node const& node) {
  if (theory::bv::RewriteRule<theory::bv::ExtractArith>::applies(node))
    return theory::bv::RewriteRule<theory::bv::ExtractArith>::run<false>(node);

  else if (theory::bv::RewriteRule<theory::bv::ExtractArith2>::applies(node)) {
    // lets throw an error for this now
    std::cerr << "ABORTING : only support extract of type [[e]](i : 0)"
              << std::endl;
    // orax
    node.printAst(std::cerr, 0);
    exit(EXIT_FAILURE);
  }

  if (theory::bv::RewriteRule<theory::bv::EvalExtract>::applies(node))
    return theory::bv::RewriteRule<theory::bv::EvalExtract>::run<false>(node);

  return node;
}

void AUFBVCodeGenerator::handleBvConcat2(std::ostream& out, Node const& nd) {
  size_t bvsize0 = nd[0].getType().getBitVectorSize();
  size_t bvsize1 = nd[1].getType().getBitVectorSize();

  Assert (bvsize1 + bvsize0 <= sizeof(size_t) * 8);
  // TODO: remove the const
  out << "((";
  dumpExprRecursive(out, nd[0]);
  out << " << " << bvsize1 << ") | ";
  dumpExprRecursive(out, nd[1]);
  out << ")";
}

bool AUFBVCodeGenerator::concatIsLSHR(Node const& nd){
  if (nd.getNumChildren() != 2) return false;
  if (nd[0].getKind() == kind::CONST_BITVECTOR || nd[1].getKind() == kind::BITVECTOR_EXTRACT) {
      unsigned long value = nd[0].getConst<BitVector>().getValue().getUnsignedLong();
      if (value == 0) return true;
  }
  return false;
}

void AUFBVCodeGenerator::handleBvConcat(std::ostream& out, Node const& nd) {
  size_t numn = nd.getNumChildren();
  assert (numn > 2);
  std::vector<size_t> size_vector;
  size_t size_sum = 0;
  size_t offset = 0;
  for (size_t i = 0; i < numn; ++i){
    size_t bv_size = nd[0].getType().getBitVectorSize();
    size_sum += bv_size;
    size_vector.push_back(bv_size);
  }
  offset = size_sum;
  Assert (size_sum <= sizeof(size_t) * 8);
  out << "(";
  for (size_t i = 0; i + 1 < numn; ++i){
    offset -= size_vector[i];
    out << "(";
    dumpExprRecursive(out, nd[i]);
    out << " << " << offset;
    out << ") | ";
  }
  dumpExprRecursive(out, nd[numn - 1]);
  out << ")";
}

static std::set<Node> external_visited;
bool AUFBVCodeGenerator::hasExternalRecursive(Node const& nd){
  if (external_visited.find(nd) != external_visited.end())
    return false;
  external_visited.insert(nd);
  std::string name = getNodeName(nd);
  // std::unordered_set<std::string> efunc = {"foo"};
  size_t numn = nd.getNumChildren();
  if (name.find("isalpha") != std::string::npos){
    return true;
  }
  if (name.find("foo") != std::string::npos){
    return true;
  }
  if (nd.getKind() == kind::VARIABLE) {
    assert(numn == 0);
  }
  for (size_t i = 0; i < numn; ++i){
    if (hasExternalRecursive(nd[i]))
      return true;
  }
  return false;
}
bool AUFBVCodeGenerator::hasExternal(){
  external_visited.clear();
  auto thi = theoryPtr->facts_begin();
  auto the = theoryPtr->facts_end();
  for (;thi != the;++thi) {
    Node tnode = Node(*thi);
    if (hasExternalRecursive(tnode))
      return true;
  }
  return false;
}

}  // namespace cgen
}  // namespace cvc5
