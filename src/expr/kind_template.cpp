/*********************                                                        */
/*! \file kind_template.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli, Christopher L. Conway, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include <sstream>

#include "expr/kind.h"
// orax
#include "fuzzer/aufbv-jitgen.h"

namespace cvc5 {
namespace kind {

const char* toString(cvc5::Kind k)
{
  using namespace cvc5::kind;

  switch (k)
  {
    /* special cases */
    case UNDEFINED_KIND: return "UNDEFINED_KIND";
    case NULL_EXPR: return "NULL";
    ${kind_printers}
    case LAST_KIND: return "LAST_KIND";
    default: return "?";
  }
}

std::ostream& operator<<(std::ostream& out, cvc5::Kind k)
{
  out << toString(k);
  return out;
}

/** Returns true if the given kind is associative. This is used by ExprManager to
 * decide whether it's safe to modify big expressions by changing the grouping of
 * the arguments. */
/* TODO: This could be generated. */
bool isAssociative(::cvc5::Kind k)
{
  switch(k) {
  case kind::AND:
  case kind::OR:
  case kind::MULT:
  case kind::PLUS:
    return true;

  default:
    return false;
  }
}

std::string kindToString(::cvc5::Kind k)
{
  std::stringstream ss;
  ss << k;
  return ss.str();
}

}  // namespace kind

std::ostream& operator<<(std::ostream& out, TypeConstant typeConstant) {
  switch(typeConstant) {
${type_constant_descriptions}
  default:
    out << "UNKNOWN_TYPE_CONSTANT";
    break;
  }
  return out;
}

namespace theory {

std::set<cvc5::Kind> MergedKinds = {
  kind::APPLY_UF,
  kind::CONST_FLOATINGPOINT, kind::CONST_ROUNDINGMODE, kind::FLOATINGPOINT_TYPE, kind::FLOATINGPOINT_FP, kind::FLOATINGPOINT_EQ, kind::FLOATINGPOINT_ABS, kind::FLOATINGPOINT_NEG, kind::FLOATINGPOINT_PLUS, kind::FLOATINGPOINT_SUB, kind::FLOATINGPOINT_MULT, kind::FLOATINGPOINT_DIV, kind::FLOATINGPOINT_FMA, kind::FLOATINGPOINT_SQRT, kind::FLOATINGPOINT_REM, kind::FLOATINGPOINT_RTI, kind::FLOATINGPOINT_MIN, kind::FLOATINGPOINT_MAX, kind::FLOATINGPOINT_MIN_TOTAL, kind::FLOATINGPOINT_MAX_TOTAL, kind::FLOATINGPOINT_LEQ, kind::FLOATINGPOINT_LT, kind::FLOATINGPOINT_GEQ, kind::FLOATINGPOINT_GT, kind::FLOATINGPOINT_ISN, kind::FLOATINGPOINT_ISSN, kind::FLOATINGPOINT_ISZ, kind::FLOATINGPOINT_ISINF, kind::FLOATINGPOINT_ISNAN, kind::FLOATINGPOINT_ISNEG, kind::FLOATINGPOINT_ISPOS, kind::FLOATINGPOINT_TO_FP_IEEE_BITVECTOR_OP, kind::FLOATINGPOINT_TO_FP_IEEE_BITVECTOR, kind::FLOATINGPOINT_TO_FP_FLOATINGPOINT_OP, kind::FLOATINGPOINT_TO_FP_FLOATINGPOINT, kind::FLOATINGPOINT_TO_FP_REAL_OP, kind::FLOATINGPOINT_TO_FP_REAL, kind::FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR_OP, kind::FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR, kind::FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR_OP, kind::FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR, kind::FLOATINGPOINT_TO_FP_GENERIC_OP, kind::FLOATINGPOINT_TO_FP_GENERIC, kind::FLOATINGPOINT_TO_UBV_OP, kind::FLOATINGPOINT_TO_UBV, kind::FLOATINGPOINT_TO_UBV_TOTAL_OP, kind::FLOATINGPOINT_TO_UBV_TOTAL, kind::FLOATINGPOINT_TO_SBV_OP, kind::FLOATINGPOINT_TO_SBV, kind::FLOATINGPOINT_TO_SBV_TOTAL_OP, kind::FLOATINGPOINT_TO_SBV_TOTAL, kind::FLOATINGPOINT_TO_REAL, kind::FLOATINGPOINT_TO_REAL_TOTAL, kind::FLOATINGPOINT_COMPONENT_NAN, kind::FLOATINGPOINT_COMPONENT_INF, kind::FLOATINGPOINT_COMPONENT_ZERO, kind::FLOATINGPOINT_COMPONENT_SIGN, kind::FLOATINGPOINT_COMPONENT_EXPONENT, kind::FLOATINGPOINT_COMPONENT_SIGNIFICAND, kind::ROUNDINGMODE_BITBLAST
};

bool isMergedKind(::cvc5::Kind k){
  return MergedKinds.find(k) != MergedKinds.end();
}

TheoryId kindToTheoryId(::cvc5::Kind k)
{
  // orax
  if (cvc5::FPMergedInBV){
    if (MergedKinds.find(k) != MergedKinds.end()){
      return THEORY_BV;
    }
  }

  switch(k) {
  case kind::UNDEFINED_KIND:
  case kind::NULL_EXPR:
    break;
${kind_to_theory_id}
  case kind::LAST_KIND:
    break;
  }
  throw IllegalArgumentException("", "k", __PRETTY_FUNCTION__, "bad kind");
}

TheoryId typeConstantToTheoryId(::cvc5::TypeConstant typeConstant)
{
  // orax
  if (cvc5::FPMergedInBV){
    switch (typeConstant)
    {
    case ROUNDINGMODE_TYPE:
      return THEORY_BV;
    default:
      break;
    }
  }

  switch (typeConstant)
  {
${type_constant_to_theory_id}
    case LAST_TYPE: break;
  }
  throw IllegalArgumentException(
      "", "k", __PRETTY_FUNCTION__, "bad type constant");
}

}  // namespace theory
}  // namespace cvc5
