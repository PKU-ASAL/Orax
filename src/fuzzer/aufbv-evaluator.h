#ifndef __AUFBV_EVALUATOR__
#define __AUFBV_EVALUATOR__
#include <memory>
#include <vector>

namespace cvc5 {
namespace cgen {
float bv2float(uint64_t bv);
double bv2double(uint64_t bv);
uint64_t float2bv(float f);
uint64_t double2bv(double d);
uint64_t evaluateExFunc(void* func, std::vector<unsigned int> widthVector, std::vector<bool> isFloatVector, std::vector<uint64_t> args);
} // end namespace cgen
} // end namespace cvc5

#endif