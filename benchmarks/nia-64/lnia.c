#include "lnia.h"

uint64_t _mul(uint64_t a, uint64_t b) {
  return a * b;
}

uint64_t _mod(uint64_t a, uint64_t b) { return a % b; }

// (declare-fun pow2 (Int) Int)
uint64_t pow2 (uint64_t x) {
  return 1 << x;
}

uint64_t intxor3 (uint64_t a, uint64_t b, uint64_t c) { return b ^ c; }

uint64_t intand (uint64_t k, uint64_t b, uint64_t c) { return b && c; }
uint64_t intor (uint64_t k, uint64_t b, uint64_t c) { return c || b; }

uint64_t intmodtotal(uint64_t k, uint64_t a, uint64_t b) {
  if (b == 0) return a;
  else return a % b;
}

uint64_t in_range(uint64_t k, uint64_t x) {
  if (x >= 0 && x <= (1 << k))
    return 1;

  return 0;
}

uint64_t _lt(uint64_t a, uint64_t b) {
  if (a < b) return 1;
  else return 0;
}

uint64_t ite_zero (uint64_t x, uint64_t y, uint64_t z) {
  if (x == 0) return y;
  else return z;
}

