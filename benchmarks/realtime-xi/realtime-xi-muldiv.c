#include "realtime-xi-muldiv.h"

uint32_t ite_int(uint32_t p, uint32_t a , uint32_t b) {
  if (p) return a;
  else return b;
}

uint32_t bvmul_int(uint32_t a, uint32_t b) {
  return a * b;
}

uint32_t bvdiv_int(uint32_t a, uint32_t b) {
  if (b == 0) return 0;
  return a / b;
}

uint32_t bvudiv_int(uint32_t a, uint32_t b) {
  if (b == 0 ) return 0;
  return a / b;
}


uint32_t in_natural_bv32(uint32_t x) {
  if (x >= 0)
    if ( x <= 127)
      return 1;

  return 0;
}

uint32_t get_hword(uint32_t x) {
  return x << 8;
}

uint32_t get_lword(uint32_t x) {
  return x & 0x000000FF;
}

uint32_t bvudaddo_64 (uint32_t a, uint32_t b) {
  uint32_t result = a + b;
  uint32_t bit16 = (result >> 15) & 1;
  return bit16 == 1;
}

uint32_t bvshl_int(uint32_t x, uint32_t y) {
  return x << y;
}

uint32_t bvshr_int(uint32_t x, uint32_t y) {
  return x >> y;
}

uint32_t bvlshr_int(uint32_t x, uint32_t y) {
  return 1;
}

uint32_t bvurem_int(uint32_t x, uint32_t m) {
  if (m == 0) return 0;
  return x % m;
}

