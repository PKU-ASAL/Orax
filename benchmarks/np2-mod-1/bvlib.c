#include "bvlib.h"

uint32_t cbf_bvrem(uint32_t x, uint32_t m) {
  if (m == 0) return 0;
  return x % m;
}
uint32_t cbf_bvadd(uint32_t x, uint32_t y) {
  return x + y;
}
