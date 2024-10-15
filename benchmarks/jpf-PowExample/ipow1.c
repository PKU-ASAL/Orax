
#include "ipow.h"

int64_t ipow2(int64_t exp) {
  return 1 << exp;
}

int64_t ipow(int64_t base, uint8_t exp) {
  uint8_t highest_bit_set[256];
  highest_bit_set[0] = 0;
  highest_bit_set[1] = 1;
  highest_bit_set[2] = 2;
  highest_bit_set[3] = 2;
  uint8_t i = 4;
  uint8_t v = 3;
  uint8_t cnt = 4;
  for (int j = 0; j < cnt; j++) {
    highest_bit_set[i + j] = v;
    i++;
  }
  v = 4;
  cnt = 8;
  for (int j = 0; j < cnt; j++) {
    highest_bit_set[i + j] = v;
    i++;
  }
  v = 5;
  cnt = 16;
  for (int j = 0; j < cnt; j++) {
    highest_bit_set[i + j] = v;
    i++;
  }
  v = 6;
  cnt = 31;
  for (int j = 0; j < cnt; j++) {
    highest_bit_set[i + j] = v;
    i++;
  }
  v = 255;
  cnt = 256 - 63;
  for (int j = 0; j < cnt; j++) {
    highest_bit_set[i + j] = v;
    i++;
  }
  // {
  //   0, 1, 2, 2, 3, 3, 3, 3,
  //   4, 4, 4, 4, 4, 4, 4, 4,
  //   5, 5, 5, 5, 5, 5, 5, 5,
  //   5, 5, 5, 5, 5, 5, 5, 5,
  //   6, 6, 6, 6, 6, 6, 6, 6,
  //   6, 6, 6, 6, 6, 6, 6, 6,
  //   6, 6, 6, 6, 6, 6, 6, 6,
  //   6, 6, 6, 6, 6, 6, 6, 255, // anything past 63 is a guaranteed overflow with base > 1
  //   255, 255, 255, 255, 255, 255, 255, 255,
  //   255, 255, 255, 255, 255, 255, 255, 255,
  //   255, 255, 255, 255, 255, 255, 255, 255,
  //   255, 255, 255, 255, 255, 255, 255, 255,
  //   255, 255, 255, 255, 255, 255, 255, 255,
  //   255, 255, 255, 255, 255, 255, 255, 255,
  //   255, 255, 255, 255, 255, 255, 255, 255,
  //   255, 255, 255, 255, 255, 255, 255, 255,
  //   255, 255, 255, 255, 255, 255, 255, 255,
  //   255, 255, 255, 255, 255, 255, 255, 255,
  //   255, 255, 255, 255, 255, 255, 255, 255,
  //   255, 255, 255, 255, 255, 255, 255, 255,
  //   255, 255, 255, 255, 255, 255, 255, 255,
  //   255, 255, 255, 255, 255, 255, 255, 255,
  //   255, 255, 255, 255, 255, 255, 255, 255,
  //   255, 255, 255, 255, 255, 255, 255, 255,
  //   255, 255, 255, 255, 255, 255, 255, 255,
  //   255, 255, 255, 255, 255, 255, 255, 255,
  //   255, 255, 255, 255, 255, 255, 255, 255,
  //   255, 255, 255, 255, 255, 255, 255, 255,
  //   255, 255, 255, 255, 255, 255, 255, 255,
  //   255, 255, 255, 255, 255, 255, 255, 255,
  //   255, 255, 255, 255, 255, 255, 255, 255,
  //   255, 255, 255, 255, 255, 255, 255, 255,
  // };

  int64_t result = 1;

  switch (highest_bit_set[exp]) {
  case 255: // we use 255 as an overflow marker and return 0 on overflow/underflow
    if (base == 1) {
      return 1;
    }

    if (base == -1) {
      return 1 - 2 * (exp & 1);
    }

    return 0;
  case 6:
    if (exp & 1) result *= base;
    exp >>= 1;
    base *= base;
  case 5:
    if (exp & 1) result *= base;
    exp >>= 1;
    base *= base;
  case 4:
    if (exp & 1) result *= base;
    exp >>= 1;
    base *= base;
  case 3:
    if (exp & 1) result *= base;
    exp >>= 1;
    base *= base;
  case 2:
    if (exp & 1) result *= base;
    exp >>= 1;
    base *= base;
  case 1:
    if (exp & 1) result *= base;
  default:
    return result;
  }
}
