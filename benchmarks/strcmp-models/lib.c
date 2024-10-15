#include "lib.h"

uint32_t strcmp_int (uint32_t a, uint32_t b, uint32_t c, uint32_t d,
		     uint32_t p, uint32_t q, uint32_t r, uint32_t s)
{

  uint32_t count = 0;

  if (a == p) ++count;
  if (b == q) ++count;
  if (c == r) ++count;
  if (d == s) ++count;

  return count;
}
