#include "lib.h"

uint64_t strcmp_int (uint64_t a, uint64_t b, uint64_t c, uint64_t d,
		     uint64_t p, uint64_t q, uint64_t r, uint64_t s)
{

  uint64_t count = 0;

  if (a == p) ++count;
  if (b == q) ++count;
  if (c == r) ++count;
  if (d == s) ++count;

  return count;
}
