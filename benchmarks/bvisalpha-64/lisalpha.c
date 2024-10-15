#include "lisalpha.h"

uint64_t isalpha_(uint64_t c) {
  if (c >= 'a' && c <= 'z') return 1;
  else if (c >= 'A' && c <= 'Z') return 1;
  return 0;
}
