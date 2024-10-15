
#include "cbf_tolower.h"

uint32_t cbf_tolower(uint32_t c)
{
  if (c >= 'A' && c <= 'Z')
    c += 32;

  return (c);
}
