
#include "cbf_tolower.h"

uint16_t cbf_tolower(uint16_t c)
{
  if (c >= 'A' && c <= 'Z')
    c += 32;

  return (c);
}
