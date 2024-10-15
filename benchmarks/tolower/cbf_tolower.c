
#include "cbf_tolower.h"

uint8_t cbf_tolower(uint8_t c)
{
  if (c >= 'A' && c <= 'Z')
    c += 32;

  return (c);
}
