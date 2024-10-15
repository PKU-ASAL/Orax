#include "isxdigit.h"

uint32_t isxdigit_(uint32_t c)
{
  if (c >= '0') {
    if (c <= '9') {
      return 1;
    }
  }

  if (c >= 'A')
    if (c <= 'F')
      return 1;

  if (c >= 'a')
    if (c <= 'f')
      return 1;

  return 0;
}
