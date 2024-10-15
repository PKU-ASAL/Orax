
#include "lstrmodels.h"

uint8_t numvowels_str6 (uint8_t s0, uint8_t s1, uint8_t s2, uint8_t s3, uint8_t s4, uint8_t s5)
{
  uint8_t vcount;
  uint8_t s[] = {s0, s1, s2, s3, s4, s5};
  uint8_t *cptr = NULL;

  vcount = 0;

  for (cptr = s; *cptr != '\0'; cptr++)
    switch (*cptr)
    {
      case 'A':  case 'E':  case 'I':  case 'O':  case 'U':  
	vcount++; break;
    }
  
  return (vcount);
}

uint8_t numvowels_str3 (uint8_t s0, uint8_t s1, uint8_t s2)
{
  uint8_t vcount;
  uint8_t s[] = {s0, s1, s2};
  uint8_t cptr;

  vcount = 0;

  for (cptr = 0; cptr < 4; cptr++)
    switch (s[cptr])
    {
      case 'A':  case 'E':  case 'I':  case 'O':  case 'U':  
	vcount++; break;
    }
  
  return (vcount);
}


uint8_t numvowels_str4 (uint8_t s0, uint8_t s1, uint8_t s2, uint8_t s3)
{
  uint8_t vcount = 0;
  
  switch (s0)
    {
    case 'A':  case 'E':  case 'I':  case 'O':  case 'U':  
      vcount++; break;
    }

  switch (s1)
    {
    case 'A':  case 'E':  case 'I':  case 'O':  case 'U':  
      vcount++; break;
    }
      
  switch (s2)
    {
    case 'A':  case 'E':  case 'I':  case 'O':  case 'U':  
	vcount++; break;
    }

  switch (s3)
    {
    case 'A':  case 'E':  case 'I':  case 'O':  case 'U':  
      vcount++; break;
    }

  
  return (vcount);
}
