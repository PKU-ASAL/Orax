
#include "lstrmodels.h"

uint32_t numvowels_str6 (uint32_t s0, uint32_t s1, uint32_t s2, uint32_t s3, uint32_t s4, uint32_t s5)
{
  uint32_t vcount;
  uint32_t s[] = {s0, s1, s2, s3, s4, s5};
  uint32_t *cptr = NULL;

  vcount = 0;

  for (cptr = s; *cptr != '\0'; cptr++)
    switch (*cptr)
    {
      case 'A':  case 'E':  case 'I':  case 'O':  case 'U':  
	vcount++; break;
    }
  
  return (vcount);
}

uint32_t numvowels_str3 (uint32_t s0, uint32_t s1, uint32_t s2)
{
  uint32_t vcount;
  uint32_t s[] = {s0, s1, s2};
  uint32_t cptr;

  vcount = 0;

  for (cptr = 0; cptr < 4; cptr++)
    switch (s[cptr])
    {
      case 'A':  case 'E':  case 'I':  case 'O':  case 'U':  
	vcount++; break;
    }
  
  return (vcount);
}


uint32_t numvowels_str4 (uint32_t s0, uint32_t s1, uint32_t s2, uint32_t s3)
{
  uint32_t vcount = 0;
  
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
