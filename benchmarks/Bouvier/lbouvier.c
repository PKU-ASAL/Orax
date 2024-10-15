#include "lbouvier.h"

uint16_t u_vlsat3_d57(uint8_t x0) {

  uint16_t a1, a2, a3, a4;

  if (x0 == 4) {
    a1 = 8;
  } else {
    if (x0 == 10) {
      a1 = 128;
    } else {
      if (x0 == 22) a1 = 32;
      else a1 = 8;
    }
  }

  if (x0 == 17) a2 = 16;
  else {
    if (x0 == 3) a2 = 4;
    else {
      if (x0 == 14) a2 = 512;
      else a2 = a1;
    }
  }

  if (x0 == 7) a3 = 64;
  else {
    if (x0 == 9) a3 = 128;
    else {
      if (x0 == 18) a3 = 4;
      else a3 = a2;
    }
  }

  if (x0 == 1) a4 = 1;
  else {
    if (x0 == 11 || x0 == 12) a4 = 128;
    else a4 = a3;
  }
  

  if ( x0 == 19 || x0 == 20) return 256;
  else {
    if (x0 == 16) return 8;
    else {
      if (x0 == 2) return 2;
      else return a4;
    }
  }
}


uint32_t u_vlsat3_j02(uint8_t x0) {

  uint32_t a1, a2, a3, a4;

  if (x0 == 4) {
    a1 = 8;
  } else {
    if (x0 == 10) {
      a1 = 128;
    } else {
      if (x0 == 22) a1 = 32;
      else a1 = 8;
    }
  }

  if (x0 == 17) a2 = 16;
  else {
    if (x0 == 3) a2 = 4;
    else {
      if (x0 == 14) a2 = 512;
      else a2 = a1;
    }
  }

  if (x0 == 7) a3 = 64;
  else {
    if (x0 == 9) a3 = 128;
    else {
      if (x0 == 18) a3 = 4;
      else a3 = a2;
    }
  }

  if (x0 == 1) a4 = 1;
  else {
    if (x0 == 11 || x0 == 12) a4 = 128;
    else a4 = a3;
  }
  

  if ( x0 == 19 || x0 == 20) return 256;
  else {
    if (x0 == 16) return 8;
    else {
      if (x0 == 2) return 2;
      else return a4;
    }
  }
}
