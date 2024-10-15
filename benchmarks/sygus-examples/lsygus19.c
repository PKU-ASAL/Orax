#include "lsygus19.h"



/* int ex (int x, int y) { */
/*   if ((! ( x >= 5)) && (! ( ( 2 * x) == (-16 - 3 * y)))) return 1 + (3 * x); */
/*   else return (17 + (5 * x) + (3 * y)); */
/* } */


uint32_t f1 (uint32_t p1, uint32_t P1) { return P1 - 1; }
uint32_t f2 (uint32_t p1, uint32_t P1) { return 2*P1 - 2; }
uint32_t f3 (uint32_t p1, uint32_t P1) { return 3*P1 - 3; }
uint32_t f4 (uint32_t p1, uint32_t P1) { return 4*P1 - 4; }
uint32_t f5 (uint32_t p1, uint32_t P1) { return 5*P1 - 5; }
uint32_t g1 (uint32_t p1, uint32_t P1) { return (uint32_t) -1; }
uint32_t g2 (uint32_t p1, uint32_t P1) { return 0; }



uint32_t fg_array_search_4 (uint32_t y1, uint32_t y2, uint32_t y3, uint32_t y4, uint32_t k1) {

    uint32_t _let_1 = -k1;
    uint32_t _let_2 = y2 + _let_1;
    uint32_t _let_3 = (_let_2 >= 1);
    uint32_t _let_4 = (y1 + _let_1); 
    uint32_t _let_5 = (_let_4 >= 0);
    uint32_t _let_6 = (_let_5 || (! _let_3));
    uint32_t _let_7 = (y4 + _let_1);
    uint32_t _let_8 = (_let_7 >= 1);
    uint32_t _let_9 = (y3 + _let_1);
    uint32_t _let_10 = (_let_9 >= 0);
    uint32_t _let_11 = (_let_10 || (! _let_8));
    uint32_t _let_12 = (_let_9 >= 1);
    uint32_t _let_13 = (_let_2 >= 0);
    uint32_t _let_14 = (_let_13 || (! _let_12));
    uint32_t _let_15 = (!(_let_4 >= 1));
    uint32_t _let_16 = (_let_7 >= 0);

    
    if ((! (( y1 - y2) >= 0)) &&
        (! ((y2 - y3) >= 0)) &&
        (! ((y3 - y4) >= 0) &&
        ((! _let_16) || ((! _let_5) && _let_3) || ((! _let_13) && _let_12) || ((! _let_10) && _let_8))
	 )) {
     if (_let_16 && _let_15 && _let_14 && _let_11)  return 1;
         else {
            if (_let_16 && _let_15 && _let_14 && _let_11 && _let_6) return (-1);
            else {
                if (_let_16 && _let_15 && _let_11 && _let_6) return 2;
                else {
                    if (_let_15 && _let_14 && _let_11 && _let_6) return 4; else return 3;
                }
            }
        }    
    }
    else return 0;
}

uint32_t fg_array_sum_2_15(uint32_t y1, uint32_t y2) {
  uint32_t _let_1 = y1 + y2;
  if (_let_1 >= 16 && (y1 != -y2)) return _let_1;
  else return 0;
}

uint32_t findSum4 (uint32_t y1, uint32_t y2, uint32_t y3, uint32_t y4) {
  if (y1 + y2 > 5) return y1 + y2;
  else {
    if (y2 + y3 > 5) return y2 + y3;
    else {
      if (y3 + y4) return y3 + y4;
      else return 0;
    }
  }
}

uint32_t f_jmbl_fg_VC22_a(uint32_t x1, uint32_t x2) {
  if (x1 == x2) return 0;
  else return 1;
}

uint32_t InV1 (uint32_t v, uint32_t V_min, uint32_t V_mux_) {
  if (v >= V_min)
    if (v <= V_mux_)
      return 1;

  return 0;
}


uint32_t InV2 (uint32_t v1, uint32_t v2, uint32_t V_min, uint32_t V_mux_) {
  if (v1 >= V_min)
    if (v1 <= V_mux_)
      if (v2 >= V_min)
	if (v2 <= V_mux_)
	  return 1;

  return 0;
}


uint32_t UnsafeSame(uint32_t x1, uint32_t x2, uint32_t v1, uint32_t v2) {
  uint32_t t0 = x1 + v1;
  uint32_t t1 = x2 + v2;

  uint32_t t2 = (x1 >= x2) && (t1 >= t0);
  uint32_t t3 = (x2 >= x1) && (t1 >= t0);

  return t2 || t3;
}


uint32_t ex(uint32_t x, uint32_t y) {
  if ((x < 5) && ((2 * x) != ((-3 * y) - 16 ))) {
    return 3 * x + 1;
  }
  else
    return 17 + 5 * x + 3 * y;
}

int32_t ex_fg_mpg_example1 (int32_t x, int32_t y) {
  if ((x < 5) && (2 * x != y * (-3) - 16))
    return 3*x - 1;
  else
    return 5 *x + 3 * y + 17;
}

uint32_t LinExpr1_eq1ex(uint32_t x, uint32_t y, uint32_t z) {
  if ((y + 1) == x) return z;
  else return x;
}
