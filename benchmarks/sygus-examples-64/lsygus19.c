#include "lsygus19.h"



/* int ex (int x, int y) { */
/*   if ((! ( x >= 5)) && (! ( ( 2 * x) == (-16 - 3 * y)))) return 1 + (3 * x); */
/*   else return (17 + (5 * x) + (3 * y)); */
/* } */


uint64_t f1 (uint64_t p1, uint64_t P1) { return P1 - 1; }
uint64_t f2 (uint64_t p1, uint64_t P1) { return 2*P1 - 2; }
uint64_t f3 (uint64_t p1, uint64_t P1) { return 3*P1 - 3; }
uint64_t f4 (uint64_t p1, uint64_t P1) { return 4*P1 - 4; }
uint64_t f5 (uint64_t p1, uint64_t P1) { return 5*P1 - 5; }
uint64_t g1 (uint64_t p1, uint64_t P1) { return (uint64_t) -1; }
uint64_t g2 (uint64_t p1, uint64_t P1) { return 0; }



uint64_t fg_array_search_4 (uint64_t y1, uint64_t y2, uint64_t y3, uint64_t y4, uint64_t k1) {

    uint64_t _let_1 = -k1;
    uint64_t _let_2 = y2 + _let_1;
    uint64_t _let_3 = (_let_2 >= 1);
    uint64_t _let_4 = (y1 + _let_1); 
    uint64_t _let_5 = (_let_4 >= 0);
    uint64_t _let_6 = (_let_5 || (! _let_3));
    uint64_t _let_7 = (y4 + _let_1);
    uint64_t _let_8 = (_let_7 >= 1);
    uint64_t _let_9 = (y3 + _let_1);
    uint64_t _let_10 = (_let_9 >= 0);
    uint64_t _let_11 = (_let_10 || (! _let_8));
    uint64_t _let_12 = (_let_9 >= 1);
    uint64_t _let_13 = (_let_2 >= 0);
    uint64_t _let_14 = (_let_13 || (! _let_12));
    uint64_t _let_15 = (!(_let_4 >= 1));
    uint64_t _let_16 = (_let_7 >= 0);

    
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

uint64_t fg_array_sum_2_15(uint64_t y1, uint64_t y2) {
  uint64_t _let_1 = y1 + y2;
  if (_let_1 >= 16 && (y1 != -y2)) return _let_1;
  else return 0;
}

uint64_t findSum4 (uint64_t y1, uint64_t y2, uint64_t y3, uint64_t y4) {
  if (y1 + y2 > 5) return y1 + y2;
  else {
    if (y2 + y3 > 5) return y2 + y3;
    else {
      if (y3 + y4) return y3 + y4;
      else return 0;
    }
  }
}

uint64_t f_jmbl_fg_VC22_a(uint64_t x1, uint64_t x2) {
  if (x1 == x2) return 0;
  else return 1;
}

uint64_t InV1 (uint64_t v, uint64_t V_min, uint64_t V_mux_) {
  if (v >= V_min)
    if (v <= V_mux_)
      return 1;

  return 0;
}


uint64_t InV2 (uint64_t v1, uint64_t v2, uint64_t V_min, uint64_t V_mux_) {
  if (v1 >= V_min)
    if (v1 <= V_mux_)
      if (v2 >= V_min)
	if (v2 <= V_mux_)
	  return 1;

  return 0;
}


uint64_t UnsafeSame(uint64_t x1, uint64_t x2, uint64_t v1, uint64_t v2) {
  uint64_t t0 = x1 + v1;
  uint64_t t1 = x2 + v2;

  uint64_t t2 = (x1 >= x2) && (t1 >= t0);
  uint64_t t3 = (x2 >= x1) && (t1 >= t0);

  return t2 || t3;
}


uint64_t ex(uint64_t x, uint64_t y) {
  if ((x < 5) && ((2 * x) != ((-3 * y) - 16 ))) {
    return 3 * x + 1;
  }
  else
    return 17 + 5 * x + 3 * y;
}

int64_t ex_fg_mpg_example1 (int64_t x, int64_t y) {
  if ((x < 5) && (2 * x != y * (-3) - 16))
    return 3*x - 1;
  else
    return 5 *x + 3 * y + 17;
}

uint64_t LinExpr1_eq1ex(uint64_t x, uint64_t y, uint64_t z) {
  if ((y + 1) == x) return z;
  else return x;
}
