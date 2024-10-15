#include "core.h"

uint32_t add_(uint32_t a, uint32_t b) {
  return a + b;
}

uint32_t uremtotal4 (uint32_t a, uint32_t b) {
  if (b == 0) return a;

  return a % b;
}

int mul4(int a, int b, int c, int d) {
  return a * b * c * d;
}

long int isPrimeLUT (long int num) {
  if (num == 2) return 1;
  if (num == 3) return 1;
  if (num == 5) return 1;
  if (num == 7) return 1;
  if (num == 11) return 1;
  if (num == 13) return 1;
  if (num == 17) return 1;
  if (num == 19) return 1;
  if (num == 23) return 1;
  if (num == 29) return 1;
  if (num == 31) return 1;
  if (num == 37) return 1;
  if (num == 41) return 1;
  if (num == 43) return 1;
  if (num == 47) return 1;
  if (num == 53) return 1;
  if (num == 59) return 1;
  if (num == 61) return 1;
  if (num == 67) return 1;
  if (num == 71) return 1;
  if (num == 73) return 1;
  if (num == 79) return 1;
  if (num == 83) return 1;
  if (num == 89) return 1;
  if (num == 97) return 1;
  if (num == 101) return 1;
  if (num == 103) return 1;
  if (num == 107) return 1;
  if (num == 109) return 1;
  if (num == 113) return 1;
  if (num == 127) return 1;
  if (num == 131) return 1;
  if (num == 137) return 1;
  if (num == 139) return 1;
  if (num == 149) return 1;
  if (num == 151) return 1;
  if (num == 157) return 1;
  if (num == 163) return 1;
  if (num == 167) return 1;
  if (num == 173) return 1;
  if (num == 179) return 1;
  if (num == 181) return 1;
  if (num == 191) return 1;
  if (num == 193) return 1;
  if (num == 197) return 1;
  if (num == 199) return 1;
  if (num == 211) return 1;
  if (num == 223) return 1;
  if (num == 227) return 1;
  if (num == 229) return 1;
  if (num == 233) return 1;
  if (num == 239) return 1;
  if (num == 241) return 1;
  if (num == 251) return 1;

  return 0;
}



uint32_t isTriangular(uint32_t num)
{
 
    // A Triangular number must be sum of first n
    // natural numbers
    uint32_t sum = 0;
    for (uint32_t n=1; sum<=num; n++)
    {
        sum = sum + n;
        if (sum==num)
            return 1;
    }
 
    return 0;
}

uint32_t isSquare(uint32_t n)
{
    for (uint32_t i = 1; i * i <= n; i++) {
        // If (i * i = n)
        if ((n % i == 0) && (n / i == i)) {
            return 1;
        }
    }
    return 0;
}
 
