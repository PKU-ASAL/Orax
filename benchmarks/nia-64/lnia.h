#ifndef __NIA_H__
#define __NIA_H__

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <inttypes.h>

uint64_t _mul(uint64_t a, uint64_t b);
uint64_t pow2 (uint64_t x);
uint64_t intmodtotal(uint64_t k, uint64_t a, uint64_t b);
uint64_t intxor3 (uint64_t a, uint64_t b, uint64_t c);
uint64_t in_range(uint64_t k, uint64_t x);

uint64_t _lt(uint64_t a, uint64_t b);
uint64_t _mod(uint64_t a, uint64_t b);

uint64_t intand (uint64_t k, uint64_t b, uint64_t c);
uint64_t intor (uint64_t k, uint64_t b, uint64_t c);

uint64_t ite_zero (uint64_t x, uint64_t y, uint64_t z);

#endif
