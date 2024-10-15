#ifndef __NIA_H__
#define __NIA_H__

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <inttypes.h>

uint32_t _mul(uint32_t a, uint32_t b);
uint32_t pow2 (uint32_t x);
uint32_t intmodtotal(uint32_t k, uint32_t a, uint32_t b);
uint32_t intxor3 (uint32_t a, uint32_t b, uint32_t c);
uint32_t in_range(uint32_t k, uint32_t x);

uint32_t _lt(uint32_t a, uint32_t b);
uint32_t _mod(uint32_t a, uint32_t b);

uint32_t intand (uint32_t k, uint32_t b, uint32_t c);
uint32_t intor (uint32_t k, uint32_t b, uint32_t c);

uint32_t ite_zero (uint32_t x, uint32_t y, uint32_t z);

#endif
