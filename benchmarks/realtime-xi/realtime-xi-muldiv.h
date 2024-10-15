
#ifndef __RESLTIME_XI_MULDIV_H__
#define __RESLTIME_XI_MULDIV_H__

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <inttypes.h>

uint32_t in_natural_bv32(uint32_t x);
uint32_t get_hword(uint32_t x);
uint32_t get_lword(uint32_t x);

uint32_t bvudaddo_64 (uint32_t a, uint32_t b);
uint32_t bvshl_int(uint32_t x, uint32_t y);
uint32_t bvshr_int(uint32_t x, uint32_t y);
uint32_t bvlshr_int(uint32_t x, uint32_t y);
uint32_t bvurem_int(uint32_t x, uint32_t m);

uint32_t bvmul_int(uint32_t a, uint32_t b);
uint32_t bvdiv_int(uint32_t a, uint32_t b);
uint32_t bvudiv_int(uint32_t a, uint32_t b);

uint32_t ite_int(uint32_t p, uint32_t a , uint32_t b);
#endif
