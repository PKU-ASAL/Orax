#ifndef __LSTR_MODELS_H__
#define __LSTR_MODELS_H__

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <inttypes.h>

uint16_t numvowels_str6 (uint16_t s0, uint16_t s1, uint16_t s2, uint16_t s3, uint16_t s4, uint16_t s5);
uint16_t numvowels_str4 (uint16_t s0, uint16_t s1, uint16_t s2, uint16_t s3);
uint16_t numvowels_str5 (uint16_t s0, uint16_t s1, uint16_t s2, uint16_t s3, uint16_t s4);
uint16_t numvowels_str3 (uint16_t s0, uint16_t s1, uint16_t s2);

#endif
