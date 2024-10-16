#ifndef MUTATOR_H
#define MUTATOR_H
#include "seed.h"
#include <vector>

extern bool is_big_endian_flag;

void bit_flip_mutator(const fuzz_seed& seed, std::vector<fuzz_seed>& out, size_t bit_step, size_t bits);
void bit_flip_gap_mutator(const fuzz_seed& seed, std::vector<fuzz_seed>& out, size_t bit_step, size_t bits, size_t flip_gap, size_t group_cnt);
void bit_set_gap_mutator(const fuzz_seed& seed, std::vector<fuzz_seed>& out, size_t value, size_t bit_step, size_t bits, size_t flip_gap, size_t group_cnt);
void arithmetic_mutator(const fuzz_seed& seed, std::vector<fuzz_seed>& out, size_t bit_step, size_t bits);
void interest_mutator(const fuzz_seed& seed, std::vector<fuzz_seed>& out, size_t bit_step, size_t bits);
void havoc_mutator(const fuzz_seed& seed, std::vector<fuzz_seed>& out);
void splice_mutator(const fuzz_seed& seed1, const fuzz_seed& seed2, std::vector<fuzz_seed>& out);

void bit_flip_mutator_masked(const fuzz_seed& seed, std::vector<fuzz_seed>& out, size_t bit_step, size_t bits, std::vector<uint8_t> &mask);
void bit_flip_gap_mutator_masked(const fuzz_seed& seed, std::vector<fuzz_seed>& out, size_t bit_step, size_t bits, size_t flip_gap, size_t group_cnt, std::vector<uint8_t> &mask);
void bit_set_gap_mutator_masked(const fuzz_seed& seed, std::vector<fuzz_seed>& out, size_t value, size_t bit_step, size_t bits, size_t flip_gap, size_t group_cnt, std::vector<uint8_t> &mask);
void arithmetic_mutator_masked(const fuzz_seed& seed, std::vector<fuzz_seed>& out, size_t bit_step, size_t bits, std::vector<uint8_t> &mask);
void interest_mutator_masked(const fuzz_seed& seed, std::vector<fuzz_seed>& out, size_t bit_step, size_t bits, std::vector<uint8_t> &mask);

// type aware mutators
void arithmetic_mutator_bitvector(const fuzz_seed& seed, std::vector<fuzz_seed>& out, size_t start, size_t len);
void arithmetic_mutator_float(const fuzz_seed& seed, std::vector<fuzz_seed>& out, size_t start, size_t len);
void interest_mutator_bitvector(const fuzz_seed& seed, std::vector<fuzz_seed>& out, size_t start, size_t len);
void interest_mutator_float(const fuzz_seed& seed, std::vector<fuzz_seed>& out, size_t start, size_t len);

#endif