#ifndef HAVOC_MUTATOR_H
#define HAVOC_MUTATOR_H
#include "seed.h"
#include <vector>

typedef void (*havoc_mutator_ptr)(fuzz_seed &seed);

void random_bit_flip(fuzz_seed &seed);
void random_byte_to_interest(fuzz_seed &seed);
void random_word_to_interest(fuzz_seed &seed);
void random_dword_to_interest(fuzz_seed &seed);
void random_byte_minus(fuzz_seed &seed);
void random_byte_plus(fuzz_seed &seed);
void random_word_minus(fuzz_seed &seed);
void random_word_plus(fuzz_seed &seed);
void random_dword_minus(fuzz_seed &seed);
void random_dword_plus(fuzz_seed &seed);
void random_byte(fuzz_seed &seed);
void random_bytes_delete(fuzz_seed &seed);
void random_insert(fuzz_seed &seed);
void random_replace(fuzz_seed &seed);

const havoc_mutator_ptr havoc_mutators[] = {
    random_bit_flip,
    random_byte_to_interest,
    random_word_to_interest,
    random_dword_to_interest,
    random_byte_minus,
    random_byte_plus,
    random_word_minus,
    random_word_plus,
    random_dword_minus,
    random_dword_plus,
    random_byte,
    random_bytes_delete,
    random_insert,
    random_replace
};

const size_t havoc_mutators_len = sizeof(havoc_mutators) / sizeof(*havoc_mutators);

#endif