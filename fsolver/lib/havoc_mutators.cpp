#include "havoc_mutators.h"
#include "config.h"

void random_bit_flip(fuzz_seed &seed){
    seed.flip_bit(rand() % (seed.get_len() << 3));
}

void random_byte_to_interest(fuzz_seed &seed){
    seed.set_byte(rand() % seed.get_len(), interesting_8[rand() % interesting_8_len]);
}

void random_word_to_interest(fuzz_seed &seed){
    if (seed.get_len() < 2){
        return;
    }
    if (rand() % 2){
        // big end
        seed.set_word(rand() % (seed.get_len() - 1), interesting_16[rand() % interesting_16_len], true);
    }
    else {
        // little end
        seed.set_word(rand() % (seed.get_len() - 1), interesting_16[rand() % interesting_16_len], false);
    }
}

void random_dword_to_interest(fuzz_seed &seed){
    if (seed.get_len() < 4){
        return;
    }
    if (rand() % 2){
        // big end
        seed.set_dword(rand() % (seed.get_len() - 3), interesting_32[rand() % interesting_32_len], true);
    }
    else {
        // little end
        seed.set_dword(rand() % (seed.get_len() - 3), interesting_32[rand() % interesting_32_len], false);
    }
}

void random_byte_minus(fuzz_seed &seed){
    size_t i = rand() % seed.get_len();
    uint8_t value = seed.get_byte(i);
    uint8_t MINUS_LIMIT = 128;
    value -= rand() % MINUS_LIMIT;
    seed.set_byte(i, value);
}

void random_byte_plus(fuzz_seed &seed){
    size_t i = rand() % seed.get_len();
    uint8_t value = seed.get_byte(i);
    uint8_t PLUS_LIMIT = 128;
    value += rand() % PLUS_LIMIT;
    seed.set_byte(i, value);
}

void random_word_minus(fuzz_seed &seed){
    if (seed.get_len() < 2){
        return;
    }
    size_t i = rand() % (seed.get_len() - 1);
    bool big_end = rand() % 2;
    uint16_t value = seed.get_word(i, big_end);
    uint16_t MINUS_LIMIT = 32768;
    value -= rand() % MINUS_LIMIT;
    seed.set_word(i, value, big_end);
}

void random_word_plus(fuzz_seed &seed){
    if (seed.get_len() < 2){
        return;
    }
    size_t i = rand() % (seed.get_len() - 1);
    bool big_end = rand() % 2;
    uint16_t value = seed.get_word(i, big_end);
    uint16_t PLUS_LIMIT = 32768;
    value += rand() % PLUS_LIMIT;
    seed.set_word(i, value, big_end);
}

void random_dword_minus(fuzz_seed &seed){
    if (seed.get_len() < 4){
        return;
    }
    size_t i = rand() % (seed.get_len() - 3);
    bool big_end = rand() % 2;
    uint32_t value = seed.get_dword(i, big_end);
    uint32_t MINUS_LIMIT = 2147483648;
    value -= rand() % MINUS_LIMIT;
    seed.set_dword(i, value, big_end);
}

void random_dword_plus(fuzz_seed &seed){
    if (seed.get_len() < 4){
        return;
    }
    size_t i = rand() % (seed.get_len() - 3);
    bool big_end = rand() % 2;
    uint32_t value = seed.get_dword(i, big_end);
    uint32_t PLUS_LIMIT = 2147483648;
    value += rand() % PLUS_LIMIT;
    seed.set_dword(i, value, big_end);
}

void random_byte(fuzz_seed &seed){
    seed.set_byte(rand() % seed.get_len(), rand() % (UINT8_MAX + 1));
}

void random_bytes_delete(fuzz_seed &seed){
    size_t start = rand() % seed.get_len();
    size_t len = rand() % (seed.get_len() - start) + 1;
    seed.delete_bytes(start, len);
}

void random_insert(fuzz_seed &seed){
    size_t pos = rand() % seed.get_len();
    if (rand() % 4 == 0){
        // 25%
        size_t len = rand() % seed.get_len();
        seed.insert_bytes_random(pos, len);
    }
    else {
        // 75%
        size_t start = rand() % seed.get_len();
        size_t len = rand() % (seed.get_len() - start) + 1;
        seed.insert_bytes_copy(pos, start, len);
    }
}

void random_replace(fuzz_seed &seed){
    size_t pos = rand() % seed.get_len();
    size_t len = rand() % (seed.get_len() - pos) + 1;
    if (rand() % 4 == 0){
        // 25%
        seed.replace_bytes_random(pos, len);
    }
    else {
        // 75%
        size_t start = rand() % (seed.get_len() - len + 1);
        seed.replace_bytes_copy(pos, start, len);
    }
}