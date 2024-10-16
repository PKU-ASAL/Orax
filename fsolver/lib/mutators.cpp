#include "mutators.h"
#include <assert.h>
#include "config.h"
#include "havoc_mutators.h"
#include <endian.h>

bool is_big_endian_flag = __BYTE_ORDER == __BIG_ENDIAN;
static bool is_big_endian(){
    return is_big_endian_flag;
    // return __BYTE_ORDER == __BIG_ENDIAN;
}

void bit_flip_mutator(const fuzz_seed& seed, std::vector<fuzz_seed>& out, size_t bit_step, size_t bits){
    if ((seed.get_len() << 3) <= bits - 1)
        return;
    for (int i = 0; i < (seed.get_len() << 3) - bits + 1; i+=bit_step){
        fuzz_seed new_seed(seed, true);
        if (bits % 8 == 0){
            // FIXME: i % 8 can be non-zero
            assert(bit_step % 8 == 0);
            for (int j = 0; j < bits; j+=8){
                new_seed.flip_byte((i+j)/8);
            }
        }
        else {
            for (int j = 0; j < bits; j++){
                new_seed.flip_bit(i + j);
            }
        }
        out.push_back(new_seed);
    }
    return;
}

void bit_flip_gap_mutator(const fuzz_seed& seed, std::vector<fuzz_seed>& out, size_t bit_step, size_t bits, size_t flip_gap, size_t group_cnt){
    if (group_cnt == 1)
        assert(flip_gap >= bits);
    if ((seed.get_len() << 3) <= flip_gap * group_cnt + bits - 1)
        return;
    for (int i = 0; i < (seed.get_len() << 3) - flip_gap * group_cnt - bits + 1; i+=bit_step){
        fuzz_seed new_seed(seed, true);
        for (int j = 0; j < bits; j++){
            for (int k = 0; k < group_cnt; k++){
                new_seed.flip_bit(i + k * flip_gap + j);
            }
        }
        out.push_back(new_seed);
    }
    return;
}

void bit_set_gap_mutator(const fuzz_seed& seed, std::vector<fuzz_seed>& out, size_t value, size_t bit_step, size_t bits, size_t flip_gap, size_t group_cnt){
    if (group_cnt > 1)
        assert(flip_gap >= bits);
    assert(value == 0 || value == 1);
    if ((seed.get_len() << 3) <= flip_gap * group_cnt + bits - 1)
        return;
    for (int i = 0; i < (seed.get_len() << 3) - flip_gap * group_cnt - bits + 1; i+=bit_step){
        fuzz_seed new_seed(seed, true);
        for (int j = 0; j < bits; j++){
            for (int k = 0; k < group_cnt; k++){
                new_seed.set_bit(i + k * flip_gap + j, value);
            }
        }
        out.push_back(new_seed);
    }
    return;
}

void arithmetic_mutator(const fuzz_seed& seed, std::vector<fuzz_seed>& out, size_t bit_step, size_t bits){
    assert(bit_step % 8 == 0 && bits % 8 == 0);
    size_t byte_step = bit_step / 8;
    size_t byte_len = bits / 8;
    assert (byte_len == 1 || byte_len == 2 || byte_len == 4 || byte_len == 8);
    if (seed.get_len() <= byte_len - 1)
        return;
    for (int i = 0; i < seed.get_len() - byte_len + 1; i+=byte_step){
        switch (byte_len){
            case 1:
                for (int j = 1; j <= ARITH_MAX; j++){
                    fuzz_seed new_seed(seed, true);
                    uint8_t val = new_seed.get_byte(i);
                    val += j;
                    new_seed.set_byte(i, val);
                    out.push_back(new_seed);
                }
                for (int j = 1; j <= ARITH_MAX; j++){
                    fuzz_seed new_seed(seed, true);
                    uint8_t val = new_seed.get_byte(i);
                    val -= j;
                    new_seed.set_byte(i, val);
                    out.push_back(new_seed);
                }
                break;
            case 2:
                for (int j = 1; j <= ARITH_MAX; j++){
                    fuzz_seed new_seed(seed, true);
                    uint16_t val = new_seed.get_word(i, is_big_endian());
                    val += j;
                    new_seed.set_word(i, val, is_big_endian());
                    out.push_back(new_seed);
                }
                for (int j = 1; j <= ARITH_MAX; j++){
                    fuzz_seed new_seed(seed, true);
                    uint16_t val = new_seed.get_word(i, is_big_endian());
                    val -= j;
                    new_seed.set_word(i, val, is_big_endian());
                    out.push_back(new_seed);
                }
                break;
            case 4:
                for (int j = 1; j <= ARITH_MAX; j++){
                    fuzz_seed new_seed(seed, true);
                    uint32_t val = new_seed.get_dword(i, is_big_endian());
                    val += j;
                    new_seed.set_dword(i, val, is_big_endian());
                    out.push_back(new_seed);
                }
                for (int j = 1; j <= ARITH_MAX; j++){
                    fuzz_seed new_seed(seed, true);
                    uint32_t val = new_seed.get_dword(i, is_big_endian());
                    val -= j;
                    new_seed.set_dword(i, val, is_big_endian());
                    out.push_back(new_seed);
                }
                break;
            case 8:
                for (int j = 1; j <= ARITH_MAX; j++){
                    fuzz_seed new_seed(seed, true);
                    uint64_t val = new_seed.get_qword(i, is_big_endian());
                    val += j;
                    new_seed.set_qword(i, val, is_big_endian());
                    out.push_back(new_seed);
                }
                for (int j = 1; j <= ARITH_MAX; j++){
                    fuzz_seed new_seed(seed, true);
                    uint64_t val = new_seed.get_qword(i, is_big_endian());
                    val -= j;
                    new_seed.set_qword(i, val, is_big_endian());
                    out.push_back(new_seed);
                }
                break;
            default:
                assert(false);
        }
    }
    return;
}

void interest_mutator(const fuzz_seed& seed, std::vector<fuzz_seed>& out, size_t bit_step, size_t bits){
    assert(bit_step % 8 == 0 && bits % 8 == 0);
    size_t byte_step = bit_step / 8;
    size_t byte_len = bits / 8;
    assert (byte_len == 1 || byte_len == 2 || byte_len == 4 || byte_len == 8);
    if (seed.get_len() <= byte_len - 1)
        return;
    for (int i = 0; i < seed.get_len() - byte_len + 1; i+=byte_step){
        switch (byte_len){
            case 1:
                for(auto &j : interesting_8){
                    fuzz_seed new_seed(seed, true);
                    new_seed.set_byte(i, j);
                    out.push_back(new_seed);
                }
                break;
            case 2:
                for(auto &j : interesting_16){
                    fuzz_seed new_seed(seed, true);
                    new_seed.set_word(i, j, is_big_endian());
                    out.push_back(new_seed);
                }
                break;
            case 4:
                for(auto &j : interesting_32){
                    fuzz_seed new_seed(seed, true);
                    new_seed.set_dword(i, j, is_big_endian());
                    out.push_back(new_seed);
                }
                break;
            case 8:
                for (auto &j : interesting_64){
                    fuzz_seed new_seed(seed, true);
                    new_seed.set_qword(i, j, is_big_endian());
                    out.push_back(new_seed);
                }
                break;
            default:
                assert(false);
        }
    }
}

void havoc_mutator(const fuzz_seed& seed, std::vector<fuzz_seed>& out){
    size_t MAX_MUTATIONS = 5;
    size_t MUTATION_TIMES = rand() % MAX_MUTATIONS + 1;
    fuzz_seed new_seed(seed, true);
    for (int i = 0; i < MUTATION_TIMES; ++i){
        havoc_mutators[rand() % havoc_mutators_len](new_seed);
    }
    out.push_back(new_seed);
}
void splice_mutator(const fuzz_seed& seed1, const fuzz_seed& seed2, std::vector<fuzz_seed>& out){
    for (int i = 0; i < SPLICE_TIMES; ++i){
        fuzz_seed new_seed1(seed1, true), new_seed2(seed2, true);
        size_t pos1 = rand() % seed1.get_len();
        size_t pos2 = rand() % seed2.get_len();
        new_seed1.splice(pos1, seed2, pos2);
        new_seed2.splice(pos2, seed1, pos1);
        out.push_back(new_seed1);
        out.push_back(new_seed2);
    }
}

static bool is_bit_masked(std::vector<uint8_t> &mask, size_t bit){
    assert(bit < mask.size() * 8);
    return mask[bit / 8] & (1 << (bit % 8));
}

static bool is_byte_masked(std::vector<uint8_t> &mask, size_t byte){
    assert(byte < mask.size());
    return mask[byte] == 0xff;
}

static bool is_word_masked(std::vector<uint8_t> &mask, size_t word){
    assert(word < mask.size() - 1);
    return mask[word] == 0xff && mask[word + 1] == 0xff;
}

static bool is_dword_masked(std::vector<uint8_t> &mask, size_t dword){
    assert(dword < mask.size() - 3);
    return mask[dword] == 0xff && mask[dword + 1] == 0xff && mask[dword + 2] == 0xff && mask[dword + 3] == 0xff;
}

static bool is_qword_masked(std::vector<uint8_t> &mask, size_t qword){
    assert(qword < mask.size() - 7);
    return mask[qword] == 0xff && mask[qword + 1] == 0xff && mask[qword + 2] == 0xff && mask[qword + 3] == 0xff && mask[qword + 4] == 0xff && mask[qword + 5] == 0xff && mask[qword + 6] == 0xff && mask[qword + 7] == 0xff;
}

void bit_flip_mutator_masked(const fuzz_seed& seed, std::vector<fuzz_seed>& out, size_t bit_step, size_t bits, std::vector<uint8_t> &mask){
    if ((seed.get_len() << 3) <= bits - 1)
        return;
    for (int i = 0; i < (seed.get_len() << 3) - bits + 1; i+=bit_step){
        fuzz_seed new_seed(seed, true);
        bool modified = false;
        if (bits % 8 == 0){
            // FIXME: i % 8 can be non-zero
            assert(bit_step % 8 == 0);
            for (int j = 0; j < bits; j+=8){
                if (is_byte_masked(mask, (i+j)/8)){
                    new_seed.flip_byte((i+j)/8);
                    modified = true;
                }
            }
        }
        else {
            for (int j = 0; j < bits; j++){
                if (is_bit_masked(mask, i + j)){
                    new_seed.flip_bit(i + j);
                    modified = true;
                }
            }
        }
        if (modified)
            out.push_back(new_seed);
    }
    return;
}

void bit_flip_gap_mutator_masked(const fuzz_seed& seed, std::vector<fuzz_seed>& out, size_t bit_step, size_t bits, size_t flip_gap, size_t group_cnt, std::vector<uint8_t> &mask){
    if (group_cnt == 1)
        assert(flip_gap >= bits);
    if ((seed.get_len() << 3) <= flip_gap * group_cnt + bits - 1)
        return;
    for (int i = 0; i < (seed.get_len() << 3) - flip_gap * group_cnt - bits + 1; i+=bit_step){
        fuzz_seed new_seed(seed, true);
        bool modified = false;
        for (int j = 0; j < bits; j++){
            for (int k = 0; k < group_cnt; k++){
                if (is_bit_masked(mask, i + k * flip_gap + j)){
                    new_seed.flip_bit(i + k * flip_gap + j);
                    modified = true;
                }
            }
        }
        if (modified)
            out.push_back(new_seed);
    }
    return;
}

void bit_set_gap_mutator_masked(const fuzz_seed& seed, std::vector<fuzz_seed>& out, size_t value, size_t bit_step, size_t bits, size_t flip_gap, size_t group_cnt, std::vector<uint8_t> &mask){
    if (group_cnt > 1)
        assert(flip_gap >= bits);
    assert(value == 0 || value == 1);
    if ((seed.get_len() << 3) <= flip_gap * group_cnt + bits - 1)
        return;
    for (int i = 0; i < (seed.get_len() << 3) - flip_gap * group_cnt - bits + 1; i+=bit_step){
        fuzz_seed new_seed(seed, true);
        bool modified = false;
        for (int j = 0; j < bits; j++){
            for (int k = 0; k < group_cnt; k++){
                if (is_bit_masked(mask, i + k * flip_gap + j)){
                    new_seed.set_bit(i + k * flip_gap + j, value);
                    modified = true;
                }
            }
        }
        if (modified)
            out.push_back(new_seed);
    }
    return;
}

void arithmetic_mutator_masked(const fuzz_seed& seed, std::vector<fuzz_seed>& out, size_t bit_step, size_t bits, std::vector<uint8_t> &mask){
    assert(bit_step % 8 == 0 && bits % 8 == 0);
    size_t byte_step = bit_step / 8;
    size_t byte_len = bits / 8;
    assert (byte_len == 1 || byte_len == 2 || byte_len == 4 || byte_len == 8);
    if (seed.get_len() <= byte_len - 1)
        return;
    for (int i = 0; i < seed.get_len() - byte_len + 1; i+=byte_step){
        switch (byte_len){
            case 1:
                for (int j = 1; j <= ARITH_MAX; j++){
                    if (is_byte_masked(mask, i)){
                        fuzz_seed new_seed(seed, true);
                        uint8_t val = new_seed.get_byte(i);
                        val += j;
                        new_seed.set_byte(i, val);
                        out.push_back(new_seed);
                    }
                }
                for (int j = 1; j <= ARITH_MAX; j++){
                    if (is_byte_masked(mask, i)){
                        fuzz_seed new_seed(seed, true);
                        uint8_t val = new_seed.get_byte(i);
                        val -= j;
                        new_seed.set_byte(i, val);
                        out.push_back(new_seed);
                    }
                }
                break;
            case 2:
                for (int j = 1; j <= ARITH_MAX; j++){
                    if (is_word_masked(mask, i)){
                        fuzz_seed new_seed(seed, true);
                        uint16_t val = new_seed.get_word(i, is_big_endian());
                        val += j;
                        new_seed.set_word(i, val, is_big_endian());
                        out.push_back(new_seed);
                    }
                }
                for (int j = 1; j <= ARITH_MAX; j++){
                    if (is_word_masked(mask, i)){
                        fuzz_seed new_seed(seed, true);
                        uint16_t val = new_seed.get_word(i, is_big_endian());
                        val -= j;
                        new_seed.set_word(i, val, is_big_endian());
                        out.push_back(new_seed);
                    }
                }
                break;
            case 4:
                for (int j = 1; j <= ARITH_MAX; j++){
                    if (is_dword_masked(mask, i)){
                        fuzz_seed new_seed(seed, true);
                        uint32_t val = new_seed.get_dword(i, is_big_endian());
                        val += j;
                        new_seed.set_dword(i, val, is_big_endian());
                        out.push_back(new_seed);
                    }
                }
                for (int j = 1; j <= ARITH_MAX; j++){
                    if (is_dword_masked(mask, i)){
                        fuzz_seed new_seed(seed, true);
                        uint32_t val = new_seed.get_dword(i, is_big_endian());
                        val -= j;
                        new_seed.set_dword(i, val, is_big_endian());
                        out.push_back(new_seed);
                    }
                }
                break;
            case 8:
                for (int j = 1; j <= ARITH_MAX; j++){
                    if (is_qword_masked(mask, i)){
                        fuzz_seed new_seed(seed, true);
                        uint64_t val = new_seed.get_qword(i, is_big_endian());
                        val += j;
                        new_seed.set_qword(i, val, is_big_endian());
                        out.push_back(new_seed);
                    }
                }
                for (int j = 1; j <= ARITH_MAX; j++){
                    if (is_qword_masked(mask, i)){
                        fuzz_seed new_seed(seed, true);
                        uint64_t val = new_seed.get_qword(i, is_big_endian());
                        val -= j;
                        new_seed.set_qword(i, val, is_big_endian());
                        out.push_back(new_seed);
                    }
                }
                break;
            default:
                assert(false);
        }
    }
    return;
}

void interest_mutator_masked(const fuzz_seed& seed, std::vector<fuzz_seed>& out, size_t bit_step, size_t bits, std::vector<uint8_t> &mask){
    assert(bit_step % 8 == 0 && bits % 8 == 0);
    size_t byte_step = bit_step / 8;
    size_t byte_len = bits / 8;
    assert (byte_len == 1 || byte_len == 2 || byte_len == 4 || byte_len == 8);
    if (seed.get_len() <= byte_len - 1)
        return;
    for (int i = 0; i < seed.get_len() - byte_len + 1; i+=byte_step){
        switch (byte_len){
            case 1:
                for(auto &j : interesting_8){
                    if (is_byte_masked(mask, i)){
                        fuzz_seed new_seed(seed, true);
                        new_seed.set_byte(i, j);
                        out.push_back(new_seed);
                    }
                }
                break;
            case 2:
                for(auto &j : interesting_16){
                    if (is_word_masked(mask, i)){
                        fuzz_seed new_seed(seed, true);
                        new_seed.set_word(i, j, is_big_endian());
                        out.push_back(new_seed);
                    }
                }
                break;
            case 4:
                for(auto &j : interesting_32){
                    if (is_dword_masked(mask, i)){
                        fuzz_seed new_seed(seed, true);
                        new_seed.set_dword(i, j, is_big_endian());
                        out.push_back(new_seed);
                    }
                }
                break;
            case 8:
                for (auto &j : interesting_64){
                    if (is_qword_masked(mask, i)){
                        fuzz_seed new_seed(seed, true);
                        new_seed.set_qword(i, j, is_big_endian());
                        out.push_back(new_seed);
                    }
                }
                break;
            default:
                assert(false);
        }
    }
}

// type aware mutators
void arithmetic_mutator_bitvector(const fuzz_seed& seed, std::vector<fuzz_seed>& out, size_t start, size_t len){
    len *= 8;
    assert(len == 8 || len == 16 || len == 32 || len == 64);
    switch(len){
        case 8:
            for (int j = 1; j <= ARITH_MAX; j++){
                fuzz_seed new_seed(seed, true);
                uint8_t val = new_seed.get_byte(start);
                val += j;
                new_seed.set_byte(start, val);
                out.push_back(new_seed);
            }
            for (int j = 1; j <= ARITH_MAX; j++){
                fuzz_seed new_seed(seed, true);
                uint8_t val = new_seed.get_byte(start);
                val -= j;
                new_seed.set_byte(start, val);
                out.push_back(new_seed);
            }
            break;
        case 16:
            for (int j = 1; j <= ARITH_MAX; j++){
                fuzz_seed new_seed(seed, true);
                uint16_t val = new_seed.get_word(start, is_big_endian());
                val += j;
                new_seed.set_word(start, val, is_big_endian());
                out.push_back(new_seed);
            }
            for (int j = 1; j <= ARITH_MAX; j++){
                fuzz_seed new_seed(seed, true);
                uint16_t val = new_seed.get_word(start, is_big_endian());
                val -= j;
                new_seed.set_word(start, val, is_big_endian());
                out.push_back(new_seed);
            }
            break;
        case 32:
            for (int j = 1; j <= ARITH_MAX; j++){
                fuzz_seed new_seed(seed, true);
                uint32_t val = new_seed.get_dword(start, is_big_endian());
                val += j;
                new_seed.set_dword(start, val, is_big_endian());
                out.push_back(new_seed);
            }
            for (int j = 1; j <= ARITH_MAX; j++){
                fuzz_seed new_seed(seed, true);
                uint32_t val = new_seed.get_dword(start, is_big_endian());
                val -= j;
                new_seed.set_dword(start, val, is_big_endian());
                out.push_back(new_seed);
            }
            break;
        case 64:
            for (int j = 1; j <= ARITH_MAX; j++){
                fuzz_seed new_seed(seed, true);
                uint64_t val = new_seed.get_qword(start, is_big_endian());
                val += j;
                new_seed.set_qword(start, val, is_big_endian());
                out.push_back(new_seed);
            }
            for (int j = 1; j <= ARITH_MAX; j++){
                fuzz_seed new_seed(seed, true);
                uint64_t val = new_seed.get_qword(start, is_big_endian());
                val -= j;
                new_seed.set_qword(start, val, is_big_endian());
                out.push_back(new_seed);
            }
            break;
        default:
            assert(false);
    }
    return;
}
void arithmetic_mutator_float(const fuzz_seed& seed, std::vector<fuzz_seed>& out, size_t start, size_t len){
    len *= 8;
    assert(len == 32 || len == 64);
    uint32_t float_exp_deltas[] = {1, 2, 4, 8, 16, 0xffffffff, 0xfffffffe, 0xfffffffc, 0xfffffff8, 0xfffffff0};
    uint32_t float_frac_deltas[] = {1, 2, 4, 8, 16, 0xffffffff, 0xfffffffe, 0xfffffffc, 0xfffffff8, 0xfffffff0};
    uint64_t float_exp_deltas_64[] = {1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 0xffffffff, 0xfffffffe, 0xfffffffc, 0xfffffff8, 0xfffffff0, 0xffffffe0, 0xffffffc0, 0xffffff80, 0xffffff00, 0xfffffe00};
    uint64_t float_frac_deltas_64[] = {1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 0xffffffff, 0xfffffffe, 0xfffffffc, 0xfffffff8, 0xfffffff0, 0xffffffe0, 0xffffffc0, 0xffffff80, 0xffffff00, 0xfffffe00};
    switch(len){
        case 32:{
            uint32_t uv = seed.get_dword(start, is_big_endian());
            // sign bit influenced by bitflip, here we ignore it
            uint32_t exp = (uv >> 23) & 0xff;
            uint32_t frac = uv & 0x7fffff;
            // exp: +1, +2, +4, +8, +16, -1, -2, -4, -8, -16
            // if more add/sub is needed, bitflip may be influential
            for (auto &delta : float_exp_deltas){
                fuzz_seed new_seed(seed, true);
                uint32_t new_exp = exp + delta;
                if (new_exp >= 0 && new_exp <= 0xff){
                    uint32_t new_uv = (uv & 0x80000000) | (new_exp << 23) | frac;
                    new_seed.set_dword(start, new_uv, is_big_endian());
                    out.push_back(new_seed);
                }
            }
            // frac: +1, +2, +4, +8, +16, -1, -2, -4, -8, -16
            for (auto &delta : float_frac_deltas){
                fuzz_seed new_seed(seed, true);
                uint32_t new_frac = frac + delta;
                if (new_frac >= 0 && new_frac <= 0x7fffff){
                    uint32_t new_uv = (uv & 0x80000000) | (exp << 23) | new_frac;
                    new_seed.set_dword(start, new_uv, is_big_endian());
                    out.push_back(new_seed);
                }
            }
            break;
        }
        case 64:{
            uint64_t uv = seed.get_qword(start, is_big_endian());
            // sign bit influenced by bitflip, here we ignore it
            uint64_t exp = (uv >> 52) & 0x7ff;
            uint64_t frac = uv & 0xfffffffffffff;
            // exp: +1, +2, +4, +8, +16, +32, +64, +128, +256, +512, -1, -2, -4, -8, -16, -32, -64, -128, -256, -512
            // if more add/sub is needed, bitflip may be influential
            for (auto &delta : float_exp_deltas_64){
                fuzz_seed new_seed(seed, true);
                uint64_t new_exp = exp + delta;
                if (new_exp >= 0 && new_exp <= 0x7ff){
                    uint64_t new_uv = (uv & 0x8000000000000000) | (new_exp << 52) | frac;
                    new_seed.set_qword(start, new_uv, is_big_endian());
                    out.push_back(new_seed);
                }
            }
            // frac: +1, +2, +4, +8, +16, +32, +64, +128, +256, +512, -1, -2, -4, -8, -16, -32, -64, -128, -256, -512
            for (auto &delta : float_frac_deltas_64){
                fuzz_seed new_seed(seed, true);
                uint64_t new_frac = frac + delta;
                if (new_frac >= 0 && new_frac <= 0xfffffffffffff){
                    uint64_t new_uv = (uv & 0x8000000000000000) | (exp << 52) | new_frac;
                    new_seed.set_qword(start, new_uv, is_big_endian());
                    out.push_back(new_seed);
                }
            }
            break;
        }
        default:
            assert(false);
    }
    return;
}
void interest_mutator_bitvector(const fuzz_seed& seed, std::vector<fuzz_seed>& out, size_t start, size_t len){
    len *= 8;
    assert(len == 8 || len == 16 || len == 32 || len == 64);
    switch(len){
        case 8:
            for(auto &j : interesting_8_bitvector){
                fuzz_seed new_seed(seed, true);
                new_seed.set_byte(start, j);
                out.push_back(new_seed);
            }
            break;
        case 16:
            for(auto &j : interesting_16_bitvector){
                fuzz_seed new_seed(seed, true);
                new_seed.set_word(start, j, is_big_endian());
                out.push_back(new_seed);
            }
            break;
        case 32:
            for(auto &j : interesting_32_bitvector){
                fuzz_seed new_seed(seed, true);
                new_seed.set_dword(start, j, is_big_endian());
                out.push_back(new_seed);
            }
            break;
        case 64:
            for(auto &j : interesting_64_bitvector){
                fuzz_seed new_seed(seed, true);
                new_seed.set_qword(start, j, is_big_endian());
                out.push_back(new_seed);
            }
            break;
        default:
            assert(false);
    }
    return;
}
void interest_mutator_float(const fuzz_seed& seed, std::vector<fuzz_seed>& out, size_t start, size_t len){
    len *= 8;
    assert(len == 32 || len == 64);
    switch(len){
        case 32:
            for(auto &j : interesting_32_float){
                fuzz_seed new_seed(seed, true);
                new_seed.set_dword(start, j, is_big_endian());
                out.push_back(new_seed);
            }
            break;
        case 64:
            for(auto &j : interesting_64_float){
                fuzz_seed new_seed(seed, true);
                new_seed.set_qword(start, j, is_big_endian());
                out.push_back(new_seed);
            }
            break;
        default:
            assert(false);
    }
    return;
}