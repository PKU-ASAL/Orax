#include "seed.h"
#include "fsolve.h"
#include <fstream>
#include <cstdlib>
#include <cassert>
#include <cstring>
#include "mutators.h"
#include "config.h"
#include <random>
#include <endian.h>

static bool is_big_endian(){
    return __BYTE_ORDER == __BIG_ENDIAN;
}
extern size_t SOLVE_CNT;
extern std::vector<std::vector<size_t>> global_data_info;
bool STRICT_MODE = false;
bool USE_WEIGHT = false;
std::vector<size_t> weights;
std::vector<size_t> new_weights;
size_t WEIGHT_INCREASE_CNT = 0;

fuzz_seed::fuzz_seed(loss_function_ptr target, int len, int loss_cnt){
    assert(false);
    this->target = target;
    this->data.reset(new uint8_t[len]);
    this->len = len;
    this->loss_cnt = loss_cnt;
    this->loss_vector = std::vector<double>(loss_cnt, __DBL_MAX__);
    this->loss_acc = std::vector<double>(loss_cnt, __DBL_MAX__);
    this->loss = __DBL_MAX__;
    update();
}

fuzz_seed::fuzz_seed(loss_function_ptr target, int len, int loss_cnt, size_t oracle_info_len){
    this->target = target;
    this->data.reset(new uint8_t[len]);
    this->len = len;
    this->loss_cnt = loss_cnt;
    this->loss_vector = std::vector<double>(loss_cnt, __DBL_MAX__);
    this->loss_acc = std::vector<double>(loss_cnt, __DBL_MAX__);
    this->loss = __DBL_MAX__;
    this->oracle_info = std::vector<uint64_t>(oracle_info_len, 0);
    this->oracle_info_len = oracle_info_len;
    update();
}

fuzz_seed::fuzz_seed(fuzz_seed const &other){
    // shallow copy
    this->target = other.target;
    this->data = other.data;
    this->len = other.len;
    this->loss_cnt = other.loss_cnt;
    this->loss_vector = other.loss_vector;
    this->loss_acc = other.loss_acc;
    this->loss = other.loss;
    this->oracle_info = other.oracle_info;
    this->oracle_info_len = other.oracle_info_len;
    this->hash = other.hash;
}
fuzz_seed::fuzz_seed(fuzz_seed const &other, bool deep_copy){
    if (deep_copy){
        // deep copy
        this->target = other.target;
        this->len = other.len;
        this->data.reset(new uint8_t[this->len]);
        memcpy(this->data.get(), other.data.get(), this->len);
        this->loss_cnt = other.loss_cnt;
        this->loss_vector = other.loss_vector;
        this->loss_acc = other.loss_acc;
        this->loss = other.loss;
        this->oracle_info = other.oracle_info;
        this->oracle_info_len = other.oracle_info_len;
        this->hash = other.hash;
    }
    else {
        // shallow copy
        this->target = other.target;
        this->data = other.data;
        this->len = other.len;
        this->loss_cnt = other.loss_cnt;
        this->loss_vector = other.loss_vector;
        this->loss_acc = other.loss_acc;
        this->loss = other.loss;
        this->oracle_info = other.oracle_info;
        this->oracle_info_len = other.oracle_info_len;
        this->hash = other.hash;
    }
}
fuzz_seed& fuzz_seed::operator=(fuzz_seed const &other){
    if (this == &other)
        return *this;
    // shallow copy
    this->target = other.target;
    this->data = other.data;
    this->len = other.len;
    this->loss_cnt = other.loss_cnt;
    this->loss_vector = other.loss_vector;
    this->loss_acc = other.loss_acc;
    this->loss = other.loss;
    this->oracle_info = other.oracle_info;
    this->oracle_info_len = other.oracle_info_len;
    this->hash = other.hash;
    return *this;
}
fuzz_seed::~fuzz_seed(){
    this->target = nullptr;
    this->data.reset();
    this->len = 0;
}
void fuzz_seed::copy(fuzz_seed const &other){
    // deep copy
    this->target = other.target;
    this->len = other.len;
    this->data.reset(new uint8_t[this->len]);
    memcpy(this->data.get(), other.data.get(), this->len);
    this->loss_cnt = other.loss_cnt;
    this->loss_vector = other.loss_vector;
    this->loss_acc = other.loss_acc;
    this->loss = other.loss;
    this->oracle_info = other.oracle_info;
    this->oracle_info_len = other.oracle_info_len;
    this->hash = other.hash;
}

double fuzz_seed::get_loss() const{
    return this->loss;
}

double fuzz_seed::get_partial_loss(size_t cnt) const{
    assert(cnt <= this->loss_cnt && cnt >= 0);
    if (cnt == 0)
        return 0;
    return this->loss_acc[cnt - 1];
}

double fuzz_seed::get_masked_loss(std::set<size_t> &indices) const{
    double loss = 0;
    for (auto &index : indices){
        assert(index < this->loss_cnt);
        loss += this->loss_vector[index];
    }
    return loss;
}

uint64_t fuzz_seed::get_hash() const{
    return this->hash;
}
static double loss_truncate(double loss){
    if (loss < 0){
        // FIXME: fathom why the loss is negative
        return __DBL_MAX__;
    }
    if (loss != loss){
        return __DBL_MAX__;
    }
    if (loss == std::numeric_limits<double>::infinity()){
        return __DBL_MAX__;
    }
    return loss;
}

void fuzz_seed::update_loss(){
    if (this->loss_cnt == 0){
        this->loss_vector = std::vector<double>(this->loss_cnt, 0);
        this->loss_acc = std::vector<double>(this->loss_cnt, 0);
        this->loss = 0;
        return;
    }
    auto loss_data = this->loss_vector.data();
    auto oracle_info_data = this->oracle_info.data();
    assert(loss_data != nullptr && oracle_info_data != nullptr);
    bool success = this->target(this->data.get(), this->len, loss_data, this->loss_cnt, oracle_info_data);
    assert(this->loss_vector.size() == this->loss_cnt);
    double tloss = 0;
    if (!success){
        this->loss_vector = std::vector<double>(this->loss_cnt, __DBL_MAX__);
        this->loss_acc = std::vector<double>(this->loss_cnt, __DBL_MAX__);
        this->loss = __DBL_MAX__;
    }
    else {
        assert(VerificationModeFsolve || !global_data_info.empty());
        assert(SOLVE_CNT >= 1 && SOLVE_CNT <= this->loss_cnt);
        if (USE_WEIGHT){
            assert(weights.size() == this->loss_vector.size());
            assert(new_weights.size() == this->loss_vector.size());
        }
        for (int i = 0; i < SOLVE_CNT; ++i){
            if (USE_WEIGHT){
                tloss += loss_truncate(this->loss_vector[i] * weights[i]);
                if (this->loss_vector[i] != 0){
                    new_weights[i] += 1;
                    WEIGHT_INCREASE_CNT += 1;
                }
            }
            else {
                tloss += loss_truncate(this->loss_vector[i]);
            }
            tloss = loss_truncate(tloss);
            this->loss_acc[i] = tloss;
        }
        this->loss = tloss;
        for (int i = SOLVE_CNT; i < this->loss_cnt; ++i){
            if (USE_WEIGHT){
                tloss += loss_truncate(this->loss_vector[i] * weights[i]);
                if (this->loss_vector[i] != 0){
                    new_weights[i] += 1;
                    WEIGHT_INCREASE_CNT += 1;
                }
            }
            else {
                tloss += loss_truncate(this->loss_vector[i]);
            }
            tloss = loss_truncate(tloss);
            this->loss_acc[i] = tloss;
        }
        // FIXME: now this extra loss may not be compatible with mask/since now SOLVE_CNT is maximum, it is not a problem
        if (STRICT_MODE){
            for (auto &info : global_data_info){
                auto dtype = info[0];
                auto start = info[1];
                auto len = info[2]; // bytesize
                if (dtype != _BITVECTOR_TYPE){
                    continue;
                }
                if (info.size() == 3){
                    continue;
                }
                assert(info.size() > 3);
                uint64_t value = 0;
                for (int i = 0; i < len; ++i){
                    assert(start + i < this->len);
                    value = (value << 8) | this->data.get()[start + i];
                }
                int step = 3;
                for (int i = 3; i < info.size(); i+=step){
                    auto op = info[i];
                    if (op == _OR){
                        auto value_cnt = info[i + 1];
                        step = 1 + value_cnt + 2;
                        continue;
                    }
                    else {
                        step = 3;
                        auto cmp_value = info[i + 1];
                        auto mode = info[i + 2];
                        if (mode == _REQUIRE_STRICT_MODE){
                            if (op == _DIVISIBLE){
                                if (cmp_value == 0){ // x | y, y is a variable
                                    continue;
                                }
                                if (value == 0){
                                    this->loss += __DBL_MAX__ / global_data_info.size();
                                }
                                else if (value > cmp_value){
                                    this->loss += __DBL_MAX__ / global_data_info.size();
                                }
                                else {
                                    if (cmp_value % value != 0){
                                        this->loss += cmp_value;
                                    }
                                }
                            }
                            else if (op == _LT){
                                // a < b: loss += max(0, a - b + epsilon)
                                this->loss += std::max(0.0, (double)value - (double)cmp_value + 1e-6);
                            }
                            else if (op == _LEQ){
                                // a <= b: loss += max(0, a - b)
                                this->loss += std::max(0.0, (double)value - (double)cmp_value);
                            }
                            this->loss = loss_truncate(this->loss);
                        }
                    }
                }
            }
        }
    }
    assert(this->loss >= 0);
}

void fuzz_seed::update_loss(double loss){
    assert(loss >= 0);
    this->loss = loss;
}

size_t fuzz_seed::get_len() const{
    return this->len;
}

uint8_t fuzz_seed::get_byte(size_t index) const {
    assert(index < this->len);
    return this->data.get()[index];
}

uint16_t fuzz_seed::get_word(size_t index, bool big_end) const {
    assert(index + 1 < this->len);
    if (big_end){
        return (this->data.get()[index] << 8) | this->data.get()[index + 1];
    }
    else {
        return (this->data.get()[index + 1] << 8) | this->data.get()[index];
    }
}

uint32_t fuzz_seed::get_dword(size_t index, bool big_end) const {
    assert(index + 3 < this->len);
    if (big_end){
        return (this->data.get()[index] << 24) | (this->data.get()[index + 1] << 16) | (this->data.get()[index + 2] << 8) | this->data.get()[index + 3];
    }
    else {
        return (this->data.get()[index + 3] << 24) | (this->data.get()[index + 2] << 16) | (this->data.get()[index + 1] << 8) | this->data.get()[index];
    }
}

uint64_t fuzz_seed::get_qword(size_t index, bool big_end) const {
    assert(index + 7 < this->len);
    if (big_end){
        return ((uint64_t)this->data.get()[index] << 56) | ((uint64_t)this->data.get()[index + 1] << 48) | ((uint64_t)this->data.get()[index + 2] << 40) | ((uint64_t)this->data.get()[index + 3] << 32) | ((uint64_t)this->data.get()[index + 4] << 24) | ((uint64_t)this->data.get()[index + 5] << 16) | ((uint64_t)this->data.get()[index + 6] << 8) | (uint64_t)this->data.get()[index + 7];
    }
    else {
        return ((uint64_t)this->data.get()[index + 7] << 56) | ((uint64_t)this->data.get()[index + 6] << 48) | ((uint64_t)this->data.get()[index + 5] << 40) | ((uint64_t)this->data.get()[index + 4] << 32) | ((uint64_t)this->data.get()[index + 3] << 24) | ((uint64_t)this->data.get()[index + 2] << 16) | ((uint64_t)this->data.get()[index + 1] << 8) | (uint64_t)this->data.get()[index];
    }
}

void fuzz_seed::set_bit(size_t bit, uint8_t value){
    assert(bit < (this->len << 3));
    assert(value == 0 || value == 1);
    int byte = bit >> 3;
    int bit_in_byte = bit & 0x7;
    if (value)
        this->data.get()[byte] |= (128 >> bit_in_byte);
    else
        this->data.get()[byte] &= ~(128 >> bit_in_byte);
    this->update();
    return;
}

void fuzz_seed::set_byte(size_t index, uint8_t value){
    assert(index < this->len);
    this->data.get()[index] = value;
    this->update();
    return;
}

void fuzz_seed::set_word(size_t index, uint16_t value, bool big_end){
    assert(index + 1 < this->len);
    if (big_end){
        this->data.get()[index] = (value >> 8) & 0xff;
        this->data.get()[index + 1] = value & 0xff;
    }
    else {
        this->data.get()[index + 1] = (value >> 8) & 0xff;
        this->data.get()[index] = value & 0xff;
    }
    this->update();
    return;
}

void fuzz_seed::set_dword(size_t index, uint32_t value, bool big_end){
    assert(index + 3 < this->len);
    if (big_end){
        this->data.get()[index] = (value >> 24) & 0xff;
        this->data.get()[index + 1] = (value >> 16) & 0xff;
        this->data.get()[index + 2] = (value >> 8) & 0xff;
        this->data.get()[index + 3] = value & 0xff;
    }
    else {
        this->data.get()[index + 3] = (value >> 24) & 0xff;
        this->data.get()[index + 2] = (value >> 16) & 0xff;
        this->data.get()[index + 1] = (value >> 8) & 0xff;
        this->data.get()[index] = value & 0xff;
    }
    this->update();
    return;
}

void fuzz_seed::set_qword(size_t index, uint64_t value, bool big_end){
    assert(index + 7 < this->len);
    if (big_end){
        this->data.get()[index] = (value >> 56) & 0xff;
        this->data.get()[index + 1] = (value >> 48) & 0xff;
        this->data.get()[index + 2] = (value >> 40) & 0xff;
        this->data.get()[index + 3] = (value >> 32) & 0xff;
        this->data.get()[index + 4] = (value >> 24) & 0xff;
        this->data.get()[index + 5] = (value >> 16) & 0xff;
        this->data.get()[index + 6] = (value >> 8) & 0xff;
        this->data.get()[index + 7] = value & 0xff;
    }
    else {
        this->data.get()[index + 7] = (value >> 56) & 0xff;
        this->data.get()[index + 6] = (value >> 48) & 0xff;
        this->data.get()[index + 5] = (value >> 40) & 0xff;
        this->data.get()[index + 4] = (value >> 32) & 0xff;
        this->data.get()[index + 3] = (value >> 24) & 0xff;
        this->data.get()[index + 2] = (value >> 16) & 0xff;
        this->data.get()[index + 1] = (value >> 8) & 0xff;
        this->data.get()[index] = value & 0xff;
    }
}

void fuzz_seed::flip_bit(size_t bit){
    assert(bit < (this->len << 3));
    int byte = bit >> 3;
    int bit_in_byte = bit & 0x7;
    this->data.get()[byte] ^= (128 >> bit_in_byte);
    this->update();
    return;
}

void fuzz_seed::flip_byte(size_t byte){
    assert(byte < this->len);
    this->data.get()[byte] ^= 0xff;
    this->update();
    return;
}

void fuzz_seed::delete_bytes(size_t start, size_t len){
    // len at least 1
    if (len >= this->len)
        return;
    assert(len <= this->len);
    uint8_t* new_data = new uint8_t[this->len - len];
    int newi = 0;
    for (int i = 0; i < this->len; ++i){
        if (i < start || i >= start + len){
            new_data[newi] = this->data.get()[i];
            ++ newi;
        }
    }
    assert(newi == this->len - len);
    this->data.reset(new_data);
    this->len -= len;
    update();
}

void fuzz_seed::insert_bytes_copy(size_t pos, size_t start, size_t len){
    assert(pos < this->len);
    assert(start + len <= this->len);
    uint8_t* new_data = new uint8_t[this->len + len];
    int newi = 0;
    for (int i = 0; i < this->len; ++i){
        if (i == pos){
            for (int j = 0; j < len; ++j){
                new_data[newi] = this->data.get()[start + j];
                ++ newi;
            }
        }
        new_data[newi] = this->data.get()[i];
        ++ newi;
    }
    assert(newi == this->len + len);
    this->data.reset(new_data);
    this->len += len;
    update();
}

void fuzz_seed::insert_bytes_random(size_t pos, size_t len){
    assert(pos < this->len);
    uint8_t* new_data = new uint8_t[this->len + len];
    int newi = 0;
    for (int i = 0; i < this->len; ++i){
        if (i == pos){
            for (int j = 0; j < len; ++j){
                new_data[newi] = rand() % (UINT8_MAX + 1);
                ++ newi;
            }
        }
        new_data[newi] = this->data.get()[i];
        ++ newi;
    }
    assert(newi == this->len + len);
    this->data.reset(new_data);
    this->len += len;
    update();
}

void fuzz_seed::replace_bytes_copy(size_t pos, size_t start, size_t len){
    assert(pos + len <= this->len);
    assert(start + len <= this->len);
    if (pos == start)
        return;
    else if (pos < start){
        for (int i = 0; i < len; ++i){
            this->data.get()[pos + i] = this->data.get()[start + i];
        }
    }
    else {
        for (int i = len - 1; i >= 0; --i){
            this->data.get()[pos + i] = this->data.get()[start + i];
        }
    }
    update();
}

void fuzz_seed::replace_bytes_random(size_t pos, size_t len){
    assert(pos + len <= this->len);
    for (int i = 0; i < len; ++i){
        this->data.get()[pos + i] = rand() % (UINT8_MAX + 1);
    }
    update();
}

void fuzz_seed::splice(size_t pos1, fuzz_seed const &other, size_t pos2){
    assert(pos1 < this->len);
    assert(pos2 < other.get_len());
    size_t new_len = pos1 + other.get_len() - pos2;
    if (new_len == this->len){
        for (int i = pos2; i < other.get_len(); ++i){
            this->data.get()[pos1 + i - pos2] = other.data.get()[i];
        }
        update();
        return;
    }
    uint8_t* new_data = new uint8_t[new_len];
    for (int i = 0; i < pos1; ++i){
        new_data[i] = this->data.get()[i];
    }
    for (int i = pos2; i < other.get_len(); ++i){
        new_data[pos1 + i - pos2] = other.data.get()[i];
    }
    this->data.reset(new_data);
    this->len = new_len;
    update();
}

void fuzz_seed::fuzz(std::vector<fuzz_seed> & out){
    // bit flip
    bit_flip_mutator(*this, out, 1, 1);
    bit_flip_mutator(*this, out, 1, 2);
    bit_flip_mutator(*this, out, 1, 4);
    bit_flip_mutator(*this, out, 8, 8);
    bit_flip_mutator(*this, out, 8, 16);
    bit_flip_mutator(*this, out, 8, 32);
    // bit gap flip
    bit_flip_gap_mutator(*this, out, 1, 1, 2, 2);
    bit_flip_gap_mutator(*this, out, 1, 1, 4, 2);
    bit_flip_gap_mutator(*this, out, 1, 1, 8, 2);
    bit_flip_gap_mutator(*this, out, 1, 2, 4, 2);
    bit_flip_gap_mutator(*this, out, 1, 2, 8, 2);
    bit_flip_gap_mutator(*this, out, 1, 4, 8, 2);
    bit_flip_gap_mutator(*this, out, 1, 1, 2, 3);
    bit_flip_gap_mutator(*this, out, 1, 1, 4, 3);
    bit_flip_gap_mutator(*this, out, 1, 1, 8, 3);
    bit_flip_gap_mutator(*this, out, 1, 2, 4, 3);
    bit_flip_gap_mutator(*this, out, 1, 2, 8, 3);
    bit_flip_gap_mutator(*this, out, 1, 4, 8, 3);
    bit_flip_gap_mutator(*this, out, 1, 1, 2, 4);
    bit_flip_gap_mutator(*this, out, 1, 1, 4, 4);
    bit_flip_gap_mutator(*this, out, 1, 1, 8, 4);
    bit_flip_gap_mutator(*this, out, 1, 2, 4, 4);
    bit_flip_gap_mutator(*this, out, 1, 2, 8, 4);
    bit_flip_gap_mutator(*this, out, 1, 4, 8, 4);
    // bit gap set
    bit_set_gap_mutator(*this, out, 0, 1, 1, 1, 1);
    bit_set_gap_mutator(*this, out, 0, 1, 2, 1, 1);
    bit_set_gap_mutator(*this, out, 0, 1, 3, 1, 1);
    bit_set_gap_mutator(*this, out, 0, 1, 4, 1, 1);
    bit_set_gap_mutator(*this, out, 0, 1, 5, 1, 1);
    bit_set_gap_mutator(*this, out, 0, 1, 6, 1, 1);
    bit_set_gap_mutator(*this, out, 0, 1, 7, 1, 1);
    bit_set_gap_mutator(*this, out, 0, 1, 8, 1, 1);
    bit_set_gap_mutator(*this, out, 1, 1, 1, 1, 1);
    bit_set_gap_mutator(*this, out, 1, 1, 2, 1, 1);
    bit_set_gap_mutator(*this, out, 1, 1, 3, 1, 1);
    bit_set_gap_mutator(*this, out, 1, 1, 4, 1, 1);
    bit_set_gap_mutator(*this, out, 1, 1, 5, 1, 1);
    bit_set_gap_mutator(*this, out, 1, 1, 6, 1, 1);
    bit_set_gap_mutator(*this, out, 1, 1, 7, 1, 1);
    bit_set_gap_mutator(*this, out, 1, 1, 8, 1, 1);

    bit_set_gap_mutator(*this, out, 0, 1, 1, 2, 2);
    bit_set_gap_mutator(*this, out, 0, 1, 1, 4, 2);
    bit_set_gap_mutator(*this, out, 0, 1, 1, 8, 2);
    bit_set_gap_mutator(*this, out, 0, 1, 2, 4, 2);
    bit_set_gap_mutator(*this, out, 0, 1, 2, 8, 2);
    bit_set_gap_mutator(*this, out, 0, 1, 4, 8, 2);
    bit_set_gap_mutator(*this, out, 1, 1, 1, 2, 2);
    bit_set_gap_mutator(*this, out, 1, 1, 1, 4, 2);
    bit_set_gap_mutator(*this, out, 1, 1, 1, 8, 2);
    bit_set_gap_mutator(*this, out, 1, 1, 2, 4, 2);
    bit_set_gap_mutator(*this, out, 1, 1, 2, 8, 2);
    bit_set_gap_mutator(*this, out, 1, 1, 4, 8, 2);

    // arithmetic
    arithmetic_mutator(*this, out, 8, 8);
    arithmetic_mutator(*this, out, 8, 16);
    arithmetic_mutator(*this, out, 8, 32);
    arithmetic_mutator(*this, out, 8, 64);
    // interesting values
    interest_mutator(*this, out, 8, 8);
    interest_mutator(*this, out, 8, 16);
    interest_mutator(*this, out, 8, 32);
    interest_mutator(*this, out, 8, 64);
    // havoc
    for (int i = 0; i < HAVOC_TIMES; ++i){
        havoc_mutator(*this, out);
    }
    return;
}

void fuzz_seed::fuzz_masked(std::vector<fuzz_seed> &out, std::vector<uint8_t> &mask){
    assert(mask.size() == this->len);
    // bit flip
    bit_flip_mutator_masked(*this, out, 1, 1, mask);
    bit_flip_mutator_masked(*this, out, 1, 2, mask);
    bit_flip_mutator_masked(*this, out, 1, 4, mask);
    bit_flip_mutator_masked(*this, out, 8, 8, mask);
    bit_flip_mutator_masked(*this, out, 8, 16, mask);
    bit_flip_mutator_masked(*this, out, 8, 32, mask);
    // bit gap flip
    bit_flip_gap_mutator_masked(*this, out, 1, 1, 2, 2, mask);
    bit_flip_gap_mutator_masked(*this, out, 1, 1, 4, 2, mask);
    bit_flip_gap_mutator_masked(*this, out, 1, 1, 8, 2, mask);
    bit_flip_gap_mutator_masked(*this, out, 1, 2, 4, 2, mask);
    bit_flip_gap_mutator_masked(*this, out, 1, 2, 8, 2, mask);
    bit_flip_gap_mutator_masked(*this, out, 1, 4, 8, 2, mask);
    bit_flip_gap_mutator_masked(*this, out, 1, 1, 2, 3, mask);
    bit_flip_gap_mutator_masked(*this, out, 1, 1, 4, 3, mask);
    bit_flip_gap_mutator_masked(*this, out, 1, 1, 8, 3, mask);
    bit_flip_gap_mutator_masked(*this, out, 1, 2, 4, 3, mask);
    bit_flip_gap_mutator_masked(*this, out, 1, 2, 8, 3, mask);
    bit_flip_gap_mutator_masked(*this, out, 1, 4, 8, 3, mask);
    bit_flip_gap_mutator_masked(*this, out, 1, 1, 2, 4, mask);
    bit_flip_gap_mutator_masked(*this, out, 1, 1, 4, 4, mask);
    bit_flip_gap_mutator_masked(*this, out, 1, 1, 8, 4, mask);
    bit_flip_gap_mutator_masked(*this, out, 1, 2, 4, 4, mask);
    bit_flip_gap_mutator_masked(*this, out, 1, 2, 8, 4, mask);
    bit_flip_gap_mutator_masked(*this, out, 1, 4, 8, 4, mask);
    // bit gap set
    bit_set_gap_mutator_masked(*this, out, 0, 1, 1, 1, 1, mask);
    bit_set_gap_mutator_masked(*this, out, 0, 1, 2, 1, 1, mask);
    bit_set_gap_mutator_masked(*this, out, 0, 1, 3, 1, 1, mask);
    bit_set_gap_mutator_masked(*this, out, 0, 1, 4, 1, 1, mask);
    bit_set_gap_mutator_masked(*this, out, 0, 1, 5, 1, 1, mask);
    bit_set_gap_mutator_masked(*this, out, 0, 1, 6, 1, 1, mask);
    bit_set_gap_mutator_masked(*this, out, 0, 1, 7, 1, 1, mask);
    bit_set_gap_mutator_masked(*this, out, 0, 1, 8, 1, 1, mask);
    bit_set_gap_mutator_masked(*this, out, 1, 1, 1, 1, 1, mask);
    bit_set_gap_mutator_masked(*this, out, 1, 1, 2, 1, 1, mask);
    bit_set_gap_mutator_masked(*this, out, 1, 1, 3, 1, 1, mask);
    bit_set_gap_mutator_masked(*this, out, 1, 1, 4, 1, 1, mask);
    bit_set_gap_mutator_masked(*this, out, 1, 1, 5, 1, 1, mask);
    bit_set_gap_mutator_masked(*this, out, 1, 1, 6, 1, 1, mask);
    bit_set_gap_mutator_masked(*this, out, 1, 1, 7, 1, 1, mask);
    bit_set_gap_mutator_masked(*this, out, 1, 1, 8, 1, 1, mask);

    bit_set_gap_mutator_masked(*this, out, 0, 1, 1, 2, 2, mask);
    bit_set_gap_mutator_masked(*this, out, 0, 1, 1, 4, 2, mask);
    bit_set_gap_mutator_masked(*this, out, 0, 1, 1, 8, 2, mask);
    bit_set_gap_mutator_masked(*this, out, 0, 1, 2, 4, 2, mask);
    bit_set_gap_mutator_masked(*this, out, 0, 1, 2, 8, 2, mask);
    bit_set_gap_mutator_masked(*this, out, 0, 1, 4, 8, 2, mask);
    bit_set_gap_mutator_masked(*this, out, 1, 1, 1, 2, 2, mask);
    bit_set_gap_mutator_masked(*this, out, 1, 1, 1, 4, 2, mask);
    bit_set_gap_mutator_masked(*this, out, 1, 1, 1, 8, 2, mask);
    bit_set_gap_mutator_masked(*this, out, 1, 1, 2, 4, 2, mask);
    bit_set_gap_mutator_masked(*this, out, 1, 1, 2, 8, 2, mask);
    bit_set_gap_mutator_masked(*this, out, 1, 1, 4, 8, 2, mask);

    // arithmetic
    arithmetic_mutator_masked(*this, out, 8, 8, mask);
    arithmetic_mutator_masked(*this, out, 8, 16, mask);
    arithmetic_mutator_masked(*this, out, 8, 32, mask);
    // interesting values
    interest_mutator_masked(*this, out, 8, 8, mask);
    interest_mutator_masked(*this, out, 8, 16, mask);
    interest_mutator_masked(*this, out, 8, 32, mask);
    // havoc
    for (int i = 0; i < HAVOC_TIMES; ++i){
        havoc_mutator(*this, out);
    }
    return;
}


void fuzz_seed::fuzz_info(std::vector<fuzz_seed> & out, std::vector<std::vector<size_t>> &info, std::vector<uint8_t> &mask){
    // try to be effective and lightweight
    // general mutators
    // bit flip
    bit_flip_mutator_masked(*this, out, 1, 1, mask);
    bit_flip_mutator_masked(*this, out, 1, 2, mask);
    bit_flip_mutator_masked(*this, out, 1, 4, mask);
    bit_flip_mutator_masked(*this, out, 8, 8, mask);
    bit_flip_mutator_masked(*this, out, 8, 16, mask);
    bit_flip_mutator_masked(*this, out, 8, 32, mask);
    // bit gap flip
    bit_flip_gap_mutator_masked(*this, out, 1, 1, 2, 2, mask);
    bit_flip_gap_mutator_masked(*this, out, 1, 1, 4, 2, mask);
    bit_flip_gap_mutator_masked(*this, out, 1, 1, 8, 2, mask);
    // bit gap flip: bonus
    bit_flip_gap_mutator_masked(*this, out, 1, 2, 4, 2, mask);
    bit_flip_gap_mutator_masked(*this, out, 1, 2, 8, 2, mask);
    bit_flip_gap_mutator_masked(*this, out, 1, 4, 8, 2, mask);
    bit_flip_gap_mutator_masked(*this, out, 1, 1, 2, 3, mask);
    bit_flip_gap_mutator_masked(*this, out, 1, 1, 4, 3, mask);
    bit_flip_gap_mutator_masked(*this, out, 1, 1, 8, 3, mask);
    bit_flip_gap_mutator_masked(*this, out, 1, 2, 4, 3, mask);
    bit_flip_gap_mutator_masked(*this, out, 1, 2, 8, 3, mask);
    bit_flip_gap_mutator_masked(*this, out, 1, 4, 8, 3, mask);
    bit_flip_gap_mutator_masked(*this, out, 1, 1, 2, 4, mask);
    bit_flip_gap_mutator_masked(*this, out, 1, 1, 4, 4, mask);
    bit_flip_gap_mutator_masked(*this, out, 1, 1, 8, 4, mask);
    bit_flip_gap_mutator_masked(*this, out, 1, 2, 4, 4, mask);
    bit_flip_gap_mutator_masked(*this, out, 1, 2, 8, 4, mask);
    bit_flip_gap_mutator_masked(*this, out, 1, 4, 8, 4, mask);
    // bit gap set
    bit_set_gap_mutator_masked(*this, out, 0, 1, 3, 1, 1, mask);
    bit_set_gap_mutator_masked(*this, out, 0, 1, 4, 1, 1, mask);
    bit_set_gap_mutator_masked(*this, out, 0, 1, 5, 1, 1, mask);
    bit_set_gap_mutator_masked(*this, out, 0, 1, 6, 1, 1, mask);
    bit_set_gap_mutator_masked(*this, out, 0, 1, 7, 1, 1, mask);
    bit_set_gap_mutator_masked(*this, out, 0, 1, 8, 1, 1, mask);
    bit_set_gap_mutator_masked(*this, out, 1, 1, 1, 1, 1, mask);
    bit_set_gap_mutator_masked(*this, out, 1, 1, 2, 1, 1, mask);
    bit_set_gap_mutator_masked(*this, out, 1, 1, 3, 1, 1, mask);
    bit_set_gap_mutator_masked(*this, out, 1, 1, 4, 1, 1, mask);
    bit_set_gap_mutator_masked(*this, out, 1, 1, 5, 1, 1, mask);
    bit_set_gap_mutator_masked(*this, out, 1, 1, 6, 1, 1, mask);
    bit_set_gap_mutator_masked(*this, out, 1, 1, 7, 1, 1, mask);
    bit_set_gap_mutator_masked(*this, out, 1, 1, 8, 1, 1, mask);

    bit_set_gap_mutator_masked(*this, out, 0, 1, 1, 2, 2, mask);
    bit_set_gap_mutator_masked(*this, out, 0, 1, 1, 4, 2, mask);
    bit_set_gap_mutator_masked(*this, out, 0, 1, 1, 8, 2, mask);
    bit_set_gap_mutator_masked(*this, out, 0, 1, 2, 4, 2, mask);
    bit_set_gap_mutator_masked(*this, out, 0, 1, 2, 8, 2, mask);
    bit_set_gap_mutator_masked(*this, out, 0, 1, 4, 8, 2, mask);
    bit_set_gap_mutator_masked(*this, out, 1, 1, 1, 2, 2, mask);
    bit_set_gap_mutator_masked(*this, out, 1, 1, 1, 4, 2, mask);
    bit_set_gap_mutator_masked(*this, out, 1, 1, 1, 8, 2, mask);
    bit_set_gap_mutator_masked(*this, out, 1, 1, 2, 4, 2, mask);
    bit_set_gap_mutator_masked(*this, out, 1, 1, 2, 8, 2, mask);
    bit_set_gap_mutator_masked(*this, out, 1, 1, 4, 8, 2, mask);
    bool flags[2] = {true, false};
    for (int i = 0; i < 2; ++i){
        is_big_endian_flag = flags[i];
        // arithmetic
        arithmetic_mutator_masked(*this, out, 8, 8, mask);
        arithmetic_mutator_masked(*this, out, 8, 16, mask);
        arithmetic_mutator_masked(*this, out, 8, 32, mask);
        // interesting values
        interest_mutator_masked(*this, out, 8, 8, mask);
        interest_mutator_masked(*this, out, 8, 16, mask);
        interest_mutator_masked(*this, out, 8, 32, mask);
    }
    for (auto data : info){
        auto dtype = data[0];
        auto start = data[1];
        auto len = data[2];
        if (mask[start] == 0)
            // based on the previous check: the data is all masked or all unmasked
            continue;
        if (dtype == _INTEGER_TYPE || dtype == _BITVECTOR_TYPE){
            for (int i = 0; i < 2; ++i){
                is_big_endian_flag = flags[i];
                arithmetic_mutator_bitvector(*this, out, start, len);
            }
        }
        else if (dtype == _FLOAT_TYPE){
            for (int i = 0; i < 2; ++i){
                is_big_endian_flag = flags[i];
                arithmetic_mutator_float(*this, out, start, len);
            }
        }
        else if (dtype == _ARRAY_TYPE){
            auto element_type = data[3];
            auto element_len = data[4];
            assert(element_type == _BITVECTOR_TYPE);
            assert(len % element_len == 0);
            auto arraysize = len / element_len;
            for (int i = 0; i < arraysize; ++i){
                for (int i = 0; i < 2; ++i){
                    is_big_endian_flag = flags[i];
                    arithmetic_mutator_bitvector(*this, out, start + i * element_len, element_len);
                }
            }
        }
        else {
            assert(false);
        }
    }
    // equality-based mutation
    // all variables plus constants: escape from 0, keep equalities
    int constants[4] = {1, -1, 0xff, 0x100};
    for (auto constant : constants){
        for (int i = 0; i < 2; ++i){
            is_big_endian_flag = flags[i];
            fuzz_seed new_seed(*this, true);
            for (auto data : info){
                auto dtype = data[0];
                auto start = data[1];
                auto len = data[2];
                if (mask[start] == 0)
                    // based on the previous check: the data is all masked or all unmasked
                    continue;
                if (dtype == _INTEGER_TYPE || dtype == _BITVECTOR_TYPE){
                    if (len == 1){
                        auto v = new_seed.get_byte(start);
                        v += constant;
                        new_seed.set_byte(start, v);
                    }
                    else if (len == 2){
                        auto v = new_seed.get_word(start, is_big_endian_flag);
                        v += constant;
                        new_seed.set_word(start, v, is_big_endian_flag);
                    }
                    else if (len == 4){
                        auto v = new_seed.get_dword(start, is_big_endian_flag);
                        v += constant;
                        new_seed.set_dword(start, v, is_big_endian_flag);
                    }
                    else if (len == 8){
                        auto v = new_seed.get_qword(start, is_big_endian_flag);
                        v += constant;
                        new_seed.set_qword(start, v, is_big_endian_flag);
                    }
                    else {
                        assert(false);
                    }
                }
                else if (dtype == _FLOAT_TYPE){
                    if (len == 4){
                        auto v = new_seed.get_dword(start, is_big_endian_flag);
                        float f = *(float*)&v;
                        f += constant;
                        v = *(uint32_t*)&f;
                        new_seed.set_dword(start, v, is_big_endian_flag);
                    }
                    else if (len == 8){
                        auto v = new_seed.get_qword(start, is_big_endian_flag);
                        double f = *(double*)&v;
                        f += constant;
                        v = *(uint64_t*)&f;
                        new_seed.set_qword(start, v, is_big_endian_flag);
                    }
                    else {
                        assert(false);
                    }
                }
                else if (dtype == _ARRAY_TYPE){
                    auto element_type = data[3];
                    auto element_len = data[4];
                    assert(element_type == _BITVECTOR_TYPE);
                    assert(len % element_len == 0);
                    auto arraysize = len / element_len;
                    for (int i = 0; i < arraysize; ++i){
                        if (element_len == 1){
                            auto v = new_seed.get_byte(start + i);
                            v += constant;
                            new_seed.set_byte(start + i, v);
                        }
                        else if (element_len == 2){
                            auto v = new_seed.get_word(start + i * 2, is_big_endian_flag);
                            v += constant;
                            new_seed.set_word(start + i * 2, v, is_big_endian_flag);
                        }
                        else if (element_len == 4){
                            auto v = new_seed.get_dword(start + i * 4, is_big_endian_flag);
                            v += constant;
                            new_seed.set_dword(start + i * 4, v, is_big_endian_flag);
                        }
                        else if (element_len == 8){
                            auto v = new_seed.get_qword(start + i * 8, is_big_endian_flag);
                            v += constant;
                            new_seed.set_qword(start + i * 8, v, is_big_endian_flag);
                        }
                        else {
                            assert(false);
                        }
                    }
                }
                else {
                    assert(false);
                }
            }
            out.push_back(new_seed);
        }
    }
    // havoc: no mask so far
    for (int i = 0; i < HAVOC_TIMES; ++i){
        havoc_mutator(*this, out);
    }
    return;
}

void fuzz_seed::dump() const{
    std::cout << "(data, len, loss) = (";
    for (int i = 0; i < this->len; i++){
        std::cout << std::hex << (unsigned int)(this->data.get()[i]) << " ";
    }
    std::cout << ", " << this->len << ", " << this->loss;
    std::cout << ")";
    std::cout << ", loss vector = (";
    for (auto loss : this->loss_vector){
        std::cout << loss << " ";
    }
    std::cout << ")";
    std::cout << ", loss acc = (";
    for (auto loss : this->loss_acc){
        std::cout << loss << " ";
    }
    std::cout << ")";
    return;
}

void fuzz_seed::prune(size_t size){
    assert(size <= this->len);
    if (size < this->len)
        this->len = size;
        update();
    return;
}

void fuzz_seed::update_hash(){
    uint64_t seed = 0;
    uint64_t hash = murmurHash3(this->data.get(), this->len, seed);
    this->hash = hash;
}

uint64_t fuzz_seed::murmurHash3(const void* key, size_t len, uint64_t seed) {
    const uint64_t m = 0xc6a4a7935bd1e995;
    const int r = 47;

    uint64_t h = seed ^ (len * m);

    const uint64_t* data = reinterpret_cast<const uint64_t*>(key);
    const uint64_t* end = data + (len / 8);

    while (data != end) {
        uint64_t k = *data++;
        k *= m;
        k ^= k >> r;
        k *= m;
        h ^= k;
        h *= m;
    }

    const unsigned char* data2 = reinterpret_cast<const unsigned char*>(data);
    switch (len & 7) {
        case 7: h ^= static_cast<uint64_t>(data2[6]) << 48;
        case 6: h ^= static_cast<uint64_t>(data2[5]) << 40;
        case 5: h ^= static_cast<uint64_t>(data2[4]) << 32;
        case 4: h ^= static_cast<uint64_t>(data2[3]) << 24;
        case 3: h ^= static_cast<uint64_t>(data2[2]) << 16;
        case 2: h ^= static_cast<uint64_t>(data2[1]) << 8;
        case 1: h ^= static_cast<uint64_t>(data2[0]);
                h *= m;
    };

    h ^= h >> r;
    h *= m;
    h ^= h >> r;

    return h;
}

void fuzz_seed::update(){
    this->update_loss();
    this->update_hash();
    return;
}

bool fuzz_seed::check() {
    // FIXME: epsilon
    const double epsilon = 1e-30;
    if (std::abs(this->get_loss() - 0) < epsilon)
        return true;
    return false;
}

void fuzz_seed::initialize_data(initial_data_type type){
    if (type == initial_data_type::ZERO){
        std::memset(this->data.get(), 0, this->len);
    }
    else if (type == initial_data_type::ONE){
        std::memset(this->data.get(), 0xff, this->len);
    }
    else if (type == initial_data_type::RANDOM){
        for (int i = 0; i < this->len; ++i){
            this->data.get()[i] = rand() % INT8_MAX;
        }
    }
    else {
        assert(false);
    }
    this->update();
}

void fuzz_seed::initialize_data_value(std::vector<uint8_t> &value){
    assert(value.size() == this->len);
    for (int i = 0; i < this->len; ++i){
        this->data.get()[i] = value[i];
    }
    this->update();
}

void fuzz_seed::initialize_data_info(initial_data_type itype, std::vector<std::vector<size_t>> &data_info){
    // if a data range is float/double, initialize it with 1.0
    for (auto info : data_info){
        auto dtype = info[0];
        auto start = info[1];
        auto len = info[2];
        if (dtype == _FLOAT_TYPE){
            assert(len == 4 || len == 8);
            if (len == 4){
                float f = 1.0;
                uint32_t uv = *(uint32_t*)&f;
                this->set_dword(start, uv, is_big_endian());
            }
            else {
                double d = 1.0;
                uint64_t uv = *(uint64_t*)&d;
                this->set_qword(start, uv, is_big_endian());
            }
        }
        else {
            if (itype == initial_data_type::ZERO){
                for (int i = 0; i < len; ++i){
                    this->data.get()[start + i] = 0;
                }
            }
            else if (itype == initial_data_type::ONE){
                for (int i = 0; i < len; ++i){
                    this->data.get()[start + i] = 0xff;
                }
            }
            else if (itype == initial_data_type::RANDOM){
                for (int i = 0; i < len; ++i){
                    this->data.get()[start + i] = rand() % INT8_MAX;
                }
            }
            else if (itype == initial_data_type::VALUE_ONE){
                assert(len == 1 || len == 2 || len == 4 || len == 8);
                if (len == 1){
                    uint8_t v = 1;
                    this->set_byte(start, v);
                }
                else if (len == 2){
                    uint16_t v = 1;
                    this->set_word(start, v, is_big_endian());
                }
                else if (len == 4){
                    uint32_t v = 1;
                    this->set_dword(start, v, is_big_endian());
                }
                else {
                    uint64_t v = 1;
                    this->set_qword(start, v, is_big_endian());
                }
            }
            else {
                assert(false);
            }
        }
    }
    this->update();
}