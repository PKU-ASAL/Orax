#ifndef SEED_H
#define SEED_H
#include <iostream>
#include <vector>
#include <memory>
#include <string>
#include "fsolve.h"

class fuzz_seed {
private:
    loss_function_ptr target;
    std::shared_ptr<uint8_t> data;
    size_t len;
    std::vector<double> loss_vector;
    std::vector<double> loss_acc;
    size_t loss_cnt;
    double loss;
    std::vector<uint64_t> oracle_info;
    size_t oracle_info_len;
    uint64_t hash;
    uint64_t murmurHash3(const void* key, size_t len, uint64_t seed);
public:
    fuzz_seed(loss_function_ptr target, int len, int loss_cnt);
    fuzz_seed(loss_function_ptr target, int len, int loss_cnt, size_t oracle_info_len);
    fuzz_seed(fuzz_seed const &other);
    fuzz_seed(fuzz_seed const &other, bool deep_copy);
    fuzz_seed& operator=(fuzz_seed const &other);
    void copy(fuzz_seed const &other);
    ~fuzz_seed();
    double get_loss() const;
    double get_partial_loss(size_t cnt) const;
    double get_masked_loss(std::set<size_t> &indices) const;
    uint64_t get_hash() const;
    void update_loss();
    void update_loss(double loss);
    void update_hash();
    void update();
    size_t get_len() const;
    uint8_t get_byte(size_t index) const;
    uint16_t get_word(size_t index, bool big_end) const;
    uint32_t get_dword(size_t index, bool big_end) const;
    uint64_t get_qword(size_t index, bool big_end) const;
    void set_bit(size_t bit, uint8_t value);
    void set_byte(size_t index, uint8_t value);
    void set_word(size_t index, uint16_t value, bool big_end);
    void set_dword(size_t index, uint32_t value, bool big_end);
    void set_qword(size_t index, uint64_t value, bool big_end);
    void flip_bit(size_t bit);
    void flip_byte(size_t byte);
    void delete_bytes(size_t start, size_t len);
    void insert_bytes_copy(size_t pos, size_t start, size_t len);
    void insert_bytes_random(size_t pos, size_t len);
    void replace_bytes_copy(size_t pos, size_t start, size_t len);
    void replace_bytes_random(size_t pos, size_t len);
    void splice(size_t pos1, fuzz_seed const &other, size_t pos2);
    void fuzz(std::vector<fuzz_seed> &out);
    void fuzz_masked(std::vector<fuzz_seed> &out, std::vector<uint8_t> &mask);
    void fuzz_info(std::vector<fuzz_seed> &out, std::vector<std::vector<size_t>> &data_info, std::vector<uint8_t> &mask);
    void dump() const;
    void prune(size_t size);
    bool check();
    std::shared_ptr<uint8_t> get_data() const { return data; }
    enum initial_data_type {
        ZERO,
        ONE,
        RANDOM,
        VALUE_ONE
    };
    void initialize_data(initial_data_type type);
    void initialize_data_value(std::vector<uint8_t> &value);
    void initialize_data_info(initial_data_type type, std::vector<std::vector<size_t>> &data_info);
    const std::vector<double> & get_loss_vector() const { return loss_vector; }
    const std::vector<uint64_t> & get_oracle_info() const { return oracle_info; }
};
#endif