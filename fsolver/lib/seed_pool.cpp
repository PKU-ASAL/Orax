#include <thread>
#include <algorithm>
#include <iostream>
#include <chrono>
#include <assert.h>
#include "seed_pool.h"
#include "mutators.h"

static void print_speed(double speed);
extern bool USE_WEIGHT;
extern std::vector<size_t> weights;
extern std::vector<size_t> new_weights;
size_t SOLVE_CNT = 0;
std::vector<std::vector<size_t>> global_data_info;
std::map<uint64_t, std::map<uint64_t, std::set<oracle_point>>> fuzz_seed_pool::oracle_info_points = std::map<uint64_t, std::map<uint64_t, std::set<oracle_point>>>();

bool fuzz_seed_pool::seed_comparator::operator()(const fuzz_seed &a, const fuzz_seed &b) const {
    return a.get_partial_loss(SOLVE_CNT) > b.get_partial_loss(SOLVE_CNT);
}

fuzz_seed_pool::fuzz_seed_pool(loss_function_ptr target, size_t seed_size, std::vector<std::vector<uint8_t>> &masks) {
    this->target = target;
    this->masks = masks;
    this->seeds.clear();
    this->seed_min_size = seed_size;
    this->hash_set.clear();
    this->partial_solutions.clear();
    for (auto i = 0; i < masks.size(); i++){
        this->partial_solutions.push_back(fuzz_seed(target, seed_size, masks.size()));
    }
    this->oracle_pruned_cnt = 0;
}

fuzz_seed_pool::fuzz_seed_pool(loss_function_ptr target, size_t seed_size, std::vector<std::vector<uint8_t>> &masks, std::vector<std::vector<size_t>> &data_info) {
    this->target = target;
    this->masks = masks;
    this->seeds.clear();
    this->seed_min_size = seed_size;
    this->hash_set.clear();
    this->partial_solutions.clear();
    for (auto i = 0; i < masks.size(); i++){
        this->partial_solutions.push_back(fuzz_seed(target, seed_size, masks.size()));
    }
    this->data_info = data_info;
    this->oracle_pruned_cnt = 0;
}

fuzz_seed_pool::fuzz_seed_pool(loss_function_ptr target, size_t seed_size, std::vector<std::vector<uint8_t>> &masks, std::vector<std::vector<size_t>> &data_info, size_t oracle_info_len, std::map<uint64_t, size_t> &oracle_id_to_len) {
    this->target = target;
    this->masks = masks;
    this->seeds.clear();
    this->seed_min_size = seed_size;
    this->hash_set.clear();
    this->partial_solutions.clear();
    for (auto i = 0; i < masks.size(); i++){
        this->partial_solutions.push_back(fuzz_seed(target, seed_size, masks.size(), oracle_info_len));
    }
    this->data_info = data_info;
    this->oracle_info_len = oracle_info_len;
    this->oracle_id_to_len = oracle_id_to_len;
    this->oracle_pruned_cnt = 0;
}

fuzz_seed_pool::~fuzz_seed_pool() {}

void fuzz_seed_pool::dump(){
    std::cout << "dumping seeds..." << std::endl;
    for (auto i = 0; i < this->MAX_SEEDS; i++) {
        this->seeds.top().dump();
        std::cout << std::endl;
        this->seeds.pop();
    }
}

static size_t ds_find(std::vector<size_t>& parent, size_t x) {
    if (parent[x] != x) {
        parent[x] = ds_find(parent, parent[x]);
    }
    return parent[x];
}

static void ds_merge(std::vector<size_t>& parent, size_t x, size_t y) {
    parent[ds_find(parent, x)] = ds_find(parent, y);
}

// core fuzz
void fuzz_seed_pool::fuzz() {
    assert(this->seeds.size() > 0);
    std::vector<fuzz_seed> fuzzed;
    auto best = this->seeds.top();
    this->seeds.pop();
    // calculate the related mask
    assert(masks.size() > 0 && masks[0].size() == this->seed_min_size);
    std::vector<uint8_t> fuzzed_mask(this->seed_min_size, 0);
    for (auto i = 0; i < SOLVE_CNT; i++){
        auto mask = this->masks[i];
        // union operation
        for (auto j = 0; j < mask.size(); j++){
            if (mask[j] != 0)
                fuzzed_mask[j] = fuzzed_mask[j] | mask[j];
        }
    }
    // segregation
    std::vector<std::vector<size_t>> masked_by(this->seed_min_size);
    for (size_t i = 0; i < SOLVE_CNT; i++) {
        for (size_t j = 0; j < this->seed_min_size; j++) {
            if (masks[i][j] != 0) {
                masked_by[j].push_back(i);
            }
        }
    }
    std::vector<size_t> parent(SOLVE_CNT);
    for (size_t i = 0; i < SOLVE_CNT; i++) {
        parent[i] = i;
    }
    for (size_t i = 0; i < this->seed_min_size; i++) {
        auto _masked_by = masked_by[i];
        // merge every two elements in mask
        for (size_t j = 0; j < _masked_by.size(); j++) {
            for (size_t k = j + 1; k < _masked_by.size(); k++) {
                ds_merge(parent, _masked_by[j], _masked_by[k]);
            }
        }
    }
    std::map<size_t, std::set<size_t>> groups;
    for (size_t i = 0; i < SOLVE_CNT; i++) {
        if (groups.find(ds_find(parent, i)) == groups.end()) {
            groups[ds_find(parent, i)] = std::set<size_t>();
        }
        groups[ds_find(parent, i)].insert(i);
    }
    #ifdef ENABLE_CBF_DEBUG
    std::cout << "groups size: " << groups.size() << std::endl;
    #endif
    for (auto& group: groups) {
        std::set<size_t> indices = group.second;
        double masked_loss = best.get_masked_loss(indices);
        if (masked_loss == 0.0) {
            // clear the mask from the fuzzed mask
            for (auto i: indices) {
                for (size_t j = 0; j < this->seed_min_size; j++) {
                    if (masks[i][j] != 0) {
                        fuzzed_mask[j] = fuzzed_mask[j] & (~masks[i][j]);
                    }
                }
            }
        }
    }
    #ifdef ENABLE_CBF_DEBUG
    std::cout << "fuzzed mask: ";
    for (auto i: fuzzed_mask) {
        std::cout << std::hex << (int)i << " ";
    }
    std::cout << std::endl;
    #endif
    best.fuzz_info(fuzzed, this->data_info, fuzzed_mask);
    // splice
    if (this->seeds.size() > 0) {
        auto second_best = this->seeds.top();
        this->seeds.pop();
        second_best.fuzz_info(fuzzed, this->data_info, fuzzed_mask);
        splice_mutator(best, second_best, fuzzed);
    }
    // FIXME: clear instantly
    this->clear();
    for (auto& seed: fuzzed){
        if (seed.get_len() < this->seed_min_size)
            continue;
        if (this->hash_set.find(seed.get_hash()) != this->hash_set.end()){
            continue;
        }
        seed.prune(this->seed_min_size);
        this->add_seed(seed);
        // save oracle info
        auto oracle_info = seed.get_oracle_info();
        std::map<uint64_t, std::vector<std::vector<uint64_t>>> oracle_info_points;
        assert(oracle_info.size() == this->oracle_info_len && this->oracle_info_len > 0);
        size_t index = 0;
        while (index < oracle_info.size()){
            uint64_t oracle_id = oracle_info[index];
            assert(oracle_id_to_len.find(oracle_id) != oracle_id_to_len.end());
            size_t len = oracle_id_to_len[oracle_id];
            assert(len >= 1 && index + len < oracle_info.size());
            std::vector<uint64_t> x;
            uint64_t y = oracle_info[index + len];
            for (int j = 1; j < len; ++j){
                x.push_back(oracle_info[index + j]);
            }
            index += len + 1;
            if (this->oracle_info_points.find(oracle_id) == this->oracle_info_points.end()){
                this->oracle_info_points[oracle_id] = std::map<uint64_t, std::set<oracle_point>>();
            }
            if (this->oracle_info_points[oracle_id].find(y) == this->oracle_info_points[oracle_id].end()){
                this->oracle_info_points[oracle_id][y] = std::set<oracle_point>();
            }
            this->oracle_info_points[oracle_id][y].insert(oracle_point(x, y, seed.get_loss()));
            size_t MAX_CNT_EACH_VALUE = 100000;
            size_t MAX_CNT_EACH_VALUE_AFTER = 100;
            if (this->oracle_info_points[oracle_id][y].size() > MAX_CNT_EACH_VALUE){
                oracle_pruned_cnt++;
                // randomly select MAX_CNT_EACH_VALUE
                std::set<oracle_point> new_set;
                // convert set to vector
                std::vector<oracle_point> candidates = std::vector<oracle_point>(this->oracle_info_points[oracle_id][y].begin(), this->oracle_info_points[oracle_id][y].end());
                assert(candidates.size() == this->oracle_info_points[oracle_id][y].size());
                std::random_shuffle(candidates.begin(), candidates.end());
                for (size_t i = 0; i < MAX_CNT_EACH_VALUE_AFTER; i++){
                    new_set.insert(candidates[i]);
                }
                this->oracle_info_points[oracle_id][y] = new_set;
            }
        }
    }
    prune_seeds();
    return;
}

fuzz_seed fuzz_seed_pool::get_best_seed() {
    return this->seeds.top();
}

fuzz_seed fuzz_seed_pool::fetch_best_seed() {
    fuzz_seed best = this->seeds.top();
    this->seeds.pop();
    return best;
}

bool fuzz_seed_pool::check() {
    auto best = this->seeds.top();
    const double epsilon = 1e-30;
    if (std::abs(best.get_loss() - 0) < epsilon)
        return true;
    return false;
}

void fuzz_seed_pool::prune_seeds() {
    const int EXPAND_FACTOR = 2;
    if (this->seeds.size() <= this->MAX_SEEDS * EXPAND_FACTOR)
        return;
    seeds_queue new_queue;
    for (int i = 0; i < this->MAX_SEEDS; i++) {
        auto seed = this->seeds.top();
        new_queue.push(this->seeds.top());
        this->seeds.pop();
    }
    this->seeds = new_queue;
    return;
}

// utils
static void print_speed(double speed){
    if (speed > 1e9)
        std::cout << "average speed: " << speed / 1e9 << " G seeds/s" << std::endl;
    else if (speed > 1e6)
        std::cout << "average speed: " << speed / 1e6 << " M seeds/s" << std::endl;
    else if (speed > 1e3)
        std::cout << "average speed: " << speed / 1e3 << " k seeds/s" << std::endl;
    else
        std::cout << "average speed: " << speed << " seeds/s" << std::endl;
    return;
}

void fuzz_seed_pool::add_seed(fuzz_seed seed){
    this->seeds.push(seed);
    this->hash_set.insert(seed.get_hash());
    auto loss_vector = seed.get_loss_vector();
    for (auto i = 0; i < loss_vector.size(); i++){
        if (loss_vector[i] < this->partial_solutions[i].get_loss_vector()[i])
            this->partial_solutions[i] = seed;
        else {
            if (loss_vector[i] == 0.0)
                if (seed.get_loss() < this->partial_solutions[i].get_loss()){
                    this->partial_solutions[i] = seed;
                }
        }
    }
    return;
}

void fuzz_seed_pool::clear(){
    this->seeds.clear();
    return;
}

void fuzz_seed_pool::merge_partial_solutions(fuzz_seed seed, std::vector<std::vector<uint8_t>> &masks, std::vector<fuzz_seed>& out){
    assert(this->partial_solutions.size() == masks.size());
    auto all_new_seed = fuzz_seed(seed, true);
    for (auto i = 0; i < this->partial_solutions.size(); i++){
        if (seed.get_loss_vector()[i] == 0.0)
            continue;
        auto partial_solution = this->partial_solutions[i];
        if (partial_solution.get_loss_vector()[i] > seed.get_loss_vector()[i])
            continue;
        auto mask = masks[i];
        auto new_seed = fuzz_seed(seed, true);
        for (auto j = 0; j < mask.size(); j++){
            if (mask[j] == 0)
                continue;
            new_seed.set_byte(j, partial_solution.get_byte(j));
            all_new_seed.set_byte(j, partial_solution.get_byte(j));
        }
        out.push_back(new_seed);
    }
    out.push_back(all_new_seed);
    return;
}

void fuzz_seed_pool::fuzz_partial_solutions(std::vector<std::vector<uint8_t>> &masks){
    for (auto i = 0; i < this->partial_solutions.size(); i++){
        size_t FUZZ_PARTIAL_CNT = 3;
        bool updated = true;
        for (auto j = 0; j < FUZZ_PARTIAL_CNT; j++){
            if (this->partial_solutions[i].get_loss_vector()[i] == 0.0)
                break;
            if (!updated)
                break;
            updated = false;
            auto partial_solution = this->partial_solutions[i];
            auto mask = masks[i];
            std::vector<fuzz_seed> fuzzed;
            partial_solution.fuzz_masked(fuzzed, mask);
            fuzz_seed zero_seed(partial_solution, true);
            zero_seed.initialize_data(fuzz_seed::ZERO);
            zero_seed.fuzz_masked(fuzzed, mask);
            fuzz_seed one_seed(partial_solution, true);
            one_seed.initialize_data(fuzz_seed::ONE);
            one_seed.fuzz_masked(fuzzed, mask);
            for (auto& seed: fuzzed){
                if (seed.get_loss_vector()[i] < this->partial_solutions[i].get_loss_vector()[i]){
                    this->partial_solutions[i] = seed;
                    updated = true;
                }
                else if (seed.get_loss_vector()[i] == 0.0){
                    if (seed.get_loss() < this->partial_solutions[i].get_loss()){
                        this->partial_solutions[i] = seed;
                        updated = true;
                    }
                }
            }
        }
    }
}

void fuzz_seed_pool::rearrange(){
    seeds_queue new_queue;
    while (!this->seeds.empty()){
        auto s = this->seeds.pop();
        // update loss
        s.update();
        new_queue.push(s);
    }
    this->seeds = new_queue;
    return;
}