#ifndef SEED_POOL_H
#define SEED_POOL_H
#include <vector>
#include <set>
#include "utils/ThreadSafePriorityQueue.h"
#include "seed.h"

extern size_t SOLVE_CNT;

class oracle_point {
public:
    std::vector<uint64_t> args;
    uint64_t result;
    double loss;
    int cluster;
    oracle_point() : args(std::vector<uint64_t>()), result(0), loss(0), cluster(-1) {}
    oracle_point(std::vector<uint64_t> args, uint64_t result) : args(args), result(result), loss(0), cluster(-1) {}
    oracle_point(std::vector<uint64_t> args, uint64_t result, double loss) : args(args), result(result), loss(loss), cluster(-1) {}
    // compare two oracle points
    bool operator<(const oracle_point &other) const {
        return args < other.args;
    }
    bool operator==(const oracle_point &other) const {
        return args == other.args;
    }
    std::vector<uint64_t> toVector() const {
        std::vector<uint64_t> ret;
        ret.insert(ret.end(), args.begin(), args.end());
        ret.push_back(result);
        return ret;
    }
    std::vector<uint64_t> toArgsVector() const {
        std::vector<uint64_t> ret;
        ret.insert(ret.end(), args.begin(), args.end());
        return ret;
    }
};

// TODO: multi-thread queue's functions
class fuzz_seed_pool {
private:
    const size_t MAX_SEEDS = 2 << 30;
    loss_function_ptr target;
    std::vector<std::vector<uint8_t>> masks;
    struct seed_comparator {
        bool operator()(const fuzz_seed &a, const fuzz_seed &b) const;
    };
    typedef ThreadSafePriorityQueue<fuzz_seed, seed_comparator> seeds_queue;
    seeds_queue seeds;
    size_t seed_min_size;
    std::set<uint64_t> hash_set;
    std::vector<fuzz_seed> partial_solutions;
    std::vector<std::vector<size_t>> data_info;
    size_t oracle_info_len;
    std::map<uint64_t, size_t> oracle_id_to_len;
    static std::map<uint64_t, std::map<uint64_t, std::set<oracle_point>>> oracle_info_points;
    // statistics
    size_t oracle_pruned_cnt;
public:
    fuzz_seed_pool(loss_function_ptr target, size_t seed_size, std::vector<std::vector<uint8_t>> &masks);
    fuzz_seed_pool(loss_function_ptr target, size_t seed_size, std::vector<std::vector<uint8_t>> &masks, std::vector<std::vector<size_t>> &data_info);
    fuzz_seed_pool(loss_function_ptr target, size_t seed_size, std::vector<std::vector<uint8_t>> &masks, std::vector<std::vector<size_t>> &data_info, size_t oracle_info_len, std::map<uint64_t, size_t> &oracle_id_to_len);
    ~fuzz_seed_pool();
    void dump();
    void fuzz();
    fuzz_seed get_best_seed();
    fuzz_seed fetch_best_seed();
    bool check();
    void prune_seeds();
    void add_seed(fuzz_seed seed);
    void clear();
    void merge_partial_solutions(fuzz_seed seed, std::vector<std::vector<uint8_t>> &masks, std::vector<fuzz_seed>& out);
    void fuzz_partial_solutions(std::vector<std::vector<uint8_t>> &masks);
    std::vector<std::vector<size_t>> & get_data_info() { return data_info; }
    void rearrange();
    std::map<uint64_t, std::map<uint64_t, std::set<oracle_point>> > & get_oracle_info_points() { return oracle_info_points; }
    size_t get_oracle_pruned_cnt() { return oracle_pruned_cnt; }
};
#endif