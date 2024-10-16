#include "fsolve.h"
#include <dlfcn.h>
#include "seed_pool.h"
#include <random>
#include <chrono>
#include <assert.h>
#include "clustering.h"
#include <algorithm>

extern std::vector<std::vector<size_t>> global_data_info;
extern bool STRICT_MODE;
extern bool USE_WEIGHT;
extern std::vector<size_t> weights;
extern std::vector<size_t> new_weights;
extern size_t WEIGHT_INCREASE_CNT;
std::map<std::string, std::set<std::vector<uint64_t>>> oracleKeyPoints;
std::map<std::string, std::map<uint64_t, std::set<std::vector<uint64_t>>>> oracleDatabase;
bool VerificationModeFsolve = false;
bool VerificationModeResult = false;
const static size_t MAX_DARABASE_SIZE_PER_ORACLE = 100000;
static std::vector<uint64_t> sieve(uint64_t max) {
    std::vector<bool> is_prime(max + 1, true);
    is_prime[0] = is_prime[1] = false;
    for (uint64_t p = 2; p * p <= max; ++p) {
        if (is_prime[p]) {
            for (uint64_t multiple = p * p; multiple <= max; multiple += p) {
                is_prime[multiple] = false;
            }
        }
    }
    std::vector<uint64_t> primes;
    for (uint64_t i = 2; i <= max; ++i) {
        if (is_prime[i]) {
            primes.push_back(i);
        }
    }
    return primes;
}
const static int MAX_ITERATION = 30/2 * 2;
static size_t DATA_MIN_SIZE = 0;
static size_t restart = 0;
static bool initial_fuzz_seeds_used = false;
static void initialize_pool_info(fuzz_seed_pool& pool, loss_function_ptr target, size_t loss_cnt, size_t oracle_info_len, std::vector<std::vector<uint8_t>> &initial_fuzz_seeds){
    if (initial_fuzz_seeds.size() > 0 && !initial_fuzz_seeds_used){
        for (auto &v : initial_fuzz_seeds){
            fuzz_seed initial_seed(target, DATA_MIN_SIZE, loss_cnt, oracle_info_len);
            initial_seed.initialize_data_value(v);
            pool.add_seed(initial_seed);
            #ifdef ENABLE_CBF_DEBUG
            std::cout << "\033[36m" << "* Initial seed: " << "\033[0m";
            initial_seed.dump();
            std::cout << std::endl;
            #endif
        }
        initial_fuzz_seeds_used = true;
    }
    if (restart == 0){
        fuzz_seed zero_seed(target, DATA_MIN_SIZE, loss_cnt, oracle_info_len);
        zero_seed.initialize_data_info(fuzz_seed::initial_data_type::ZERO, pool.get_data_info());
        pool.add_seed(zero_seed);
        #ifdef ENABLE_CBF_DEBUG
        std::cout << "\033[36m" << "* Initial seed: " << "\033[0m";
        zero_seed.dump();
        std::cout << std::endl;
        #endif
        restart += 1;
    }
    else if (restart == 1){
        fuzz_seed one_seed(target, DATA_MIN_SIZE, loss_cnt, oracle_info_len);
        one_seed.initialize_data_info(fuzz_seed::initial_data_type::ONE, pool.get_data_info());
        pool.add_seed(one_seed);
        #ifdef ENABLE_CBF_DEBUG
        std::cout << "\033[36m" << "* Initial seed: " << "\033[0m";
        one_seed.dump();
        std::cout << std::endl;
        #endif
        fuzz_seed value_one_seed(target, DATA_MIN_SIZE, loss_cnt, oracle_info_len);
        value_one_seed.initialize_data_info(fuzz_seed::initial_data_type::VALUE_ONE, pool.get_data_info());
        pool.add_seed(value_one_seed);
        #ifdef ENABLE_CBF_DEBUG
        std::cout << "\033[36m" << "* Initial seed: " << "\033[0m";
        value_one_seed.dump();
        std::cout << std::endl;
        #endif
        restart += 1;
    }
    else {
        size_t RANDOM_SEEDS_CNT = 10;
        for (int i = 0; i < RANDOM_SEEDS_CNT; ++i){
            fuzz_seed random_seed(target, DATA_MIN_SIZE, loss_cnt, oracle_info_len);
            random_seed.initialize_data_info(fuzz_seed::initial_data_type::RANDOM, pool.get_data_info());
            pool.add_seed(random_seed);
            #ifdef ENABLE_CBF_DEBUG
            std::cout << "\033[36m" << "* Initial seed: " << "\033[0m";
            random_seed.dump();
            std::cout << std::endl;
            #endif
        }
    }
    return;
}

enum fuzz_state {
    NORMAL,
    SECOND_CHANCE,
    THIRD_CHANCE
} FUZZ_STATE;

static std::pair<std::shared_ptr<uint8_t>, size_t> do_fuzz_info(std::vector<loss_function_ptr> const & targets, std::vector<std::vector<uint8_t>> &masks, std::vector<std::vector<size_t>> &data_info, size_t oracle_info_len, std::map<uint64_t, size_t> &oracle_id_to_len, std::map<uint64_t, std::string> &oracle_id_reverse_map, std::vector<std::vector<uint8_t>> &initial_fuzz_seeds){
    #ifdef ENABLE_CBF_DEBUG
    std::cout << "\033[36m" << "* Start Fuzzing ..." << "\033[0m" << "\n";
    #endif
    srand(time(NULL));
    restart = 0;
    assert(targets.size() == 1);
    SOLVE_CNT = masks.size(); // no progressive solving
    STRICT_MODE = false;
    if (USE_WEIGHT){
        weights = std::vector<size_t>(masks.size(), 1);
        new_weights = std::vector<size_t>(masks.size(), 1);
    }
    assert(SOLVE_CNT >= 0 && SOLVE_CNT <= masks.size());
    size_t RESTART_THRESHOLD = 3;
    FUZZ_STATE = NORMAL;
    // initialize pool
    loss_function_ptr target = targets[0];
    global_data_info = data_info;
    fuzz_seed_pool pool(target, DATA_MIN_SIZE, masks, data_info, oracle_info_len, oracle_id_to_len);
    initial_fuzz_seeds_used = false;
    initialize_pool_info(pool, target, masks.size(), oracle_info_len, initial_fuzz_seeds);
    // initialize iteration
    fuzz_seed best = pool.get_best_seed();
    double last_best_loss = best.get_loss();
    if (VerificationModeFsolve){
        assert(SOLVE_CNT == masks.size());
        if (best.check()){
            VerificationModeResult = true;
            return std::make_pair(nullptr, 0);
        }
        else {
            VerificationModeResult = false;
            return std::make_pair(nullptr, 0);
        }
    }
    size_t stagnation_cnt = 0;
    auto start_time = std::chrono::high_resolution_clock::now();
    size_t TIME_LIMIT_S = 60;
    for (int i = 0; i < MAX_ITERATION; i++) {
        // check before fuzzing
        bool sat_flag = false;
        while (best.check()){
            if (SOLVE_CNT == masks.size()){
                sat_flag = true;
                break;
            }
            else {
                // SOLVE_CNT, rearrange: "atomic" use starts
                SOLVE_CNT++;
                pool.rearrange();
                // SOLVE_CNT, rearrange: "atomic" use ends
                best = pool.get_best_seed();
                last_best_loss = best.get_loss();
                stagnation_cnt = 0;
            }
        }
        if (sat_flag)
            break;
        // check time limit
        auto end_time = std::chrono::high_resolution_clock::now();
        auto duration = std::chrono::duration_cast<std::chrono::seconds>(end_time - start_time);
        if (duration.count() > TIME_LIMIT_S){
            break;
        }
        if(USE_WEIGHT){
            const size_t MAX_WEIGHT = 100;
            const size_t MAX_INC = 20;
            while (WEIGHT_INCREASE_CNT > MAX_INC){
                WEIGHT_INCREASE_CNT -= MAX_INC;
                for (int i = 0; i < new_weights.size(); ++i){
                    if (new_weights[i] > 1){
                        new_weights[i] = new_weights[i] - 1;
                    }
                    else {
                        new_weights[i] = 1;
                    }
                }
            }
            for (int i = 0; i < new_weights.size(); ++i){
                if (new_weights[i] > MAX_WEIGHT){
                    new_weights[i] = MAX_WEIGHT;
                }
            }
            weights = new_weights;
        }
        pool.fuzz();
        fuzz_seed best_in_pool = pool.get_best_seed();
        if (best_in_pool.get_loss() < best.get_loss()) {
            best = best_in_pool;
        }
        if (best.get_loss() == last_best_loss){
            stagnation_cnt++;
        }
        else {
            assert(best.get_loss() < last_best_loss);
            stagnation_cnt = 0;
            last_best_loss = best.get_loss();
        }
        if (stagnation_cnt > RESTART_THRESHOLD){
            if (FUZZ_STATE == NORMAL){
                #ifdef ENABLE_CBF_DEBUG
                std::cout << "\033[36m" << "* Merging partial solutions..." << "\033[0m" << "\n";
                #endif
                // merge best seed with partial solutions and then fuzz
                std::vector<fuzz_seed> merged_seeds;
                pool.merge_partial_solutions(best, masks, merged_seeds);
                pool.clear();
                for (auto seed : merged_seeds){
                    pool.add_seed(seed);
                }
                best = pool.get_best_seed();
                last_best_loss = best.get_loss();
                stagnation_cnt = 0;
                FUZZ_STATE = SECOND_CHANCE;
            }
            else if (FUZZ_STATE == SECOND_CHANCE){
                #ifdef ENABLE_CBF_DEBUG
                std::cout << "\033[36m" << "* Fuzzing then Merging partial solutions ..." << "\033[0m" << "\n";
                #endif
                pool.fuzz_partial_solutions(masks);
                std::vector<fuzz_seed> merged_seeds;
                pool.merge_partial_solutions(best, masks, merged_seeds);
                pool.clear();
                for (auto seed : merged_seeds){
                    pool.add_seed(seed);
                }
                best = pool.get_best_seed();
                last_best_loss = best.get_loss();
                stagnation_cnt = 0;
                FUZZ_STATE = THIRD_CHANCE;
            }
            else if (FUZZ_STATE == THIRD_CHANCE){
                #ifdef ENABLE_CBF_DEBUG
                std::cout << "\033[36m" << "* Resampling..." << "\033[0m" << "\n";
                #endif
                pool.clear();
                initialize_pool_info(pool, target, masks.size(), oracle_info_len, initial_fuzz_seeds);
                best = pool.get_best_seed();
                last_best_loss = best.get_loss();
                stagnation_cnt = 0;
                FUZZ_STATE = NORMAL;
            }
        }
        #ifdef ENABLE_CBF_DEBUG
        std::cout << "iteration: " << std::dec << i + 1 << "; progress: " << SOLVE_CNT << "/" << masks.size() << ":\n";
        // print in yellow
        std::cout << "\033[33m" << "best seed: " << "\033[0m";
        best.dump();
        std::cout << std::endl;
        std::cout << "\033[33m" << "best seed in pool: " << "\033[0m";
        best_in_pool.dump();
        std::cout << std::endl;
        #endif
    }
    bool sat = best.check();
    std::shared_ptr<uint8_t> data = nullptr;
    size_t data_len = 0;
    if (sat){
        data = best.get_data();
        data_len = best.get_len();
        #ifdef ENABLE_CBF_DEBUG
        // print in green
        std::cout << "\033[32m" << "FOUND A SOLUTION!" << "\033[0m" << "\n";
        // print solution
        best.dump();
        std::cout << std::endl;
        #endif
        return std::make_pair(data, data_len);
    }
    else {
        #ifdef ENABLE_CBF_DEBUG
        // print in red
        std::cout << "\033[32m" << "No solution found. The best seed:" << "\033[0m";
        best.dump();
        std::cout << std::endl;
        #endif
    }
    #ifdef ENABLE_CBF_DEBUG
    // print oracle_id_to_len
    for (auto &x : oracle_id_to_len){
        std::cout << "oracle id: " << x.first << "; len: " << x.second << std::endl;
    }
    #endif
    auto oracle_info_points = pool.get_oracle_info_points();
    // learn from oracle info
    std::map<std::string, std::set<std::vector<uint64_t>>> oracle_key_points;
    size_t MAX_LEARN = 10;
    size_t learned_cnt = 0;
    // if SAT, return early
    // update datebase
    for (auto &p : oracle_info_points){
        auto oracle_id = p.first;
        auto points = p.second;
        auto oracle_name = oracle_id_reverse_map[oracle_id];
        if (oracleDatabase.find(oracle_name) == oracleDatabase.end()){
            oracleDatabase[oracle_name] = std::map<uint64_t, std::set<std::vector<uint64_t>>>();
        }
        for (auto &k : points){
            auto return_value = k.first;
            auto _points = k.second;
            if (oracleDatabase[oracle_name].find(return_value) == oracleDatabase[oracle_name].end()){
                oracleDatabase[oracle_name][return_value] = std::set<std::vector<uint64_t>>();
            }
            for (auto &x : _points){
                oracleDatabase[oracle_name][return_value].insert(x.toArgsVector());
            }
        }
    }
    // prune database
    for (auto &p : oracleDatabase){
        auto oracle_id = p.first;
        auto v_to_points = p.second;
        size_t oracle_cnt = 0;
        for (auto &k : v_to_points){
            auto return_value = k.first;
            auto points = k.second;
            oracle_cnt += points.size();
        }
        if (oracle_cnt > MAX_DARABASE_SIZE_PER_ORACLE){
            size_t average_points_cnt = MAX_DARABASE_SIZE_PER_ORACLE / v_to_points.size();
            if (average_points_cnt == 0){
                average_points_cnt = 1;
            }
            // prune: randomly
            size_t pruned_cnt = 0;
            for (auto &k : v_to_points){
                auto return_value = k.first;
                auto points = k.second;
                if (points.size() > average_points_cnt){
                    auto vec_points = std::vector<std::vector<uint64_t>>();
                    for (auto &x : points){
                        vec_points.push_back(x);
                    }
                    std::random_shuffle(vec_points.begin(), vec_points.end());
                    auto new_points = std::set<std::vector<uint64_t>>();
                    for (int i = 0; i < average_points_cnt; ++i){
                        new_points.insert(vec_points[i]);
                    }
                    oracleDatabase[oracle_id][return_value] = new_points;
                }
                pruned_cnt += oracleDatabase[oracle_id][return_value].size();
            }
            assert(pruned_cnt <= MAX_DARABASE_SIZE_PER_ORACLE * 2);
        }
    }
    // observe interesting value: divisible
    std::set<uint64_t> interesting_args;
    for (auto &info : data_info){
        auto dtype = info[0];
        auto start = info[1];
        auto len = info[2]; // bytesize
        if (dtype != _BITVECTOR_TYPE){
            continue;
        }
        if (info.size() == 3){
            continue;
        }
        // divisible as start values
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
                        uint64_t sieve_max = cmp_value;
                        if (cmp_value == 0 || cmp_value > 256){
                            sieve_max = 256;
                        }
                        std::vector<uint64_t> factors = sieve(sieve_max);
                        for (auto &p : factors){
                            if (cmp_value % p == 0)
                                interesting_args.insert(p);
                        }
                    }
                }
            }
        }
        // eliminate bad values
    }
    // select key oracle points
    for (auto &p : oracle_info_points){
        auto oracle_id = p.first;
        auto points = p.second;
        auto oracle_name = oracle_id_reverse_map[oracle_id];
        if (oracle_key_points.find(oracle_name) == oracle_key_points.end()){
            oracle_key_points[oracle_name] = std::set<std::vector<uint64_t>>();
        }
        // select one point from each oracle return value
        size_t return_value_cnt = points.size();
        size_t MAX_RETURN_VALUE_CNT = 5;
        size_t MAX_SELECTED_CNT_EACH_CLUSTER = 3;
        std::set<uint64_t> selected_return_values;
        if (return_value_cnt > MAX_RETURN_VALUE_CNT){
            // FIXME: maybe buggy
            std::set<oracle_point> return_value_points;
            for (auto &k : points){
                return_value_points.insert(oracle_point(std::vector<uint64_t>(1, k.first), 0, 0));
            }
            assert(return_value_points.size() == return_value_cnt);
            auto selected_return_value_points = clustering(return_value_points, MAX_RETURN_VALUE_CNT);
            std::vector<std::vector<uint64_t>> clustered_return_values(MAX_RETURN_VALUE_CNT);
            std::vector<std::set<oracle_point>> clustered_return_value_points(MAX_RETURN_VALUE_CNT);
            for (auto &k : selected_return_value_points){
                assert(k.args.size() == 1);
                assert(k.cluster >= 0 && k.cluster < MAX_RETURN_VALUE_CNT);
                assert(points.find(k.args[0]) != points.end());
                clustered_return_values[k.cluster].push_back(k.args[0]);
                for (auto &x : points[k.args[0]]){
                    clustered_return_value_points[k.cluster].insert(x);
                }
            }
            // cluster key points in each cluster
            for (auto &k : clustered_return_value_points){
                auto selected_xs = clustering_select(k, MAX_SELECTED_CNT_EACH_CLUSTER);
                for (auto &x : selected_xs){
                    oracle_key_points[oracle_name].insert(x.toVector());
                }
                learned_cnt++;
                if (learned_cnt >= MAX_LEARN){
                    break;
                }
            }
        }
        else {
            for (auto &k : points){
                selected_return_values.insert(k.first);
            }
            for (auto &y : selected_return_values){
                assert(points.find(y) != points.end());
                auto xs = points[y];
                assert(xs.size() > 0);
                if (xs.begin()->args.size() == 1){
                    // like f(x)
                    for (auto& point : xs) {
                        uint64_t arg_value = point.args[0];
                        if (interesting_args.find(arg_value) != interesting_args.end()){
                            oracle_key_points[oracle_name].insert(point.toVector());
                        }
                    }
                }
                auto selected_xs = clustering_select(xs, MAX_SELECTED_CNT_EACH_CLUSTER);
                for (auto &x : selected_xs){
                    oracle_key_points[oracle_name].insert(x.toVector());
                }
                learned_cnt++;
                if (learned_cnt >= MAX_LEARN){
                    break;
                }
            }
        }
        if (learned_cnt >= MAX_LEARN){
            break;
        }
    }
    oracleKeyPoints = oracle_key_points;
    #ifdef ENABLE_CBF_DEBUG
    // print oracle key points
    for (auto &point : oracleKeyPoints){
        auto oracle_id = point.first;
        auto points = point.second;
        std::cout << "oracle id: " << oracle_id << "; key points: ";
        for (auto &x : points){
            for (auto &y : x){
                std::cout << y << " ";
            }
            std::cout << "; ";
        }
        std::cout << std::endl;
    }
    std::cout << "\033[36m" << "* Oracle Prune Cnt: " << pool.get_oracle_pruned_cnt() << "\033[0m" << "\n";
    #endif
    return std::make_pair(data, data_len);
}

bool check_data_info(std::vector<std::vector<size_t>> &data_info){
    size_t index = 0;
    for (auto info : data_info){
        assert(info.size() >= 3);
        auto type = info[0];
        if (type == _ARRAY_TYPE){
            assert(info.size() == 5);
            auto element_type = info[3];
            assert(element_type == _BITVECTOR_TYPE);
        }
        else {
            if (type == _BITVECTOR_TYPE){
                int step = 3;
                for (int i = 3; i < info.size(); i+=step){
                    auto op = info[i];
                    if (op == _OR){
                        auto value_cnt = info[i + 1];
                        auto mode = info[i + 1 + value_cnt + 1];
                        assert(mode == _REQUIRE_STRICT_MODE);
                        step = 1 + value_cnt + 2;
                    }
                    else {
                        auto cmp_value = info[i + 1];
                        auto mode = info[i + 2];
                        assert(mode == _REQUIRE_STRICT_MODE);
                        step = 3;
                    }
                }
            }
            else {
                assert(info.size() == 3);
            }
        }
        auto start = info[1];
        auto len = info[2];
        assert(start == index);
        index += len;
        assert(index <= DATA_MIN_SIZE);
    }
    assert(index == DATA_MIN_SIZE);
    return true;
}

bool check_masks_data_info_consistency(std::vector<std::vector<uint8_t>> &masks, std::vector<std::vector<size_t>> &data_info){
    for (int i = 0; i < masks.size(); ++i){
        auto mask = masks[i];
        std::set<size_t> masked_indices;
        for (int j = 0; j < mask.size(); ++j){
            if (mask[j] != 0){
                assert(mask[j] == 0xff);
                masked_indices.insert(j);
            }
        }
        for (auto info : data_info){
            auto start = info[1];
            auto len = info[2];
            // if start is in masked_indices, then all indices in [start, start + len) should be in masked_indices
            if (masked_indices.find(start) != masked_indices.end()){
                for (int k = start; k < start + len; ++k){
                    assert(masked_indices.find(k) != masked_indices.end());
                    // remove k from masked_indices
                    masked_indices.erase(k);
                }
            }
        }
        // all indices in masked_indices should be checked
        assert(masked_indices.size() == 0);
    }
    return true;
}

std::pair<std::shared_ptr<uint8_t>, size_t> fsolve_targets(std::vector<loss_function_ptr> targets, size_t data_min_size, std::vector<std::vector<uint8_t>> &masks, std::vector<std::vector<size_t>> &data_info, size_t oracle_info_len, std::map<uint64_t, size_t> &oracle_id_to_len, std::map<uint64_t, std::string> &oracle_id_reverse_map, std::vector<std::vector<uint8_t>> &initial_fuzz_seeds){
    // clear global_data_info
    global_data_info.clear();
    DATA_MIN_SIZE = data_min_size;
    if (!check_data_info(data_info) || !check_masks_data_info_consistency(masks, data_info)){
        assert(false);
        exit(1);
    }
    // build some initial_fuzz_seeds from data_info
    for (auto info : data_info){
        assert(info.size() >= 3);
        auto type = info[0];
        auto start = info[1];
        auto len = info[2];
        if (type == _BITVECTOR_TYPE){
            int step = 3;
            for (int i = 3; i < info.size(); i+=step){
                auto op = info[i];
                if (op == _OR){
                    auto value_cnt = info[i + 1];
                    auto mode = info[i + 1 + value_cnt + 1];
                    assert(mode == _REQUIRE_STRICT_MODE);
                    // create initial fuzz seeds for each value
                    for (int j = 1; j <= value_cnt; ++j){
                        auto _value = info[i + 1 + j];
                        std::vector<uint8_t> fuzz_seed(data_min_size, 0);
                        for (int k = 0; k < len; ++k){
                            fuzz_seed[start + k] = (_value >> (len - 1 - k)) & 0xff;
                        }
                        initial_fuzz_seeds.push_back(fuzz_seed);
                    }
                    step = 1 + value_cnt + 2;
                }
                else {
                    step = 3;
                }
            }
        }
    }
    std::pair<std::shared_ptr<uint8_t>, size_t> solution = do_fuzz_info(targets, masks, data_info, oracle_info_len, oracle_id_to_len, oracle_id_reverse_map, initial_fuzz_seeds);
    return solution;
}