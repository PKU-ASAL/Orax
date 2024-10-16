#ifndef FSOLVE_H
#define FSOLVE_H
#include <string>
#include <memory>
#include <vector>
#include <map>
#include <set>

#define _INTEGER_TYPE 0
#define _BITVECTOR_TYPE 1
#define _FLOAT_TYPE 2
#define _ARRAY_TYPE 3

#define _DIVISIBLE 10
#define _GT 11
#define _GEQ 12
#define _LT 13
#define _LEQ 14
#define _OR 15 //_OR 2(2 possible values) a b _REQUIRE_STRICT_MODE

#define _REQUIRE_STRICT_MODE 20
#define _REAL_MODE 21

typedef bool (*loss_function_ptr) (uint8_t* data, size_t len, double *losses, size_t loss_cnt, uint64_t * oracle_info);
std::pair<std::shared_ptr<uint8_t>, size_t> fsolve_targets(std::vector<loss_function_ptr>, size_t, std::vector<std::vector<uint8_t>>&, std::vector<std::vector<size_t>>&, size_t, std::map<uint64_t, size_t>&, std::map<uint64_t, std::string>&, std::vector<std::vector<uint8_t>>&);
extern std::map<std::string, std::set<std::vector<uint64_t>>> oracleKeyPoints;
extern std::map<std::string, std::map<uint64_t, std::set<std::vector<uint64_t>>>> oracleDatabase;
extern bool VerificationModeFsolve;
extern bool VerificationModeResult;
#endif