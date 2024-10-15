#ifndef __AUFBV_UTILS_H__
#define __AUFBV_UTILS_H__
#include "aufbv-jitgen.h"
namespace cvc5 {
namespace cgen {
bool copyLLVMFunctionToModule(llvm::Function *F, llvm::Module *M);

template <typename T>
void topsort_dfs(std::map<T, std::vector<T>>& graph, T v, std::set<T>& visited, std::stack<T>& reverse_result) {
    visited.insert(v);
    for (auto& w : graph[v]) {
        if (visited.find(w) == visited.end()) {
            topsort_dfs(graph, w, visited, reverse_result);
        }
    }
    reverse_result.push(v);
    return;
}

template <typename T>
void topsort(std::map<T, std::vector<T>>& graph, std::vector<T>& result) {
    // topological sort: based on dfs
    std::set<T> visited;
    std::stack<T> reverse_result;
    for (auto& item : graph) {
        if (visited.find(item.first) == visited.end()) {
            topsort_dfs(graph, item.first, visited, reverse_result);
        }
    }
    while (!reverse_result.empty()) {
        result.push_back(reverse_result.top());
        reverse_result.pop();
    }
    return;
}

template <typename T>
void reverse_topsort(std::map<T, std::vector<T>>& graph, std::vector<T>& result) {
    // reverse topological sort graph, and add result to result
    // edge: v -> w, w is a precondition of v
    // build a reverse graph
    std::map<T, std::vector<T>> reverse_graph;
    for (auto& item : graph) {
        reverse_graph[item.first] = std::vector<T>();
    }
    for (auto& item : graph) {
        for (auto& w : item.second) {
            reverse_graph[w].push_back(item.first);
        }
    }
    // topological sort
    std::vector<T> reverse_result;
    topsort(reverse_graph, reverse_result);
    // add result
    for (auto& item : reverse_result) {
        result.push_back(item);
    }
    return;
}
}
}
#endif