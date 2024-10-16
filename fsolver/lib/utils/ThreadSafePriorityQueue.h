#ifndef THREAD_SAFE_PRIORITY_QUEUE_H
#define THREAD_SAFE_PRIORITY_QUEUE_H
#include <queue>
#include <vector>
#include <mutex>

template<typename T, typename COMP>
class ThreadSafePriorityQueue {
private:
    std::priority_queue<T, std::vector<T>, COMP> pq;
    mutable std::mutex m;

public:
    ThreadSafePriorityQueue() {}
    ThreadSafePriorityQueue(const ThreadSafePriorityQueue& other) {
        pq = other.pq;
    }
    ThreadSafePriorityQueue& operator=(const ThreadSafePriorityQueue& other) {
        pq = other.pq;
        return *this;
    }
    void push(T item) {
        std::lock_guard<std::mutex> lock(m);
        pq.push(item);
    }
    T pop() {
        std::lock_guard<std::mutex> lock(m);
        T item = pq.top();
        pq.pop();
        return item;
    }
    T top() {
        std::lock_guard<std::mutex> lock(m);
        T item = pq.top();
        return item;
    }
    bool empty() const {
        std::lock_guard<std::mutex> lock(m);
        return pq.empty();
    }
    std::size_t size() const {
        std::lock_guard<std::mutex> lock(m);
        return pq.size();
    }
    void clear() {
        std::lock_guard<std::mutex> lock(m);
        // create a new pq
        pq = std::priority_queue<T, std::vector<T>, COMP>();
    }
};
#endif