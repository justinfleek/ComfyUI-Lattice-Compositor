/****
 * QueueSet.h
 *
 * Naive implementation of a queue that keeps track of its contents and contains only unique
 * elements.
 * Aleksei Kalinov, 2025
 ****/
#pragma once

#include <queue>
#include <vector>

#include "absl/container/flat_hash_set.h"

template <class T>
class QueueSet {
 public:
	QueueSet(){};

	void reserve(size_t n) { set_.reserve(n); }

	typename std::queue<T>::reference front() { return queue_.front(); }

	void pop() {
		set_.erase(queue_.front());
		queue_.pop();
	}

	// Inserts element in the queue only if it is not already present in it. Otherwise, does nothing.
	void insert(const T& element) {
		auto [_, is_inserted] = set_.insert(element);
		if (is_inserted) {
			queue_.push(element);
		}
	}

	bool empty() { return queue_.empty(); }

	bool contains(const T& element) { return set_.contains(element); }

 private:
	absl::flat_hash_set<T> set_;
	std::queue<T> queue_;
};