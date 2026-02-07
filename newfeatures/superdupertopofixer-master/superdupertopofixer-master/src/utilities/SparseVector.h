/****
 * SparseVector.h
 * Aleksei Kalinov, 2024
 ****/

#pragma once

#include <vector>

template <class T>
class SparseVector {
 public:
	void assign(int key, T value) {
		int idx = find(key);
		if (value == 0) {
			if (idx != -1) {
				dropElement(idx);
			}
			return;
		}
		if (idx == -1) {
			keys_.push_back(key);
			values_.push_back(value);
			return;
		}
		values_[idx] = value;
	}

	void add(int key, T value) {
		if (value == 0) {
			return;
		}

		int idx = find(key);
		if (idx == -1) {
			keys_.push_back(key);
			values_.push_back(value);
			return;
		}
		values_[idx] += value;
		if (values_[idx] == 0) {
			dropElement(idx);
		}
	};

	int find(int key) const {
		for (size_t i = 0; i < keys_.size(); ++i) {
			if (keys_[i] == key) {
				return i;
			}
		}
		return -1;
	}

	int getKey(int idx) const { return keys_[idx]; }
	T getValue(int idx) const { return values_[idx]; }
	int getNNZ() const { return keys_.size(); }

 private:
	void dropElement(int idx) {
		keys_.erase(keys_.begin() + idx);
		values_.erase(values_.begin() + idx);
	}

	std::vector<int> keys_;
	std::vector<T> values_;
};

template <class T>
bool operator==(const SparseVector<T>& first, const SparseVector<T>& second) {
	int nnz = first.getNNZ();
	if (nnz != second.getNNZ()) {
		return false;
	}

	for (int i = 0; i < nnz; ++i) {
		int key = first.getKey(i);
		int j = second.find(key);
		if (j == -1 || first.getValue(i) != second.getValue(j)) {
			return false;
		}
	}
	return true;
}

template <class T>
bool operator!=(const SparseVector<T>& first, const SparseVector<T>& second) {
	return !(first == second);
}