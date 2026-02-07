/****
 * UnionFind.h
 * Aleksei Kalinov, 2020
 ****/
#include <cstddef>
#include <vector>

class UnionFind {
 public:
	UnionFind(size_t num_elements) : num_elements_(num_elements) {
		parent_.reserve(num_elements);
		sizes_.reserve(num_elements);
		for (size_t i = 0; i < num_elements; ++i) {
			parent_.push_back(i);
			sizes_.push_back(1);
		}
	};

	size_t Find(size_t elem) {
		size_t current = elem;
		size_t parent;
		size_t root;

		// find the root of the tree containing `elem`
		while ((parent = parent_[current]) != current) {
			current = parent;
		}
		root = current;

		// set parents of all elements along the path from `elem` to `root` to be `root`, thus reducing
		// the depth of the tree
		current = elem;
		while (current != root) {
			parent = parent_[current];
			parent_[current] = root;
			current = parent;
		}

		return root;
	}

	void Union(size_t first, size_t second) {
		size_t root_first = Find(first);
		size_t root_second = Find(second);
		// if `first` and `second` are in the same set, nothing needs to be done
		if (root_first == root_second) {
			return;
		}

		long long size_first = sizes_[root_first];
		long long size_second = sizes_[root_second];

		if (size_first < size_second) {
			std::swap(root_first, root_second);
			std::swap(size_first, size_second);
		}

		// at this point we know that `size_first` >= `size_second`
		parent_[root_second] = root_first;
		sizes_[root_first] += size_second;
	};

	long long GetSize(size_t elem) { return sizes_[elem]; }

 private:
	// number of elements in the data structure
	size_t num_elements_;
	// parent of each element in the tree
	std::vector<size_t> parent_;
	// septh of a tree at and below each element
	std::vector<long long> sizes_;
};