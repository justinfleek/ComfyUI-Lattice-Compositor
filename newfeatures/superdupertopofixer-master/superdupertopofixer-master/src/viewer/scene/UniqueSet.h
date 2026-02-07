#pragma once

#include <memory>

#include <absl/container/flat_hash_map.h>

// WIP, not used

namespace sdtf::viewer::scene {
;

template <typename T>
class UniqueSet
{
 public:
	UniqueSet() = default;

	auto size() const { map_.size(); }
	T* insert(std::unique_ptr<T>&& uptr) {
		auto ptr = uptr.get();
		map_.insert({ptr, std::move(uptr)});
		return ptr;
	}
	auto remove(const T* ptr) { return map_.erase(ptr); }
	bool contains(const T* ptr) const { return map_.contains(ptr); }

 private:
	absl::flat_hash_map<const T*, std::unique_ptr<T>> map_;
};

}