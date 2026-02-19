// s4-runtime // containers/disjoint_sets.h
// Disjoint sets data structure for managing equivalence relationships.
//
// NOTE: This is NOT a classic union-find with path compression. It uses
// shared_ptr-based set sharing with explicit rebuild on merge. This design
// prioritizes deterministic iteration order and simple implementation over
// the O(α(n)) amortized complexity of true union-find.
//
// Complexity:
//   - mapEntries: O(n) where n is the size of the larger set
//   - areMapped: O(1) average case
//   - initializeSet: O(1) average case
//   - iteration: O(total elements), deterministic order
#pragma once

#include <s4/containers/unique_vector.h>
#include <s4/core/exceptions.h>

#include <algorithm>
#include <functional>
#include <memory>
#include <sstream>
#include <unordered_map>
#include <vector>

namespace s4::containers {

// Manages equivalence relationships between elements.
// Elements are grouped into disjoint sets; sets can be merged.
//
// Invariants:
// - Each element belongs to exactly one set.
// - Sets are non-empty.
// - The mapping is consistent with set contents.
//
// Complexity:
// - mapEntries: O(n) where n is the size of the larger set.
// - areMapped: O(1) average case.
// - initializeSet: O(1) average case.
template <typename T, typename Hash = std::hash<T>, typename Equal = std::equal_to<T>>
class disjoint_sets final {
public:
  using set_type = std::shared_ptr<unique_vector<T, Hash, Equal>>;
  using map_type = std::unordered_map<T, set_type, Hash, Equal>;

  disjoint_sets() = default;
  
  disjoint_sets(const disjoint_sets& other) {
    // Deep copy: create new sets and rebuild mappings.
    std::unordered_map<set_type, std::size_t> ptr_map;
    
    for (const auto& other_set : other.sets_) {
      auto new_set = std::make_shared<unique_vector<T, Hash, Equal>>(*other_set);
      std::size_t new_set_index = sets_.size();
      sets_.emplace_back(new_set);
      ptr_map.emplace(other_set, new_set_index);
    }
    
    for (const auto& [key, other_set_ptr] : other.map_) {
      auto new_set_index = ptr_map.at(other_set_ptr);
      map_.emplace(key, sets_.at(new_set_index));
    }
  }

  disjoint_sets(disjoint_sets&&) noexcept = default;

  auto operator=(const disjoint_sets& other) -> disjoint_sets& {
    if (this != &other) {
      disjoint_sets copy(other);
      swap(*this, copy);
    }
    return *this;
  }

  auto operator=(disjoint_sets&&) noexcept -> disjoint_sets& = default;

  friend void swap(disjoint_sets& a, disjoint_sets& b) noexcept {
    using std::swap;
    swap(a.sets_, b.sets_);
    swap(a.map_, b.map_);
  }

  // Access the mapping from elements to sets.
  [[nodiscard]] auto map() const noexcept -> const map_type& { return map_; }

  // Access all disjoint sets in deterministic order.
  [[nodiscard]] auto sets() const noexcept -> const std::vector<set_type>& {
    return sets_;
  }

  [[nodiscard]] auto find(const T& entry) -> typename map_type::iterator {
    return map_.find(entry);
  }

  [[nodiscard]] auto find(const T& entry) const -> typename map_type::const_iterator {
    return map_.find(entry);
  }

  [[nodiscard]] auto end() -> typename map_type::iterator { return map_.end(); }
  [[nodiscard]] auto end() const -> typename map_type::const_iterator { return map_.end(); }

  // Get the set containing a given entry. Entry must exist.
  [[nodiscard]] auto get_set_of(const T& entry) const 
      -> const unique_vector<T, Hash, Equal>& {
    auto it = map_.find(entry);
    S4_ERROR(it != map_.end(), "Entry not found in disjoint sets");
    return *(it->second);
  }

  // Initialize a new singleton set for an entry.
  // Returns iterator and whether insertion happened.
  auto initialize_set(const T& entry) 
      -> std::pair<typename map_type::iterator, bool> {
    auto it = map_.find(entry);
    if (it != map_.end()) {
      return {it, false};
    }
    
    auto new_set = std::make_shared<unique_vector<T, Hash, Equal>>();
    new_set->push_back(entry);
    sets_.push_back(new_set);
    return map_.emplace(entry, sets_.back());
  }

  // Merge the sets containing entry0 and entry1.
  // Creates new sets if entries don't exist.
  auto map_entries(const T& entry0, const T& entry1) -> void {
    auto it0 = map_.find(entry0);
    auto it1 = map_.find(entry1);
    
    bool found0 = (it0 != map_.end());
    bool found1 = (it1 != map_.end());
    
    // Already in the same set?
    if (found0 && found1 && it0->second == it1->second) {
      return;
    }
    
    // Create new merged set.
    auto new_set = std::make_shared<unique_vector<T, Hash, Equal>>();
    
    auto merge_existing = [this, &new_set](const T& entry) {
      auto it = map_.find(entry);
      if (it != map_.end()) {
        auto existing_set = it->second;
        for (const auto& existing_entry : *existing_set) {
          new_set->push_back(existing_entry);
          map_[existing_entry] = new_set;
        }
        // Guard: only erase if set is found (should always be true if invariants hold).
        auto set_it = std::find(sets_.begin(), sets_.end(), existing_set);
        if (set_it != sets_.end()) {
          sets_.erase(set_it);
        }
      } else {
        new_set->push_back(entry);
        map_[entry] = new_set;
      }
    };
    
    sets_.push_back(new_set);
    merge_existing(entry0);
    
    if (entry0 != entry1) {
      merge_existing(entry1);
    }
  }

  // Check if two entries are in the same set.
  // entry0 must exist; returns false if entry1 doesn't exist.
  [[nodiscard]] auto strict_are_mapped(const T& entry0, const T& entry1) const -> bool {
    auto it = map_.find(entry0);
    S4_ERROR(it != map_.end(), "Entry0 must exist for strict mapping check");
    return it->second->contains(entry1);
  }

  // Check if two entries are in the same set.
  // Returns false if either entry doesn't exist.
  [[nodiscard]] auto permissive_are_mapped(const T& entry0, const T& entry1) const -> bool {
    auto it = map_.find(entry0);
    if (it == map_.end()) return false;
    return it->second->contains(entry1);
  }

  // Check if an entry has been added to any set.
  [[nodiscard]] auto mapping_exists(const T& entry) const -> bool {
    return map_.find(entry) != map_.end();
  }

  // Append an item to an existing set.
  auto append_to_set(const T& item, set_type set) -> void {
    S4_CHECK(!mapping_exists(item), "Item already exists in disjoint sets");
    S4_CHECK(!set->empty(), "Cannot append to empty set");
    set->push_back(item);
    map_[item] = set;
  }

  // Remove an entry from the disjoint sets.
  auto erase(const T& entry) -> bool {
    auto it = map_.find(entry);
    if (it == map_.end()) return false;
    
    auto set = it->second;
    if (set->size() == 1) {
      S4_ERROR(set->front() == entry, "Inconsistent disjoint set state");
      map_.erase(entry);
      // Guard: only erase if set is found (should always be true if invariants hold).
      auto set_it = std::find(sets_.begin(), sets_.end(), set);
      if (set_it != sets_.end()) {
        sets_.erase(set_it);
      }
    } else {
      map_.erase(entry);
      set->erase(entry);
    }
    return true;
  }

  // Get all elements across all sets in deterministic order.
  [[nodiscard]] auto all_elements() const -> unique_vector<T, Hash, Equal> {
    unique_vector<T, Hash, Equal> result;
    for (const auto& set : sets_) {
      result.push_back(*set);
    }
    return result;
  }

  auto clear() noexcept -> void {
    map_.clear();
    sets_.clear();
  }

  [[nodiscard]] auto to_string() const -> std::string {
    std::ostringstream ss;
    ss << "disjoint_sets {\n";
    for (const auto& set : sets_) {
      ss << "  " << set->to_string() << "\n";
    }
    ss << "}";
    return ss.str();
  }

  [[nodiscard]] auto size() const noexcept -> std::size_t { return sets_.size(); }

  [[nodiscard]] auto empty() const noexcept -> bool { return sets_.empty(); }

private:
  map_type map_;
  std::vector<set_type> sets_;
};

}  // namespace s4::containers
