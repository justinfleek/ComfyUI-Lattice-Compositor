// s4-runtime // containers/unique_vector.h
// A vector that maintains uniqueness via a backing set.
// Provides O(1) lookup with deterministic iteration order.
//
// Complexity:
//   - push_back: O(1) amortized
//   - contains/has: O(1)
//   - erase: O(n) - must scan vector to remove element
//   - iteration: O(n), deterministic insertion order
//
// Use when you need both fast membership tests and stable iteration order.
// If you don't need ordered iteration, prefer std::unordered_set.
#pragma once

#include <s4/core/exceptions.h>

#include <algorithm>
#include <functional>
#include <initializer_list>
#include <iterator>
#include <sstream>
#include <unordered_set>
#include <vector>

namespace s4::containers {

// Vector-like container that prevents duplicate entries.
// Maintains insertion order while providing O(1) membership tests.
//
// Invariants:
// - vector_.size() == set_.size()
// - For all i: set_.contains(vector_[i])
// - No duplicates in vector_
template <typename T, typename Hash = std::hash<T>, typename Equal = std::equal_to<T>>
class unique_vector final {
public:
  using value_type = T;
  using size_type = std::size_t;
  using difference_type = std::ptrdiff_t;
  using reference = T&;
  using const_reference = const T&;
  using pointer = T*;
  using const_pointer = const T*;
  using iterator = typename std::vector<T>::iterator;
  using const_iterator = typename std::vector<T>::const_iterator;
  using reverse_iterator = typename std::vector<T>::reverse_iterator;
  using const_reverse_iterator = typename std::vector<T>::const_reverse_iterator;

  unique_vector() = default;

  unique_vector(std::initializer_list<T> init)
      : unique_vector(init.begin(), init.end()) {}

  unique_vector(const unique_vector& other) = default;
  unique_vector(unique_vector&& other) noexcept = default;
  unique_vector& operator=(const unique_vector& other) = default;
  unique_vector& operator=(unique_vector&& other) noexcept = default;

  template <typename InputIt>
  unique_vector(InputIt first, InputIt last) {
    push_back(first, last);
  }

  template <typename Container>
  explicit unique_vector(const Container& container)
      : unique_vector(std::begin(container), std::end(container)) {}

  // Insert a single element. Returns true if inserted, false if duplicate.
  [[nodiscard]] auto push_back(const T& entry) -> bool {
    if (set_.emplace(entry).second) {
      vector_.push_back(entry);
      return true;
    }
    return false;
  }

  [[nodiscard]] auto push_back(T&& entry) -> bool {
    if (set_.emplace(entry).second) {
      vector_.push_back(std::move(entry));
      return true;
    }
    return false;
  }

  // Insert range of elements. Returns true if any were inserted.
  template <typename InputIt>
  [[nodiscard]] auto push_back(InputIt first, InputIt last) -> bool {
    bool any_added = false;
    while (first != last) {
      any_added |= push_back(*first++);
    }
    return any_added;
  }

  // Insert all elements from another unique_vector.
  [[nodiscard]] auto push_back(const unique_vector& other) -> bool {
    return push_back(other.begin(), other.end());
  }

  // Compute intersection preserving this container's order.
  [[nodiscard]] auto intersect(const unique_vector& other) const -> unique_vector {
    unique_vector result;
    for (const auto& entry : vector_) {
      if (other.contains(entry)) {
        result.push_back(entry);
      }
    }
    return result;
  }

  // Check if any element exists in both containers.
  [[nodiscard]] auto has_intersection(const unique_vector& other) const -> bool {
    return std::any_of(vector_.begin(), vector_.end(),
                       [&](const auto& e) { return other.contains(e); });
  }

  // Compute set difference (elements in this but not in other).
  [[nodiscard]] auto subtract(const unique_vector& other) const -> unique_vector {
    unique_vector result;
    for (const auto& entry : vector_) {
      if (!other.contains(entry)) {
        result.push_back(entry);
      }
    }
    return result;
  }

  // Compute union of both containers.
  [[nodiscard]] auto unite(const unique_vector& other) const -> unique_vector {
    unique_vector result(*this);
    result.push_back(other);
    return result;
  }

  // Access underlying vector for iteration.
  [[nodiscard]] auto vector() const noexcept -> const std::vector<T>& {
    return vector_;
  }

  [[nodiscard]] auto set() const noexcept 
      -> const std::unordered_set<T, Hash, Equal>& {
    return set_;
  }

  [[nodiscard]] auto operator==(const unique_vector& other) const -> bool {
    return vector_ == other.vector_;
  }

  [[nodiscard]] auto operator!=(const unique_vector& other) const -> bool {
    return !(*this == other);
  }

  [[nodiscard]] auto front() const -> const T& {
    S4_DEBUG_ERROR(!empty(), "front() on empty unique_vector");
    return vector_.front();
  }

  [[nodiscard]] auto back() const -> const T& {
    S4_DEBUG_ERROR(!empty(), "back() on empty unique_vector");
    return vector_.back();
  }

  auto pop_back() -> T {
    S4_DEBUG_ERROR(!empty(), "pop_back() on empty unique_vector");
    T v = std::move(vector_.back());
    set_.erase(v);
    vector_.pop_back();
    return v;
  }

  [[nodiscard]] auto empty() const noexcept -> bool { return vector_.empty(); }

  auto clear() noexcept -> void {
    vector_.clear();
    set_.clear();
  }

  [[nodiscard]] auto size() const noexcept -> size_type { return vector_.size(); }

  [[nodiscard]] auto contains(const T& entry) const -> bool {
    return set_.find(entry) != set_.end();
  }

  // Alias for contains() for compatibility.
  [[nodiscard]] auto has(const T& entry) const -> bool { return contains(entry); }

  auto erase(const T& entry) -> size_type {
    vector_.erase(std::remove(vector_.begin(), vector_.end(), entry),
                  vector_.end());
    return set_.erase(entry);
  }

  template <typename InputIt>
  auto insert(InputIt begin_it, InputIt end_it) -> void {
    push_back(begin_it, end_it);
  }

  // Iterators.
  [[nodiscard]] auto begin() noexcept -> iterator { return vector_.begin(); }
  [[nodiscard]] auto end() noexcept -> iterator { return vector_.end(); }
  [[nodiscard]] auto begin() const noexcept -> const_iterator { return vector_.begin(); }
  [[nodiscard]] auto end() const noexcept -> const_iterator { return vector_.end(); }
  [[nodiscard]] auto cbegin() const noexcept -> const_iterator { return vector_.cbegin(); }
  [[nodiscard]] auto cend() const noexcept -> const_iterator { return vector_.cend(); }
  [[nodiscard]] auto rbegin() noexcept -> reverse_iterator { return vector_.rbegin(); }
  [[nodiscard]] auto rend() noexcept -> reverse_iterator { return vector_.rend(); }
  [[nodiscard]] auto rbegin() const noexcept -> const_reverse_iterator { return vector_.rbegin(); }
  [[nodiscard]] auto rend() const noexcept -> const_reverse_iterator { return vector_.rend(); }

  [[nodiscard]] auto at(size_type pos) -> T& { return vector_.at(pos); }
  [[nodiscard]] auto at(size_type pos) const -> const T& { return vector_.at(pos); }
  [[nodiscard]] auto operator[](size_type pos) -> T& { return vector_[pos]; }
  [[nodiscard]] auto operator[](size_type pos) const -> const T& { return vector_[pos]; }

  [[nodiscard]] auto to_string() const -> std::string {
    std::ostringstream ss;
    ss << "{ ";
    bool first = true;
    for (const auto& entry : vector_) {
      if (!first) ss << ", ";
      ss << entry;
      first = false;
    }
    ss << " }";
    return ss.str();
  }

private:
  std::vector<T> vector_;
  std::unordered_set<T, Hash, Equal> set_;
};

// Deduction guide.
template <typename T>
unique_vector(std::initializer_list<T>) -> unique_vector<T>;

}  // namespace s4::containers
