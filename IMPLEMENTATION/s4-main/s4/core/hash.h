// s4-runtime // include/s4/core/hash.h
// Hash utilities for combining hash values.
#pragma once

#include <cstddef>
#include <functional>
#include <type_traits>
#include <tuple>

namespace s4::core {

/// Combine an existing hash with a new hash value.
/// Inspired by boost::hash_combine.
/// See https://stackoverflow.com/q/35985960
inline void hash_combine(std::size_t& seed, std::size_t new_hash) noexcept {
  seed ^= new_hash + 0x9e3779b9 + (seed << 6) + (seed >> 2);
}

/// Combine multiple values into a hash.
template <typename T, typename... Rest>
inline void hash_combine(std::size_t& seed, const T& v, const Rest&... rest) {
  hash_combine(seed, std::hash<T>{}(v));
  if constexpr (sizeof...(rest) > 0) {
    hash_combine(seed, rest...);
  }
}

/// Compute combined hash for multiple values.
template <typename... Args>
[[nodiscard]] inline std::size_t combined_hash(const Args&... args) {
  std::size_t seed = 0;
  hash_combine(seed, args...);
  return seed;
}

/// Hash a range of elements.
template <typename Iterator>
[[nodiscard]] inline std::size_t hash_range(Iterator begin, Iterator end) {
  std::size_t seed = 0;
  for (auto it = begin; it != end; ++it) {
    hash_combine(seed, std::hash<std::remove_cvref_t<decltype(*it)>>{}(*it));
  }
  return seed;
}

/// Hash a container.
template <typename Container>
[[nodiscard]] inline std::size_t hash_container(const Container& c) {
  return hash_range(std::begin(c), std::end(c));
}

/// Hasher for pairs.
template <typename T1, typename T2>
struct pair_hash {
  std::size_t operator()(const std::pair<T1, T2>& p) const noexcept {
    return combined_hash(p.first, p.second);
  }
};

/// Hasher for tuples.
template <typename... Args>
struct tuple_hash {
  std::size_t operator()(const std::tuple<Args...>& t) const noexcept {
    return hash_impl(t, std::index_sequence_for<Args...>{});
  }

private:
  template <std::size_t... Is>
  static std::size_t hash_impl(const std::tuple<Args...>& t,
                                std::index_sequence<Is...>) {
    return combined_hash(std::get<Is>(t)...);
  }
};

}  // namespace s4::core
