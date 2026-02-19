// s4-runtime // include/s4/core/generator.h
// C++20 coroutine-based generator for lazy iteration.
// Extracted and adapted from nvfuser.
#pragma once

#include <coroutine>
#include <exception>
#include <functional>
#include <iterator>
#include <optional>
#include <ranges>
#include <type_traits>
#include <utility>

namespace s4::core {

// Helper to store yielded values: references become reference_wrapper.
template <typename T>
using yielded_type = std::conditional_t<
    std::is_reference_v<T>,
    std::reference_wrapper<std::remove_reference_t<T>>,
    T>;

/// A C++20 coroutine-based generator for lazy iteration.
///
/// Usage:
/// ```cpp
/// Generator<int> range(int start, int end) {
///   for (int i = start; i < end; ++i) {
///     co_yield i;
///   }
/// }
///
/// for (int x : range(0, 10)) {
///   std::cout << x << " ";
/// }
/// ```
///
/// Features:
/// - Lazy evaluation: values are computed on demand.
/// - Exception propagation: exceptions thrown during iteration are rethrown.
/// - Reference yielding: can yield references to avoid copies.
/// - Range-compatible: works with std::ranges algorithms.
template <typename T>
class Generator : public std::ranges::view_interface<Generator<T>> {
public:
  struct promise_type;
  using handle_type = std::coroutine_handle<promise_type>;
  using stored_type = yielded_type<T>;

  /// Construct from a coroutine handle.
  explicit Generator(handle_type h) : coroutine_(h) {}

  /// Move constructor.
  Generator(Generator&& other) noexcept : coroutine_(other.coroutine_) {
    other.coroutine_ = nullptr;
  }

  /// Move assignment.
  Generator& operator=(Generator&& other) noexcept {
    if (this != &other) {
      if (coroutine_) {
        coroutine_.destroy();
      }
      coroutine_ = other.coroutine_;
      other.coroutine_ = nullptr;
    }
    return *this;
  }

  /// Destructor destroys the coroutine.
  ~Generator() {
    if (coroutine_) {
      coroutine_.destroy();
    }
  }

  // Non-copyable.
  Generator(const Generator&) = delete;
  Generator& operator=(const Generator&) = delete;

  /// Input iterator for the generator.
  struct iterator {
    using value_type = std::remove_reference_t<T>;
    using reference = T;
    using difference_type = std::ptrdiff_t;
    using iterator_category = std::input_iterator_tag;

    iterator() = default;

    explicit iterator(handle_type h) : coroutine_(h) {
      ++(*this);  // Advance to first element.
    }

    reference operator*() const {
      if constexpr (std::is_reference_v<T>) {
        return value_->get();  // Unwrap reference_wrapper.
      } else {
        return *value_;
      }
    }

    iterator& operator++() {
      coroutine_.resume();
      if (coroutine_.done()) {
        if (coroutine_.promise().exception) {
          std::rethrow_exception(coroutine_.promise().exception);
        }
        value_.reset();
      } else {
        value_ = coroutine_.promise().current_value;
      }
      return *this;
    }

    iterator operator++(int) {
      auto tmp = *this;
      ++(*this);
      return tmp;
    }

    bool operator==(std::default_sentinel_t) const {
      return !value_.has_value();
    }

    bool operator!=(std::default_sentinel_t) const {
      return value_.has_value();
    }

    friend bool operator==(std::default_sentinel_t s, const iterator& it) {
      return it == s;
    }

    friend bool operator!=(std::default_sentinel_t s, const iterator& it) {
      return it != s;
    }

  private:
    handle_type coroutine_ = nullptr;
    std::optional<stored_type> value_;
  };

  iterator begin() const { return iterator{coroutine_}; }
  std::default_sentinel_t end() const { return {}; }

  /// The promise type for the coroutine.
  struct promise_type {
    std::optional<stored_type> current_value;
    std::exception_ptr exception;

    Generator get_return_object() {
      return Generator{handle_type::from_promise(*this)};
    }

    std::suspend_always initial_suspend() { return {}; }
    std::suspend_always final_suspend() noexcept { return {}; }

    std::suspend_always yield_value(T value) {
      if constexpr (std::is_reference_v<T>) {
        current_value = std::ref(value);  // Wrap T& as reference_wrapper.
      } else {
        current_value = std::move(value);
      }
      return {};
    }

    void return_void() {}

    void unhandled_exception() {
      exception = std::current_exception();
    }
  };

private:
  handle_type coroutine_;
};

/// Create a generator from a range (useful for testing/examples).
template <std::ranges::range R>
Generator<std::ranges::range_value_t<R>> from_range(R&& range) {
  for (auto&& elem : std::forward<R>(range)) {
    co_yield elem;
  }
}

/// Create a generator that yields integers in [start, end).
inline Generator<int64_t> iota(int64_t start, int64_t end) {
  for (int64_t i = start; i < end; ++i) {
    co_yield i;
  }
}

/// Create a generator that yields integers in [0, n).
inline Generator<int64_t> iota(int64_t n) {
  return iota(0, n);
}

/// Filter a generator with a predicate.
template <typename T, typename Pred>
Generator<T> filter(Generator<T> gen, Pred pred) {
  for (auto&& elem : gen) {
    if (pred(elem)) {
      co_yield elem;
    }
  }
}

/// Map a function over a generator.
template <typename T, typename Func>
Generator<std::invoke_result_t<Func, T>> map(Generator<T> gen, Func func) {
  for (auto&& elem : gen) {
    co_yield func(elem);
  }
}

/// Take the first n elements from a generator.
template <typename T>
Generator<T> take(Generator<T> gen, std::size_t n) {
  std::size_t count = 0;
  for (auto&& elem : gen) {
    if (count >= n) break;
    co_yield elem;
    ++count;
  }
}

}  // namespace s4::core
