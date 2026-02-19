// s4-runtime // traits/traits.h
// Type traits and concepts for GPU inference programming.
#pragma once

#include <concepts>
#include <cstddef>
#include <cstdint>
#include <sstream>
#include <string>
#include <type_traits>

namespace s4::traits {

// NonCopyable mixin - suppress copy and move operations.
class non_copyable {
public:
  non_copyable() = default;
  non_copyable(const non_copyable&) = delete;
  non_copyable& operator=(const non_copyable&) = delete;
  non_copyable(non_copyable&&) = delete;
  non_copyable& operator=(non_copyable&&) = delete;
};

// NonMovable mixin - suppress move but allow copy.
class non_movable {
public:
  non_movable() = default;
  non_movable(const non_movable&) = default;
  non_movable& operator=(const non_movable&) = default;
  non_movable(non_movable&&) = delete;
  non_movable& operator=(non_movable&&) = delete;
};

// Polymorphic base with runtime type checking.
class polymorphic_base {
public:
  virtual ~polymorphic_base() = default;

  // Safe downcasting: ptr->as<Derived>().
  template <typename T>
  [[nodiscard]] auto as() -> T* {
#ifdef NDEBUG
    return static_cast<T*>(this);
#else
    auto* ptr = dynamic_cast<T*>(this);
    if (ptr == nullptr) {
      // In debug mode, we could throw or assert.
      // For now, return nullptr for safety.
    }
    return ptr;
#endif
  }

  template <typename T>
  [[nodiscard]] auto as() const -> const T* {
#ifdef NDEBUG
    return static_cast<const T*>(this);
#else
    auto* ptr = dynamic_cast<const T*>(this);
    return ptr;
#endif
  }

  // Runtime type check: node->is<T>().
  template <typename T>
  [[nodiscard]] auto is() const -> bool {
    return dynamic_cast<const T*>(this) != nullptr;
  }

  // Strict type check (not derived classes).
  template <typename T>
  [[nodiscard]] auto is_strictly() const -> bool {
    return typeid(*this) == typeid(T);
  }

  // Check if type is one of several types.
  template <typename... Ts>
  [[nodiscard]] auto is_one_of() const -> bool {
    return (is<Ts>() || ...);
  }

  template <typename... Ts>
  [[nodiscard]] auto is_strictly_one_of() const -> bool {
    return (is_strictly<Ts>() || ...);
  }
};

// Concept: Type has a toString() method.
template <typename T>
concept has_to_string = requires(const T& t) {
  { t.toString() } -> std::convertible_to<std::string>;
};

// Concept: Type has a to_string() method.
template <typename T>
concept has_to_string_snake = requires(const T& t) {
  { t.to_string() } -> std::convertible_to<std::string>;
};

// Concept: Type is streamable to std::ostream.
template <typename T>
concept streamable = requires(std::ostream& os, const T& t) {
  { os << t } -> std::same_as<std::ostream&>;
};

// Universal to_string that works with multiple conventions.
template <typename T>
[[nodiscard]] auto to_string_universal(const T& value) -> std::string {
  if constexpr (has_to_string<T>) {
    if constexpr (std::is_pointer_v<T>) {
      return value->toString();
    } else {
      return value.toString();
    }
  } else if constexpr (has_to_string_snake<T>) {
    if constexpr (std::is_pointer_v<T>) {
      return value->to_string();
    } else {
      return value.to_string();
    }
  } else if constexpr (streamable<T>) {
    std::ostringstream ss;
    ss << value;
    return ss.str();
  } else {
    return "<value>";
  }
}

// Concept: Type is a power of two size.
template <typename T>
concept power_of_two_size = (sizeof(T) & (sizeof(T) - 1)) == 0;

// Concept: Type is trivially copyable (safe for GPU memcpy).
template <typename T>
concept gpu_safe = std::is_trivially_copyable_v<T>;

// Concept: Integral type that fits in 32 bits.
template <typename T>
concept int32_compatible = std::integral<T> && sizeof(T) <= sizeof(std::int32_t);

// Concept: Integral type that fits in 64 bits.
template <typename T>
concept int64_compatible = std::integral<T> && sizeof(T) <= sizeof(std::int64_t);

// Compile-time power of two check.
[[nodiscard]] constexpr auto is_power_of_two(std::size_t n) noexcept -> bool {
  return n != 0 && (n & (n - 1)) == 0;
}

// Compile-time alignment check.
[[nodiscard]] constexpr auto is_aligned(std::size_t value, std::size_t alignment) noexcept 
    -> bool {
  return alignment != 0 && (value % alignment) == 0;
}

// Round up to next multiple.
[[nodiscard]] constexpr auto round_up(std::size_t value, std::size_t multiple) noexcept 
    -> std::size_t {
  if (multiple == 0) return value;
  return ((value + multiple - 1) / multiple) * multiple;
}

// Ceiling division.
[[nodiscard]] constexpr auto ceil_div(std::int64_t dividend, std::int64_t divisor) noexcept 
    -> std::int64_t {
  if (divisor == 0) return 0;
  if (divisor > 0) {
    return (dividend + divisor - 1) / divisor;
  } else {
    return (dividend + divisor + 1) / divisor;
  }
}

// Constexpr pair-based switch helper for enums.
template <typename E>
  requires std::is_enum_v<E>
[[nodiscard]] constexpr auto switch_pair(E e1, E e2) noexcept -> std::uint32_t {
  constexpr std::uint32_t shift = 16;
  return (static_cast<std::uint32_t>(e1) << shift) | 
         static_cast<std::uint32_t>(e2);
}

// Type identity (like std::type_identity but with additional helpers).
template <typename T>
struct identity {
  using type = T;
  
  [[nodiscard]] static constexpr auto size() noexcept -> std::size_t {
    return sizeof(T);
  }
  
  [[nodiscard]] static constexpr auto alignment() noexcept -> std::size_t {
    return alignof(T);
  }
};

// Lazy type evaluation for recursive types.
template <typename F>
struct lazy_type {
  using type = typename F::type;
};

}  // namespace s4::traits
