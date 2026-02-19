// s4-runtime // dtypes/dispatch.h
// Runtime dispatch based on dtype codes.
#pragma once

#include <s4/dtypes/dtype.h>
#include <s4/core/exceptions.h>

#include <cstdint>
#include <type_traits>
#include <utility>

// Forward declare CUDA types if available.
#if defined(__CUDACC__) || defined(__CUDA__)
#include <cuda_bf16.h>
#include <cuda_fp16.h>
#include <cuda_fp8.h>
#endif

namespace s4::dtypes {

// Type tag for compile-time type dispatch.
template <typename T>
struct type_tag final {
  using type = T;
};

// Placeholder for unsupported/invalid types.
struct invalid_type final {};

// CUDA-compatible type aliases.
#if defined(__CUDACC__) || defined(__CUDA__)
using float16 = __half;
using bfloat16 = __nv_bfloat16;
using float8_e4m3 = __nv_fp8_e4m3;
using float8_e5m2 = __nv_fp8_e5m2;
#else
// CPU placeholders when CUDA is not available.
struct float16 { std::uint16_t bits; };
struct bfloat16 { std::uint16_t bits; };
struct float8_e4m3 { std::uint8_t bits; };
struct float8_e5m2 { std::uint8_t bits; };
#endif

// Trait to get dtype_code from C++ type.
template <typename T>
struct dtype_of {
  static constexpr dtype_code value = dtype_code::invalid;
};

#define S4_DTYPE_TRAIT(TYPE, CODE) \
  template <> struct dtype_of<TYPE> { static constexpr dtype_code value = dtype_code::CODE; }

S4_DTYPE_TRAIT(float16, float16);
S4_DTYPE_TRAIT(bfloat16, bfloat16);
S4_DTYPE_TRAIT(float, float32);
S4_DTYPE_TRAIT(double, float64);
S4_DTYPE_TRAIT(float8_e4m3, float8_e4m3);
S4_DTYPE_TRAIT(float8_e5m2, float8_e5m2);
S4_DTYPE_TRAIT(std::int8_t, int8);
S4_DTYPE_TRAIT(std::int16_t, int16);
S4_DTYPE_TRAIT(std::int32_t, int32);
S4_DTYPE_TRAIT(std::int64_t, int64);
S4_DTYPE_TRAIT(std::uint8_t, uint8);
S4_DTYPE_TRAIT(std::uint16_t, uint16);
S4_DTYPE_TRAIT(std::uint32_t, uint32);
S4_DTYPE_TRAIT(std::uint64_t, uint64);
S4_DTYPE_TRAIT(bool, boolean);

#undef S4_DTYPE_TRAIT

template <typename T>
inline constexpr dtype_code dtype_of_v = dtype_of<T>::value;

// Dispatch to a functor based on runtime dtype_code.
// The functor receives a type_tag<T> where T is the corresponding C++ type.
//
// Usage:
//   dispatch_dtype(code, [&](auto tag) {
//     using element_type = typename decltype(tag)::type;
//     // ... use element_type ...
//   });
template <typename Functor>
auto dispatch_dtype(dtype_code code, Functor&& functor) -> decltype(auto) {
  switch (code) {
    case dtype_code::float16:
      return std::forward<Functor>(functor)(type_tag<float16>{});
    case dtype_code::bfloat16:
      return std::forward<Functor>(functor)(type_tag<bfloat16>{});
    case dtype_code::float32:
      return std::forward<Functor>(functor)(type_tag<float>{});
    case dtype_code::float64:
      return std::forward<Functor>(functor)(type_tag<double>{});
    case dtype_code::float8_e4m3:
      return std::forward<Functor>(functor)(type_tag<float8_e4m3>{});
    case dtype_code::float8_e5m2:
      return std::forward<Functor>(functor)(type_tag<float8_e5m2>{});
    case dtype_code::int8:
      return std::forward<Functor>(functor)(type_tag<std::int8_t>{});
    case dtype_code::int16:
      return std::forward<Functor>(functor)(type_tag<std::int16_t>{});
    case dtype_code::int32:
      return std::forward<Functor>(functor)(type_tag<std::int32_t>{});
    case dtype_code::int64:
      return std::forward<Functor>(functor)(type_tag<std::int64_t>{});
    case dtype_code::uint8:
      return std::forward<Functor>(functor)(type_tag<std::uint8_t>{});
    case dtype_code::uint16:
      return std::forward<Functor>(functor)(type_tag<std::uint16_t>{});
    case dtype_code::uint32:
      return std::forward<Functor>(functor)(type_tag<std::uint32_t>{});
    case dtype_code::uint64:
      return std::forward<Functor>(functor)(type_tag<std::uint64_t>{});
    case dtype_code::boolean:
      return std::forward<Functor>(functor)(type_tag<bool>{});
    default:
      return std::forward<Functor>(functor)(type_tag<invalid_type>{});
  }
}

// Dispatch only for floating point types.
template <typename Functor>
auto dispatch_float_dtype(dtype_code code, Functor&& functor) -> decltype(auto) {
  switch (code) {
    case dtype_code::float16:
      return std::forward<Functor>(functor)(type_tag<float16>{});
    case dtype_code::bfloat16:
      return std::forward<Functor>(functor)(type_tag<bfloat16>{});
    case dtype_code::float32:
      return std::forward<Functor>(functor)(type_tag<float>{});
    case dtype_code::float64:
      return std::forward<Functor>(functor)(type_tag<double>{});
    case dtype_code::float8_e4m3:
      return std::forward<Functor>(functor)(type_tag<float8_e4m3>{});
    case dtype_code::float8_e5m2:
      return std::forward<Functor>(functor)(type_tag<float8_e5m2>{});
    default:
      return std::forward<Functor>(functor)(type_tag<invalid_type>{});
  }
}

// Dispatch for common compute dtypes (fp16, bf16, fp32).
template <typename Functor>
auto dispatch_compute_dtype(dtype_code code, Functor&& functor) -> decltype(auto) {
  switch (code) {
    case dtype_code::float16:
      return std::forward<Functor>(functor)(type_tag<float16>{});
    case dtype_code::bfloat16:
      return std::forward<Functor>(functor)(type_tag<bfloat16>{});
    case dtype_code::float32:
      return std::forward<Functor>(functor)(type_tag<float>{});
    default:
      return std::forward<Functor>(functor)(type_tag<invalid_type>{});
  }
}

// Multi-dtype dispatch for operations involving two types.
template <typename Functor>
auto dispatch_dtype_pair(dtype_code code1, dtype_code code2, Functor&& functor) 
    -> decltype(auto) {
  return dispatch_dtype(code1, [&](auto tag1) {
    return dispatch_dtype(code2, [&](auto tag2) {
      return std::forward<Functor>(functor)(tag1, tag2);
    });
  });
}

// Check if a type_tag represents a valid type.
template <typename T>
constexpr bool is_valid_type_tag_v = !std::is_same_v<T, invalid_type>;

// SFINAE helper for valid type tags.
template <typename Tag>
using require_valid_type = std::enable_if_t<
    is_valid_type_tag_v<typename Tag::type>, bool>;

}  // namespace s4::dtypes
