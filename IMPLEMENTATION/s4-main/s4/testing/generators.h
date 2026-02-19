// s4-runtime // testing/generators.h
// Property-based testing generators for RapidCheck.
#pragma once

#include <s4/dtypes/dtype.h>
#include <s4/containers/unique_vector.h>
#include <s4/containers/disjoint_sets.h>

#include <rapidcheck.h>

#include <cmath>
#include <limits>
#include <random>
#include <vector>

namespace s4::testing {

// Generator for valid dtype codes.
inline auto gen_dtype_code() -> rc::Gen<dtypes::dtype_code> {
  return rc::gen::element(
      dtypes::dtype_code::float16,
      dtypes::dtype_code::bfloat16,
      dtypes::dtype_code::float32,
      dtypes::dtype_code::float64,
      dtypes::dtype_code::float8_e4m3,
      dtypes::dtype_code::float8_e5m2,
      dtypes::dtype_code::int8,
      dtypes::dtype_code::int16,
      dtypes::dtype_code::int32,
      dtypes::dtype_code::int64,
      dtypes::dtype_code::uint8,
      dtypes::dtype_code::uint16,
      dtypes::dtype_code::uint32,
      dtypes::dtype_code::uint64,
      dtypes::dtype_code::boolean
  );
}

// Generator for floating point dtype codes only.
inline auto gen_float_dtype_code() -> rc::Gen<dtypes::dtype_code> {
  return rc::gen::element(
      dtypes::dtype_code::float16,
      dtypes::dtype_code::bfloat16,
      dtypes::dtype_code::float32,
      dtypes::dtype_code::float64
  );
}

// Generator for compute dtype codes (common inference types).
inline auto gen_compute_dtype_code() -> rc::Gen<dtypes::dtype_code> {
  return rc::gen::element(
      dtypes::dtype_code::float16,
      dtypes::dtype_code::bfloat16,
      dtypes::dtype_code::float32
  );
}

// Generator for power-of-two alignments.
inline auto gen_alignment() -> rc::Gen<std::size_t> {
  return rc::gen::map(
      rc::gen::inRange(0, 8),
      [](int exp) -> std::size_t { return std::size_t{1} << exp; }
  );
}

// Generator for reasonable tensor dimensions.
inline auto gen_dim(std::int64_t max_dim = 4096) -> rc::Gen<std::int64_t> {
  return rc::gen::inRange<std::int64_t>(1, max_dim);
}

// Generator for tensor shapes (1D to 4D).
inline auto gen_shape(std::size_t max_rank = 4, std::int64_t max_dim = 256)
    -> rc::Gen<std::vector<std::int64_t>> {
  return rc::gen::withSize([max_rank, max_dim](int size) {
    std::size_t rank = std::min(max_rank, static_cast<std::size_t>(size % 4 + 1));
    return rc::gen::container<std::vector<std::int64_t>>(
        rank, gen_dim(max_dim));
  });
}

// Generator for unique vectors of integers.
template <typename T = int>
inline auto gen_unique_vector(std::size_t max_size = 100)
    -> rc::Gen<containers::unique_vector<T>> {
  return rc::gen::map(
      rc::gen::container<std::vector<T>>(
          rc::gen::inRange<std::size_t>(0, max_size),
          rc::gen::arbitrary<T>()),
      [](std::vector<T> vec) {
        containers::unique_vector<T> result;
        for (const auto& v : vec) {
          result.push_back(v);
        }
        return result;
      }
  );
}

// Generator for valid byte counts (respecting alignment).
inline auto gen_byte_count(std::size_t max_bytes = 1 << 20) 
    -> rc::Gen<std::size_t> {
  return rc::gen::inRange<std::size_t>(0, max_bytes);
}

// Generator for element counts that won't overflow.
inline auto gen_element_count(dtypes::dtype_code dtype, 
                               std::size_t max_elements = 1 << 20)
    -> rc::Gen<std::size_t> {
  return rc::gen::inRange<std::size_t>(0, max_elements);
}

// Generator for float values (handles special cases).
inline auto gen_float(float min_val = -1e6f, float max_val = 1e6f) 
    -> rc::Gen<float> {
  return rc::gen::oneOf(
      // Normal values.
      rc::gen::map(
          rc::gen::inRange<int>(-1000000, 1000000),
          [min_val, max_val](int i) {
            float t = (i + 1000000.0f) / 2000000.0f;
            return min_val + t * (max_val - min_val);
          }),
      // Special values (less frequent).
      rc::gen::element(0.0f, -0.0f, 1.0f, -1.0f)
  );
}

// Generator for float values including special cases.
inline auto gen_float_with_special() -> rc::Gen<float> {
  return rc::gen::oneOf(
      gen_float(),
      rc::gen::element(
          std::numeric_limits<float>::infinity(),
          -std::numeric_limits<float>::infinity(),
          std::numeric_limits<float>::quiet_NaN(),
          std::numeric_limits<float>::min(),
          std::numeric_limits<float>::max(),
          std::numeric_limits<float>::denorm_min()
      )
  );
}

// Generator for pairs of related values (for testing mappings).
template <typename T>
inline auto gen_pair() -> rc::Gen<std::pair<T, T>> {
  return rc::gen::pair(rc::gen::arbitrary<T>(), rc::gen::arbitrary<T>());
}

// Generator for allocation scenarios.
struct allocation_scenario {
  std::size_t capacity;
  std::vector<std::pair<std::size_t, std::size_t>> requests;  // (size, alignment)
};

inline auto gen_allocation_scenario(std::size_t max_capacity = 1 << 20,
                                     std::size_t max_requests = 100)
    -> rc::Gen<allocation_scenario> {
  return rc::gen::apply(
      [](std::size_t capacity, 
         std::vector<std::pair<std::size_t, std::size_t>> requests) {
        return allocation_scenario{capacity, requests};
      },
      rc::gen::inRange<std::size_t>(1, max_capacity),
      rc::gen::container<std::vector<std::pair<std::size_t, std::size_t>>>(
          rc::gen::inRange<std::size_t>(1, max_requests),
          rc::gen::pair(
              gen_byte_count(1 << 16),
              gen_alignment()
          )
      )
  );
}

// Property: a predicate that should hold for all generated values.
// Returns std::nullopt on success, or an error message on failure.
template <typename T>
using property = std::function<std::optional<std::string>(const T&)>;

// Helper to run a property check with custom message.
template <typename T>
inline auto check_property(const T& value, property<T> prop) -> bool {
  auto result = prop(value);
  if (result.has_value()) {
    RC_FAIL(*result);
    return false;
  }
  return true;
}

}  // namespace s4::testing
