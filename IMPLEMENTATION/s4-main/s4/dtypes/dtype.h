// s4-runtime // dtypes/dtype.h
// Stable, serializable data type vocabulary for GPU inference.
#pragma once

#include <cstddef>
#include <cstdint>
#include <optional>
#include <string_view>
#include <type_traits>

namespace s4::dtypes {

// Stable dtype enumeration for serialization.
// Values are explicit and stable across versions.
enum class dtype_code : std::uint32_t {
  invalid = 0,

  // Standard IEEE-ish floating point.
  float16 = 1,
  bfloat16 = 2,
  float32 = 3,
  float64 = 4,

  // FP8 variants.
  float8_e4m3 = 10,
  float8_e5m2 = 11,

  // FP4 packed formats (2 logical elements per byte).
  nvfp4_e2m1_packed = 20,
  
  // Integer types.
  int8 = 30,
  int16 = 31,
  int32 = 32,
  int64 = 33,
  
  uint8 = 40,
  uint16 = 41,
  uint32 = 42,
  uint64 = 43,
  
  // Boolean.
  boolean = 50,
};

// Comprehensive dtype description for runtime introspection.
struct dtype_description final {
  dtype_code code = dtype_code::invalid;
  const char* name = "invalid";
  
  // Size/alignment of the storage unit in bytes.
  std::size_t storage_size_bytes = 0;
  std::size_t storage_alignment_bytes = 0;
  
  // Is this a packed format?
  bool is_packed = false;
  
  // For packed formats, logical elements per storage unit.
  std::int32_t logical_elements_per_storage_unit = 1;
  
  // Is this a floating point type?
  bool is_floating_point = false;
  
  // Is this a signed type?
  bool is_signed = false;
  
  // Number of bits for exponent/mantissa (for floating point).
  std::int32_t exponent_bits = 0;
  std::int32_t mantissa_bits = 0;
};

// Get description for a dtype code.
[[nodiscard]] constexpr auto describe(dtype_code code) noexcept -> dtype_description {
  switch (code) {
    case dtype_code::float16:
      return {code, "float16", 2, 2, false, 1, true, true, 5, 10};
    case dtype_code::bfloat16:
      return {code, "bfloat16", 2, 2, false, 1, true, true, 8, 7};
    case dtype_code::float32:
      return {code, "float32", 4, 4, false, 1, true, true, 8, 23};
    case dtype_code::float64:
      return {code, "float64", 8, 8, false, 1, true, true, 11, 52};
    case dtype_code::float8_e4m3:
      return {code, "float8_e4m3", 1, 1, false, 1, true, true, 4, 3};
    case dtype_code::float8_e5m2:
      return {code, "float8_e5m2", 1, 1, false, 1, true, true, 5, 2};
    case dtype_code::nvfp4_e2m1_packed:
      return {code, "nvfp4_e2m1_packed", 1, 1, true, 2, true, true, 2, 1};
    case dtype_code::int8:
      return {code, "int8", 1, 1, false, 1, false, true, 0, 0};
    case dtype_code::int16:
      return {code, "int16", 2, 2, false, 1, false, true, 0, 0};
    case dtype_code::int32:
      return {code, "int32", 4, 4, false, 1, false, true, 0, 0};
    case dtype_code::int64:
      return {code, "int64", 8, 8, false, 1, false, true, 0, 0};
    case dtype_code::uint8:
      return {code, "uint8", 1, 1, false, 1, false, false, 0, 0};
    case dtype_code::uint16:
      return {code, "uint16", 2, 2, false, 1, false, false, 0, 0};
    case dtype_code::uint32:
      return {code, "uint32", 4, 4, false, 1, false, false, 0, 0};
    case dtype_code::uint64:
      return {code, "uint64", 8, 8, false, 1, false, false, 0, 0};
    case dtype_code::boolean:
      return {code, "boolean", 1, 1, false, 1, false, false, 0, 0};
    default:
      return {};
  }
}

// Convenience accessors.
[[nodiscard]] constexpr auto storage_size_bytes(dtype_code code) noexcept -> std::size_t {
  return describe(code).storage_size_bytes;
}

[[nodiscard]] constexpr auto storage_alignment_bytes(dtype_code code) noexcept -> std::size_t {
  return describe(code).storage_alignment_bytes;
}

[[nodiscard]] constexpr auto is_packed(dtype_code code) noexcept -> bool {
  return describe(code).is_packed;
}

[[nodiscard]] constexpr auto logical_elements_per_storage_unit(dtype_code code) noexcept 
    -> std::int32_t {
  return describe(code).logical_elements_per_storage_unit;
}

[[nodiscard]] constexpr auto is_floating_point(dtype_code code) noexcept -> bool {
  return describe(code).is_floating_point;
}

[[nodiscard]] constexpr auto is_signed(dtype_code code) noexcept -> bool {
  return describe(code).is_signed;
}

[[nodiscard]] constexpr auto name(dtype_code code) noexcept -> const char* {
  return describe(code).name;
}

// Try to parse a dtype from string.
[[nodiscard]] constexpr auto from_string(std::string_view str) noexcept 
    -> std::optional<dtype_code> {
  // List all known dtypes for parsing.
  constexpr dtype_code all_codes[] = {
    dtype_code::float16, dtype_code::bfloat16, dtype_code::float32, dtype_code::float64,
    dtype_code::float8_e4m3, dtype_code::float8_e5m2,
    dtype_code::nvfp4_e2m1_packed,
    dtype_code::int8, dtype_code::int16, dtype_code::int32, dtype_code::int64,
    dtype_code::uint8, dtype_code::uint16, dtype_code::uint32, dtype_code::uint64,
    dtype_code::boolean,
  };
  
  for (dtype_code code : all_codes) {
    if (str == name(code)) {
      return code;
    }
  }
  return std::nullopt;
}

// Compute storage bytes for a given number of logical elements.
[[nodiscard]] inline auto try_compute_storage_bytes(
    dtype_code code, std::size_t logical_element_count,
    std::size_t* out_storage_bytes) noexcept -> bool {
  
  if (out_storage_bytes == nullptr) return false;
  
  const auto desc = describe(code);
  if (desc.storage_size_bytes == 0 || desc.logical_elements_per_storage_unit <= 0) {
    return false;
  }
  
  if (!desc.is_packed) {
    // Overflow check.
    const std::size_t max_safe = static_cast<std::size_t>(-1) / desc.storage_size_bytes;
    if (logical_element_count > max_safe) return false;
    
    *out_storage_bytes = logical_element_count * desc.storage_size_bytes;
    return true;
  }
  
  // Packed case: ceil(logical / elements_per_unit) * storage_size.
  const auto elements_per_unit = 
      static_cast<std::size_t>(desc.logical_elements_per_storage_unit);
  const std::size_t unit_count =
      (logical_element_count + elements_per_unit - 1) / elements_per_unit;
  
  const std::size_t max_safe = static_cast<std::size_t>(-1) / desc.storage_size_bytes;
  if (unit_count > max_safe) return false;
  
  *out_storage_bytes = unit_count * desc.storage_size_bytes;
  return true;
}

// Compute logical element count from storage bytes.
[[nodiscard]] inline auto try_compute_logical_elements(
    dtype_code code, std::size_t storage_bytes,
    std::size_t* out_logical_elements) noexcept -> bool {
  
  if (out_logical_elements == nullptr) return false;
  
  const auto desc = describe(code);
  if (desc.storage_size_bytes == 0) return false;
  
  const std::size_t storage_units = storage_bytes / desc.storage_size_bytes;
  *out_logical_elements = storage_units * 
      static_cast<std::size_t>(desc.logical_elements_per_storage_unit);
  return true;
}

// Alias for try_compute_storage_bytes (compatibility).
[[nodiscard]] inline auto try_compute_storage_bytes_for_logical_elements(
    dtype_code code, std::size_t logical_element_count,
    std::size_t* out_storage_bytes) noexcept -> bool {
  return try_compute_storage_bytes(code, logical_element_count, out_storage_bytes);
}

}  // namespace s4::dtypes
