// s4 // cuda/nvfp4/nvfp4.cuh
// NVFP4 (E2M1) quantization primitives for Blackwell (SM100+).
//
// Key features:
//   - Vectorized float2 loads for coalesced memory access
//   - 8 fp32 → 4 bytes PTX packing (pack_fp32x8_to_e2m1x8)
//   - SA3-compatible 128-token permutation
//   - SA3-compatible 64×16 scale factor swizzle
//
// E2M1 format: sign(1) | exponent(2) | mantissa(1)
//   - Exponent bias = 1
//   - exp=0, mant=0 → 0.0
//   - exp=0, mant=1 → 0.5 (subnormal)
//   - exp>0 → (1 + mant/2) × 2^(exp-1)
//   - Positive values: {0, 0.5, 1, 1.5, 2, 3, 4, 6}
#pragma once

#include <cuda_runtime.h>
#include <cuda_bf16.h>
#include <cuda_fp16.h>
#include <cuda_fp8.h>

#include <cstdint>

namespace s4::quantization::nvfp4 {

// ============================================================================
// Constants
// ============================================================================

// Block size for per-block scaling (16 elements per scale factor).
inline constexpr int block_size = 16;

// E2M1 maximum representable value.
inline constexpr float e2m1_max_value = 6.0f;

// Reciprocal of max value for scale computation.
inline constexpr float e2m1_rcp_max = 1.0f / 6.0f;

// FP8 E4M3 maximum finite value (for clamping).
inline constexpr float fp8_e4m3_max_finite = 448.0f;

// ============================================================================
// Scale layout enumeration
// ============================================================================

enum class scale_layout : std::uint8_t {
  linear = 0,           // Contiguous row-major scales.
  sa3_64x16_swizzle = 1 // SA3 kernel's 64×16 tile swizzle.
};

// ============================================================================
// FP8 E4M3 helpers
// ============================================================================

__device__ __forceinline__ auto clamp_to_fp8_range(float value) noexcept -> float {
  if (!isfinite(value)) return 0.0f;
  return fminf(fmaxf(value, 0.0f), fp8_e4m3_max_finite);
}

__device__ __forceinline__ auto fp8_e4m3_to_bits(float value) noexcept -> std::uint8_t {
  __nv_fp8_e4m3 const fp8 = __nv_fp8_e4m3(value);
  return *reinterpret_cast<const std::uint8_t*>(&fp8);
}

__device__ __forceinline__ auto bits_to_fp8_e4m3_float(std::uint8_t bits) noexcept -> float {
  __nv_fp8_e4m3 const fp8 = *reinterpret_cast<const __nv_fp8_e4m3*>(&bits);
  return static_cast<float>(fp8);
}

// ============================================================================
// E2M1 decode (for dequantization / diagnostics)
// ============================================================================

__device__ __forceinline__ auto e2m1_nibble_to_float(std::uint8_t nibble) noexcept -> float {
  std::uint8_t const sign = (nibble >> 3) & 0x1u;
  std::uint8_t const exp = (nibble >> 1) & 0x3u;
  std::uint8_t const mant = nibble & 0x1u;

  float mag = 0.0f;
  if (exp == 0) {
    mag = 0.5f * static_cast<float>(mant);  // 0 or 0.5
  } else {
    float const significand = 1.0f + 0.5f * static_cast<float>(mant);
    int const exponent = static_cast<int>(exp) - 1;
    mag = ldexpf(significand, exponent);
  }

  return sign ? -mag : mag;
}

// ============================================================================
// Vectorized E2M1 packing (SM100+ PTX)
//
// Converts 8 float values (as 4 float2) into 4 packed bytes (uint32).
// Uses cvt.rn.satfinite.e2m1x2.f32 instruction.
// ============================================================================

__device__ __forceinline__ auto pack_fp32x8_to_e2m1x8(
    const float2* float2_pairs) noexcept -> std::uint32_t {
#if defined(__CUDA_ARCH__) && (__CUDA_ARCH__ >= 1000)
  std::uint32_t packed = 0;
  asm volatile(
      "{\n"
      ".reg .b8 b0, b1, b2, b3;\n"
      "cvt.rn.satfinite.e2m1x2.f32 b0, %2, %1;\n"
      "cvt.rn.satfinite.e2m1x2.f32 b1, %4, %3;\n"
      "cvt.rn.satfinite.e2m1x2.f32 b2, %6, %5;\n"
      "cvt.rn.satfinite.e2m1x2.f32 b3, %8, %7;\n"
      "mov.b32 %0, {b0, b1, b2, b3};\n"
      "}\n"
      : "=r"(packed)
      : "f"(float2_pairs[0].x), "f"(float2_pairs[0].y),
        "f"(float2_pairs[1].x), "f"(float2_pairs[1].y),
        "f"(float2_pairs[2].x), "f"(float2_pairs[2].y),
        "f"(float2_pairs[3].x), "f"(float2_pairs[3].y));
  return packed;
#else
  (void)float2_pairs;
  return 0u;
#endif
}

// ============================================================================
// SA3 token permutation within 128-token blocks
//
// Maps logical token index to physical storage index within each 128-token
// block. This permutation optimizes tensor core access patterns.
//
// Pattern per 32 tokens:
//   [0,1,8,9,16,17,24,25, 2,3,10,11,18,19,26,27,
//    4,5,12,13,20,21,28,29, 6,7,14,15,22,23,30,31]
// ============================================================================

__device__ __forceinline__ auto sa3_token_permute_within_128(
    int token_idx_within_128) noexcept -> int {
  int const idx_in_32 = token_idx_within_128 % 32;
  int const block_32 = token_idx_within_128 / 32;

  // Permutation formula derived from SA3 layout requirements.
  int const permuted = (idx_in_32 / 8) * 2 +
                       ((idx_in_32 % 8) / 2) * 8 +
                       (idx_in_32 % 2);

  return block_32 * 32 + permuted;
}

// ============================================================================
// SA3 64×16 scale factor swizzle
//
// Computes byte offset for scale factor storage in SA3's swizzled layout.
// Tiles are 64 rows × 16 columns of scale factors.
//
// Formula: offset = (col/4)*256 + (col%4) + (row/16)*4 + (row%16)*16
// ============================================================================

__device__ __forceinline__ auto sa3_scale_swizzle_offset(
    int row_within_64,
    int col_idx) noexcept -> int {
  int const col_group = col_idx / 4;
  int const col_in_group = col_idx % 4;
  int const row_group = row_within_64 / 16;
  int const row_in_group = row_within_64 % 16;

  return col_group * 256 + col_in_group + row_group * 4 + row_in_group * 16;
}

// ============================================================================
// Input type traits for vectorized loads
// ============================================================================

template <typename ScalarT>
struct input_traits;

template <>
struct input_traits<__half> {
  using scalar = __half;
  using vec2 = __half2;

  __device__ __forceinline__ static auto load_vec2(const scalar* ptr) noexcept -> vec2 {
    return *reinterpret_cast<const vec2*>(ptr);
  }

  __device__ __forceinline__ static auto to_float2(vec2 v) noexcept -> float2 {
    return __half22float2(v);
  }
};

template <>
struct input_traits<__nv_bfloat16> {
  using scalar = __nv_bfloat16;
  using vec2 = __nv_bfloat162;

  __device__ __forceinline__ static auto load_vec2(const scalar* ptr) noexcept -> vec2 {
    return *reinterpret_cast<const vec2*>(ptr);
  }

  __device__ __forceinline__ static auto to_float2(vec2 v) noexcept -> float2 {
    return __bfloat1622float2(v);
  }
};

template <>
struct input_traits<float> {
  using scalar = float;
  using vec2 = float2;

  __device__ __forceinline__ static auto load_vec2(const scalar* ptr) noexcept -> vec2 {
    return *reinterpret_cast<const vec2*>(ptr);
  }

  __device__ __forceinline__ static auto to_float2(vec2 v) noexcept -> float2 {
    return v;
  }
};

// ============================================================================
// Block quantization helper
//
// Quantizes 8 float2 pairs (16 elements = 1 block) to packed FP4.
// Returns two uint32 values (8 bytes total = 16 packed FP4 values).
// ============================================================================

struct quantized_block_result {
  std::uint32_t packed_lo;  // First 8 FP4 values.
  std::uint32_t packed_hi;  // Second 8 FP4 values.
  std::uint8_t scale_bits;  // FP8 E4M3 scale factor.
};

__device__ __forceinline__ auto quantize_block_16(
    float2* pairs,  // 8 float2 = 16 floats, modified in-place
    bool has_data) noexcept -> quantized_block_result {
  
  // Find max absolute value.
  float max_abs = 0.0f;
  if (has_data) {
    #pragma unroll
    for (int i = 0; i < 8; ++i) {
      float const abs_x = isfinite(pairs[i].x) ? fabsf(pairs[i].x) : 0.0f;
      float const abs_y = isfinite(pairs[i].y) ? fabsf(pairs[i].y) : 0.0f;
      max_abs = fmaxf(max_abs, fmaxf(abs_x, abs_y));
    }
  }

  // Compute scale: scale = clamp(max_abs / 6) as FP8.
  float scale_f = clamp_to_fp8_range(max_abs * e2m1_rcp_max);
  std::uint8_t const scale_bits = fp8_e4m3_to_bits(scale_f);
  scale_f = bits_to_fp8_e4m3_float(scale_bits);  // Roundtrip for exact inverse.

  float const inv_scale = (scale_f == 0.0f) ? 0.0f : (1.0f / scale_f);

  // Scale values.
  #pragma unroll
  for (int i = 0; i < 8; ++i) {
    pairs[i].x *= inv_scale;
    pairs[i].y *= inv_scale;
  }

  // Pack to E2M1.
  quantized_block_result result;
  result.packed_lo = pack_fp32x8_to_e2m1x8(pairs + 0);
  result.packed_hi = pack_fp32x8_to_e2m1x8(pairs + 4);
  result.scale_bits = scale_bits;
  return result;
}

}  // namespace s4::quantization::nvfp4
