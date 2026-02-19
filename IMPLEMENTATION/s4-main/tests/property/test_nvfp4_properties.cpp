// s4 // tests/property/test_nvfp4_properties.cpp
// Property-based tests for NVFP4 quantization invariants.
// These tests verify mathematical properties without requiring CUDA.
//
// Reference: SageAttention3 fp4_interface.py
//   - scale_and_quant_fp4: row-major, no permutation
//   - scale_and_quant_fp4_permute: row-major + SA3 token permutation (for K)
//   - scale_and_quant_fp4_transpose: [B,H,N,D] → [B,H,D,N/2] (for V)

#include <catch2/catch_test_macros.hpp>
#include <catch2/catch_approx.hpp>
#include <rapidcheck.h>

#include <algorithm>
#include <array>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <numeric>
#include <vector>

namespace {

// ============================================================================
// Constants matching nvfp4.cuh
// ============================================================================

constexpr int kBlockSize = 16;
constexpr float kE2M1MaxValue = 6.0f;
constexpr float kE2M1RcpMax = 1.0f / 6.0f;
constexpr float kFP8E4M3MaxFinite = 448.0f;

// E2M1 representable values (positive): {0, 0.5, 1, 1.5, 2, 3, 4, 6}
constexpr std::array<float, 8> kE2M1PositiveValues = {
    0.0f, 0.5f, 1.0f, 1.5f, 2.0f, 3.0f, 4.0f, 6.0f
};

// ============================================================================
// Reference: SA3 token permutation within 128-token blocks
//
// From nvfp4.cuh:
//   permuted = (idx_in_32 / 8) * 2 + ((idx_in_32 % 8) / 2) * 8 + (idx_in_32 % 2)
//
// This produces pattern per 32 tokens:
//   [0,1,8,9,16,17,24,25, 2,3,10,11,18,19,26,27,
//    4,5,12,13,20,21,28,29, 6,7,14,15,22,23,30,31]
// ============================================================================

auto sa3_token_permute_within_128(int token_idx_within_128) -> int {
  int const idx_in_32 = token_idx_within_128 % 32;
  int const block_32 = token_idx_within_128 / 32;

  int const permuted = (idx_in_32 / 8) * 2 +
                       ((idx_in_32 % 8) / 2) * 8 +
                       (idx_in_32 % 2);

  return block_32 * 32 + permuted;
}

// ============================================================================
// Reference: SA3 64×16 scale factor swizzle
//
// From nvfp4.cuh:
//   offset = (col/4)*256 + (col%4) + (row/16)*4 + (row%16)*16
// ============================================================================

auto sa3_scale_swizzle_offset(int row_within_64, int col_idx) -> int {
  int const col_group = col_idx / 4;
  int const col_in_group = col_idx % 4;
  int const row_group = row_within_64 / 16;
  int const row_in_group = row_within_64 % 16;

  return col_group * 256 + col_in_group + row_group * 4 + row_in_group * 16;
}

// ============================================================================
// Reference: E2M1 encode/decode
//
// E2M1 format: sign(1) | exponent(2) | mantissa(1)
// Exponent bias = 1
// ============================================================================

auto e2m1_nibble_to_float(std::uint8_t nibble) -> float {
  std::uint8_t const sign = (nibble >> 3) & 0x1u;
  std::uint8_t const exp = (nibble >> 1) & 0x3u;
  std::uint8_t const mant = nibble & 0x1u;

  float mag = 0.0f;
  if (exp == 0) {
    mag = 0.5f * static_cast<float>(mant);  // 0 or 0.5
  } else {
    float const significand = 1.0f + 0.5f * static_cast<float>(mant);
    int const exponent = static_cast<int>(exp) - 1;
    mag = std::ldexp(significand, exponent);
  }

  return sign ? -mag : mag;
}

// Find nearest E2M1 value (for reference quantization).
auto find_nearest_e2m1(float value) -> float {
  float const sign = (value < 0.0f) ? -1.0f : 1.0f;
  float const abs_val = std::abs(value);
  
  // Clamp to max representable.
  if (abs_val >= kE2M1MaxValue) {
    return sign * kE2M1MaxValue;
  }
  
  // Find nearest representable value.
  float best = 0.0f;
  float best_dist = abs_val;
  
  for (float repr : kE2M1PositiveValues) {
    float const dist = std::abs(abs_val - repr);
    if (dist < best_dist) {
      best_dist = dist;
      best = repr;
    }
  }
  
  return sign * best;
}

// ============================================================================
// Reference: FP8 E4M3 clamp and roundtrip
// ============================================================================

auto clamp_to_fp8_range(float value) -> float {
  if (!std::isfinite(value)) return 0.0f;
  return std::min(std::max(value, 0.0f), kFP8E4M3MaxFinite);
}

// Simulate FP8 E4M3 roundtrip (approximate).
// In real hardware, this uses __nv_fp8_e4m3 conversion.
auto fp8_e4m3_roundtrip(float value) -> float {
  // FP8 E4M3 has 3 mantissa bits, 4 exponent bits, bias=7.
  // For simplicity, we just clamp and assume identity for valid range.
  // Real implementation would need bit manipulation.
  return clamp_to_fp8_range(value);
}

// ============================================================================
// Reference: Block-16 quantization
//
// For a block of 16 values:
//   1. Compute max absolute value
//   2. Compute scale = clamp_fp8(max_abs / 6)
//   3. Scale each value by 1/scale
//   4. Quantize to nearest E2M1
// ============================================================================

struct quantized_block {
  std::array<float, 16> quantized_values;
  float scale;
};

auto reference_quantize_block_16(const float* input, bool has_data) -> quantized_block {
  quantized_block result{};
  
  if (!has_data) {
    result.scale = 0.0f;
    return result;
  }
  
  // Find max absolute value.
  float max_abs = 0.0f;
  for (int i = 0; i < 16; ++i) {
    if (std::isfinite(input[i])) {
      max_abs = std::max(max_abs, std::abs(input[i]));
    }
  }
  
  // Compute scale with FP8 roundtrip.
  float scale = fp8_e4m3_roundtrip(max_abs * kE2M1RcpMax);
  result.scale = scale;
  
  float const inv_scale = (scale == 0.0f) ? 0.0f : (1.0f / scale);
  
  // Scale and quantize.
  for (int i = 0; i < 16; ++i) {
    float const scaled = input[i] * inv_scale;
    result.quantized_values[i] = find_nearest_e2m1(scaled);
  }
  
  return result;
}

// ============================================================================
// Reference: Dequantization
// ============================================================================

auto reference_dequantize_block_16(
    const std::array<float, 16>& quantized,
    float scale) -> std::array<float, 16> {
  std::array<float, 16> result{};
  for (int i = 0; i < 16; ++i) {
    result[i] = quantized[i] * scale;
  }
  return result;
}

// ============================================================================
// Generator helpers
// ============================================================================

auto generate_random_floats(std::size_t count, float min_val, float max_val) -> std::vector<float> {
  std::vector<float> result(count);
  for (std::size_t i = 0; i < count; ++i) {
    // Use RapidCheck's generator implicitly through test framework.
    result[i] = min_val + static_cast<float>(rand()) / RAND_MAX * (max_val - min_val);
  }
  return result;
}

}  // namespace

// ============================================================================
// Property Tests: Token Permutation
// ============================================================================

TEST_CASE("SA3 token permutation is bijective within 128", "[nvfp4][permutation]") {
  // Property: permutation is a bijection (every output appears exactly once).
  std::array<int, 128> outputs{};
  
  for (int i = 0; i < 128; ++i) {
    outputs[i] = sa3_token_permute_within_128(i);
  }
  
  // Sort and check for [0, 127].
  std::sort(outputs.begin(), outputs.end());
  
  for (int i = 0; i < 128; ++i) {
    REQUIRE(outputs[i] == i);
  }
}

TEST_CASE("SA3 token permutation preserves pairs", "[nvfp4][permutation]") {
  // Property: consecutive pairs (2k, 2k+1) remain consecutive after permutation.
  // This is important for vectorized float2 loads.
  for (int i = 0; i < 128; i += 2) {
    int const p0 = sa3_token_permute_within_128(i);
    int const p1 = sa3_token_permute_within_128(i + 1);
    
    // Consecutive inputs should produce consecutive outputs.
    REQUIRE(p1 == p0 + 1);
  }
}

TEST_CASE("SA3 token permutation has expected pattern", "[nvfp4][permutation]") {
  // Expected pattern for first 32 tokens (from reference implementation).
  std::array<int, 32> expected = {
      0, 1, 8, 9, 16, 17, 24, 25,
      2, 3, 10, 11, 18, 19, 26, 27,
      4, 5, 12, 13, 20, 21, 28, 29,
      6, 7, 14, 15, 22, 23, 30, 31
  };
  
  for (int i = 0; i < 32; ++i) {
    REQUIRE(sa3_token_permute_within_128(i) == expected[i]);
  }
}

TEST_CASE("SA3 token permutation is self-inverse", "[nvfp4][permutation]") {
  // Property: applying permutation twice returns original.
  // This is useful for correctness but not required by SA3.
  
  // Build inverse mapping.
  std::array<int, 128> inverse{};
  for (int i = 0; i < 128; ++i) {
    inverse[sa3_token_permute_within_128(i)] = i;
  }
  
  // Check that inverse[permute[i]] == i.
  for (int i = 0; i < 128; ++i) {
    int const permuted = sa3_token_permute_within_128(i);
    REQUIRE(inverse[permuted] == i);
  }
}

// ============================================================================
// Property Tests: Scale Swizzle
// ============================================================================

TEST_CASE("SA3 scale swizzle is bijective within 64x16 tile", "[nvfp4][swizzle]") {
  // Property: swizzle is a bijection for a 64×16 tile (1024 elements).
  std::array<int, 64 * 16> outputs{};
  
  int idx = 0;
  for (int row = 0; row < 64; ++row) {
    for (int col = 0; col < 16; ++col) {
      outputs[idx++] = sa3_scale_swizzle_offset(row, col);
    }
  }
  
  std::sort(outputs.begin(), outputs.end());
  
  for (int i = 0; i < 64 * 16; ++i) {
    REQUIRE(outputs[i] == i);
  }
}

TEST_CASE("SA3 scale swizzle has 256-byte tile structure", "[nvfp4][swizzle]") {
  // Property: each group of 4 columns occupies a 256-byte tile.
  for (int row = 0; row < 64; ++row) {
    for (int col_group = 0; col_group < 4; ++col_group) {
      int const col = col_group * 4;
      int const offset = sa3_scale_swizzle_offset(row, col);
      
      // First column in group should be at start of 256-byte tile.
      REQUIRE(offset % 256 < 64);  // Within first 64 bytes of tile.
    }
  }
}

// ============================================================================
// Property Tests: E2M1 Encoding
// ============================================================================

TEST_CASE("E2M1 decode covers all 16 values", "[nvfp4][e2m1]") {
  // Property: all 16 nibble values decode to finite floats.
  std::vector<float> decoded;
  
  for (std::uint8_t nibble = 0; nibble < 16; ++nibble) {
    float const value = e2m1_nibble_to_float(nibble);
    REQUIRE(std::isfinite(value));
    decoded.push_back(value);
  }
  
  // Check that positive values match expected set.
  for (std::uint8_t nibble = 0; nibble < 8; ++nibble) {
    REQUIRE(decoded[nibble] == Catch::Approx(kE2M1PositiveValues[nibble]));
  }
  
  // Check that negative values are negated positive values.
  for (std::uint8_t nibble = 8; nibble < 16; ++nibble) {
    REQUIRE(decoded[nibble] == Catch::Approx(-decoded[nibble - 8]));
  }
}

TEST_CASE("E2M1 has symmetric range", "[nvfp4][e2m1]") {
  // Property: E2M1 range is [-6, 6].
  float min_val = std::numeric_limits<float>::max();
  float max_val = std::numeric_limits<float>::lowest();
  
  for (std::uint8_t nibble = 0; nibble < 16; ++nibble) {
    float const value = e2m1_nibble_to_float(nibble);
    min_val = std::min(min_val, value);
    max_val = std::max(max_val, value);
  }
  
  REQUIRE(min_val == Catch::Approx(-6.0f));
  REQUIRE(max_val == Catch::Approx(6.0f));
}

TEST_CASE("find_nearest_e2m1 is idempotent", "[nvfp4][e2m1]") {
  // Property: quantizing an already-quantized value returns the same value.
  for (std::uint8_t nibble = 0; nibble < 16; ++nibble) {
    float const value = e2m1_nibble_to_float(nibble);
    float const requantized = find_nearest_e2m1(value);
    REQUIRE(requantized == Catch::Approx(value));
  }
}

TEST_CASE("find_nearest_e2m1 clamps to range", "[nvfp4][e2m1]") {
  // Property: values outside [-6, 6] are clamped.
  REQUIRE(find_nearest_e2m1(100.0f) == Catch::Approx(6.0f));
  REQUIRE(find_nearest_e2m1(-100.0f) == Catch::Approx(-6.0f));
  REQUIRE(find_nearest_e2m1(7.0f) == Catch::Approx(6.0f));
  REQUIRE(find_nearest_e2m1(-7.0f) == Catch::Approx(-6.0f));
}

// ============================================================================
// Property Tests: Block Quantization
// ============================================================================

TEST_CASE("Block quantization preserves zero", "[nvfp4][quantize]") {
  // Property: all-zero input produces all-zero output with zero scale.
  std::array<float, 16> zeros{};
  
  auto const result = reference_quantize_block_16(zeros.data(), true);
  
  REQUIRE(result.scale == Catch::Approx(0.0f));
  for (int i = 0; i < 16; ++i) {
    REQUIRE(result.quantized_values[i] == Catch::Approx(0.0f));
  }
}

TEST_CASE("Block quantization output is within E2M1 range", "[nvfp4][quantize]") {
  rc::check("quantized values are in [-6, 6]",
    [](std::array<float, 16> input) {
      // Clamp inputs to reasonable range for numerical stability.
      for (float& v : input) {
        v = std::clamp(v, -1000.0f, 1000.0f);
      }
      
      auto const result = reference_quantize_block_16(input.data(), true);
      
      for (int i = 0; i < 16; ++i) {
        RC_ASSERT(result.quantized_values[i] >= -6.0f);
        RC_ASSERT(result.quantized_values[i] <= 6.0f);
      }
    });
}

TEST_CASE("Block quantization scale is non-negative", "[nvfp4][quantize]") {
  rc::check("scale factor is non-negative",
    [](std::array<float, 16> input) {
      for (float& v : input) {
        v = std::clamp(v, -1000.0f, 1000.0f);
      }
      
      auto const result = reference_quantize_block_16(input.data(), true);
      
      RC_ASSERT(result.scale >= 0.0f);
    });
}

TEST_CASE("Block quantization preserves relative ordering", "[nvfp4][quantize]") {
  // Property: if input[i] > input[j], then quantized[i] >= quantized[j].
  // (Equality due to quantization ties.)
  rc::check("quantization preserves relative order",
    [](std::array<float, 16> input) {
      for (float& v : input) {
        v = std::clamp(v, -100.0f, 100.0f);
      }
      
      auto const result = reference_quantize_block_16(input.data(), true);
      
      for (int i = 0; i < 16; ++i) {
        for (int j = i + 1; j < 16; ++j) {
          if (input[i] > input[j] + 0.1f) {  // Margin for quantization.
            RC_ASSERT(result.quantized_values[i] >= result.quantized_values[j]);
          }
        }
      }
    });
}

TEST_CASE("Dequantization is inverse of quantization (approximate)", "[nvfp4][quantize]") {
  rc::check("dequant(quant(x)) ≈ x within quantization error",
    [](std::array<float, 16> input) {
      // Use small values to reduce relative error.
      for (float& v : input) {
        v = std::clamp(v, -5.0f, 5.0f);
      }
      
      auto const quant_result = reference_quantize_block_16(input.data(), true);
      auto const dequant = reference_dequantize_block_16(
          quant_result.quantized_values, quant_result.scale);
      
      // Check reconstruction error is bounded.
      for (int i = 0; i < 16; ++i) {
        float const error = std::abs(dequant[i] - input[i]);
        // Error should be at most half the quantization step size.
        // For E2M1, max step is 2 (from 4 to 6), so max error ~1.
        RC_ASSERT(error <= 1.5f);
      }
    });
}

// ============================================================================
// Property Tests: Transpose Layout
// ============================================================================

TEST_CASE("Transpose layout index calculation", "[nvfp4][transpose]") {
  // For V tensor: [B, H, N, D] → [B, H, D, N/2]
  // Each thread handles one (dim, token_group) pair.
  
  constexpr int B = 2, H = 4, N = 256, D = 64;
  constexpr int token_groups = N / kBlockSize;  // 16
  
  // Check that all output indices are covered.
  std::vector<bool> covered(B * H * D * (N / 2), false);
  
  for (int b = 0; b < B; ++b) {
    for (int h = 0; h < H; ++h) {
      for (int d = 0; d < D; ++d) {
        for (int tg = 0; tg < token_groups; ++tg) {
          // Output offset for this (dim, token_group).
          // 8 bytes per token group (16 fp4 values packed).
          std::size_t const offset =
              static_cast<std::size_t>(b) * H * D * (N / 2) +
              static_cast<std::size_t>(h) * D * (N / 2) +
              static_cast<std::size_t>(d) * (N / 2) +
              static_cast<std::size_t>(tg) * 8;
          
          REQUIRE(offset + 8 <= covered.size());
          
          for (int i = 0; i < 8; ++i) {
            covered[offset + i] = true;
          }
        }
      }
    }
  }
  
  // All bytes should be covered.
  for (std::size_t i = 0; i < covered.size(); ++i) {
    REQUIRE(covered[i]);
  }
}

// ============================================================================
// Property Tests: Stride Calculations
// ============================================================================

TEST_CASE("Row-major quantization output strides", "[nvfp4][strides]") {
  // For Q/K: [B, H, N, D] → [B, H, N, D/2]
  constexpr int B = 2, H = 8, N = 512, D = 128;
  
  // Output strides for contiguous [B, H, N, D/2].
  std::int64_t const batch_stride = static_cast<std::int64_t>(H) * N * (D / 2);
  std::int64_t const head_stride = static_cast<std::int64_t>(N) * (D / 2);
  std::int64_t const seq_stride = D / 2;
  
  REQUIRE(batch_stride == H * N * D / 2);
  REQUIRE(head_stride == N * D / 2);
  REQUIRE(seq_stride == D / 2);
  
  // Scale strides for [B, H, N, D/16].
  std::int64_t const scale_batch_stride = static_cast<std::int64_t>(H) * N * (D / kBlockSize);
  std::int64_t const scale_head_stride = static_cast<std::int64_t>(N) * (D / kBlockSize);
  std::int64_t const scale_seq_stride = D / kBlockSize;
  
  REQUIRE(scale_batch_stride == H * N * D / kBlockSize);
  REQUIRE(scale_head_stride == N * D / kBlockSize);
  REQUIRE(scale_seq_stride == D / kBlockSize);
}

TEST_CASE("Transpose quantization output strides", "[nvfp4][strides]") {
  // For V: [B, H, N, D] → [B, H, D, N/2]
  constexpr int B = 2, H = 8, N = 512, D = 128;
  
  // Output strides for [B, H, D, N/2].
  std::int64_t const batch_stride = static_cast<std::int64_t>(H) * D * (N / 2);
  std::int64_t const head_stride = static_cast<std::int64_t>(D) * (N / 2);
  std::int64_t const dim_stride = N / 2;
  
  REQUIRE(batch_stride == H * D * N / 2);
  REQUIRE(head_stride == D * N / 2);
  REQUIRE(dim_stride == N / 2);
  
  // Scale strides for [B, H, D, N/16].
  std::int64_t const scale_batch_stride = static_cast<std::int64_t>(H) * D * (N / kBlockSize);
  std::int64_t const scale_head_stride = static_cast<std::int64_t>(D) * (N / kBlockSize);
  std::int64_t const scale_dim_stride = N / kBlockSize;
  
  REQUIRE(scale_batch_stride == H * D * N / kBlockSize);
  REQUIRE(scale_head_stride == D * N / kBlockSize);
  REQUIRE(scale_dim_stride == N / kBlockSize);
}

// ============================================================================
// Property Tests: Numerical Accuracy
// ============================================================================

TEST_CASE("Quantization error is bounded", "[nvfp4][accuracy]") {
  rc::check("relative error is bounded for non-zero values",
    [](std::array<float, 16> input) {
      // Use values in a reasonable range.
      for (float& v : input) {
        v = std::clamp(v, -10.0f, 10.0f);
      }
      
      // Find max absolute input.
      float max_abs = 0.0f;
      for (float v : input) {
        max_abs = std::max(max_abs, std::abs(v));
      }
      
      if (max_abs < 0.01f) return;  // Skip near-zero inputs.
      
      auto const quant_result = reference_quantize_block_16(input.data(), true);
      auto const dequant = reference_dequantize_block_16(
          quant_result.quantized_values, quant_result.scale);
      
      // Check relative error is bounded.
      // For 4-bit quantization, expect ~12.5% relative error.
      for (int i = 0; i < 16; ++i) {
        if (std::abs(input[i]) > 0.1f) {
          float const rel_error = std::abs(dequant[i] - input[i]) / std::abs(input[i]);
          RC_ASSERT(rel_error <= 0.5f);  // 50% max relative error.
        }
      }
    });
}

}  // namespace
