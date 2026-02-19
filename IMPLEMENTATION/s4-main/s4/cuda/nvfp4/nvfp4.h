// s4 // cuda/nvfp4/nvfp4.h
#pragma once

#include <s4/core/workspace.h>
#include <s4/dtypes/dtype.h>
#include <s4/tensor/view.h>

#include <cuda_runtime.h>

#include <cstddef>
#include <cstdint>

namespace s4::quantization::nvfp4 {

constexpr int nvfp4_block_size_elements = 16;
constexpr float fp8_e4m3_max_value = 448.0f;
constexpr float e2m1_max_value = 6.0f;

struct affine_bias_configuration final {
  bool enable = false;
};

struct quantization_configuration final {
  int block_size = nvfp4_block_size_elements;

  // Block scale storage:
  // - float8_e4m3 => stored as raw bits in uint8 (preferred)
  // - float16 / float32 => debug storage
  s4::dtypes::dtype_code block_scale_dtype_code =
      s4::dtypes::dtype_code::float8_e4m3;

  // ModelOpt-style scale_2:
  //   scale_2 = global_amax / (448 * 6)
  //   global_scale = 1/scale_2
  //   stored_scale_fp8 = fp8(block_max * global_scale / 6)
  bool use_scale_2 = true;

  bool scale_2_provided = false;

  affine_bias_configuration affine_bias{};
};

[[nodiscard]] constexpr auto
is_supported_block_scale_dtype(s4::dtypes::dtype_code code) noexcept -> bool {
  return code == s4::dtypes::dtype_code::float8_e4m3 ||
         code == s4::dtypes::dtype_code::float16 ||
         code == s4::dtypes::dtype_code::float32;
}

[[nodiscard]] constexpr auto
is_supported_input_dtype(s4::dtypes::dtype_code code) noexcept -> bool {
  return code == s4::dtypes::dtype_code::float16 ||
         code == s4::dtypes::dtype_code::bfloat16 ||
         code == s4::dtypes::dtype_code::float32;
}

// Geometry only. Strides live in tensor views.
struct quantization_problem_2d final {
  std::int64_t row_count = 0;

  std::int64_t column_count_elements = 0;
  std::int64_t column_count_rounded_elements = 0;
};

struct quantize_inputs_2d final {
  s4::tensor::tensor_view_2d input{};
  s4::tensor::tensor_view_1d affine_bias_per_row{}; // float32 or invalid

  [[nodiscard]] constexpr auto has_affine_bias() const noexcept -> bool {
    return affine_bias_per_row.data != nullptr;
  }
};

struct quantize_outputs_2d final {
  s4::tensor::packed_tensor_view_2d output_packed_fp4{};
  s4::tensor::mutable_tensor_view_2d
      output_block_scales{}; // dtype determined by configuration

  [[nodiscard]] constexpr auto is_valid() const noexcept -> bool {
    return output_packed_fp4.data != nullptr &&
           output_block_scales.data != nullptr;
  }
};

struct dequantize_inputs_2d final {
  s4::tensor::const_packed_tensor_view_2d input_packed_fp4{};

  s4::tensor::tensor_view_2d
      input_block_scales{}; // dtype determined by configuration

  [[nodiscard]] constexpr auto is_valid() const noexcept -> bool {
    return input_packed_fp4.data != nullptr &&
           input_block_scales.data != nullptr;
  }
};

struct dequantize_outputs_2d final {
  s4::tensor::mutable_tensor_view_2d output{};

  [[nodiscard]] constexpr auto is_valid() const noexcept -> bool {
    return output.data != nullptr;
  }
};

auto compute_scale_2_from_global_amax(float global_amax_fp32) noexcept -> float;

auto quantize_2d(const quantize_inputs_2d &inputs,
                 const quantize_outputs_2d &outputs, float *scale_2_io,
                 float global_amax_fp32, const quantization_problem_2d &problem,
                 const quantization_configuration &configuration,
                 cudaStream_t stream) noexcept -> cudaError_t;

auto dequantize_2d(const dequantize_inputs_2d &inputs,
                   const dequantize_outputs_2d &outputs, float scale_2_fp32,
                   const quantization_problem_2d &problem,
                   const quantization_configuration &configuration,
                   cudaStream_t stream) noexcept -> cudaError_t;

auto fake_quantize_2d(const quantize_inputs_2d &inputs,
                      const dequantize_outputs_2d &outputs,
                      float global_amax_fp32,
                      const quantization_problem_2d &problem,
                      const quantization_configuration &configuration,
                      s4::core::workspace_allocator *workspace_allocator,
                      cudaStream_t stream) noexcept -> cudaError_t;

// ============================================================================
// 4D Attention Quantization API (for SageAttention)
//
// These functions quantize Q, K, V tensors with layouts optimized for the
// SA3 FP4 attention kernel:
//   - Token permutation within 128-token blocks
//   - 64×16 swizzled scale factor layout
//   - Transposed packing for V tensor
// ============================================================================

// Scale layout for attention tensors.
enum class attention_scale_layout : std::uint8_t {
  linear = 0,           // Contiguous row-major.
  sa3_swizzle = 1       // SA3 64×16 tile swizzle.
};

// Quantize Q or K tensor: [B, H, N, D] → [B, H, N, D/2] packed + [B, H, N, D/16] scales.
// Applies SA3 token permutation and scale swizzle.
auto quantize_attention_qk(
    const void* input,              // [B, H, N, D] BF16
    void* output_packed,            // [B, H, N, D/2] uint8
    void* output_scales,            // [B, H, N, D/16] FP8 E4M3
    std::int32_t batch_size,
    std::int32_t head_count,
    std::int32_t sequence_length,
    std::int32_t head_dimension,
    s4::dtypes::dtype_code input_dtype,
    attention_scale_layout scale_layout,
    cudaStream_t stream) noexcept -> cudaError_t;

// Quantize V tensor: [B, H, N, D] → [B, H, D, N/2] transposed+packed + scales.
// Transposed layout optimizes V @ Attention^T computation.
auto quantize_attention_v(
    const void* input,              // [B, H, N, D] BF16
    void* output_packed,            // [B, H, D, N/2] uint8
    void* output_scales,            // [B, H, D, N/16] FP8 E4M3
    std::int32_t batch_size,
    std::int32_t head_count,
    std::int32_t sequence_length,
    std::int32_t head_dimension,
    s4::dtypes::dtype_code input_dtype,
    attention_scale_layout scale_layout,
    cudaStream_t stream) noexcept -> cudaError_t;

} // namespace s4::quantization::nvfp4
