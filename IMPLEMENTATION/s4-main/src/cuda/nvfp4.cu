// s4 // cuda/nvfp4.cu
// NVFP4 quantization kernels for SageAttention.
//
// Provides three kernel variants:
//   1. Row-major with token permutation (for Q, K)
//   2. Transpose with token grouping (for V)
//   3. Linear row-major (for general use)
//
// All kernels use:
//   - Vectorized float2 loads
//   - 8→4 byte PTX packing
//   - SA3 64×16 scale swizzle
//   - 128-token blocking
#include <s4/cuda/nvfp4/nvfp4.cuh>

#include <cuda_runtime.h>
#include <cuda_bf16.h>
#include <cuda_fp8.h>

#include <algorithm>
#include <cstdint>

namespace s4::quantization::nvfp4 {

namespace {

// ============================================================================
// Row-major quantization kernel with optional token permutation
//
// Input:  [B, H, N_unpadded, D]  (BF16/FP16/FP32)
// Output: [B, H, N_padded, D/2]  (packed FP4, 2 values per byte)
// Scales: [B, H, N_padded, D/16] (FP8 E4M3)
//
// Grid:  (N_padded/128, B, H)
// Block: 128 * (D/16) threads
// ============================================================================

template <typename InputScalar, bool ApplyTokenPermutation, scale_layout ScaleLayout>
__global__ void quantize_row_major_kernel(
    const InputScalar* __restrict__ input,
    std::uint8_t* __restrict__ output_packed,
    std::uint8_t* __restrict__ output_scales,
    std::int32_t batch_size,
    std::int32_t head_count,
    std::int32_t seq_len_unpadded,
    std::int32_t seq_len_padded,
    std::int32_t head_dim,
    std::int64_t input_batch_stride,
    std::int64_t input_head_stride,
    std::int64_t input_seq_stride,
    std::int64_t output_batch_stride,
    std::int64_t output_head_stride,
    std::int64_t output_seq_stride,
    std::int64_t scale_batch_stride,
    std::int64_t scale_head_stride,
    std::int64_t scale_seq_stride) {

  constexpr int kTokenBlockSize = 128;

  int const batch_idx = static_cast<int>(blockIdx.y);
  int const head_idx = static_cast<int>(blockIdx.z);
  int const token_block_idx = static_cast<int>(blockIdx.x);

  int const dim_blocks = head_dim / block_size;  // D/16
  int const threads_per_token = dim_blocks;
  int const threads_per_block = kTokenBlockSize * threads_per_token;

  int const tid = static_cast<int>(threadIdx.x);
  if (tid >= threads_per_block) return;

  int const token_in_block = tid / threads_per_token;
  int const dim_block_idx = tid % threads_per_token;

  int const output_token_idx = token_block_idx * kTokenBlockSize + token_in_block;
  if (output_token_idx >= seq_len_padded) return;

  // Apply token permutation if requested.
  int input_token_idx = output_token_idx;
  if constexpr (ApplyTokenPermutation) {
    int const permuted = sa3_token_permute_within_128(token_in_block);
    input_token_idx = token_block_idx * kTokenBlockSize + permuted;
  }

  // Compute input offset.
  std::size_t const input_offset =
      static_cast<std::size_t>(batch_idx) * input_batch_stride +
      static_cast<std::size_t>(head_idx) * input_head_stride +
      static_cast<std::size_t>(input_token_idx) * input_seq_stride +
      static_cast<std::size_t>(dim_block_idx) * block_size;

  // Load 16 elements as 8 float2 pairs.
  using Traits = input_traits<InputScalar>;
  float2 pairs[8] = {};
  bool const has_data = (input_token_idx < seq_len_unpadded);

  if (has_data) {
    #pragma unroll
    for (int i = 0; i < 8; ++i) {
      auto const v = Traits::load_vec2(input + input_offset + i * 2);
      pairs[i] = Traits::to_float2(v);
    }
  }

  // Quantize block.
  auto const result = quantize_block_16(pairs, has_data);

  // Write packed output.
  std::size_t const output_offset =
      static_cast<std::size_t>(batch_idx) * output_batch_stride +
      static_cast<std::size_t>(head_idx) * output_head_stride +
      static_cast<std::size_t>(output_token_idx) * output_seq_stride +
      static_cast<std::size_t>(dim_block_idx) * 8;

  *reinterpret_cast<std::uint32_t*>(output_packed + output_offset + 0) = result.packed_lo;
  *reinterpret_cast<std::uint32_t*>(output_packed + output_offset + 4) = result.packed_hi;

  // Write scale factor.
  std::size_t const scale_base =
      static_cast<std::size_t>(batch_idx) * scale_batch_stride +
      static_cast<std::size_t>(head_idx) * scale_head_stride;

  if constexpr (ScaleLayout == scale_layout::linear) {
    std::size_t const scale_offset =
        scale_base +
        static_cast<std::size_t>(output_token_idx) * scale_seq_stride +
        static_cast<std::size_t>(dim_block_idx);
    output_scales[scale_offset] = result.scale_bits;
  } else {
    // SA3 64×16 swizzle.
    int const row_in_64 = output_token_idx % 64;
    int const tile_idx = output_token_idx / 64;
    std::size_t const tile_offset = scale_base + tile_idx * 64 * scale_seq_stride;
    int const swizzled = sa3_scale_swizzle_offset(row_in_64, dim_block_idx);
    output_scales[tile_offset + swizzled] = result.scale_bits;
  }
}

// ============================================================================
// Transpose quantization kernel for V tensor
//
// Input:  [B, H, N_unpadded, D]  (row-major)
// Output: [B, H, D, N_padded/2]  (transposed, packed)
// Scales: [B, H, D, N_padded/16] (FP8 E4M3)
//
// Each thread handles one (dim, token_group) pair.
// Grid:  (N_padded/128, B, H)
// Block: D * 8 threads (8 = 128/16 token groups per block)
// ============================================================================

template <typename InputScalar, scale_layout ScaleLayout>
__global__ void quantize_transpose_kernel(
    const InputScalar* __restrict__ input,
    std::uint8_t* __restrict__ output_packed,
    std::uint8_t* __restrict__ output_scales,
    std::int32_t batch_size,
    std::int32_t head_count,
    std::int32_t seq_len_unpadded,
    std::int32_t seq_len_padded,
    std::int32_t head_dim,
    std::int64_t input_batch_stride,
    std::int64_t input_head_stride,
    std::int64_t input_seq_stride,
    std::int64_t output_batch_stride,
    std::int64_t output_head_stride,
    std::int64_t output_dim_stride,
    std::int64_t scale_batch_stride,
    std::int64_t scale_head_stride,
    std::int64_t scale_dim_stride) {

  constexpr int kTokenBlockSize = 128;
  constexpr int kTokenGroupsPerBlock = kTokenBlockSize / block_size;  // 8

  int const batch_idx = static_cast<int>(blockIdx.y);
  int const head_idx = static_cast<int>(blockIdx.z);
  int const token_block_idx = static_cast<int>(blockIdx.x);

  int const threads_per_block = head_dim * kTokenGroupsPerBlock;
  int const tid = static_cast<int>(threadIdx.x);
  if (tid >= threads_per_block) return;

  int const dim_idx = tid / kTokenGroupsPerBlock;
  int const token_group_in_block = tid % kTokenGroupsPerBlock;

  int const token_group_start =
      token_block_idx * kTokenBlockSize + token_group_in_block * block_size;

  // Load 16 tokens for this dimension (transposed read pattern).
  float2 pairs[8] = {};
  bool has_any_data = false;

  if (dim_idx < head_dim) {
    #pragma unroll
    for (int i = 0; i < 8; ++i) {
      int const tok0 = token_group_start + i * 2 + 0;
      int const tok1 = token_group_start + i * 2 + 1;

      float v0 = 0.0f, v1 = 0.0f;

      if (tok0 < seq_len_unpadded) {
        std::size_t const off0 =
            static_cast<std::size_t>(batch_idx) * input_batch_stride +
            static_cast<std::size_t>(head_idx) * input_head_stride +
            static_cast<std::size_t>(tok0) * input_seq_stride +
            static_cast<std::size_t>(dim_idx);
        v0 = static_cast<float>(input[off0]);
        has_any_data = true;
      }

      if (tok1 < seq_len_unpadded) {
        std::size_t const off1 =
            static_cast<std::size_t>(batch_idx) * input_batch_stride +
            static_cast<std::size_t>(head_idx) * input_head_stride +
            static_cast<std::size_t>(tok1) * input_seq_stride +
            static_cast<std::size_t>(dim_idx);
        v1 = static_cast<float>(input[off1]);
        has_any_data = true;
      }

      pairs[i] = float2{v0, v1};
    }
  }

  // Quantize block.
  auto const result = quantize_block_16(pairs, has_any_data);

  // Write packed output: [B, H, D, N_padded/2].
  // token_group_start/2 gives byte offset within the N dimension.
  std::size_t const output_offset =
      static_cast<std::size_t>(batch_idx) * output_batch_stride +
      static_cast<std::size_t>(head_idx) * output_head_stride +
      static_cast<std::size_t>(dim_idx) * output_dim_stride +
      static_cast<std::size_t>(token_group_start / 2);

  *reinterpret_cast<std::uint32_t*>(output_packed + output_offset + 0) = result.packed_lo;
  *reinterpret_cast<std::uint32_t*>(output_packed + output_offset + 4) = result.packed_hi;

  // Write scale factor: [B, H, D, N_padded/16].
  int const token_group_global = token_group_start / block_size;

  std::size_t const scale_base =
      static_cast<std::size_t>(batch_idx) * scale_batch_stride +
      static_cast<std::size_t>(head_idx) * scale_head_stride;

  if constexpr (ScaleLayout == scale_layout::linear) {
    std::size_t const scale_offset =
        scale_base +
        static_cast<std::size_t>(dim_idx) * scale_dim_stride +
        static_cast<std::size_t>(token_group_global);
    output_scales[scale_offset] = result.scale_bits;
  } else {
    // SA3 swizzle: rows are D, columns are token groups.
    int const row_in_64 = dim_idx % 64;
    int const tile_idx = dim_idx / 64;
    std::size_t const tile_offset = scale_base + tile_idx * 64 * scale_dim_stride;
    int const swizzled = sa3_scale_swizzle_offset(row_in_64, token_group_global);
    output_scales[tile_offset + swizzled] = result.scale_bits;
  }
}

}  // namespace

// ============================================================================
// Launcher helpers
// ============================================================================

template <typename InputScalar>
static auto launch_quantize_qk(
    const InputScalar* input,
    std::uint8_t* output_packed,
    std::uint8_t* output_scales,
    std::int32_t B, std::int32_t H, std::int32_t N, std::int32_t D,
    cudaStream_t stream) -> cudaError_t {

  constexpr int kTokenBlockSize = 128;
  int const dim_blocks = D / block_size;
  int const threads = kTokenBlockSize * dim_blocks;

  if (threads > 1024) return cudaErrorInvalidValue;

  int const token_blocks = (N + kTokenBlockSize - 1) / kTokenBlockSize;
  dim3 const grid(token_blocks, B, H);
  dim3 const block(threads);

  // Strides for contiguous [B, H, N, D] layout.
  std::int64_t const input_batch_stride = static_cast<std::int64_t>(H) * N * D;
  std::int64_t const input_head_stride = static_cast<std::int64_t>(N) * D;
  std::int64_t const input_seq_stride = D;

  std::int64_t const output_batch_stride = static_cast<std::int64_t>(H) * N * (D / 2);
  std::int64_t const output_head_stride = static_cast<std::int64_t>(N) * (D / 2);
  std::int64_t const output_seq_stride = D / 2;

  std::int64_t const scale_batch_stride = static_cast<std::int64_t>(H) * N * dim_blocks;
  std::int64_t const scale_head_stride = static_cast<std::int64_t>(N) * dim_blocks;
  std::int64_t const scale_seq_stride = dim_blocks;

  quantize_row_major_kernel<InputScalar, true, scale_layout::sa3_64x16_swizzle>
      <<<grid, block, 0, stream>>>(
          input, output_packed, output_scales,
          B, H, N, N, D,
          input_batch_stride, input_head_stride, input_seq_stride,
          output_batch_stride, output_head_stride, output_seq_stride,
          scale_batch_stride, scale_head_stride, scale_seq_stride);

  return cudaGetLastError();
}

template <typename InputScalar>
static auto launch_quantize_v(
    const InputScalar* input,
    std::uint8_t* output_packed,
    std::uint8_t* output_scales,
    std::int32_t B, std::int32_t H, std::int32_t N, std::int32_t D,
    cudaStream_t stream) -> cudaError_t {

  constexpr int kTokenBlockSize = 128;
  constexpr int kTokenGroupsPerBlock = kTokenBlockSize / block_size;

  int const threads = D * kTokenGroupsPerBlock;
  if (threads > 1024) return cudaErrorInvalidValue;

  int const token_blocks = (N + kTokenBlockSize - 1) / kTokenBlockSize;
  dim3 const grid(token_blocks, B, H);
  dim3 const block(threads);

  // Input strides for [B, H, N, D].
  std::int64_t const input_batch_stride = static_cast<std::int64_t>(H) * N * D;
  std::int64_t const input_head_stride = static_cast<std::int64_t>(N) * D;
  std::int64_t const input_seq_stride = D;

  // Output strides for [B, H, D, N/2].
  std::int64_t const output_batch_stride = static_cast<std::int64_t>(H) * D * (N / 2);
  std::int64_t const output_head_stride = static_cast<std::int64_t>(D) * (N / 2);
  std::int64_t const output_dim_stride = N / 2;

  // Scale strides for [B, H, D, N/16].
  int const scale_cols = N / block_size;
  std::int64_t const scale_batch_stride = static_cast<std::int64_t>(H) * D * scale_cols;
  std::int64_t const scale_head_stride = static_cast<std::int64_t>(D) * scale_cols;
  std::int64_t const scale_dim_stride = scale_cols;

  quantize_transpose_kernel<InputScalar, scale_layout::sa3_64x16_swizzle>
      <<<grid, block, 0, stream>>>(
          input, output_packed, output_scales,
          B, H, N, N, D,
          input_batch_stride, input_head_stride, input_seq_stride,
          output_batch_stride, output_head_stride, output_dim_stride,
          scale_batch_stride, scale_head_stride, scale_dim_stride);

  return cudaGetLastError();
}

}  // namespace s4::quantization::nvfp4

// ============================================================================
// Extern "C" API for SageAttention plugin
// ============================================================================

extern "C" {

void s4_launch_fp4_quantize_query(
    const __nv_bfloat16* input,
    std::uint8_t* output,
    __nv_fp8_e4m3* scale_factors,
    int batch_size,
    int head_count,
    int sequence_length,
    int head_dimension,
    cudaStream_t stream) {
  
  using namespace s4::quantization::nvfp4;
  launch_quantize_qk(
      input,
      output,
      reinterpret_cast<std::uint8_t*>(scale_factors),
      batch_size, head_count, sequence_length, head_dimension,
      stream);
}

void s4_launch_fp4_quantize_key(
    const __nv_bfloat16* input,
    std::uint8_t* output,
    __nv_fp8_e4m3* scale_factors,
    int batch_size,
    int head_count,
    int sequence_length,
    int head_dimension,
    cudaStream_t stream) {
  
  using namespace s4::quantization::nvfp4;
  launch_quantize_qk(
      input,
      output,
      reinterpret_cast<std::uint8_t*>(scale_factors),
      batch_size, head_count, sequence_length, head_dimension,
      stream);
}

void s4_launch_fp4_quantize_value(
    const __nv_bfloat16* input,
    std::uint8_t* output,
    __nv_fp8_e4m3* scale_factors,
    int batch_size,
    int head_count,
    int sequence_length,
    int head_dimension,
    cudaStream_t stream) {
  
  using namespace s4::quantization::nvfp4;
  launch_quantize_v(
      input,
      output,
      reinterpret_cast<std::uint8_t*>(scale_factors),
      batch_size, head_count, sequence_length, head_dimension,
      stream);
}

}  // extern "C"

// ============================================================================
// Public C++ API implementations
// ============================================================================

namespace s4::quantization::nvfp4 {

auto compute_scale_2_from_global_amax(float global_amax_fp32) noexcept -> float {
  // ModelOpt formula: scale_2 = amax / (fp8_max * e2m1_max)
  constexpr float fp8_max = 448.0f;
  constexpr float e2m1_max = 6.0f;
  if (global_amax_fp32 <= 0.0f) return 1.0f;
  return global_amax_fp32 / (fp8_max * e2m1_max);
}

auto quantize_attention_qk(
    const void* input,
    void* output_packed,
    void* output_scales,
    std::int32_t batch_size,
    std::int32_t head_count,
    std::int32_t sequence_length,
    std::int32_t head_dimension,
    s4::dtypes::dtype_code input_dtype,
    attention_scale_layout /*scale_layout*/,
    cudaStream_t stream) noexcept -> cudaError_t {

  // Currently only BF16 input supported for attention.
  if (input_dtype != s4::dtypes::dtype_code::bfloat16) {
    return cudaErrorInvalidValue;
  }

  return launch_quantize_qk(
      static_cast<const __nv_bfloat16*>(input),
      static_cast<std::uint8_t*>(output_packed),
      static_cast<std::uint8_t*>(output_scales),
      batch_size, head_count, sequence_length, head_dimension,
      stream);
}

auto quantize_attention_v(
    const void* input,
    void* output_packed,
    void* output_scales,
    std::int32_t batch_size,
    std::int32_t head_count,
    std::int32_t sequence_length,
    std::int32_t head_dimension,
    s4::dtypes::dtype_code input_dtype,
    attention_scale_layout /*scale_layout*/,
    cudaStream_t stream) noexcept -> cudaError_t {

  if (input_dtype != s4::dtypes::dtype_code::bfloat16) {
    return cudaErrorInvalidValue;
  }

  return launch_quantize_v(
      static_cast<const __nv_bfloat16*>(input),
      static_cast<std::uint8_t*>(output_packed),
      static_cast<std::uint8_t*>(output_scales),
      batch_size, head_count, sequence_length, head_dimension,
      stream);
}

// Stub implementations for 2D API (backward compatibility).
// Full implementation would require the old kernel code.

auto quantize_2d(
    const quantize_inputs_2d& /*inputs*/,
    const quantize_outputs_2d& /*outputs*/,
    float* /*scale_2_io*/,
    float /*global_amax_fp32*/,
    const quantization_problem_2d& /*problem*/,
    const quantization_configuration& /*configuration*/,
    cudaStream_t /*stream*/) noexcept -> cudaError_t {
  // TODO: Implement 2D quantization if needed.
  return cudaErrorNotSupported;
}

auto dequantize_2d(
    const dequantize_inputs_2d& /*inputs*/,
    const dequantize_outputs_2d& /*outputs*/,
    float /*scale_2_fp32*/,
    const quantization_problem_2d& /*problem*/,
    const quantization_configuration& /*configuration*/,
    cudaStream_t /*stream*/) noexcept -> cudaError_t {
  // TODO: Implement 2D dequantization if needed.
  return cudaErrorNotSupported;
}

auto fake_quantize_2d(
    const quantize_inputs_2d& /*inputs*/,
    const dequantize_outputs_2d& /*outputs*/,
    float /*global_amax_fp32*/,
    const quantization_problem_2d& /*problem*/,
    const quantization_configuration& /*configuration*/,
    s4::core::workspace_allocator* /*workspace_allocator*/,
    cudaStream_t /*stream*/) noexcept -> cudaError_t {
  // TODO: Implement fake quantization if needed.
  return cudaErrorNotSupported;
}

}  // namespace s4::quantization::nvfp4
