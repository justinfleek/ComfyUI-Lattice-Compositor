// s4 // attention/mean_centering.cuh
// Key centering and query group mean kernels for SageAttention.
//
// Mathematical background:
//   SageAttention uses the identity Q @ K^T = Q' @ K'^T + δS where:
//   - K' = K - mean(K, dim=sequence)     [key centering]
//   - Q' = Q - group_mean(Q)             [query group mean]
//   - δS = group_mean(Q) @ K'^T          [score correction]
//
//   This allows low-precision Q'K'^T with high-precision δS correction.
#pragma once

#include <cuda_runtime.h>
#include <cuda_bf16.h>

#include <algorithm>
#include <cstddef>
#include <cstdint>

namespace s4::attention {

// ============================================================================
// Key centering kernel
//
// For each (batch, head, dimension) position, computes:
//   key_output[b,h,:,d] = key_input[b,h,:,d] - mean(key_input[b,h,:,d])
//
// The mean is computed along the sequence dimension.
//
// Grid: (ceil(head_dim/kBlockDim), heads, batch)
// Block: kBlockDim threads
//
// Complexity: O(batch * heads * seq * dim)
// Memory: 2 passes over input (sum, then subtract)
// ============================================================================

template <int kBlockDim = 256>
__global__ void key_centering_kernel(
    const __nv_bfloat16* __restrict__ key_input,
    __nv_bfloat16* __restrict__ key_output,
    std::int32_t batch_size,
    std::int32_t head_count,
    std::int32_t sequence_length,
    std::int32_t head_dimension) {
  
  int const batch_idx = blockIdx.z;
  int const head_idx = blockIdx.y;

  for (int dim_idx = blockIdx.x * kBlockDim + threadIdx.x;
       dim_idx < head_dimension;
       dim_idx += gridDim.x * kBlockDim) {
    
    // Offset to (batch, head, :, dim) slice.
    std::size_t const offset =
        static_cast<std::size_t>(batch_idx) * head_count * sequence_length * head_dimension +
        static_cast<std::size_t>(head_idx) * sequence_length * head_dimension +
        dim_idx;

    // Accumulate sum along sequence dimension.
    float sum = 0.0f;
    #pragma unroll 4
    for (int seq_idx = 0; seq_idx < sequence_length; ++seq_idx) {
      sum += __bfloat162float(key_input[offset + seq_idx * head_dimension]);
    }
    float const mean = sum / static_cast<float>(sequence_length);

    // Subtract mean.
    #pragma unroll 4
    for (int seq_idx = 0; seq_idx < sequence_length; ++seq_idx) {
      float const val = __bfloat162float(key_input[offset + seq_idx * head_dimension]);
      key_output[offset + seq_idx * head_dimension] = __float2bfloat16(val - mean);
    }
  }
}

// ============================================================================
// Query group mean kernel
//
// For each group of kGroupSize queries, computes:
//   group_mean[g] = mean(query[g*kGroupSize : (g+1)*kGroupSize])
//   query_centered[i] = query[i] - group_mean[i // kGroupSize]
//
// Grid: (group_count, heads, batch)
// Block: kBlockDim threads
//
// Output layouts:
//   query_centered: [batch, heads, seq, dim] - same as input
//   query_group_mean: [batch*heads, groups, dim] - collapsed batch/head
// ============================================================================

template <int kBlockDim = 256, int kGroupSize = 128>
__global__ void query_group_mean_kernel(
    const __nv_bfloat16* __restrict__ query_input,
    __nv_bfloat16* __restrict__ query_centered,
    __nv_bfloat16* __restrict__ query_group_mean,
    std::int32_t batch_size,
    std::int32_t head_count,
    std::int32_t sequence_length,
    std::int32_t head_dimension) {
  
  int const batch_idx = blockIdx.z;
  int const head_idx = blockIdx.y;
  int const group_idx = blockIdx.x;
  int const group_count = gridDim.x;

  int const group_start = group_idx * kGroupSize;
  int const group_end = min(group_start + kGroupSize, sequence_length);
  int const group_len = group_end - group_start;

  // Offset to (batch, head, :, :) slice.
  std::size_t const bh_offset =
      static_cast<std::size_t>(batch_idx) * head_count * sequence_length * head_dimension +
      static_cast<std::size_t>(head_idx) * sequence_length * head_dimension;

  // Offset for storing group mean: [batch*heads, groups, dim].
  std::size_t const mean_offset =
      static_cast<std::size_t>(batch_idx) * head_count * group_count * head_dimension +
      static_cast<std::size_t>(head_idx) * group_count * head_dimension +
      static_cast<std::size_t>(group_idx) * head_dimension;

  for (int dim_idx = threadIdx.x; dim_idx < head_dimension; dim_idx += kBlockDim) {
    // Compute mean for this dimension across the group.
    float sum = 0.0f;
    for (int seq_idx = group_start; seq_idx < group_end; ++seq_idx) {
      sum += __bfloat162float(
          query_input[bh_offset + seq_idx * head_dimension + dim_idx]);
    }
    float const mean = sum / static_cast<float>(group_len);

    // Store group mean.
    query_group_mean[mean_offset + dim_idx] = __float2bfloat16(mean);

    // Subtract mean from each position in the group.
    for (int seq_idx = group_start; seq_idx < group_end; ++seq_idx) {
      float const val = __bfloat162float(
          query_input[bh_offset + seq_idx * head_dimension + dim_idx]);

      query_centered[bh_offset + seq_idx * head_dimension + dim_idx] =
          __float2bfloat16(val - mean);
    }
  }
}

// ============================================================================
// Kernel launchers
// ============================================================================

inline cudaError_t launch_key_centering(
    const __nv_bfloat16* key_input,
    __nv_bfloat16* key_output,
    std::int32_t batch_size,
    std::int32_t head_count,
    std::int32_t sequence_length,
    std::int32_t head_dimension,
    cudaStream_t stream) {
  
  constexpr int kBlockDim = 256;
  int const grid_x = std::min((head_dimension + kBlockDim - 1) / kBlockDim, 32);
  dim3 const grid(grid_x, head_count, batch_size);

  key_centering_kernel<kBlockDim><<<grid, kBlockDim, 0, stream>>>(
      key_input, key_output,
      batch_size, head_count, sequence_length, head_dimension);
  
  return cudaGetLastError();
}

template <int kGroupSize = 128>
inline cudaError_t launch_query_group_mean(
    const __nv_bfloat16* query_input,
    __nv_bfloat16* query_centered,
    __nv_bfloat16* query_group_mean,
    std::int32_t batch_size,
    std::int32_t head_count,
    std::int32_t sequence_length,
    std::int32_t head_dimension,
    cudaStream_t stream) {
  
  constexpr int kBlockDim = 256;
  int const group_count = (sequence_length + kGroupSize - 1) / kGroupSize;
  dim3 const grid(group_count, head_count, batch_size);

  query_group_mean_kernel<kBlockDim, kGroupSize><<<grid, kBlockDim, 0, stream>>>(
      query_input, query_centered, query_group_mean,
      batch_size, head_count, sequence_length, head_dimension);
  
  return cudaGetLastError();
}

// ============================================================================
// Group count helper
// ============================================================================

[[nodiscard]] constexpr auto compute_group_count(
    std::int32_t sequence_length,
    std::int32_t group_size) noexcept -> std::int32_t {
  return (sequence_length + group_size - 1) / group_size;
}

}  // namespace s4::attention
