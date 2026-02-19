// s4 // attention/score_correction.h
// Score correction (δS) computation for SageAttention.
//
// Computes: δS = query_group_mean @ key_centered^T
//
// This is the correction term that restores attention score accuracy
// after using centered queries and keys:
//   Q @ K^T = Q' @ K'^T + δS
//
// The GEMM is batched over (batch * heads) and uses TF32 tensor cores
// for BF16 inputs with FP32 accumulation.
#pragma once

#include <cuda_runtime.h>

#include <cstddef>
#include <cstdint>

// Forward declare cuBLAS handle to avoid header dependency.
struct cublasContext;
typedef struct cublasContext* cublasHandle_t;

namespace s4::attention {

// ============================================================================
// Score correction problem specification
// ============================================================================

struct score_correction_problem final {
  std::int32_t batch_size          = 0;
  std::int32_t head_count          = 0;
  std::int32_t group_count         = 0;         // Number of query groups.
  std::int32_t key_sequence_length = 0; // Unpadded key sequence length.
  std::int32_t head_dimension      = 0;
};

// ============================================================================
// Score correction computation
//
// Inputs:
//   key_centered:     [batch, heads, key_seq, dim] BF16 - centered keys
//   query_group_mean: [batch*heads, groups, dim] BF16 - per-group query means
//
// Output:
//   score_correction: [batch*heads, groups, key_seq] FP32
//
// The output layout matches what the SA3 attention kernel expects for
// per-block score correction.
//
// Returns 0 on success, -1 on failure.
// ============================================================================

auto compute_score_correction(
    cublasHandle_t cublas_handle,
    const void* key_centered,        // BF16 [batch, heads, key_seq, dim]
    const void* query_group_mean,    // BF16 [batch*heads, groups, dim]
    void* score_correction,          // FP32 [batch*heads, groups, key_seq]
    const score_correction_problem& problem,
    cudaStream_t stream) noexcept -> int;

// ============================================================================
// Workspace size for score correction (currently zero, uses cuBLAS)
// ============================================================================

[[nodiscard]] constexpr auto score_correction_workspace_bytes(
    const score_correction_problem& /*problem*/) noexcept -> std::size_t {
  return 0;  // cuBLAS handles its own workspace.
}

}  // namespace s4::attention
