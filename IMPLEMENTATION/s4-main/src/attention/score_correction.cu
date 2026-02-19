// s4 // attention/score_correction.cu
#include <cublas_v2.h>
#include <s4/attention/score_correction.h>

namespace s4::attention {

auto compute_score_correction(cublasHandle_t cublas_handle, const void* key_centered,
                              const void* query_group_mean, void* score_correction,
                              const score_correction_problem& problem, cudaStream_t stream) noexcept
    -> int {

  cublasStatus_t status = cublasSetStream(cublas_handle, stream);
  if (status != CUBLAS_STATUS_SUCCESS)
    return -1;

  status = cublasSetPointerMode(cublas_handle, CUBLAS_POINTER_MODE_HOST);
  if (status != CUBLAS_STATUS_SUCCESS)
    return -1;

#if CUDART_VERSION >= 12000
  status = cublasSetMathMode(cublas_handle, CUBLAS_TF32_TENSOR_OP_MATH);
  if (status != CUBLAS_STATUS_SUCCESS)
    return -1;
#endif

  float const alpha = 1.0f;
  float const beta = 0.0f;

  std::int64_t const batch_count =
      static_cast<std::int64_t>(problem.batch_size) * problem.head_count;

  // GEMM: score_correction = query_group_mean @ key_centered^T
  //
  // Dimensions (column-major cuBLAS convention):
  //   A = key_centered^T:    [dim, key_seq] -> transposed to [key_seq, dim]
  //   B = query_group_mean:  [dim, groups]  -> [groups, dim] row-major
  //   C = score_correction:  [key_seq, groups]
  //
  // We compute C = A^T @ B which gives [key_seq, groups].
  // In row-major terms: C[groups, key_seq] = B[groups, dim] @ A[key_seq, dim]^T
  //
  int const m = problem.key_sequence_length;  // Rows of C (and A^T).
  int const n = problem.group_count;          // Cols of C (and B).
  int const k = problem.head_dimension;       // Inner dimension.

  // Strides for batched GEMM (in elements).
  long long const stride_key =
      static_cast<long long>(problem.key_sequence_length) * problem.head_dimension;

  long long const stride_query_mean =
      static_cast<long long>(problem.group_count) * problem.head_dimension;
  
  long long const stride_correction =
      static_cast<long long>(problem.group_count) * problem.key_sequence_length;

  // Leading dimensions.
  int const lda = problem.head_dimension;  // key_centered is [key_seq, dim] per head.
  int const ldb = problem.head_dimension;  // query_group_mean is [groups, dim] per head.
  int const ldc = problem.key_sequence_length;

  status = cublasGemmStridedBatchedEx(
      cublas_handle,
      CUBLAS_OP_T,  // Transpose A (key_centered).
      CUBLAS_OP_N,  // No transpose B (query_group_mean).
      m, n, k, &alpha, key_centered, CUDA_R_16BF, lda, stride_key, query_group_mean, CUDA_R_16BF,
      ldb, stride_query_mean, &beta, score_correction, CUDA_R_32F, ldc, stride_correction,
      batch_count, CUBLAS_COMPUTE_32F, CUBLAS_GEMM_DEFAULT_TENSOR_OP);

  return (status == CUBLAS_STATUS_SUCCESS) ? 0 : -1;
}

}  // namespace s4::attention
