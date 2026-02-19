// s4 // attention/sage_attention_plugin.h
// SageAttention TensorRT plugin with FP4 quantization.
//
// Pipeline:
//   1. Key centering: K' = K - mean(K, dim=sequence)
//   2. Query group mean: Q' = Q - group_mean(Q), store group_mean
//   3. Score correction: δS = group_mean(Q) @ K'^T
//   4. FP4 quantization of Q', K', V
//   5. FP4 attention with score correction: softmax((Q' @ K'^T + δS) / √d) @ V
//
// Mathematical identity:
//   Q @ K^T = Q' @ K'^T + δS
//
// This allows low-precision Q'K'^T computation with high-precision correction.
#pragma once

#include <s4/attention/mean_centering.cuh>
#include <s4/attention/score_correction.h>
#include <s4/core/nvtx.h>

#include <NvInferPlugin.h>
#include <cuda_runtime.h>
#include <cuda_bf16.h>
#include <cuda_fp8.h>
#include <cublas_v2.h>

#include <cuda/std/mdspan>

#include <algorithm>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <cstring>

namespace s4::attention {

// ============================================================================
// Type aliases
// ============================================================================

using bfloat16 = __nv_bfloat16;
using float8_e4m3 = __nv_fp8_e4m3;
using float32 = float;

template <typename ElementType>
using tensor_4d = cuda::std::mdspan<
    ElementType,
    cuda::std::dextents<int, 4>,
    cuda::std::layout_right>;

template <typename ElementType>
using tensor_3d = cuda::std::mdspan<
    ElementType,
    cuda::std::dextents<int, 3>,
    cuda::std::layout_right>;

// ============================================================================
// Error handling macros
// ============================================================================

#define S4_CUDA_CHECK(cuda_call)                    \
  do {                                              \
    if ((cuda_call) != cudaSuccess) return -1;      \
  } while (0)

// ============================================================================
// Plugin constants
// ============================================================================

namespace constants {

// Sequence blocking for query group mean (must match SA3 kernel tile size).
inline constexpr int sequence_block_size = 128;

// Scale factor grouping for FP4 quantization.
inline constexpr int scale_factor_group_size = 16;

// Serialization version for forward compatibility.
inline constexpr std::uint32_t serialization_version = 2;

// Workspace alignment (tensor core friendly, 128 bytes).
inline constexpr std::size_t workspace_alignment = 128;

}  // namespace constants

// ============================================================================
// Workspace allocator
//
// Returns cuda::std::mdspan tensors for typed, bounds-checked access.
// All allocations are 128-byte aligned for tensor core efficiency.
//
// Invariants:
//   - bytes_used() increases monotonically
//   - All returned pointers are workspace_alignment-aligned
//   - allocate_tensor_* returns contiguous row-major (layout_right) tensors
// ============================================================================

class plugin_workspace_allocator final {
public:
  explicit plugin_workspace_allocator(void* workspace_base) noexcept
      : base_pointer_(static_cast<char*>(workspace_base)) {}

  template <typename ElementType>
  [[nodiscard]] auto allocate_raw(std::size_t element_count) noexcept -> ElementType* {
    bytes_used_ = (bytes_used_ + constants::workspace_alignment - 1) &
                  ~(constants::workspace_alignment - 1);
    ElementType* allocation =
        reinterpret_cast<ElementType*>(base_pointer_ + bytes_used_);
    bytes_used_ += element_count * sizeof(ElementType);
    return allocation;
  }

  template <typename ElementType>
  [[nodiscard]] auto allocate_tensor_4d(
      int dim0, int dim1, int dim2, int dim3) noexcept -> tensor_4d<ElementType> {
    std::size_t const count =
        static_cast<std::size_t>(dim0) * dim1 * dim2 * dim3;
    ElementType* data = allocate_raw<ElementType>(count);
    return tensor_4d<ElementType>(data, dim0, dim1, dim2, dim3);
  }

  template <typename ElementType>
  [[nodiscard]] auto allocate_tensor_3d(
      int dim0, int dim1, int dim2) noexcept -> tensor_3d<ElementType> {
    std::size_t const count = static_cast<std::size_t>(dim0) * dim1 * dim2;
    ElementType* data = allocate_raw<ElementType>(count);
    return tensor_3d<ElementType>(data, dim0, dim1, dim2);
  }

  [[nodiscard]] auto bytes_used() const noexcept -> std::size_t {
    return bytes_used_;
  }

private:
  char* base_pointer_ = nullptr;
  std::size_t bytes_used_ = 0;
};

// ============================================================================
// FP4 quantization launchers (extern, linked from s4-cuda)
// ============================================================================

extern "C" {

void s4_launch_fp4_quantize_query(
    const bfloat16* input,
    std::uint8_t* output,
    float8_e4m3* scale_factors,
    int batch_size,
    int head_count,
    int sequence_length,
    int head_dimension,
    cudaStream_t stream);

void s4_launch_fp4_quantize_key(
    const bfloat16* input,
    std::uint8_t* output,
    float8_e4m3* scale_factors,
    int batch_size,
    int head_count,
    int sequence_length,
    int head_dimension,
    cudaStream_t stream);

void s4_launch_fp4_quantize_value(
    const bfloat16* input,
    std::uint8_t* output,
    float8_e4m3* scale_factors,
    int batch_size,
    int head_count,
    int sequence_length,
    int head_dimension,
    cudaStream_t stream);

}  // extern "C"

// ============================================================================
// SA3 forward parameters
//
// Stride contract:
//   - All strides are in ELEMENTS, not bytes.
//   - FP4 tensors: each uint8 holds 2 values, stride counts logical elements.
//   - SA3 kernel internally multiplies by 2 when computing byte offsets.
//   - Scale factors: one fp8 per 16 elements along the quantized dimension.
// ============================================================================

struct sage_attention_forward_parameters final {
  // Tensor pointers.
  void* query_pointer = nullptr;
  void* key_pointer = nullptr;
  void* value_pointer = nullptr;
  void* score_correction_pointer = nullptr;
  void* scale_factors_query_pointer = nullptr;
  void* scale_factors_key_pointer = nullptr;
  void* scale_factors_value_pointer = nullptr;
  void* output_pointer = nullptr;
  int* tile_count_semaphore = nullptr;

  // Query strides (elements).
  int query_row_stride = 0;
  int query_head_stride = 0;
  int query_batch_stride = 0;

  // Key strides.
  int key_row_stride = 0;
  int key_head_stride = 0;
  int key_batch_stride = 0;

  // Value strides (transposed layout).
  int value_row_stride = 0;
  int value_head_stride = 0;
  int value_batch_stride = 0;

  // Score correction strides.
  int score_correction_row_stride = 0;
  int score_correction_head_stride = 0;
  int score_correction_batch_stride = 0;

  // Scale factor strides.
  int scale_query_row_stride = 0;
  int scale_query_head_stride = 0;
  int scale_query_batch_stride = 0;
  int scale_key_row_stride = 0;
  int scale_key_head_stride = 0;
  int scale_key_batch_stride = 0;
  int scale_value_row_stride = 0;
  int scale_value_head_stride = 0;
  int scale_value_batch_stride = 0;

  // Output strides.
  int output_row_stride = 0;
  int output_head_stride = 0;
  int output_batch_stride = 0;

  // Dimensions.
  int batch_size = 0;
  int head_count = 0;
  int head_count_key_value = 0;
  int query_sequence_length = 0;
  int query_sequence_length_unpadded = 0;
  int key_sequence_length = 0;
  int key_sequence_length_unpadded = 0;
  int query_sequence_length_rounded = 0;
  int key_sequence_length_rounded = 0;
  int head_dimension = 0;
  int head_dimension_rounded = 0;

  // Softmax.
  float32 softmax_scale = 0.0f;
  float32 softmax_scale_log2 = 0.0f;

  // Masking.
  bool is_causal = false;
  int window_size_left = -1;
  int window_size_right = -1;

  // Output config.
  bool is_bfloat16 = true;
  bool use_per_block_mean = true;
  int block_size_for_mean = constants::sequence_block_size;
};

// SA3 kernel launcher (extern, linked separately).
extern "C" void s4_run_sage_attention_forward(
    sage_attention_forward_parameters& parameters,
    cudaStream_t stream);

// ============================================================================
// Workspace size computation
// ============================================================================

[[nodiscard]] inline auto compute_workspace_size(
    int batch_size,
    int head_count,
    int query_sequence_length,
    int key_sequence_length,
    int head_dimension) noexcept -> std::size_t {
  
  auto pad_to_block = [](int len) -> int {
    return ((len + constants::sequence_block_size - 1) /
            constants::sequence_block_size) * constants::sequence_block_size;
  };

  int const q_pad = pad_to_block(query_sequence_length);
  int const k_pad = pad_to_block(key_sequence_length);
  int const groups = compute_group_count(query_sequence_length, constants::sequence_block_size);

  std::size_t total = 0;
  auto align_add = [&](std::size_t bytes) {
    total = (total + constants::workspace_alignment - 1) &
            ~(constants::workspace_alignment - 1);
    total += bytes;
  };

  std::size_t const bh = static_cast<std::size_t>(batch_size) * head_count;

  // BF16 tensors.
  align_add(bh * k_pad * head_dimension * sizeof(bfloat16));   // key_centered
  align_add(bh * q_pad * head_dimension * sizeof(bfloat16));   // query_centered
  align_add(bh * groups * head_dimension * sizeof(bfloat16));  // query_group_mean

  // FP32 score correction.
  align_add(bh * groups * key_sequence_length * sizeof(float32));

  // FP4 packed tensors.
  align_add(bh * q_pad * (head_dimension / 2));  // query_fp4
  align_add(bh * k_pad * (head_dimension / 2));  // key_fp4
  align_add(bh * head_dimension * (k_pad / 2));  // value_fp4

  // FP8 scale factors.
  int const scales_per_row = head_dimension / constants::scale_factor_group_size;
  int const scales_per_col = k_pad / constants::scale_factor_group_size;
  align_add(bh * q_pad * scales_per_row);
  align_add(bh * k_pad * scales_per_row);
  align_add(bh * head_dimension * scales_per_col);

  // Tile semaphore.
  align_add(sizeof(int));

  return total;
}

// ============================================================================
// TensorRT Plugin
// ============================================================================

class sage_attention_plugin : public nvinfer1::IPluginV3,
                              public nvinfer1::IPluginV3OneCore,
                              public nvinfer1::IPluginV3OneBuild,
                              public nvinfer1::IPluginV3OneRuntime {
public:
  sage_attention_plugin(int head_count, int head_dimension, bool is_causal) noexcept
      : head_count_(head_count)
      , head_dimension_(head_dimension)
      , is_causal_(is_causal) {}

  sage_attention_plugin(const void* data, std::size_t length) noexcept {
    if (length < sizeof(std::uint32_t) * 4) {
      head_count_ = -1;
      return;
    }
    const auto* u32 = static_cast<const std::uint32_t*>(data);
    if (u32[0] != constants::serialization_version) {
      head_count_ = -1;
      return;
    }
    head_count_ = static_cast<int>(u32[1]);
    head_dimension_ = static_cast<int>(u32[2]);
    is_causal_ = (u32[3] != 0);
  }

  ~sage_attention_plugin() override { terminate(); }

  sage_attention_plugin(const sage_attention_plugin&) = delete;
  auto operator=(const sage_attention_plugin&) -> sage_attention_plugin& = delete;

  // === Lifecycle ===

  std::int32_t initialize() noexcept override {
    if (head_count_ < 0) return -1;
    return (cublasCreate(&cublas_handle_) == CUBLAS_STATUS_SUCCESS) ? 0 : -1;
  }

  void terminate() noexcept override {
    if (cublas_handle_) {
      cublasDestroy(cublas_handle_);
      cublas_handle_ = nullptr;
    }
  }

  // === IPluginV3 ===

  nvinfer1::IPluginCapability* getCapabilityInterface(
      nvinfer1::PluginCapabilityType type) noexcept override {
    switch (type) {
      case nvinfer1::PluginCapabilityType::kCORE:
        return static_cast<nvinfer1::IPluginV3OneCore*>(this);
      case nvinfer1::PluginCapabilityType::kBUILD:
        return static_cast<nvinfer1::IPluginV3OneBuild*>(this);
      case nvinfer1::PluginCapabilityType::kRUNTIME:
        return static_cast<nvinfer1::IPluginV3OneRuntime*>(this);
      default:
        return nullptr;
    }
  }

  nvinfer1::IPluginV3* clone() noexcept override {
    auto* c = new sage_attention_plugin(head_count_, head_dimension_, is_causal_);
    c->max_batch_ = max_batch_;
    c->max_q_seq_ = max_q_seq_;
    c->max_k_seq_ = max_k_seq_;
    return c;
  }

  // === IPluginV3OneCore ===

  char const* getPluginName() const noexcept override { return "SageAttentionFP4"; }
  char const* getPluginVersion() const noexcept override { return "2"; }
  char const* getPluginNamespace() const noexcept override { return "s4"; }

  // === IPluginV3OneBuild ===

  std::int32_t getNbOutputs() const noexcept override { return 1; }

  bool supportsFormatCombination(
      std::int32_t idx,
      nvinfer1::DynamicPluginTensorDesc const* descs,
      std::int32_t in_count,
      std::int32_t out_count) noexcept override {
    if (idx < 0 || idx >= in_count + out_count) return false;
    auto const& d = descs[idx].desc;
    return d.type == nvinfer1::DataType::kBF16 &&
           d.format == nvinfer1::TensorFormat::kLINEAR;
  }

  std::int32_t configurePlugin(
      nvinfer1::DynamicPluginTensorDesc const* inputs,
      std::int32_t,
      nvinfer1::DynamicPluginTensorDesc const*,
      std::int32_t) noexcept override {
    max_batch_ = inputs[0].max.d[0];
    max_q_seq_ = inputs[0].max.d[2];
    max_k_seq_ = inputs[1].max.d[2];
    return 0;
  }

  std::int32_t getOutputDataTypes(
      nvinfer1::DataType* out,
      std::int32_t,
      nvinfer1::DataType const*,
      std::int32_t) const noexcept override {
    out[0] = nvinfer1::DataType::kBF16;
    return 0;
  }

  std::int32_t getOutputShapes(
      nvinfer1::DimsExprs const* in,
      std::int32_t,
      nvinfer1::DimsExprs const*,
      std::int32_t,
      nvinfer1::DimsExprs* out,
      std::int32_t,
      nvinfer1::IExprBuilder&) noexcept override {
    out[0] = in[0];
    return 0;
  }

  std::size_t getWorkspaceSize(
      nvinfer1::DynamicPluginTensorDesc const*,
      std::int32_t,
      nvinfer1::DynamicPluginTensorDesc const*,
      std::int32_t) const noexcept override {
    return compute_workspace_size(max_batch_, head_count_, max_q_seq_, max_k_seq_, head_dimension_);
  }

  std::size_t getSerializationSize() const noexcept override {
    return sizeof(std::uint32_t) * 4;
  }

  void serialize(void* buf) const noexcept override {
    auto* u32 = static_cast<std::uint32_t*>(buf);
    u32[0] = constants::serialization_version;
    u32[1] = static_cast<std::uint32_t>(head_count_);
    u32[2] = static_cast<std::uint32_t>(head_dimension_);
    u32[3] = is_causal_ ? 1u : 0u;
  }

  // === IPluginV3OneRuntime ===

  std::int32_t onShapeChange(
      nvinfer1::PluginTensorDesc const*,
      std::int32_t,
      nvinfer1::PluginTensorDesc const*,
      std::int32_t) noexcept override {
    return 0;
  }

  nvinfer1::IPluginV3* attachToContext(nvinfer1::IPluginResourceContext*) noexcept override {
    return this;
  }

  std::int32_t enqueue(
      nvinfer1::PluginTensorDesc const* in_desc,
      nvinfer1::PluginTensorDesc const*,
      void const* const* inputs,
      void* const* outputs,
      void* workspace,
      cudaStream_t stream) noexcept override;

private:
  int head_count_ = 0;
  int head_dimension_ = 0;
  bool is_causal_ = false;
  int max_batch_ = 0;
  int max_q_seq_ = 0;
  int max_k_seq_ = 0;
  cublasHandle_t cublas_handle_ = nullptr;
};

// ============================================================================
// Enqueue implementation
// ============================================================================

inline std::int32_t sage_attention_plugin::enqueue(
    nvinfer1::PluginTensorDesc const* in_desc,
    nvinfer1::PluginTensorDesc const*,
    void const* const* inputs,
    void* const* outputs,
    void* workspace,
    cudaStream_t stream) noexcept {

  s4::core::nvtx_range range("[s4] sage_attention_plugin::enqueue");

  // Extract dimensions.
  int const B = in_desc[0].dims.d[0];
  int const H = in_desc[0].dims.d[1];
  int const Sq = in_desc[0].dims.d[2];
  int const D = in_desc[0].dims.d[3];
  int const Sk = in_desc[1].dims.d[2];

  // Validate invariants.
  if (H != head_count_) return -1;
  if ((D & 1) || (D % constants::scale_factor_group_size)) return -1;
  if (B > max_batch_ || Sq > max_q_seq_ || Sk > max_k_seq_) return -1;

  // Padded dimensions.
  auto pad = [](int x) {
    return ((x + constants::sequence_block_size - 1) /
            constants::sequence_block_size) * constants::sequence_block_size;
  };
  int const Sq_pad = pad(Sq);
  int const Sk_pad = pad(Sk);
  int const G = compute_group_count(Sq, constants::sequence_block_size);

  // Input/output pointers.
  const auto* Q_in = static_cast<const bfloat16*>(inputs[0]);
  const auto* K_in = static_cast<const bfloat16*>(inputs[1]);
  const auto* V_in = static_cast<const bfloat16*>(inputs[2]);
  auto* Out = static_cast<bfloat16*>(outputs[0]);

  // Workspace allocation with typed mdspan tensors.
  plugin_workspace_allocator alloc(workspace);

  auto K_centered = alloc.allocate_tensor_4d<bfloat16>(B, H, Sk_pad, D);
  auto Q_centered = alloc.allocate_tensor_4d<bfloat16>(B, H, Sq_pad, D);
  auto Q_mean = alloc.allocate_tensor_3d<bfloat16>(B * H, G, D);
  auto delta_S = alloc.allocate_tensor_3d<float32>(B * H, G, Sk);

  auto Q_fp4 = alloc.allocate_tensor_4d<std::uint8_t>(B, H, Sq_pad, D / 2);
  auto K_fp4 = alloc.allocate_tensor_4d<std::uint8_t>(B, H, Sk_pad, D / 2);
  auto V_fp4 = alloc.allocate_tensor_4d<std::uint8_t>(B, H, D, Sk_pad / 2);

  int const spr = D / constants::scale_factor_group_size;
  int const spc = Sk_pad / constants::scale_factor_group_size;
  auto scale_Q = alloc.allocate_tensor_4d<float8_e4m3>(B, H, Sq_pad, spr);
  auto scale_K = alloc.allocate_tensor_4d<float8_e4m3>(B, H, Sk_pad, spr);
  auto scale_V = alloc.allocate_tensor_4d<float8_e4m3>(B, H, D, spc);

  int* tile_sem = alloc.allocate_raw<int>(1);

#ifndef NDEBUG
  std::size_t const expected = compute_workspace_size(B, H, Sq, Sk, D);
  if (alloc.bytes_used() > expected) return -1;
#endif

  // Zero padding regions.
  std::size_t const bh = static_cast<std::size_t>(B) * H;
  
  if (Sk_pad > Sk) {
    std::size_t const off = bh * Sk * D;
    std::size_t const len = bh * (Sk_pad - Sk) * D * sizeof(bfloat16);
    S4_CUDA_CHECK(cudaMemsetAsync(K_centered.data_handle() + off, 0, len, stream));

    std::size_t const soff = bh * Sk * spr;
    std::size_t const slen = bh * (Sk_pad - Sk) * spr;
    S4_CUDA_CHECK(cudaMemsetAsync(scale_K.data_handle() + soff, 0, slen, stream));

    std::size_t const voff = bh * D * (Sk / constants::scale_factor_group_size);
    std::size_t const vlen = bh * D * ((Sk_pad - Sk) / constants::scale_factor_group_size);
    S4_CUDA_CHECK(cudaMemsetAsync(scale_V.data_handle() + voff, 0, vlen, stream));
  }

  if (Sq_pad > Sq) {
    std::size_t const off = bh * Sq * D;
    std::size_t const len = bh * (Sq_pad - Sq) * D * sizeof(bfloat16);
    S4_CUDA_CHECK(cudaMemsetAsync(Q_centered.data_handle() + off, 0, len, stream));

    std::size_t const soff = bh * Sq * spr;
    std::size_t const slen = bh * (Sq_pad - Sq) * spr;
    S4_CUDA_CHECK(cudaMemsetAsync(scale_Q.data_handle() + soff, 0, slen, stream));
  }

  S4_CUDA_CHECK(cudaMemsetAsync(tile_sem, 0, sizeof(int), stream));

  // Step 1: Key centering.
  {
    s4::core::nvtx_range step("[s4] key_centering");
    S4_CUDA_CHECK(launch_key_centering(K_in, K_centered.data_handle(), B, H, Sk, D, stream));
  }

  // Step 2: Query group mean.
  {
    s4::core::nvtx_range step("[s4] query_group_mean");
    S4_CUDA_CHECK(launch_query_group_mean<constants::sequence_block_size>(
        Q_in, Q_centered.data_handle(), Q_mean.data_handle(),
        B, H, Sq, D, stream));
  }

  // Step 3: Score correction via cuBLAS GEMM.
  {
    s4::core::nvtx_range step("[s4] score_correction_gemm");
    
    score_correction_problem problem{
        .batch_size = B,
        .head_count = H,
        .group_count = G,
        .key_sequence_length = Sk,
        .head_dimension = D,
    };
    
    if (compute_score_correction(
            cublas_handle_,
            K_centered.data_handle(),
            Q_mean.data_handle(),
            delta_S.data_handle(),
            problem,
            stream) != 0) {
      return -1;
    }
  }

  // Step 4: FP4 quantization.
  {
    s4::core::nvtx_range step("[s4] fp4_quantization");

    s4_launch_fp4_quantize_query(
        Q_centered.data_handle(), Q_fp4.data_handle(), scale_Q.data_handle(),
        B, H, Sq_pad, D, stream);
    S4_CUDA_CHECK(cudaGetLastError());

    s4_launch_fp4_quantize_key(
        K_centered.data_handle(), K_fp4.data_handle(), scale_K.data_handle(),
        B, H, Sk_pad, D, stream);
    S4_CUDA_CHECK(cudaGetLastError());

    s4_launch_fp4_quantize_value(
        V_in, V_fp4.data_handle(), scale_V.data_handle(),
        B, H, Sk_pad, D, stream);
    S4_CUDA_CHECK(cudaGetLastError());
  }

  // Step 5: SA3 FP4 attention kernel.
  {
    s4::core::nvtx_range step("[s4] sa3_attention_kernel");

    sage_attention_forward_parameters p{};

    p.query_pointer = Q_fp4.data_handle();
    p.key_pointer = K_fp4.data_handle();
    p.value_pointer = V_fp4.data_handle();
    p.score_correction_pointer = delta_S.data_handle();
    p.scale_factors_query_pointer = scale_Q.data_handle();
    p.scale_factors_key_pointer = scale_K.data_handle();
    p.scale_factors_value_pointer = scale_V.data_handle();
    p.output_pointer = Out;
    p.tile_count_semaphore = tile_sem;

    // Element strides.
    p.query_row_stride = D;
    p.query_head_stride = Sq_pad * D;
    p.query_batch_stride = H * Sq_pad * D;

    p.key_row_stride = D;
    p.key_head_stride = Sk_pad * D;
    p.key_batch_stride = H * Sk_pad * D;

    p.value_row_stride = Sk_pad;
    p.value_head_stride = D * Sk_pad;
    p.value_batch_stride = H * D * Sk_pad;

    p.score_correction_row_stride = Sk;
    p.score_correction_head_stride = G * Sk;
    p.score_correction_batch_stride = H * G * Sk;

    p.scale_query_row_stride = spr;
    p.scale_query_head_stride = Sq_pad * spr;
    p.scale_query_batch_stride = H * Sq_pad * spr;

    p.scale_key_row_stride = spr;
    p.scale_key_head_stride = Sk_pad * spr;
    p.scale_key_batch_stride = H * Sk_pad * spr;

    p.scale_value_row_stride = spc;
    p.scale_value_head_stride = D * spc;
    p.scale_value_batch_stride = H * D * spc;

    p.output_row_stride = D;
    p.output_head_stride = Sq_pad * D;
    p.output_batch_stride = H * Sq_pad * D;

    p.batch_size = B;
    p.head_count = H;
    p.head_count_key_value = H;
    p.query_sequence_length = Sq_pad;
    p.query_sequence_length_unpadded = Sq;
    p.key_sequence_length = Sk_pad;
    p.key_sequence_length_unpadded = Sk;
    p.query_sequence_length_rounded = Sq_pad;
    p.key_sequence_length_rounded = Sk_pad;
    p.head_dimension = D;
    p.head_dimension_rounded = D;

    float32 const scale = 1.0f / std::sqrt(static_cast<float32>(D));
    p.softmax_scale = scale;
    p.softmax_scale_log2 = scale * static_cast<float32>(M_LOG2E);

    p.is_causal = is_causal_;
    p.window_size_left = -1;
    p.window_size_right = is_causal_ ? 0 : -1;

    p.is_bfloat16 = true;
    p.use_per_block_mean = true;
    p.block_size_for_mean = constants::sequence_block_size;

    s4_run_sage_attention_forward(p, stream);
    S4_CUDA_CHECK(cudaGetLastError());
  }

  return 0;
}

// ============================================================================
// Plugin Creator
// ============================================================================

class sage_attention_plugin_creator : public nvinfer1::IPluginCreatorV3One {
public:
  char const* getPluginName() const noexcept override { return "SageAttentionFP4"; }
  char const* getPluginVersion() const noexcept override { return "2"; }
  char const* getPluginNamespace() const noexcept override { return "s4"; }

  nvinfer1::PluginFieldCollection const* getFieldNames() noexcept override {
    static nvinfer1::PluginField fields[] = {
        {"head_count", nullptr, nvinfer1::PluginFieldType::kINT32, 1},
        {"head_dimension", nullptr, nvinfer1::PluginFieldType::kINT32, 1},
        {"is_causal", nullptr, nvinfer1::PluginFieldType::kINT32, 1},
    };
    static nvinfer1::PluginFieldCollection fc{3, fields};
    return &fc;
  }

  nvinfer1::IPluginV3* createPlugin(
      char const*,
      nvinfer1::PluginFieldCollection const* fc,
      nvinfer1::TensorRTPhase) noexcept override {
    int hc = 24, hd = 128, causal = 0;
    for (int i = 0; i < fc->nbFields; ++i) {
      auto const& f = fc->fields[i];
      if (std::strcmp(f.name, "head_count") == 0)
        hc = *static_cast<const int*>(f.data);
      else if (std::strcmp(f.name, "head_dimension") == 0)
        hd = *static_cast<const int*>(f.data);
      else if (std::strcmp(f.name, "is_causal") == 0)
        causal = *static_cast<const int*>(f.data);
    }
    return new sage_attention_plugin(hc, hd, causal != 0);
  }
};

REGISTER_TENSORRT_PLUGIN(sage_attention_plugin_creator);

}  // namespace s4::attention
