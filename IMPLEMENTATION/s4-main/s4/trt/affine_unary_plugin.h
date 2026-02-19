// s4 // trt/affine_unary_plugin.h
#pragma once

#include <s4/core/nvtx.h>
#include <s4/trt/trt_dtypes.h>

#include <NvInferPlugin.h>
#include <cuda_bf16.h>
#include <cuda_fp16.h>
#include <cuda_runtime.h>

#include <cstddef>
#include <cstdint>
#include <cstring>
#include <type_traits>

namespace s4::trt {

namespace constants {
constexpr std::uint32_t serialization_version = 1;
}

#define S4_TRT_CUDA_CHECK(cuda_call)                                           \
  do {                                                                         \
    if ((cuda_call) != cudaSuccess)                                            \
      return -1;                                                               \
  } while (0)

namespace detail {

template <typename element_type>
__device__ __forceinline__ float load_as_f32(const element_type *address) {
  if constexpr (std::is_same_v<element_type, __half>) {
    return __half2float(*address);
  } else if constexpr (std::is_same_v<element_type, __nv_bfloat16>) {
    return __bfloat162float(*address);
  } else {
    return *address;
  }
}

template <typename element_type>
__device__ __forceinline__ void store_from_f32(element_type *address,
                                               float value) {
  if constexpr (std::is_same_v<element_type, __half>) {
    *address = __float2half_rn(value);
  } else if constexpr (std::is_same_v<element_type, __nv_bfloat16>) {
    *address = __float2bfloat16_rn(value);
  } else {
    *address = value;
  }
}

template <typename element_type>
__global__ void affine_unary_kernel(const element_type *__restrict__ input,
                                    element_type *__restrict__ output,
                                    std::size_t element_count, float alpha,
                                    float beta) {
  const std::size_t linear_index = static_cast<std::size_t>(blockIdx.x) *
                                       static_cast<std::size_t>(blockDim.x) +
                                   static_cast<std::size_t>(threadIdx.x);

  if (linear_index >= element_count) {
    return;
  }

  const float x = load_as_f32(input + linear_index);
  const float y = alpha * x + beta;
  store_from_f32(output + linear_index, y);
}

inline auto launch_affine_unary(const void *input, void *output,
                                nvinfer1::DataType trt_dtype,
                                std::size_t element_count, float alpha,
                                float beta, cudaStream_t stream) noexcept
    -> cudaError_t {
  if (element_count == 0) {
    return cudaSuccess;
  }

  constexpr int threads_per_block = 256;
  const std::size_t blocks =
      (element_count + static_cast<std::size_t>(threads_per_block) - 1) /
      static_cast<std::size_t>(threads_per_block);

  dim3 grid(static_cast<unsigned>(blocks), 1u, 1u);
  dim3 block(static_cast<unsigned>(threads_per_block), 1u, 1u);

  switch (trt_dtype) {
  case nvinfer1::DataType::kFLOAT: {
    affine_unary_kernel<float><<<grid, block, 0, stream>>>(
        static_cast<const float *>(input), static_cast<float *>(output),
        element_count, alpha, beta);
    return cudaGetLastError();
  }

  case nvinfer1::DataType::kHALF: {
    affine_unary_kernel<__half><<<grid, block, 0, stream>>>(
        static_cast<const __half *>(input), static_cast<__half *>(output),
        element_count, alpha, beta);
    return cudaGetLastError();
  }

  case nvinfer1::DataType::kBF16: {
    affine_unary_kernel<__nv_bfloat16><<<grid, block, 0, stream>>>(
        static_cast<const __nv_bfloat16 *>(input),
        static_cast<__nv_bfloat16 *>(output), element_count, alpha, beta);
    return cudaGetLastError();
  }

  default:
    return cudaErrorInvalidValue;
  }
}

} // namespace detail

class affine_unary_plugin final : public nvinfer1::IPluginV3,
                                  public nvinfer1::IPluginV3OneCore,
                                  public nvinfer1::IPluginV3OneBuild,
                                  public nvinfer1::IPluginV3OneRuntime {
public:
  affine_unary_plugin(float alpha, float beta) noexcept
      : alpha_(alpha), beta_(beta) {}

  affine_unary_plugin(const void *serialized_data,
                      std::size_t serialized_size) noexcept {
    if (serialized_data == nullptr ||
        serialized_size < getSerializationSize()) {
      is_valid_ = false;
      return;
    }

    const std::uint32_t *words =
        static_cast<const std::uint32_t *>(serialized_data);
    const std::uint32_t version = words[0];

    if (version != constants::serialization_version) {
      is_valid_ = false;
      return;
    }

    std::uint32_t alpha_bits = words[1];
    std::uint32_t beta_bits = words[2];

    std::memcpy(&alpha_, &alpha_bits, sizeof(float));
    std::memcpy(&beta_, &beta_bits, sizeof(float));
  }

  ~affine_unary_plugin() override = default;

  std::int32_t initialize() noexcept override { return is_valid_ ? 0 : -1; }

  void terminate() noexcept override {}

  nvinfer1::IPluginCapability *getCapabilityInterface(
      nvinfer1::PluginCapabilityType capability_type) noexcept override {
    switch (capability_type) {
    case nvinfer1::PluginCapabilityType::kCORE:
      return static_cast<nvinfer1::IPluginV3OneCore *>(this);
    case nvinfer1::PluginCapabilityType::kBUILD:
      return static_cast<nvinfer1::IPluginV3OneBuild *>(this);
    case nvinfer1::PluginCapabilityType::kRUNTIME:
      return static_cast<nvinfer1::IPluginV3OneRuntime *>(this);
    default:
      return nullptr;
    }
  }

  nvinfer1::IPluginV3 *clone() noexcept override {
    affine_unary_plugin *cloned = new affine_unary_plugin(alpha_, beta_);
    cloned->is_valid_ = is_valid_;
    return cloned;
  }

  char const *getPluginName() const noexcept override {
    return "S4UnaryAffine";
  }
  char const *getPluginVersion() const noexcept override { return "1"; }
  char const *getPluginNamespace() const noexcept override { return "s4"; }

  std::int32_t getNbOutputs() const noexcept override { return 1; }

  bool supportsFormatCombination(
      std::int32_t tensor_index,
      nvinfer1::DynamicPluginTensorDesc const *input_output_descriptors,
      std::int32_t input_count, std::int32_t output_count) noexcept override {
    if (input_output_descriptors == nullptr) {
      return false;
    }

    const std::int32_t total_tensor_count = input_count + output_count;
    if (tensor_index < 0 || tensor_index >= total_tensor_count) {
      return false;
    }

    const nvinfer1::PluginTensorDesc &descriptor =
        input_output_descriptors[tensor_index].desc;

    const bool is_linear = descriptor.format == nvinfer1::TensorFormat::kLINEAR;
    if (!is_linear) {
      return false;
    }

    const bool is_supported_dtype =
        descriptor.type == nvinfer1::DataType::kFLOAT ||
        descriptor.type == nvinfer1::DataType::kHALF ||
        descriptor.type == nvinfer1::DataType::kBF16;

    if (tensor_index == 0) {
      return is_supported_dtype;
    }

    const nvinfer1::DataType input_dtype =
        input_output_descriptors[0].desc.type;
    return is_supported_dtype && (descriptor.type == input_dtype);
  }

  std::int32_t configurePlugin(nvinfer1::DynamicPluginTensorDesc const *,
                               std::int32_t,
                               nvinfer1::DynamicPluginTensorDesc const *,
                               std::int32_t) noexcept override {
    return 0;
  }

  std::int32_t
  getOutputDataTypes(nvinfer1::DataType *output_types,
                     std::int32_t output_count,
                     nvinfer1::DataType const *input_types,
                     std::int32_t input_count) const noexcept override {
    if (output_types == nullptr || input_types == nullptr) {
      return -1;
    }
    if (input_count != 1 || output_count != 1) {
      return -1;
    }

    output_types[0] = input_types[0];
    return 0;
  }

  std::int32_t getOutputShapes(nvinfer1::DimsExprs const *inputs,
                               std::int32_t input_count,
                               nvinfer1::DimsExprs const *, std::int32_t,
                               nvinfer1::DimsExprs *outputs,
                               std::int32_t output_count,
                               nvinfer1::IExprBuilder &) noexcept override {
    if (inputs == nullptr || outputs == nullptr) {
      return -1;
    }
    if (input_count != 1 || output_count != 1) {
      return -1;
    }

    outputs[0] = inputs[0];
    return 0;
  }

  std::size_t getWorkspaceSize(nvinfer1::DynamicPluginTensorDesc const *,
                               std::int32_t,
                               nvinfer1::DynamicPluginTensorDesc const *,
                               std::int32_t) const noexcept override {
    return 0;
  }

  std::size_t getSerializationSize() const noexcept override {
    return sizeof(std::uint32_t) * 3;
  }

  void serialize(void *buffer) const noexcept override {
    std::uint32_t *words = static_cast<std::uint32_t *>(buffer);
    words[0] = constants::serialization_version;

    std::uint32_t alpha_bits = 0;
    std::uint32_t beta_bits = 0;
    std::memcpy(&alpha_bits, &alpha_, sizeof(float));
    std::memcpy(&beta_bits, &beta_, sizeof(float));

    words[1] = alpha_bits;
    words[2] = beta_bits;
  }

  std::int32_t onShapeChange(nvinfer1::PluginTensorDesc const *, std::int32_t,
                             nvinfer1::PluginTensorDesc const *,
                             std::int32_t) noexcept override {
    return 0;
  }

  nvinfer1::IPluginV3 *
  attachToContext(nvinfer1::IPluginResourceContext *) noexcept override {
    return this;
  }

  std::int32_t enqueue(nvinfer1::PluginTensorDesc const *input_descriptors,
                       nvinfer1::PluginTensorDesc const *output_descriptors,
                       void const *const *inputs, void *const *outputs, void *,
                       cudaStream_t stream) noexcept override {
    s4::core::nvtx_range range("[s4] [trt] [affine_unary] enqueue");

    if (!is_valid_) {
      return -1;
    }
    if (input_descriptors == nullptr || output_descriptors == nullptr) {
      return -1;
    }
    if (inputs == nullptr || outputs == nullptr) {
      return -1;
    }
    if (inputs[0] == nullptr || outputs[0] == nullptr) {
      return -1;
    }

    const nvinfer1::DataType input_dtype = input_descriptors[0].type;
    const nvinfer1::DataType output_dtype = output_descriptors[0].type;

    if (input_dtype != output_dtype) {
      return -1;
    }

    std::size_t element_count = 0;
    if (!s4::trt::try_compute_volume_elements(input_descriptors[0].dims,
                                              &element_count)) {
      return -1;
    }

    cudaError_t launch_status = s4::trt::detail::launch_affine_unary(
        inputs[0], outputs[0], input_dtype, element_count, alpha_, beta_,
        stream);

    S4_TRT_CUDA_CHECK(launch_status);
    return 0;
  }

private:
  float alpha_ = 1.0f;
  float beta_ = 0.0f;
  bool is_valid_ = true;
};

class affine_unary_plugin_creator final : public nvinfer1::IPluginCreatorV3One {
public:
  char const *getPluginName() const noexcept override {
    return "S4UnaryAffine";
  }
  char const *getPluginVersion() const noexcept override { return "1"; }
  char const *getPluginNamespace() const noexcept override { return "s4"; }

  nvinfer1::PluginFieldCollection const *getFieldNames() noexcept override {
    static nvinfer1::PluginField fields[] = {
        {"alpha", nullptr, nvinfer1::PluginFieldType::kFLOAT32, 1},
        {"beta", nullptr, nvinfer1::PluginFieldType::kFLOAT32, 1},
    };

    static nvinfer1::PluginFieldCollection field_collection{2, fields};
    return &field_collection;
  }

  nvinfer1::IPluginV3 *
  createPlugin(char const *,
               nvinfer1::PluginFieldCollection const *field_collection,
               nvinfer1::TensorRTPhase) noexcept override {
    float alpha = 1.0f;
    float beta = 0.0f;

    if (field_collection != nullptr) {
      for (int field_index = 0; field_index < field_collection->nbFields;
           ++field_index) {

        const nvinfer1::PluginField &field =
            field_collection->fields[field_index];

        if (field.data == nullptr || field.length <= 0) {
          continue;
        }

        if (std::strcmp(field.name, "alpha") == 0) {
          alpha = *static_cast<const float *>(field.data);
        } else if (std::strcmp(field.name, "beta") == 0) {
          beta = *static_cast<const float *>(field.data);
        }
      }
    }

    return new affine_unary_plugin(alpha, beta);
  }
};

REGISTER_TENSORRT_PLUGIN(affine_unary_plugin_creator);

#undef S4_TRT_CUDA_CHECK

} // namespace s4::trt
