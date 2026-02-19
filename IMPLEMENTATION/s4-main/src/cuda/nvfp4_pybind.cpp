// s4 // aten/nvfp4_pybind.cpp
#include <s4/aten/torch.h>
#include <s4/core/workspace.h>
#include <s4/dtypes/dtype.h>
#include <s4/cuda/nvfp4/nvfp4.h>
#include <s4/tensor/view.h>

#include <torch/extension.h>

#include <cstdint>

namespace {

inline auto round_up_int64(std::int64_t value, std::int64_t multiple)
    -> std::int64_t {
  return ((value + multiple - 1) / multiple) * multiple;
}

} // namespace

static auto nvfp4_quantize_2d_binding(
    const at::Tensor &input_2d,
    const c10::optional<at::Tensor> &affine_bias_per_row_f32,
    double global_amax_fp32) -> torch::Tuple {
  s4::aten::require_cuda(input_2d, "input_2d");
  s4::aten::require_contiguous_last_dim(input_2d, "input_2d");
  TORCH_CHECK(input_2d.dim() == 2, "input_2d must be [rows, cols]");

  const std::int64_t row_count = input_2d.size(0);
  const std::int64_t column_count = input_2d.size(1);
  TORCH_CHECK(column_count > 0, "cols must be > 0");

  const std::int64_t column_count_rounded = round_up_int64(
      column_count, s4::quantization::nvfp4::nvfp4_block_size_elements);

  at::Tensor input_padded = input_2d;
  if (column_count_rounded != column_count) {
    input_padded =
        at::zeros({row_count, column_count_rounded}, input_2d.options());
    input_padded.slice(1, 0, column_count).copy_(input_2d);
  }

  at::Tensor packed = at::empty({row_count, column_count_rounded / 2},
                                input_2d.options().dtype(at::kByte));

  at::Tensor scales =
      at::empty({row_count, column_count_rounded / 16},
                input_2d.options().dtype(at::ScalarType::Float8_e4m3fn));

  float scale_2 = 0.0f;

  s4::quantization::nvfp4::quantization_problem_2d problem{};
  problem.row_count = row_count;
  problem.column_count_elements = column_count;
  problem.column_count_rounded_elements = column_count_rounded;

  s4::quantization::nvfp4::quantization_configuration configuration{};
  configuration.block_scale_dtype_code = s4::dtypes::dtype_code::float8_e4m3;
  configuration.use_scale_2 = true;
  configuration.scale_2_provided = false;

  s4::quantization::nvfp4::quantize_inputs_2d quantize_inputs{};
  quantize_inputs.input = s4::tensor::tensor_view_2d{
      .data = input_padded.data_ptr(),
      .dtype_code =
          s4::aten::dtype_code_from_scalar_type(input_2d.scalar_type()),
      .row_count = row_count,
      .column_count_elements = column_count,
      .row_stride_elements = input_padded.stride(0),
  };

  if (affine_bias_per_row_f32.has_value()) {
    const at::Tensor bias = affine_bias_per_row_f32.value();
    s4::aten::require_cuda(bias, "affine_bias_per_row_f32");
    TORCH_CHECK(bias.scalar_type() == at::kFloat,
                "affine_bias_per_row_f32 must be float32");
    TORCH_CHECK(bias.dim() == 1, "affine_bias_per_row_f32 must be [rows]");
    TORCH_CHECK(bias.numel() == row_count,
                "affine_bias_per_row_f32 length must equal rows");

    quantize_inputs.affine_bias_per_row = s4::tensor::tensor_view_1d{
        .data = bias.data_ptr(),
        .dtype_code = s4::dtypes::dtype_code::float32,
        .element_count = row_count,
        .stride_elements = 1,
    };

    configuration.affine_bias.enable = true;
  }

  s4::quantization::nvfp4::quantize_outputs_2d quantize_outputs{};
  quantize_outputs.output_packed_fp4 = s4::tensor::packed_tensor_view_2d{
      .data = packed.data_ptr(),
      .dtype_code = s4::dtypes::dtype_code::nvfp4_e2m1_packed,
      .row_count = row_count,
      .column_count_logical_elements = column_count_rounded,
      .row_stride_storage_bytes = packed.stride(0),
  };

  quantize_outputs.output_block_scales = s4::tensor::mutable_tensor_view_2d{
      .data = scales.data_ptr(),
      .dtype_code = s4::dtypes::dtype_code::float8_e4m3,
      .row_count = row_count,
      .column_count_elements = column_count_rounded / 16,
      .row_stride_elements = scales.stride(0),
  };

  const cudaStream_t stream = s4::aten::current_stream_for_tensor(input_2d);

  const cudaError_t status = s4::quantization::nvfp4::quantize_2d(
      quantize_inputs, quantize_outputs, &scale_2,
      static_cast<float>(global_amax_fp32), problem, configuration, stream);

  TORCH_CHECK(status == cudaSuccess,
              "nvfp4_quantize_2d failed: ", cudaGetErrorString(status));

  at::Tensor scale_2_tensor = at::scalar_tensor(
      scale_2, at::TensorOptions().dtype(at::kFloat).device(at::kCPU));
  return torch::make_tuple(packed, scales, scale_2_tensor);
}

static auto nvfp4_fake_quantize_2d_binding(
    const at::Tensor &input_2d,
    const c10::optional<at::Tensor> &affine_bias_per_row_f32,
    double global_amax_fp32) -> at::Tensor {
  s4::aten::require_cuda(input_2d, "input_2d");
  s4::aten::require_contiguous_last_dim(input_2d, "input_2d");
  TORCH_CHECK(input_2d.dim() == 2, "input_2d must be [rows, cols]");

  const std::int64_t row_count = input_2d.size(0);
  const std::int64_t column_count = input_2d.size(1);

  const std::int64_t column_count_rounded = round_up_int64(
      column_count, s4::quantization::nvfp4::nvfp4_block_size_elements);

  at::Tensor input_padded = input_2d;
  if (column_count_rounded != column_count) {
    input_padded =
        at::zeros({row_count, column_count_rounded}, input_2d.options());
    input_padded.slice(1, 0, column_count).copy_(input_2d);
  }

  at::Tensor output = at::empty({row_count, column_count}, input_2d.options());

  const std::int64_t block_count = column_count_rounded / 16;

  const std::size_t packed_logical_element_count =
      static_cast<std::size_t>(row_count) *
      static_cast<std::size_t>(column_count_rounded);

  const std::size_t scale_logical_element_count =
      static_cast<std::size_t>(row_count) *
      static_cast<std::size_t>(block_count);

  std::size_t packed_bytes = 0;
  std::size_t scale_bytes = 0;

  const bool ok_packed =
      s4::dtypes::try_compute_storage_bytes_for_logical_elements(
          s4::dtypes::dtype_code::nvfp4_e2m1_packed,
          packed_logical_element_count, &packed_bytes);

  const bool ok_scale =
      s4::dtypes::try_compute_storage_bytes_for_logical_elements(
          s4::dtypes::dtype_code::float8_e4m3, scale_logical_element_count,
          &scale_bytes);

  TORCH_CHECK(ok_packed && ok_scale,
              "Failed to compute workspace bytes for NVFP4 fake quant");

  const std::size_t workspace_bytes = packed_bytes + scale_bytes + 1024;

  at::Tensor workspace = at::empty({static_cast<long long>(workspace_bytes)},
                                   input_2d.options().dtype(at::kByte));

  s4::core::linear_allocator allocator(workspace.data_ptr(),
                                                 workspace_bytes);

  s4::quantization::nvfp4::quantization_problem_2d problem{};
  problem.row_count = row_count;
  problem.column_count_elements = column_count;
  problem.column_count_rounded_elements = column_count_rounded;

  s4::quantization::nvfp4::quantization_configuration configuration{};
  configuration.block_scale_dtype_code = s4::dtypes::dtype_code::float8_e4m3;
  configuration.use_scale_2 = true;
  configuration.scale_2_provided = false;

  s4::quantization::nvfp4::quantize_inputs_2d quantize_inputs{};
  quantize_inputs.input = s4::tensor::tensor_view_2d{
      .data = input_padded.data_ptr(),
      .dtype_code =
          s4::aten::dtype_code_from_scalar_type(input_2d.scalar_type()),
      .row_count = row_count,
      .column_count_elements = column_count,
      .row_stride_elements = input_padded.stride(0),
  };

  if (affine_bias_per_row_f32.has_value()) {
    const at::Tensor bias = affine_bias_per_row_f32.value();
    s4::aten::require_cuda(bias, "affine_bias_per_row_f32");
    TORCH_CHECK(bias.scalar_type() == at::kFloat,
                "affine_bias_per_row_f32 must be float32");
    TORCH_CHECK(bias.dim() == 1, "affine_bias_per_row_f32 must be [rows]");
    TORCH_CHECK(bias.numel() == row_count,
                "affine_bias_per_row_f32 length must equal rows");

    quantize_inputs.affine_bias_per_row = s4::tensor::tensor_view_1d{
        .data = bias.data_ptr(),
        .dtype_code = s4::dtypes::dtype_code::float32,
        .element_count = row_count,
        .stride_elements = 1,
    };

    configuration.affine_bias.enable = true;
  }

  s4::quantization::nvfp4::dequantize_outputs_2d dequantize_outputs{};
  dequantize_outputs.output = s4::tensor::mutable_tensor_view_2d{
      .data = output.data_ptr(),
      .dtype_code = s4::aten::dtype_code_from_scalar_type(output.scalar_type()),
      .row_count = row_count,
      .column_count_elements = column_count,
      .row_stride_elements = output.stride(0),
  };

  const cudaStream_t stream = s4::aten::current_stream_for_tensor(input_2d);

  const cudaError_t status = s4::quantization::nvfp4::fake_quantize_2d(
      quantize_inputs, dequantize_outputs, static_cast<float>(global_amax_fp32),
      problem, configuration, &allocator, stream);

  TORCH_CHECK(status == cudaSuccess,
              "nvfp4_fake_quantize_2d failed: ", cudaGetErrorString(status));
  return output;
}

PYBIND11_MODULE(TORCH_EXTENSION_NAME, m) {
  m.def("nvfp4_quantize_2d", &nvfp4_quantize_2d_binding,
        "NVFP4 quantize 2D -> (packed, scales_fp8, scale_2)");
  m.def("nvfp4_fake_quantize_2d", &nvfp4_fake_quantize_2d_binding,
        "NVFP4 fake-quantize 2D");
}
