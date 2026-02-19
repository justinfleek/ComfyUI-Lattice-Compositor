// s4 // tensor/device_tensor.h
#pragma once

#include <s4/dtypes/dtype.h>
#include <s4/dtypes/dispatch.h>
#include <s4/tensor/view.h>

#include <thrust/device_vector.h>

#include <cstddef>
#include <cstdint>
#include <span>
#include <utility>
#include <vector>

namespace s4::tensor {

// A minimal native device tensor:
// - logical: explicit dtype_code + extents + element strides
// - physical: thrust::device_vector<std::byte>
//
// This is intentionally small and explicit; it is NOT a full tensor library.
// It exists to avoid coupling core code to ATen while still offering an ergonomic
// owning container for GPU buffers.
//
// Invariants (intended for proof / TLA+ modeling):
// - storage_.size() == storage_bytes_for(extents_, dtype_code_)
// - strides_elements_ is row-major and non-negative
// - data() is aligned to at least dtype_storage_alignment_bytes(dtype_code_) when
//   allocated by CUDA runtime (cudaMalloc alignment).
class device_tensor final {
public:
    device_tensor() = default;

    explicit device_tensor(
        s4::dtypes::dtype_code dtype_code,
        std::vector<std::int64_t> extents_elements)
        : dtype_code_(dtype_code)
        , extents_elements_(std::move(extents_elements))
    {
        compute_row_major_strides_();
        allocate_storage_();
    }

    [[nodiscard]] auto dtype() const noexcept -> s4::dtypes::dtype_code { return dtype_code_; }

    [[nodiscard]] auto extents() const noexcept -> const std::vector<std::int64_t>& {
        return extents_elements_;
    }

    [[nodiscard]] auto strides_elements() const noexcept -> const std::vector<std::int64_t>& {
        return strides_elements_;
    }

    [[nodiscard]] auto data() noexcept -> void* {
        return static_cast<void*>(thrust::raw_pointer_cast(storage_.data()));
    }

    [[nodiscard]] auto data() const noexcept -> const void* {
        return static_cast<const void*>(thrust::raw_pointer_cast(storage_.data()));
    }

    [[nodiscard]] auto storage_bytes() const noexcept -> std::size_t {
        return storage_.size();
    }

    // Convenience: 2D views for the common path.
    [[nodiscard]] auto as_tensor_view_2d() const noexcept -> s4::tensor::tensor_view_2d {

        if (extents_elements_.size() != 2 || strides_elements_.size() != 2) {
            return {};
        }

        return s4::tensor::tensor_view_2d{
            .data = data(),
            .dtype_code = dtype_code_,
            .row_count = extents_elements_[0],
            .column_count_elements = extents_elements_[1],
            .row_stride_elements = strides_elements_[0],
        };
    }

    [[nodiscard]] auto as_mutable_tensor_view_2d() noexcept -> s4::tensor::mutable_tensor_view_2d {

        if (extents_elements_.size() != 2 || strides_elements_.size() != 2) {
            return {};
        }

        return s4::tensor::mutable_tensor_view_2d{
            .data = data(),
            .dtype_code = dtype_code_,
            .row_count = extents_elements_[0],
            .column_count_elements = extents_elements_[1],
            .row_stride_elements = strides_elements_[0],
        };
    }

private:
    auto compute_row_major_strides_() -> void {
        strides_elements_.clear();
        strides_elements_.resize(extents_elements_.size(), 0);

        if (extents_elements_.empty()) {
            return;
        }

        std::int64_t running_stride = 1;
        for (std::int64_t axis = static_cast<std::int64_t>(extents_elements_.size()) - 1; axis >= 0; --axis) {
            strides_elements_[static_cast<std::size_t>(axis)] = running_stride;
            running_stride *= extents_elements_[static_cast<std::size_t>(axis)];
        }
    }

    auto allocate_storage_() -> void {
        std::size_t logical_element_count = 1;
        for (std::int64_t extent : extents_elements_) {
            if (extent <= 0) {
                logical_element_count = 0;
                break;
            }
            logical_element_count *= static_cast<std::size_t>(extent);
        }

        std::size_t bytes = 0;
        const bool ok = s4::dtypes::try_compute_storage_bytes_for_logical_elements(
            dtype_code_, logical_element_count, &bytes);

        if (!ok) {
            storage_.clear();
            return;
        }

        storage_.resize(bytes);
    }

    s4::dtypes::dtype_code dtype_code_ = s4::dtypes::dtype_code::invalid;
    std::vector<std::int64_t> extents_elements_{};
    std::vector<std::int64_t> strides_elements_{};
    thrust::device_vector<std::byte> storage_{};
};

}  // namespace s4::tensor
