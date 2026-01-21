/*
 * tensor_core_py.cpp - nanobind Python bindings
 * 
 * This is the final membrane. Python developers see a clean API,
 * but every operation goes through Lean's type-checked core.
 */

#include <nanobind/nanobind.h>
#include <nanobind/stl/string.h>
#include <nanobind/stl/vector.h>
#include <nanobind/ndarray.h>

extern "C" {
#include "tensor_core.h"
}

namespace nb = nanobind;
using namespace nb::literals;

/* Python wrapper for TensorHandle */
class Tensor {
public:
    tensor_handle_t handle;
    bool owns;
    
    Tensor(tensor_handle_t h, bool own = true) : handle(h), owns(own) {}
    
    ~Tensor() {
        if (owns && handle) {
            tensor_free(handle);
        }
    }
    
    /* No copy - tensors are move-only like Rust */
    Tensor(const Tensor&) = delete;
    Tensor& operator=(const Tensor&) = delete;
    
    Tensor(Tensor&& other) noexcept : handle(other.handle), owns(other.owns) {
        other.handle = nullptr;
        other.owns = false;
    }
    
    std::vector<size_t> shape() const {
        std::vector<size_t> s;
        size_t ndim = tensor_ndim(handle);
        for (size_t i = 0; i < ndim; i++) {
            s.push_back(tensor_shape(handle, i));
        }
        return s;
    }
    
    std::string dtype_str() const {
        switch (tensor_dtype(handle)) {
            case DTYPE_F32: return "float32";
            case DTYPE_F16: return "float16";
            case DTYPE_BF16: return "bfloat16";
            case DTYPE_NVFP4: return "nvfp4";
            default: return "unknown";
        }
    }
    
    std::string repr() const {
        std::string s = "Tensor(shape=[";
        auto sh = shape();
        for (size_t i = 0; i < sh.size(); i++) {
            if (i > 0) s += ", ";
            s += std::to_string(sh[i]);
        }
        s += "], dtype=" + dtype_str() + ")";
        return s;
    }
};

/* Helper to convert Python dtype string to enum */
static dtype_t parse_dtype(const std::string& s) {
    if (s == "float32" || s == "f32") return DTYPE_F32;
    if (s == "float16" || s == "f16") return DTYPE_F16;
    if (s == "bfloat16" || s == "bf16") return DTYPE_BF16;
    if (s == "nvfp4") return DTYPE_NVFP4;
    throw std::runtime_error("Unknown dtype: " + s);
}

/* Create tensor from shape, dtype, and optional data */
static Tensor create_tensor(
    std::vector<size_t> shape,
    const std::string& dtype_str,
    nb::bytes data = nb::bytes()
) {
    dtype_t dtype = parse_dtype(dtype_str);
    
    size_t numel = 1;
    for (auto d : shape) numel *= d;
    
    size_t elem_size;
    switch (dtype) {
        case DTYPE_F32: elem_size = 4; break;
        case DTYPE_F16: elem_size = 2; break;
        case DTYPE_BF16: elem_size = 2; break;
        case DTYPE_NVFP4: elem_size = 1; break;
        default: elem_size = 4;
    }
    
    size_t expected_size = numel * elem_size;
    
    std::vector<uint8_t> buffer;
    if (data.size() > 0) {
        if (data.size() != expected_size) {
            throw std::runtime_error(
                "Data size mismatch: expected " + std::to_string(expected_size) +
                ", got " + std::to_string(data.size())
            );
        }
        buffer.assign(data.c_str(), data.c_str() + data.size());
    } else {
        buffer.resize(expected_size, 0);
    }
    
    auto result = tensor_create(
        shape.data(), shape.size(),
        dtype,
        buffer.data(), buffer.size()
    );
    
    if (!result.success) {
        throw std::runtime_error(result.error ? result.error : "Unknown error");
    }
    
    return Tensor(result.handle);
}

/* Matmul with error handling */
static Tensor matmul(Tensor& a, Tensor& b) {
    auto result = tensor_matmul(a.handle, b.handle);
    if (!result.success) {
        throw std::runtime_error(
            std::string("matmul failed: ") + (result.error ? result.error : "shape mismatch")
        );
    }
    return Tensor(result.handle);
}

/* Conv2D */
static Tensor conv2d(Tensor& input, Tensor& kernel, size_t stride = 1, size_t padding = 0) {
    auto result = tensor_conv2d(input.handle, kernel.handle, stride, padding);
    if (!result.success) {
        throw std::runtime_error(
            std::string("conv2d failed: ") + (result.error ? result.error : "shape mismatch")
        );
    }
    return Tensor(result.handle);
}

/* Add */
static Tensor add(Tensor& a, Tensor& b) {
    auto result = tensor_add(a.handle, b.handle);
    if (!result.success) {
        throw std::runtime_error(
            std::string("add failed: ") + (result.error ? result.error : "shape mismatch")
        );
    }
    return Tensor(result.handle);
}

/* ReLU */
static Tensor relu(Tensor& t) {
    auto result = tensor_relu(t.handle);
    if (!result.success) {
        throw std::runtime_error("relu failed");
    }
    return Tensor(result.handle);
}

NB_MODULE(tensor_core, m) {
    m.doc() = R"(
        TensorCore - Type-safe tensor operations
        
        This module provides tensor operations with runtime shape validation.
        The underlying implementation in Lean ensures type safety at compile time;
        this Python binding provides the same guarantees through runtime checks.
        
        The droids can't cheat here.
    )";
    
    nb::class_<Tensor>(m, "Tensor")
        .def_prop_ro("shape", &Tensor::shape)
        .def_prop_ro("dtype", &Tensor::dtype_str)
        .def("__repr__", &Tensor::repr);
    
    m.def("tensor", &create_tensor,
        "shape"_a, "dtype"_a, "data"_a = nb::bytes(),
        R"(Create a tensor with the given shape and dtype.
        
        Args:
            shape: List of dimension sizes (all must be positive)
            dtype: One of 'float32', 'float16', 'bfloat16', 'nvfp4'
            data: Optional raw bytes (must match shape * dtype size exactly)
        
        Returns:
            Tensor handle (opaque)
        
        Raises:
            RuntimeError: If validation fails (zero dims, size mismatch)
        )");
    
    m.def("matmul", &matmul,
        "a"_a, "b"_a,
        R"(Matrix multiplication: [m, k] @ [k, n] -> [m, n]
        
        Raises:
            RuntimeError: If inner dimensions don't match
        )");
    
    m.def("conv2d", &conv2d,
        "input"_a, "kernel"_a, "stride"_a = 1, "padding"_a = 0,
        R"(2D convolution: [b, c_in, h, w] * [c_out, c_in, kh, kw]
        
        Raises:
            RuntimeError: If channels don't match or input too small
        )");
    
    m.def("add", &add, "a"_a, "b"_a, "Element-wise add (shapes must match exactly)");
    m.def("relu", &relu, "t"_a, "ReLU activation");
}
