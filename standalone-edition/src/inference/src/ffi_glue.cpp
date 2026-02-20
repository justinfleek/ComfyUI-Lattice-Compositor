// C glue for Haskell FFI to TensorRT
// Exposes C++ API as extern "C" functions

#include "tensorrt_engine.hpp"

#include <cstring>
#include <memory>
#include <unordered_map>

namespace {

// Global engine registry (engines are refcounted)
std::unordered_map<lattice::TRTEngine*, std::unique_ptr<lattice::TRTEngine>> g_engines;
std::unordered_map<lattice::TRTContext*, std::unique_ptr<lattice::TRTContext>> g_contexts;

} // namespace

extern "C" {

// Engine Management
// -----------------

lattice::TRTEngine* lattice_trt_load_engine(const char* path) {
    auto result = lattice::TRTEngine::load(path);
    if (!result) {
        return nullptr;
    }
    auto engine = std::make_unique<lattice::TRTEngine>(std::move(*result));
    auto* ptr = engine.get();
    g_engines[ptr] = std::move(engine);
    return reinterpret_cast<lattice::TRTEngine*>(ptr);
}

lattice::TRTEngine* lattice_trt_build_from_onnx(
    const char* onnx_path,
    int fp16,
    int int8,
    size_t workspace_size
) {
    lattice::BuildConfig config;
    config.fp16 = fp16 != 0;
    config.int8 = int8 != 0;
    config.workspace_size = workspace_size;
    
    auto result = lattice::TRTEngine::build_from_onnx(onnx_path, config);
    if (!result) {
        return nullptr;
    }
    auto engine = std::make_unique<lattice::TRTEngine>(std::move(*result));
    auto* ptr = engine.get();
    g_engines[ptr] = std::move(engine);
    return reinterpret_cast<lattice::TRTEngine*>(ptr);
}

int lattice_trt_save_engine(lattice::TRTEngine* engine, const char* path) {
    if (!engine) return -1;
    auto it = g_engines.find(engine);
    if (it == g_engines.end()) return -1;
    
    auto result = it->second->save(path);
    return result ? 0 : -1;
}

void lattice_trt_free_engine(lattice::TRTEngine* engine) {
    if (!engine) return;
    g_engines.erase(engine);
}

// Context Management
// ------------------

nvinfer1::IExecutionContext* lattice_trt_create_context(lattice::TRTEngine* engine) {
    if (!engine) return nullptr;
    auto it = g_engines.find(engine);
    if (it == g_engines.end()) return nullptr;
    
    return it->second->create_context();
}

void lattice_trt_free_context(nvinfer1::IExecutionContext* context) {
    if (context) {
        context->destroy();
    }
}

// Inference
// ---------

int lattice_trt_set_input_shape(
    nvinfer1::IExecutionContext* context,
    const char* name,
    const int* dims,
    int num_dims
) {
    if (!context || !name || !dims) return 0;
    
    nvinfer1::Dims trt_dims;
    trt_dims.nbDims = num_dims;
    for (int i = 0; i < num_dims && i < nvinfer1::Dims::MAX_DIMS; ++i) {
        trt_dims.d[i] = dims[i];
    }
    
    return context->setInputShape(name, trt_dims) ? 1 : 0;
}

int lattice_trt_set_tensor_address(
    nvinfer1::IExecutionContext* context,
    const char* name,
    void* ptr
) {
    if (!context || !name) return 0;
    return context->setTensorAddress(name, ptr) ? 1 : 0;
}

int lattice_trt_enqueue(nvinfer1::IExecutionContext* context, cudaStream_t stream) {
    if (!context) return 0;
    return context->enqueueV3(stream) ? 1 : 0;
}

// Engine Info
// -----------

int lattice_trt_num_io_tensors(lattice::TRTEngine* engine) {
    if (!engine) return 0;
    auto it = g_engines.find(engine);
    if (it == g_engines.end()) return 0;
    
    return it->second->num_io_tensors();
}

const char* lattice_trt_io_tensor_name(lattice::TRTEngine* engine, int index) {
    if (!engine) return nullptr;
    auto it = g_engines.find(engine);
    if (it == g_engines.end()) return nullptr;
    
    return it->second->io_tensor_name(index);
}

int lattice_trt_is_input(lattice::TRTEngine* engine, const char* name) {
    if (!engine || !name) return 0;
    auto it = g_engines.find(engine);
    if (it == g_engines.end()) return 0;
    
    return it->second->is_input(name) ? 1 : 0;
}

// Tensor info
int lattice_trt_get_tensor_shape(
    lattice::TRTEngine* engine,
    const char* name,
    int* out_dims,
    int* out_num_dims
) {
    if (!engine || !name || !out_dims || !out_num_dims) return 0;
    auto it = g_engines.find(engine);
    if (it == g_engines.end()) return 0;
    
    auto dims = it->second->io_tensor_shape(name);
    *out_num_dims = dims.nbDims;
    for (int i = 0; i < dims.nbDims; ++i) {
        out_dims[i] = dims.d[i];
    }
    return 1;
}

int lattice_trt_get_tensor_dtype(lattice::TRTEngine* engine, const char* name) {
    if (!engine || !name) return -1;
    auto it = g_engines.find(engine);
    if (it == g_engines.end()) return -1;
    
    return static_cast<int>(it->second->io_tensor_dtype(name));
}

} // extern "C"
