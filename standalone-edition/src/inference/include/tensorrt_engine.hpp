#pragma once

#include <NvInfer.h>
#include <NvOnnxParser.h>
#include <cuda_runtime.h>

#include <cstdint>
#include <string>
#include <vector>
#include <memory>
#include <filesystem>
#include <expected>
#include <span>

namespace lattice {

struct TRTError {
    std::string message;
};

// Custom logger for TensorRT
class TRTLogger : public nvinfer1::ILogger {
public:
    void log(Severity severity, const char* msg) noexcept override;
    void set_verbose(bool verbose) { verbose_ = verbose; }
private:
    bool verbose_ = false;
};

// Optimization profile for dynamic shapes
struct OptProfile {
    std::string input_name;
    nvinfer1::Dims min_dims;
    nvinfer1::Dims opt_dims;
    nvinfer1::Dims max_dims;
};

// Build configuration
struct BuildConfig {
    bool fp16 = true;
    bool bf16 = false;
    bool int8 = false;
    bool fp8 = false;
    size_t workspace_size = 1ULL << 30;  // 1GB
    std::vector<OptProfile> profiles;
};

// TensorRT Engine wrapper
class TRTEngine {
public:
    TRTEngine() = default;
    ~TRTEngine();
    
    TRTEngine(const TRTEngine&) = delete;
    TRTEngine& operator=(const TRTEngine&) = delete;
    TRTEngine(TRTEngine&&) noexcept;
    TRTEngine& operator=(TRTEngine&&) noexcept;
    
    // Build from ONNX
    [[nodiscard]] static std::expected<TRTEngine, TRTError>
    build_from_onnx(const std::filesystem::path& onnx_path,
                    const BuildConfig& config);
    
    // Load serialized engine
    [[nodiscard]] static std::expected<TRTEngine, TRTError>
    load(const std::filesystem::path& engine_path);
    
    // Save serialized engine
    [[nodiscard]] std::expected<void, TRTError>
    save(const std::filesystem::path& engine_path) const;
    
    // Get input/output info
    [[nodiscard]] int32_t num_io_tensors() const;
    [[nodiscard]] const char* io_tensor_name(int32_t index) const;
    [[nodiscard]] nvinfer1::Dims io_tensor_shape(const char* name) const;
    [[nodiscard]] nvinfer1::DataType io_tensor_dtype(const char* name) const;
    [[nodiscard]] bool is_input(const char* name) const;
    
    // Create execution context
    [[nodiscard]] nvinfer1::IExecutionContext* create_context();
    
    // Raw engine access
    [[nodiscard]] nvinfer1::ICudaEngine* engine() { return engine_.get(); }
    [[nodiscard]] const nvinfer1::ICudaEngine* engine() const { return engine_.get(); }

private:
    struct EngineDeleter {
        void operator()(nvinfer1::ICudaEngine* e) const { if (e) e->destroy(); }
    };
    struct RuntimeDeleter {
        void operator()(nvinfer1::IRuntime* r) const { if (r) r->destroy(); }
    };
    
    std::unique_ptr<nvinfer1::ICudaEngine, EngineDeleter> engine_;
    std::unique_ptr<nvinfer1::IRuntime, RuntimeDeleter> runtime_;
    TRTLogger logger_;
};

// Execution context with GPU memory management  
class TRTContext {
public:
    explicit TRTContext(TRTEngine& engine);
    ~TRTContext();
    
    TRTContext(const TRTContext&) = delete;
    TRTContext& operator=(const TRTContext&) = delete;
    
    // Set input shape (for dynamic shapes)
    [[nodiscard]] bool set_input_shape(const char* name, nvinfer1::Dims dims);
    
    // Set tensor address
    [[nodiscard]] bool set_tensor_address(const char* name, void* ptr);
    
    // Run inference
    [[nodiscard]] bool enqueue(cudaStream_t stream);
    
private:
    struct ContextDeleter {
        void operator()(nvinfer1::IExecutionContext* c) const { if (c) c->destroy(); }
    };
    
    std::unique_ptr<nvinfer1::IExecutionContext, ContextDeleter> context_;
};

} // namespace lattice
