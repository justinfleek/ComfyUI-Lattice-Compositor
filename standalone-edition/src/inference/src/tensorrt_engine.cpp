#include "tensorrt_engine.hpp"

#include <fstream>
#include <cstring>
#include <iostream>

namespace lattice {

// TRTLogger implementation
void TRTLogger::log(Severity severity, const char* msg) noexcept {
    // Filter by severity
    if (!verbose_ && severity > Severity::kWARNING) {
        return;
    }
    
    const char* level = "";
    switch (severity) {
        case Severity::kINTERNAL_ERROR: level = "[INTERNAL_ERROR]"; break;
        case Severity::kERROR:          level = "[ERROR]"; break;
        case Severity::kWARNING:        level = "[WARNING]"; break;
        case Severity::kINFO:           level = "[INFO]"; break;
        case Severity::kVERBOSE:        level = "[VERBOSE]"; break;
    }
    std::cerr << "TensorRT " << level << " " << msg << "\n";
}

// TRTEngine implementation
TRTEngine::~TRTEngine() = default;

TRTEngine::TRTEngine(TRTEngine&& other) noexcept
    : engine_(std::move(other.engine_))
    , runtime_(std::move(other.runtime_))
    , logger_(std::move(other.logger_))
{}

TRTEngine& TRTEngine::operator=(TRTEngine&& other) noexcept {
    if (this != &other) {
        engine_ = std::move(other.engine_);
        runtime_ = std::move(other.runtime_);
        logger_ = std::move(other.logger_);
    }
    return *this;
}

std::expected<TRTEngine, TRTError>
TRTEngine::build_from_onnx(const std::filesystem::path& onnx_path,
                           const BuildConfig& config) {
    TRTEngine result;
    
    // Check ONNX file exists
    if (!std::filesystem::exists(onnx_path)) {
        return std::unexpected(TRTError{"ONNX file not found: " + onnx_path.string()});
    }
    
    // Create builder
    auto builder = std::unique_ptr<nvinfer1::IBuilder, decltype([](nvinfer1::IBuilder* b) { b->destroy(); })>(
        nvinfer1::createInferBuilder(result.logger_)
    );
    if (!builder) {
        return std::unexpected(TRTError{"Failed to create TensorRT builder"});
    }
    
    // Create network with explicit batch
    const auto explicit_batch = 1U << static_cast<uint32_t>(
        nvinfer1::NetworkDefinitionCreationFlag::kEXPLICIT_BATCH
    );
    auto network = std::unique_ptr<nvinfer1::INetworkDefinition, decltype([](nvinfer1::INetworkDefinition* n) { n->destroy(); })>(
        builder->createNetworkV2(explicit_batch)
    );
    if (!network) {
        return std::unexpected(TRTError{"Failed to create network"});
    }
    
    // Create ONNX parser
    auto parser = std::unique_ptr<nvonnxparser::IParser, decltype([](nvonnxparser::IParser* p) { p->destroy(); })>(
        nvonnxparser::createParser(*network, result.logger_)
    );
    if (!parser) {
        return std::unexpected(TRTError{"Failed to create ONNX parser"});
    }
    
    // Parse ONNX file
    if (!parser->parseFromFile(onnx_path.c_str(), 
            static_cast<int>(nvinfer1::ILogger::Severity::kWARNING))) {
        std::string errors;
        for (int i = 0; i < parser->getNbErrors(); ++i) {
            errors += parser->getError(i)->desc();
            errors += "\n";
        }
        return std::unexpected(TRTError{"ONNX parsing failed:\n" + errors});
    }
    
    // Create builder config
    auto builder_config = std::unique_ptr<nvinfer1::IBuilderConfig, decltype([](nvinfer1::IBuilderConfig* c) { c->destroy(); })>(
        builder->createBuilderConfig()
    );
    if (!builder_config) {
        return std::unexpected(TRTError{"Failed to create builder config"});
    }
    
    // Set workspace size
    builder_config->setMemoryPoolLimit(nvinfer1::MemoryPoolType::kWORKSPACE, config.workspace_size);
    
    // Set precision modes
    if (config.fp16 && builder->platformHasFastFp16()) {
        builder_config->setFlag(nvinfer1::BuilderFlag::kFP16);
    }
    if (config.bf16 && builder->platformHasTf32()) {
        // BF16 uses TF32 flag in TensorRT
        builder_config->setFlag(nvinfer1::BuilderFlag::kTF32);
    }
    if (config.int8 && builder->platformHasFastInt8()) {
        builder_config->setFlag(nvinfer1::BuilderFlag::kINT8);
    }
    
    // Add optimization profiles for dynamic shapes
    for (const auto& profile_spec : config.profiles) {
        auto profile = builder->createOptimizationProfile();
        if (!profile) {
            return std::unexpected(TRTError{"Failed to create optimization profile"});
        }
        
        profile->setDimensions(
            profile_spec.input_name.c_str(),
            nvinfer1::OptProfileSelector::kMIN,
            profile_spec.min_dims
        );
        profile->setDimensions(
            profile_spec.input_name.c_str(),
            nvinfer1::OptProfileSelector::kOPT,
            profile_spec.opt_dims
        );
        profile->setDimensions(
            profile_spec.input_name.c_str(),
            nvinfer1::OptProfileSelector::kMAX,
            profile_spec.max_dims
        );
        
        builder_config->addOptimizationProfile(profile);
    }
    
    // Build serialized network
    auto serialized = std::unique_ptr<nvinfer1::IHostMemory, decltype([](nvinfer1::IHostMemory* m) { m->destroy(); })>(
        builder->buildSerializedNetwork(*network, *builder_config)
    );
    if (!serialized) {
        return std::unexpected(TRTError{"Failed to build serialized network"});
    }
    
    // Create runtime
    result.runtime_.reset(nvinfer1::createInferRuntime(result.logger_));
    if (!result.runtime_) {
        return std::unexpected(TRTError{"Failed to create TensorRT runtime"});
    }
    
    // Deserialize engine
    result.engine_.reset(
        result.runtime_->deserializeCudaEngine(serialized->data(), serialized->size())
    );
    if (!result.engine_) {
        return std::unexpected(TRTError{"Failed to deserialize engine"});
    }
    
    return result;
}

std::expected<TRTEngine, TRTError>
TRTEngine::load(const std::filesystem::path& engine_path) {
    TRTEngine result;
    
    // Read serialized engine from file
    std::ifstream file(engine_path, std::ios::binary | std::ios::ate);
    if (!file) {
        return std::unexpected(TRTError{"Failed to open engine file: " + engine_path.string()});
    }
    
    auto size = file.tellg();
    file.seekg(0, std::ios::beg);
    
    std::vector<char> data(static_cast<size_t>(size));
    if (!file.read(data.data(), size)) {
        return std::unexpected(TRTError{"Failed to read engine file"});
    }
    
    // Create runtime
    result.runtime_.reset(nvinfer1::createInferRuntime(result.logger_));
    if (!result.runtime_) {
        return std::unexpected(TRTError{"Failed to create TensorRT runtime"});
    }
    
    // Deserialize engine
    result.engine_.reset(
        result.runtime_->deserializeCudaEngine(data.data(), data.size())
    );
    if (!result.engine_) {
        return std::unexpected(TRTError{"Failed to deserialize engine"});
    }
    
    return result;
}

std::expected<void, TRTError>
TRTEngine::save(const std::filesystem::path& engine_path) const {
    if (!engine_) {
        return std::unexpected(TRTError{"No engine to save"});
    }
    
    auto serialized = std::unique_ptr<nvinfer1::IHostMemory, decltype([](nvinfer1::IHostMemory* m) { m->destroy(); })>(
        engine_->serialize()
    );
    if (!serialized) {
        return std::unexpected(TRTError{"Failed to serialize engine"});
    }
    
    std::ofstream file(engine_path, std::ios::binary);
    if (!file) {
        return std::unexpected(TRTError{"Failed to create engine file: " + engine_path.string()});
    }
    
    file.write(static_cast<const char*>(serialized->data()), serialized->size());
    if (!file) {
        return std::unexpected(TRTError{"Failed to write engine file"});
    }
    
    return {};
}

int32_t TRTEngine::num_io_tensors() const {
    return engine_ ? engine_->getNbIOTensors() : 0;
}

const char* TRTEngine::io_tensor_name(int32_t index) const {
    return engine_ ? engine_->getIOTensorName(index) : nullptr;
}

nvinfer1::Dims TRTEngine::io_tensor_shape(const char* name) const {
    return engine_ ? engine_->getTensorShape(name) : nvinfer1::Dims{};
}

nvinfer1::DataType TRTEngine::io_tensor_dtype(const char* name) const {
    return engine_ ? engine_->getTensorDataType(name) : nvinfer1::DataType::kFLOAT;
}

bool TRTEngine::is_input(const char* name) const {
    return engine_ ? engine_->getTensorIOMode(name) == nvinfer1::TensorIOMode::kINPUT : false;
}

nvinfer1::IExecutionContext* TRTEngine::create_context() {
    return engine_ ? engine_->createExecutionContext() : nullptr;
}

// TRTContext implementation
TRTContext::TRTContext(TRTEngine& engine) {
    context_.reset(engine.create_context());
}

TRTContext::~TRTContext() = default;

bool TRTContext::set_input_shape(const char* name, nvinfer1::Dims dims) {
    return context_ ? context_->setInputShape(name, dims) : false;
}

bool TRTContext::set_tensor_address(const char* name, void* ptr) {
    return context_ ? context_->setTensorAddress(name, ptr) : false;
}

bool TRTContext::enqueue(cudaStream_t stream) {
    return context_ ? context_->enqueueV3(stream) : false;
}

} // namespace lattice
