// Lattice Diffusion Inference Server
// Entry point - delegates to server.cpp InferenceServer

#include "tensorrt_engine.hpp"
#include "scheduler.hpp"
#include "safetensors.hpp"

#include <cuda_runtime.h>

#include <iostream>
#include <string>
#include <cstdlib>

namespace {

void print_usage(const char* prog_name) {
    std::cout << "Usage: " << prog_name << " [OPTIONS]\n"
              << "\n"
              << "Lattice Diffusion Inference Server\n"
              << "\n"
              << "Options:\n"
              << "  --port PORT       Server port (default: 8080)\n"
              << "  --models PATH     Models directory (default: /mnt/d/models)\n"
              << "  --build-engines   Build TensorRT engines from ONNX on startup\n"
              << "  --cache PATH      Engine cache directory\n"
              << "  --fp16            Enable FP16 inference (default: on)\n"
              << "  --bf16            Enable BF16 inference\n"
              << "  --int8            Enable INT8 inference\n"
              << "  --workspace SIZE  TensorRT workspace size in MB (default: 1024)\n"
              << "  --verbose         Enable verbose logging\n"
              << "  --help            Show this help message\n"
              << "\n"
              << "Example:\n"
              << "  " << prog_name << " --port 8080 --models /mnt/d/models --fp16\n";
}

struct Config {
    int port = 8080;
    std::string models_path = "/mnt/d/models";
    std::string cache_path;
    bool build_engines = false;
    bool fp16 = true;
    bool bf16 = false;
    bool int8 = false;
    size_t workspace_mb = 1024;
    bool verbose = false;
};

bool parse_args(int argc, char* argv[], Config& config) {
    for (int i = 1; i < argc; ++i) {
        std::string arg = argv[i];
        
        if (arg == "--help" || arg == "-h") {
            print_usage(argv[0]);
            return false;
        }
        else if (arg == "--port" && i + 1 < argc) {
            config.port = std::stoi(argv[++i]);
        }
        else if (arg == "--models" && i + 1 < argc) {
            config.models_path = argv[++i];
        }
        else if (arg == "--cache" && i + 1 < argc) {
            config.cache_path = argv[++i];
        }
        else if (arg == "--build-engines") {
            config.build_engines = true;
        }
        else if (arg == "--fp16") {
            config.fp16 = true;
        }
        else if (arg == "--bf16") {
            config.bf16 = true;
        }
        else if (arg == "--int8") {
            config.int8 = true;
        }
        else if (arg == "--workspace" && i + 1 < argc) {
            config.workspace_mb = std::stoull(argv[++i]);
        }
        else if (arg == "--verbose") {
            config.verbose = true;
        }
        else {
            std::cerr << "Unknown option: " << arg << "\n";
            print_usage(argv[0]);
            return false;
        }
    }
    return true;
}

void print_cuda_info() {
    int device_count = 0;
    cudaError_t err = cudaGetDeviceCount(&device_count);
    if (err != cudaSuccess) {
        std::cerr << "CUDA error: " << cudaGetErrorString(err) << "\n";
        return;
    }
    
    std::cout << "CUDA Devices: " << device_count << "\n";
    
    for (int i = 0; i < device_count; ++i) {
        cudaDeviceProp props;
        cudaGetDeviceProperties(&props, i);
        
        std::cout << "  [" << i << "] " << props.name << "\n"
                  << "      Compute: " << props.major << "." << props.minor << "\n"
                  << "      Memory: " << (props.totalGlobalMem / (1024 * 1024)) << " MB\n"
                  << "      SM Count: " << props.multiProcessorCount << "\n";
    }
}

} // anonymous namespace

// Forward declaration from server.cpp
namespace lattice {
    class InferenceServer;
}

// The actual main is in server.cpp, this is the standalone entry point
// that does initialization and validation before starting the server

int main(int argc, char* argv[]) {
    Config config;
    if (!parse_args(argc, argv, config)) {
        return 1;
    }
    
    std::cout << "=== Lattice Diffusion Inference Server ===\n\n";
    
    // Print CUDA device info
    print_cuda_info();
    std::cout << "\n";
    
    // Check models directory
    if (!std::filesystem::exists(config.models_path)) {
        std::cerr << "Warning: Models directory does not exist: " << config.models_path << "\n";
    }
    
    // Setup cache directory
    if (config.cache_path.empty()) {
        config.cache_path = config.models_path + "/.trt_cache";
    }
    std::filesystem::create_directories(config.cache_path);
    
    std::cout << "Configuration:\n"
              << "  Port: " << config.port << "\n"
              << "  Models: " << config.models_path << "\n"
              << "  Cache: " << config.cache_path << "\n"
              << "  FP16: " << (config.fp16 ? "enabled" : "disabled") << "\n"
              << "  BF16: " << (config.bf16 ? "enabled" : "disabled") << "\n"
              << "  INT8: " << (config.int8 ? "enabled" : "disabled") << "\n"
              << "  Workspace: " << config.workspace_mb << " MB\n"
              << "\n";
    
    // Test TensorRT initialization
    std::cout << "Testing TensorRT initialization...\n";
    {
        lattice::TRTLogger logger;
        auto* runtime = nvinfer1::createInferRuntime(logger);
        if (!runtime) {
            std::cerr << "Failed to create TensorRT runtime\n";
            return 1;
        }
        
        int trt_version = getInferLibVersion();
        std::cout << "  TensorRT Version: " 
                  << (trt_version / 1000) << "."
                  << ((trt_version / 100) % 10) << "."
                  << (trt_version % 100) << "\n";
        
        runtime->destroy();
    }
    std::cout << "\n";
    
    // If build-engines flag, look for ONNX models and build
    if (config.build_engines) {
        std::cout << "Building TensorRT engines from ONNX models...\n";
        
        lattice::BuildConfig build_config;
        build_config.fp16 = config.fp16;
        build_config.bf16 = config.bf16;
        build_config.int8 = config.int8;
        build_config.workspace_size = config.workspace_mb * 1024ULL * 1024ULL;
        
        // Scan for ONNX files
        for (const auto& entry : std::filesystem::recursive_directory_iterator(config.models_path)) {
            if (entry.path().extension() == ".onnx") {
                auto onnx_path = entry.path();
                auto engine_path = std::filesystem::path(config.cache_path) / 
                                   (onnx_path.stem().string() + ".engine");
                
                if (std::filesystem::exists(engine_path)) {
                    std::cout << "  [CACHED] " << onnx_path.filename().string() << "\n";
                    continue;
                }
                
                std::cout << "  [BUILD] " << onnx_path.filename().string() << "... ";
                std::cout.flush();
                
                auto result = lattice::TRTEngine::build_from_onnx(onnx_path, build_config);
                if (result) {
                    auto save_result = result->save(engine_path);
                    if (save_result) {
                        std::cout << "OK\n";
                    } else {
                        std::cout << "SAVE FAILED: " << save_result.error().message << "\n";
                    }
                } else {
                    std::cout << "FAILED: " << result.error().message << "\n";
                }
            }
        }
        std::cout << "\n";
    }
    
    std::cout << "Starting HTTP server on port " << config.port << "...\n";
    std::cout << "Press Ctrl+C to stop\n\n";
    
    // The server main loop is in server.cpp
    // This is a placeholder - we need to refactor to have a clean interface
    // For now, compile this as main and include the server initialization
    
    // The server.cpp already has its own main() function
    // In a real build, we'd either:
    // 1. Have server.cpp export a run_server() function
    // 2. Or combine into one translation unit
    
    // For now, this main.cpp demonstrates the initialization flow
    // The actual server is started from server.cpp's main()
    
    std::cout << "Note: Run the compiled 'diffusion-server' binary to start the actual server.\n";
    std::cout << "This entry point demonstrates initialization and configuration parsing.\n";
    
    return 0;
}
