#pragma once

#include <cstdint>
#include <string>
#include <vector>
#include <unordered_map>
#include <span>
#include <expected>
#include <filesystem>

namespace lattice {

enum class DType : uint8_t {
    F32,
    F16,
    BF16,
    F64,
    I8,
    I16,
    I32,
    I64,
    U8,
    U16,
    U32,
    U64,
    BOOL,
    F8_E4M3,
    F8_E5M2,
};

[[nodiscard]] constexpr size_t dtype_size(DType dtype) noexcept {
    switch (dtype) {
        case DType::F32:
        case DType::I32:
        case DType::U32:
            return 4;
        case DType::F16:
        case DType::BF16:
        case DType::I16:
        case DType::U16:
            return 2;
        case DType::F64:
        case DType::I64:
        case DType::U64:
            return 8;
        case DType::I8:
        case DType::U8:
        case DType::BOOL:
        case DType::F8_E4M3:
        case DType::F8_E5M2:
            return 1;
    }
    return 0;
}

[[nodiscard]] constexpr const char* dtype_name(DType dtype) noexcept {
    switch (dtype) {
        case DType::F32: return "F32";
        case DType::F16: return "F16";
        case DType::BF16: return "BF16";
        case DType::F64: return "F64";
        case DType::I8: return "I8";
        case DType::I16: return "I16";
        case DType::I32: return "I32";
        case DType::I64: return "I64";
        case DType::U8: return "U8";
        case DType::U16: return "U16";
        case DType::U32: return "U32";
        case DType::U64: return "U64";
        case DType::BOOL: return "BOOL";
        case DType::F8_E4M3: return "F8_E4M3";
        case DType::F8_E5M2: return "F8_E5M2";
    }
    return "UNKNOWN";
}

struct TensorInfo {
    std::string name;
    DType dtype;
    std::vector<int64_t> shape;
    size_t data_offset_begin;
    size_t data_offset_end;
    
    [[nodiscard]] size_t numel() const noexcept {
        size_t n = 1;
        for (auto d : shape) n *= static_cast<size_t>(d);
        return n;
    }
    
    [[nodiscard]] size_t nbytes() const noexcept {
        return data_offset_end - data_offset_begin;
    }
};

struct SafetensorsError {
    std::string message;
};

class Safetensors {
public:
    Safetensors() = default;
    ~Safetensors();
    
    Safetensors(const Safetensors&) = delete;
    Safetensors& operator=(const Safetensors&) = delete;
    Safetensors(Safetensors&&) noexcept;
    Safetensors& operator=(Safetensors&&) noexcept;
    
    [[nodiscard]] static std::expected<Safetensors, SafetensorsError>
    load(const std::filesystem::path& path);
    
    [[nodiscard]] bool has_tensor(const std::string& name) const;
    [[nodiscard]] const TensorInfo* get_tensor_info(const std::string& name) const;
    [[nodiscard]] std::span<const uint8_t> get_tensor_data(const std::string& name) const;
    
    [[nodiscard]] const std::unordered_map<std::string, TensorInfo>& tensors() const {
        return tensors_;
    }
    
    [[nodiscard]] const std::unordered_map<std::string, std::string>& metadata() const {
        return metadata_;
    }

private:
    std::unordered_map<std::string, TensorInfo> tensors_;
    std::unordered_map<std::string, std::string> metadata_;
    
    // Memory-mapped file
    void* mmap_addr_ = nullptr;
    size_t mmap_size_ = 0;
    size_t data_offset_ = 0;
    int fd_ = -1;
};

} // namespace lattice
