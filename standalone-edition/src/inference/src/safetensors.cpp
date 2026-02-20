#include "safetensors.hpp"

#include <fcntl.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>

#include <cstring>
#include <fstream>

// Simple JSON parsing (minimal, just for safetensors header)
namespace {

struct JsonParser {
    const char* ptr;
    const char* end;
    
    void skip_ws() {
        while (ptr < end && (*ptr == ' ' || *ptr == '\n' || *ptr == '\r' || *ptr == '\t'))
            ++ptr;
    }
    
    bool expect(char c) {
        skip_ws();
        if (ptr < end && *ptr == c) { ++ptr; return true; }
        return false;
    }
    
    std::string parse_string() {
        skip_ws();
        if (ptr >= end || *ptr != '"') return {};
        ++ptr;
        std::string result;
        while (ptr < end && *ptr != '"') {
            if (*ptr == '\\' && ptr + 1 < end) {
                ++ptr;
                switch (*ptr) {
                    case 'n': result += '\n'; break;
                    case 'r': result += '\r'; break;
                    case 't': result += '\t'; break;
                    case '"': result += '"'; break;
                    case '\\': result += '\\'; break;
                    default: result += *ptr; break;
                }
            } else {
                result += *ptr;
            }
            ++ptr;
        }
        if (ptr < end) ++ptr; // skip closing quote
        return result;
    }
    
    int64_t parse_int() {
        skip_ws();
        int64_t result = 0;
        bool neg = false;
        if (ptr < end && *ptr == '-') { neg = true; ++ptr; }
        while (ptr < end && *ptr >= '0' && *ptr <= '9') {
            result = result * 10 + (*ptr - '0');
            ++ptr;
        }
        return neg ? -result : result;
    }
    
    std::vector<int64_t> parse_int_array() {
        std::vector<int64_t> result;
        if (!expect('[')) return result;
        skip_ws();
        if (ptr < end && *ptr == ']') { ++ptr; return result; }
        while (true) {
            result.push_back(parse_int());
            skip_ws();
            if (ptr < end && *ptr == ',') { ++ptr; continue; }
            if (ptr < end && *ptr == ']') { ++ptr; break; }
            break;
        }
        return result;
    }
    
    void skip_value() {
        skip_ws();
        if (ptr >= end) return;
        if (*ptr == '"') { parse_string(); return; }
        if (*ptr == '[') {
            ++ptr;
            int depth = 1;
            while (ptr < end && depth > 0) {
                if (*ptr == '[') ++depth;
                else if (*ptr == ']') --depth;
                ++ptr;
            }
            return;
        }
        if (*ptr == '{') {
            ++ptr;
            int depth = 1;
            while (ptr < end && depth > 0) {
                if (*ptr == '{') ++depth;
                else if (*ptr == '}') --depth;
                ++ptr;
            }
            return;
        }
        // number or literal
        while (ptr < end && *ptr != ',' && *ptr != '}' && *ptr != ']')
            ++ptr;
    }
};

lattice::DType parse_dtype(const std::string& s) {
    if (s == "F32") return lattice::DType::F32;
    if (s == "F16") return lattice::DType::F16;
    if (s == "BF16") return lattice::DType::BF16;
    if (s == "F64") return lattice::DType::F64;
    if (s == "I8") return lattice::DType::I8;
    if (s == "I16") return lattice::DType::I16;
    if (s == "I32") return lattice::DType::I32;
    if (s == "I64") return lattice::DType::I64;
    if (s == "U8") return lattice::DType::U8;
    if (s == "U16") return lattice::DType::U16;
    if (s == "U32") return lattice::DType::U32;
    if (s == "U64") return lattice::DType::U64;
    if (s == "BOOL") return lattice::DType::BOOL;
    if (s == "F8_E4M3") return lattice::DType::F8_E4M3;
    if (s == "F8_E5M2") return lattice::DType::F8_E5M2;
    return lattice::DType::F32;
}

} // anonymous namespace

namespace lattice {

Safetensors::~Safetensors() {
    if (mmap_addr_ && mmap_addr_ != MAP_FAILED) {
        munmap(mmap_addr_, mmap_size_);
    }
    if (fd_ >= 0) {
        close(fd_);
    }
}

Safetensors::Safetensors(Safetensors&& other) noexcept
    : tensors_(std::move(other.tensors_))
    , metadata_(std::move(other.metadata_))
    , mmap_addr_(other.mmap_addr_)
    , mmap_size_(other.mmap_size_)
    , data_offset_(other.data_offset_)
    , fd_(other.fd_)
{
    other.mmap_addr_ = nullptr;
    other.mmap_size_ = 0;
    other.fd_ = -1;
}

Safetensors& Safetensors::operator=(Safetensors&& other) noexcept {
    if (this != &other) {
        if (mmap_addr_ && mmap_addr_ != MAP_FAILED) {
            munmap(mmap_addr_, mmap_size_);
        }
        if (fd_ >= 0) {
            close(fd_);
        }
        tensors_ = std::move(other.tensors_);
        metadata_ = std::move(other.metadata_);
        mmap_addr_ = other.mmap_addr_;
        mmap_size_ = other.mmap_size_;
        data_offset_ = other.data_offset_;
        fd_ = other.fd_;
        other.mmap_addr_ = nullptr;
        other.mmap_size_ = 0;
        other.fd_ = -1;
    }
    return *this;
}

std::expected<Safetensors, SafetensorsError>
Safetensors::load(const std::filesystem::path& path) {
    Safetensors st;
    
    // Open file
    st.fd_ = open(path.c_str(), O_RDONLY);
    if (st.fd_ < 0) {
        return std::unexpected(SafetensorsError{"Failed to open file: " + path.string()});
    }
    
    // Get file size
    struct stat sb;
    if (fstat(st.fd_, &sb) < 0) {
        return std::unexpected(SafetensorsError{"Failed to stat file"});
    }
    st.mmap_size_ = static_cast<size_t>(sb.st_size);
    
    // Memory map
    st.mmap_addr_ = mmap(nullptr, st.mmap_size_, PROT_READ, MAP_PRIVATE, st.fd_, 0);
    if (st.mmap_addr_ == MAP_FAILED) {
        return std::unexpected(SafetensorsError{"Failed to mmap file"});
    }
    
    auto* data = static_cast<const uint8_t*>(st.mmap_addr_);
    
    // Read header size (8 bytes, little-endian u64)
    if (st.mmap_size_ < 8) {
        return std::unexpected(SafetensorsError{"File too small"});
    }
    uint64_t header_size = 0;
    std::memcpy(&header_size, data, 8);
    
    if (8 + header_size > st.mmap_size_) {
        return std::unexpected(SafetensorsError{"Invalid header size"});
    }
    
    st.data_offset_ = 8 + header_size;
    
    // Parse JSON header
    JsonParser parser{
        reinterpret_cast<const char*>(data + 8),
        reinterpret_cast<const char*>(data + 8 + header_size)
    };
    
    if (!parser.expect('{')) {
        return std::unexpected(SafetensorsError{"Invalid JSON: expected '{'"});
    }
    
    while (true) {
        parser.skip_ws();
        if (parser.ptr >= parser.end || *parser.ptr == '}') break;
        
        std::string key = parser.parse_string();
        if (!parser.expect(':')) break;
        
        if (key == "__metadata__") {
            // Skip metadata for now
            parser.skip_value();
        } else {
            // Parse tensor info
            TensorInfo info;
            info.name = key;
            
            if (!parser.expect('{')) break;
            
            while (true) {
                parser.skip_ws();
                if (parser.ptr >= parser.end || *parser.ptr == '}') break;
                
                std::string field = parser.parse_string();
                if (!parser.expect(':')) break;
                
                if (field == "dtype") {
                    info.dtype = parse_dtype(parser.parse_string());
                } else if (field == "shape") {
                    info.shape = parser.parse_int_array();
                } else if (field == "data_offsets") {
                    if (!parser.expect('[')) break;
                    info.data_offset_begin = static_cast<size_t>(parser.parse_int());
                    parser.expect(',');
                    info.data_offset_end = static_cast<size_t>(parser.parse_int());
                    parser.expect(']');
                } else {
                    parser.skip_value();
                }
                
                parser.skip_ws();
                if (parser.ptr < parser.end && *parser.ptr == ',') {
                    ++parser.ptr;
                }
            }
            parser.expect('}');
            
            st.tensors_[info.name] = std::move(info);
        }
        
        parser.skip_ws();
        if (parser.ptr < parser.end && *parser.ptr == ',') {
            ++parser.ptr;
        }
    }
    
    return st;
}

bool Safetensors::has_tensor(const std::string& name) const {
    return tensors_.contains(name);
}

const TensorInfo* Safetensors::get_tensor_info(const std::string& name) const {
    auto it = tensors_.find(name);
    if (it == tensors_.end()) return nullptr;
    return &it->second;
}

std::span<const uint8_t> Safetensors::get_tensor_data(const std::string& name) const {
    auto it = tensors_.find(name);
    if (it == tensors_.end()) return {};
    
    const auto& info = it->second;
    auto* base = static_cast<const uint8_t*>(mmap_addr_) + data_offset_;
    return {base + info.data_offset_begin, info.nbytes()};
}

} // namespace lattice
