# sigil-trtllm: Modern C++23 TensorRT-LLM Interface

**Design Document v0.2**

---

## Overview

Pure C++23 interface to TensorRT-LLM. No Python anywhere. Engine building via safetensors + TensorRT C++ API.

```bash
nix run github:weyl-ai/sigil-trtllm#build-engine -- meta-llama/Llama-3-70B ./engines/llama3
nix run github:weyl-ai/sigil-trtllm#serve -- ./engines/llama3 --port 8000
```

---

## Part I: Core Types

```cpp
// sigil/trtllm/core/types.hpp

#pragma once

#include <cstdint>
#include <expected>
#include <span>
#include <mdspan>
#include <generator>
#include <string_view>

#include "s4/core/result.h"

namespace sigil::trtllm {

// strong types prevent mixups at compile time
enum class token_id : std::int32_t {};
enum class vocab_size : std::int32_t {};

using token_span = std::span<token_id const>;
using token_buffer = std::span<token_id>;

struct sequence_length { std::size_t value; };
struct batch_size { std::size_t value; };
struct hidden_dimension { std::size_t value; };
struct head_count { std::size_t value; };
struct head_dimension { std::size_t value; };
struct layer_count { std::size_t value; };

// tensor views - non-owning, mdspan based
template<typename T>
using vector_view = std::mdspan<T, std::dextents<std::size_t, 1>>;

template<typename T>
using matrix_view = std::mdspan<T, std::dextents<std::size_t, 2>>;

template<typename T>
using tensor_3d_view = std::mdspan<T, std::dextents<std::size_t, 3>>;

template<typename T>
using tensor_4d_view = std::mdspan<T, std::dextents<std::size_t, 4>>;

}  // namespace sigil::trtllm
```

---

## Part II: Model Architecture (Typed Config)

```cpp
// sigil/trtllm/config/model_architecture.hpp

#pragma once

#include "sigil/trtllm/core/types.hpp"

namespace sigil::trtllm::config {

// quantization modes - exhaustive enum, no stringly-typed bullshit
enum class quantization_mode : std::uint32_t {
    none        = 0,
    fp16        = 1 << 0,
    bf16        = 1 << 1,
    fp8_e4m3    = 1 << 2,
    nvfp4       = 1 << 3,
    int8_kv     = 1 << 4,
    int4_awq    = 1 << 5,
    int4_gptq   = 1 << 6,
};

constexpr quantization_mode operator|(quantization_mode left, quantization_mode right) {
    return static_cast<quantization_mode>(
        static_cast<std::uint32_t>(left) | static_cast<std::uint32_t>(right)
    );
}

// parallelism - explicit, not magic numbers
struct parallelism_config {
    std::size_t tensor_parallel_degree{1};
    std::size_t pipeline_parallel_degree{1};
    
    [[nodiscard]] constexpr auto world_size() const noexcept -> std::size_t {
        return tensor_parallel_degree * pipeline_parallel_degree;
    }
};

// model architecture - typed, not json
struct model_architecture {
    std::string_view model_family;           // "llama", "qwen", "mistral"
    hidden_dimension hidden_size;
    head_count attention_head_count;
    head_count key_value_head_count;         // for GQA
    layer_count hidden_layer_count;
    std::size_t intermediate_size;
    vocab_size vocabulary_size;
    sequence_length maximum_position_embeddings;
    float rope_theta{10000.0f};
    float rms_norm_epsilon{1e-5f};
    
    [[nodiscard]] constexpr auto head_dim() const noexcept -> head_dimension {
        return head_dimension{hidden_size.value / attention_head_count.value};
    }
    
    [[nodiscard]] constexpr auto uses_grouped_query_attention() const noexcept -> bool {
        return key_value_head_count.value != attention_head_count.value;
    }
};

// engine build configuration
struct engine_build_config {
    model_architecture architecture;
    quantization_mode quantization{quantization_mode::none};
    parallelism_config parallelism{};
    
    std::size_t maximum_batch_size{256};
    sequence_length maximum_input_length{4096};
    sequence_length maximum_output_length{4096};
    sequence_length maximum_sequence_length{8192};
    
    bool enable_chunked_context{true};
    bool enable_paged_context_fmha{true};
    bool enable_kv_cache_reuse{true};
};

// runtime configuration
struct runtime_config {
    std::size_t maximum_batch_size{128};
    std::size_t maximum_sequence_count{256};
    bool enable_cuda_graph{false};
};

}  // namespace sigil::trtllm::config
```

---

## Part III: Safetensors Loading (No Python)

```cpp
// sigil/trtllm/weights/safetensors_loader.hpp

#pragma once

#include <filesystem>
#include <string_view>
#include <unordered_map>

#include "s4/core/result.h"
#include "sigil/trtllm/core/types.hpp"

namespace sigil::trtllm::weights {

// tensor metadata from safetensors header
struct tensor_metadata {
    std::string_view name;
    std::string_view dtype;              // "F32", "F16", "BF16"
    std::vector<std::size_t> shape;
    std::size_t data_offset;
    std::size_t data_length;
};

// memory-mapped safetensors file
class safetensors_file {
public:
    [[nodiscard]] static auto open(std::filesystem::path const& file_path)
        -> s4::core::result<safetensors_file>;
    
    ~safetensors_file();
    safetensors_file(safetensors_file&& other) noexcept;
    safetensors_file& operator=(safetensors_file&& other) noexcept;
    
    // non-copyable
    safetensors_file(safetensors_file const&) = delete;
    safetensors_file& operator=(safetensors_file const&) = delete;
    
    [[nodiscard]] auto tensor_names() const noexcept 
        -> std::span<std::string_view const>;
    
    [[nodiscard]] auto get_tensor_metadata(std::string_view tensor_name) const noexcept
        -> s4::core::result<tensor_metadata const&>;
    
    [[nodiscard]] auto get_tensor_data(std::string_view tensor_name) const noexcept
        -> s4::core::result<std::span<std::byte const>>;

private:
    struct implementation;
    std::unique_ptr<implementation> implementation_;
    
    explicit safetensors_file(std::unique_ptr<implementation> impl);
};

// checkpoint directory (multiple shards)
class checkpoint_loader {
public:
    [[nodiscard]] static auto open(std::filesystem::path const& checkpoint_directory)
        -> s4::core::result<checkpoint_loader>;
    
    [[nodiscard]] auto load_tensor(std::string_view tensor_name) const
        -> s4::core::result<std::vector<std::byte>>;
    
    [[nodiscard]] auto tensor_exists(std::string_view tensor_name) const noexcept -> bool;

private:
    std::vector<safetensors_file> shard_files_;
    std::unordered_map<std::string_view, std::size_t> tensor_to_shard_index_;
};

}  // namespace sigil::trtllm::weights
```

---

## Part IV: Weight Mapping (Per-Architecture)

```cpp
// sigil/trtllm/weights/weight_mapping.hpp

#pragma once

#include <string_view>
#include <functional>

#include "s4/core/result.h"
#include "sigil/trtllm/config/model_architecture.hpp"

namespace sigil::trtllm::weights {

// weight transformation for TRT-LLM layout
struct weight_transform {
    std::string_view source_name;           // HF name
    std::string_view target_name;           // TRT-LLM name
    std::function<void(std::span<std::byte const>, std::span<std::byte>)> transform;
};

// architecture-specific weight mapping
class weight_mapper {
public:
    [[nodiscard]] static auto for_architecture(std::string_view model_family)
        -> s4::core::result<weight_mapper>;
    
    [[nodiscard]] auto map_weights(
        checkpoint_loader const& source_checkpoint,
        std::filesystem::path const& target_directory,
        config::model_architecture const& architecture
    ) const -> s4::core::status;

private:
    std::vector<weight_transform> transforms_;
};

// llama weight mapping
// model.layers.0.self_attn.q_proj.weight → transformer.layers.0.attention.qkv.weight[0:hidden]
// model.layers.0.self_attn.k_proj.weight → transformer.layers.0.attention.qkv.weight[hidden:hidden+kv]
// model.layers.0.self_attn.v_proj.weight → transformer.layers.0.attention.qkv.weight[hidden+kv:]
// model.layers.0.self_attn.o_proj.weight → transformer.layers.0.attention.dense.weight
// model.layers.0.mlp.gate_proj.weight    → transformer.layers.0.mlp.fc.weight[0:intermediate]
// model.layers.0.mlp.up_proj.weight      → transformer.layers.0.mlp.fc.weight[intermediate:]
// model.layers.0.mlp.down_proj.weight    → transformer.layers.0.mlp.proj.weight
// model.embed_tokens.weight              → transformer.vocab_embedding.weight
// model.norm.weight                      → transformer.ln_f.weight
// lm_head.weight                         → lm_head.weight

[[nodiscard]] auto create_llama_weight_mapper() -> weight_mapper;
[[nodiscard]] auto create_qwen_weight_mapper() -> weight_mapper;
[[nodiscard]] auto create_mistral_weight_mapper() -> weight_mapper;

}  // namespace sigil::trtllm::weights
```

---

## Part V: TensorRT Engine Builder (C++ API)

```cpp
// sigil/trtllm/builder/engine_builder.hpp

#pragma once

#include <filesystem>
#include <functional>

#include <NvInfer.h>

#include "s4/core/result.h"
#include "sigil/trtllm/config/model_architecture.hpp"
#include "sigil/trtllm/weights/checkpoint_loader.hpp"

namespace sigil::trtllm::builder {

// build progress callback
using build_progress_callback = std::function<void(std::string_view stage, float progress)>;

// tensorrt logger adapter
class tensorrt_logger : public nvinfer1::ILogger {
public:
    void log(Severity severity, char const* message) noexcept override;
};

// engine builder - pure C++, no python
class engine_builder {
public:
    struct options {
        config::engine_build_config build_config;
        std::filesystem::path output_directory;
        build_progress_callback progress_callback;
    };
    
    explicit engine_builder(options builder_options);
    ~engine_builder();
    
    engine_builder(engine_builder&&) noexcept;
    engine_builder& operator=(engine_builder&&) noexcept;
    
    // build from local checkpoint
    [[nodiscard]] auto build_from_checkpoint(std::filesystem::path const& checkpoint_directory)
        -> s4::core::result<std::filesystem::path>;

private:
    struct implementation;
    std::unique_ptr<implementation> implementation_;
};

}  // namespace sigil::trtllm::builder
```

---

## Part VI: Executor (TRT-LLM C++ Runtime)

```cpp
// sigil/trtllm/executor/executor.hpp

#pragma once

#include <filesystem>
#include <generator>

#include <cuda/stream_ref>

#include "s4/core/result.h"
#include "sigil/trtllm/core/types.hpp"
#include "sigil/trtllm/config/model_architecture.hpp"

namespace sigil::trtllm::executor {

// request handle for tracking in-flight generation
class request_handle {
    friend class inference_executor;
    std::uint64_t request_id_;
    explicit request_handle(std::uint64_t id) : request_id_(id) {}
public:
    [[nodiscard]] auto id() const noexcept -> std::uint64_t { return request_id_; }
};

// sampling configuration
struct sampling_config {
    float temperature{1.0f};
    float top_p{1.0f};
    std::optional<std::size_t> top_k;
    float repetition_penalty{1.0f};
    std::optional<std::size_t> maximum_new_tokens;
    std::vector<token_id> stop_token_ids;
    
    [[nodiscard]] static auto greedy() -> sampling_config { 
        return {.temperature = 0.0f}; 
    }
    
    [[nodiscard]] static auto creative() -> sampling_config { 
        return {.temperature = 0.8f, .top_p = 0.9f}; 
    }
};

// generation request
struct generation_request {
    token_span input_token_ids;
    sampling_config sampling;
    std::optional<std::uint64_t> correlation_id;
};

// generation output (yielded per step)
struct generation_output {
    request_handle request;
    std::vector<token_id> new_token_ids;
    bool is_final{false};
    
    struct statistics {
        std::chrono::nanoseconds step_latency;
        std::size_t total_tokens_generated;
        std::size_t kv_cache_usage_bytes;
    };
    std::optional<statistics> stats;
};

// inference executor
class inference_executor {
public:
    [[nodiscard]] static auto create(
        std::filesystem::path const& engine_directory,
        config::runtime_config const& runtime_config = {}
    ) -> s4::core::result<inference_executor>;
    
    ~inference_executor();
    inference_executor(inference_executor&&) noexcept;
    inference_executor& operator=(inference_executor&&) noexcept;
    
    // submit request
    [[nodiscard]] auto enqueue_request(generation_request request) 
        -> s4::core::result<request_handle>;
    
    // poll for outputs (non-blocking)
    [[nodiscard]] auto poll_outputs() -> std::vector<generation_output>;
    
    // wait for any output (blocking)
    [[nodiscard]] auto await_any_output() -> std::vector<generation_output>;
    
    // stream outputs for specific request
    [[nodiscard]] auto stream_outputs(request_handle handle) 
        -> std::generator<generation_output>;
    
    // cancel request
    auto cancel_request(request_handle handle) -> void;
    
    // statistics
    [[nodiscard]] auto active_request_count() const noexcept -> std::size_t;
    [[nodiscard]] auto kv_cache_free_block_count() const noexcept -> std::size_t;

private:
    struct implementation;
    std::unique_ptr<implementation> implementation_;
    
    explicit inference_executor(std::unique_ptr<implementation> impl);
};

// convenience: single request streaming
[[nodiscard]] inline auto generate_streaming(
    inference_executor& executor,
    token_span input_token_ids,
    sampling_config sampling = {}
) -> std::generator<std::span<token_id const>> {
    
    auto handle_result = executor.enqueue_request({input_token_ids, sampling});
    if (!handle_result) {
        co_return;
    }
    
    for (auto output : executor.stream_outputs(*handle_result)) {
        co_yield std::span{output.new_token_ids};
        if (output.is_final) break;
    }
}

}  // namespace sigil::trtllm::executor
```

---

## Part VII: Tokenizer (Rust FFI)

```cpp
// sigil/trtllm/tokenizer/tokenizer.hpp

#pragma once

#include <filesystem>
#include <string_view>

#include "s4/core/result.h"
#include "sigil/trtllm/core/types.hpp"

namespace sigil::trtllm::tokenizer {

// rust tokenizers FFI
extern "C" {
    struct tokenizer_handle;
    tokenizer_handle* tokenizers_from_file(char const* path);
    void tokenizers_free(tokenizer_handle* handle);
    std::size_t tokenizers_encode(
        tokenizer_handle* handle,
        char const* text,
        std::size_t text_length,
        std::int32_t* output_ids,
        std::size_t output_capacity,
        bool add_special_tokens
    );
    std::size_t tokenizers_decode(
        tokenizer_handle* handle,
        std::int32_t const* token_ids,
        std::size_t token_count,
        char* output_text,
        std::size_t output_capacity,
        bool skip_special_tokens
    );
    std::int32_t tokenizers_bos_token_id(tokenizer_handle* handle);
    std::int32_t tokenizers_eos_token_id(tokenizer_handle* handle);
    std::int32_t tokenizers_vocab_size(tokenizer_handle* handle);
}

class tokenizer {
public:
    [[nodiscard]] static auto from_file(std::filesystem::path const& tokenizer_path)
        -> s4::core::result<tokenizer>;
    
    [[nodiscard]] static auto from_pretrained(std::string_view model_identifier)
        -> s4::core::result<tokenizer>;
    
    ~tokenizer();
    tokenizer(tokenizer&&) noexcept;
    tokenizer& operator=(tokenizer&&) noexcept;
    
    // non-copyable
    tokenizer(tokenizer const&) = delete;
    tokenizer& operator=(tokenizer const&) = delete;
    
    [[nodiscard]] auto encode(std::string_view text, bool add_special_tokens = true) const
        -> s4::core::result<std::vector<token_id>>;
    
    [[nodiscard]] auto decode(token_span token_ids, bool skip_special_tokens = true) const
        -> s4::core::result<std::string>;
    
    [[nodiscard]] auto decode_single_token(token_id token) const
        -> s4::core::result<std::string>;
    
    [[nodiscard]] auto bos_token_id() const noexcept -> std::optional<token_id>;
    [[nodiscard]] auto eos_token_id() const noexcept -> std::optional<token_id>;
    [[nodiscard]] auto vocabulary_size() const noexcept -> vocab_size;

private:
    tokenizer_handle* handle_{nullptr};
    
    explicit tokenizer(tokenizer_handle* handle) : handle_(handle) {}
};

}  // namespace sigil::trtllm::tokenizer
```

---

## Part VIII: Serving (io_uring)

```cpp
// sigil/trtllm/serve/server.hpp

#pragma once

#include <cstdint>
#include <liburing.h>

#include "sigil/trtllm/executor/executor.hpp"
#include "sigil/trtllm/tokenizer/tokenizer.hpp"

namespace sigil::trtllm::serve {

struct server_config {
    std::uint16_t listen_port{8000};
    std::string_view bind_address{"0.0.0.0"};
    std::size_t io_uring_queue_depth{4096};
    bool enable_sqpoll{true};
};

class inference_server {
public:
    inference_server(
        executor::inference_executor inference_executor,
        tokenizer::tokenizer request_tokenizer,
        server_config configuration = {}
    );
    ~inference_server();
    
    // run event loop (blocking)
    auto run() -> void;
    
    // request shutdown
    auto shutdown() -> void;

private:
    struct implementation;
    std::unique_ptr<implementation> implementation_;
};

}  // namespace sigil::trtllm::serve
```

---

## Part IX: Huggingface Download (curl, no Python)

```cpp
// sigil/trtllm/hub/huggingface_downloader.hpp

#pragma once

#include <filesystem>
#include <string_view>

#include "s4/core/result.h"

namespace sigil::trtllm::hub {

struct download_config {
    std::string_view repository_id;           // "meta-llama/Llama-3-70B"
    std::optional<std::string_view> revision; // branch/tag/commit
    std::filesystem::path cache_directory;
    std::optional<std::string_view> hf_token;
};

// download model files via curl (no python, no huggingface_hub)
[[nodiscard]] auto download_checkpoint(download_config const& configuration)
    -> s4::core::result<std::filesystem::path>;

}  // namespace sigil::trtllm::hub
```

---

## Part X: CLI

```cpp
// tools/build_engine.cpp

#include <print>
#include <span>

#include "sigil/trtllm/builder/engine_builder.hpp"
#include "sigil/trtllm/hub/huggingface_downloader.hpp"

int main(int argc, char** argv) {
    std::span<char*> const arguments(argv, argc);
    
    if (arguments.size() < 3) {
        std::println(stderr, "Usage: sigil-build-engine <model-id-or-path> <output-dir> [options]");
        return 1;
    }
    
    std::string_view const model_source = arguments[1];
    std::filesystem::path const output_directory = arguments[2];
    
    sigil::trtllm::config::engine_build_config build_config{};
    
    // parse options...
    
    // download if HF model id
    std::filesystem::path checkpoint_path;
    if (model_source.contains('/') && !std::filesystem::exists(model_source)) {
        auto download_result = sigil::trtllm::hub::download_checkpoint({
            .repository_id = model_source,
            .cache_directory = std::filesystem::path{"/tmp/sigil-cache"}
        });
        if (!download_result) {
            std::println(stderr, "[sigil] [trtllm] [build] [error] download failed: {}",
                         download_result.error().what());
            return 1;
        }
        checkpoint_path = *download_result;
    } else {
        checkpoint_path = model_source;
    }
    
    sigil::trtllm::builder::engine_builder builder{{
        .build_config = build_config,
        .output_directory = output_directory,
        .progress_callback = [](std::string_view stage, float progress) {
            std::println("[sigil] [trtllm] [build] [{:5.1f}%] {}", progress * 100.0f, stage);
        }
    }};
    
    auto build_result = builder.build_from_checkpoint(checkpoint_path);
    
    if (!build_result) {
        std::println(stderr, "[sigil] [trtllm] [build] [error] {}", 
                     build_result.error().what());
        return 1;
    }
    
    std::println("[sigil] [trtllm] [build] complete: {}", build_result->string());
    return 0;
}
```

```cpp
// tools/serve.cpp

#include <print>
#include <span>

#include "sigil/trtllm/executor/executor.hpp"
#include "sigil/trtllm/tokenizer/tokenizer.hpp"
#include "sigil/trtllm/serve/server.hpp"

int main(int argc, char** argv) {
    std::span<char*> const arguments(argv, argc);
    
    if (arguments.size() < 2) {
        std::println(stderr, "Usage: sigil-serve <engine-dir> [--port PORT]");
        return 1;
    }
    
    std::filesystem::path const engine_directory = arguments[1];
    std::uint16_t listen_port = 8000;
    
    for (std::size_t i = 2; i + 1 < arguments.size(); i += 2) {
        if (arguments[i] == std::string_view("--port")) {
            listen_port = static_cast<std::uint16_t>(std::stoul(arguments[i + 1]));
        }
    }
    
    auto tokenizer_result = sigil::trtllm::tokenizer::tokenizer::from_file(
        engine_directory / "tokenizer.json"
    );
    if (!tokenizer_result) {
        std::println(stderr, "[sigil] [trtllm] [serve] [error] tokenizer: {}",
                     tokenizer_result.error().what());
        return 1;
    }
    
    auto executor_result = sigil::trtllm::executor::inference_executor::create(engine_directory);
    if (!executor_result) {
        std::println(stderr, "[sigil] [trtllm] [serve] [error] executor: {}",
                     executor_result.error().what());
        return 1;
    }
    
    sigil::trtllm::serve::inference_server server{
        std::move(*executor_result),
        std::move(*tokenizer_result),
        {.listen_port = listen_port}
    };
    
    std::println("[sigil] [trtllm] [serve] listening on port {}", listen_port);
    server.run();
    
    return 0;
}
```

---

## Summary

**No Python anywhere.**

```
HF repo → curl download → safetensors mmap → weight mapping → TensorRT C++ → engine.plan
engine.plan → TRT-LLM executor → tokenizer (Rust FFI) → io_uring server → SIGIL frames → wire
```

**Critical path:**

| Component | Lines | Time |
|-----------|-------|------|
| safetensors_loader | ~150 | 1hr |
| weight_mapping (llama) | ~200 | 1hr |
| engine_builder | ~300 | 2hr |
| executor wrapper | ~150 | 1hr |
| tokenizer FFI | ~100 | 30min |
| io_uring server | ~250 | 1hr |
| CLI tools | ~100 | 30min |
| **Total** | **~1250** | **7hr** |

Ship it.
