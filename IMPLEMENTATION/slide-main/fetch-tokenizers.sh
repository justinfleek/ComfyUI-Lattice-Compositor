#!/usr/bin/env bash
set -e

# Helper to fetch tokenizer.json
fetch_tokenizer() {
    local model=$1
    local output_dir="tokenizers/$(basename $model)"
    
    echo "Fetching tokenizer for $model..."
    mkdir -p "$output_dir"
    
    # Try to fetch tokenizer.json
    if curl -L -f -o "$output_dir/tokenizer.json" "https://huggingface.co/$model/resolve/main/tokenizer.json"; then
        echo "✓ $model tokenizer.json downloaded."
    else
        echo "✗ Failed to download tokenizer.json for $model"
    fi
    
    # Try to fetch tokenizer_config.json (useful for metadata)
    curl -L -s -o "$output_dir/tokenizer_config.json" "https://huggingface.co/$model/resolve/main/tokenizer_config.json" || true
}

echo "Fetching tokenizers for supported model families..."

# Qwen 2.5 (Current default)
fetch_tokenizer "Qwen/Qwen2.5-7B-Instruct"

# Llama 3 (Used by Groq, Together, etc.)
# Using unsloth mirror to avoid gate checks if possible, or main if public
fetch_tokenizer "unsloth/llama-3-8b-Instruct"

# Mistral v0.3
fetch_tokenizer "mistralai/Mistral-7B-Instruct-v0.3"

# DeepSeek V3 (compatible with R1)
fetch_tokenizer "deepseek-ai/DeepSeek-V3"

# Gemma 2 (Google)
fetch_tokenizer "google/gemma-2-9b-it"

echo "Done. Tokenizers stored in tokenizers/"
