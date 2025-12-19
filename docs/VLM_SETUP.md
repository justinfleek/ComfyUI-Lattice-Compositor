# Vision Language Model (VLM) Setup Guide

Weyl Compositor uses vision-language models to analyze images and suggest motion paths, camera movements, and animation keyframes. This guide explains how to set up VLM support.

## Quick Start

1. **Open the AI Path Suggestion dialog** (in the viewport toolbar or via keyboard shortcut)
2. **Select a model** from the dropdown:
   - **Rule-Based (Offline)** - Works without any model, uses keyword matching
   - **Local Models** - Qwen2-VL, Qwen3-VL (requires setup below)
   - **Cloud Models** - GPT-4o, Claude Vision (requires API key)
3. **Enter a motion description** (e.g., "gentle dolly in towards subject")
4. **Click "Suggest Paths"** to get AI-generated motion suggestions

---

## Local Model Setup (Recommended)

### Option 1: Automatic Download (Easiest)

When you first use a local model, Weyl will attempt to download it from HuggingFace automatically. This requires:

- **Internet connection** for first-time download
- **~6-18GB disk space** depending on model size
- **~6-18GB VRAM** for GPU inference (or CPU fallback)

**Recommended models:**
| Model | Size | VRAM | Quality |
|-------|------|------|---------|
| Qwen2-VL-2B-Instruct | ~4GB | ~6GB | Good |
| Qwen2-VL-7B-Instruct | ~14GB | ~16GB | Better |
| Qwen3-VL-8B | ~16GB | ~18GB | Best |

### Option 2: Pre-download Models

For offline use or faster startup, pre-download models to your ComfyUI folder:

```bash
# Navigate to your ComfyUI models folder
cd ComfyUI/models/LLM

# Download using HuggingFace CLI
pip install huggingface_hub

# Download Qwen2-VL-2B (smaller, faster)
huggingface-cli download Qwen/Qwen2-VL-2B-Instruct --local-dir Qwen2-VL-2B-Instruct

# OR download Qwen2-VL-7B (larger, better quality)
huggingface-cli download Qwen/Qwen2-VL-7B-Instruct --local-dir Qwen2-VL-7B-Instruct
```

### Option 3: Use ComfyUI Custom Nodes

Install one of these ComfyUI custom nodes that handle model management:

**ComfyUI-QwenVL** (Recommended):
```bash
cd ComfyUI/custom_nodes
git clone https://github.com/1038lab/ComfyUI-QwenVL.git
cd ComfyUI-QwenVL
pip install -r requirements.txt
```

**ComfyUI_Qwen3-VL-Instruct**:
```bash
cd ComfyUI/custom_nodes
git clone https://github.com/IuvenisSapiens/ComfyUI_Qwen3-VL-Instruct.git
pip install -r ComfyUI_Qwen3-VL-Instruct/requirements.txt
```

---

## Model Locations

Weyl looks for VLM models in these locations (in order):

1. `ComfyUI/models/LLM/Qwen2-VL-7B-Instruct/`
2. `ComfyUI/models/LLM/Qwen2-VL-2B-Instruct/`
3. `ComfyUI/models/LLM/Qwen-VL/`
4. `ComfyUI/models/LLM/Qwen3-VL-8B/`
5. `~/.cache/huggingface/hub/` (HuggingFace cache)
6. Auto-download from HuggingFace if not found

---

## Requirements

### Python Dependencies

These are typically already installed with ComfyUI, but if needed:

```bash
pip install torch transformers accelerate pillow
```

### Hardware Requirements

| Model | Minimum VRAM | Recommended VRAM | CPU Fallback |
|-------|--------------|------------------|--------------|
| 2B | 6GB | 8GB | Yes (slow) |
| 7B | 14GB | 16GB | Possible |
| 8B | 16GB | 20GB | Not recommended |

**Quantization** (reduce VRAM):
- 8-bit quantization: ~50% VRAM reduction
- 4-bit quantization: ~75% VRAM reduction

To enable quantization, install:
```bash
pip install bitsandbytes
```

---

## Cloud Model Setup

### OpenAI GPT-4o / GPT-4V

1. Get an API key from [OpenAI Platform](https://platform.openai.com/api-keys)
2. In the AI Path Suggestion dialog, select "GPT-4o" or "GPT-4V"
3. Enter your API key in the "API Key" field
4. Click "Test" to verify connection

**Cost**: ~$0.01-0.03 per image analysis

### Claude Vision

1. Get an API key from [Anthropic Console](https://console.anthropic.com/)
2. Select "Claude Vision" in the dialog
3. Enter your API key (starts with `sk-ant-`)
4. Click "Test" to verify

**Cost**: ~$0.01-0.02 per image analysis

---

## Usage Tips

### Motion Prompts

The AI understands natural language descriptions:

**Camera movements:**
- "dolly in slowly"
- "orbit around the subject"
- "gentle drift to the right"
- "dramatic crane shot"
- "handheld shake effect"

**Path suggestions:**
- "path following the depth contours"
- "trajectory around the main subject"
- "spiral path towards center"

**Combined:**
- "gentle dolly with slight handheld shake"
- "orbit around subject while rising"

### Best Practices

1. **Provide context**: Describe what you want to achieve
2. **Use intensity words**: "gentle", "dramatic", "subtle", "strong"
3. **Specify duration**: "over 3 seconds" or "81 frames"
4. **Review suggestions**: AI suggestions are starting points, adjust as needed

---

## Troubleshooting

### "VLM model not available"

1. Check if `transformers` is installed: `pip install transformers`
2. Verify model is downloaded to correct folder
3. Check ComfyUI console for loading errors
4. Try the 2B model first (smallest)

### "CUDA out of memory"

1. Use a smaller model (2B instead of 7B)
2. Enable quantization
3. Close other GPU applications
4. Fall back to CPU (slower but works)

### "Connection failed" for cloud models

1. Verify API key is correct
2. Check internet connection
3. Ensure you have API credits/quota
4. Check if the service is operational

### Slow inference

1. Ensure GPU is being used (check console output)
2. Use smaller model
3. Reduce image resolution before sending
4. Cloud models are typically faster than local

---

## API Reference

### Check VLM Status

```bash
curl http://localhost:8188/weyl/vlm/status
```

Returns:
```json
{
  "status": "success",
  "cuda_available": true,
  "cuda_device": "NVIDIA RTX 4090",
  "transformers_available": true,
  "model_loaded": true,
  "current_model": "qwen2-vl",
  "available_models": [...]
}
```

### Analyze Image

```bash
curl -X POST http://localhost:8188/weyl/vlm \
  -H "Content-Type: application/json" \
  -d '{
    "image": "base64_encoded_png",
    "prompt": "suggest camera motion for this scene",
    "model": "qwen2-vl"
  }'
```

---

## Model Comparison

| Model | Speed | Quality | Context Window | Best For |
|-------|-------|---------|----------------|----------|
| Rule-Based | Instant | Basic | N/A | Quick prototyping |
| Qwen2-VL-2B | Fast | Good | 32K | General use |
| Qwen2-VL-7B | Medium | Very Good | 32K | Quality results |
| GPT-4o | Fast | Excellent | 128K | Best quality |
| Claude Vision | Fast | Excellent | 200K | Complex scenes |

---

## Links

- [Qwen2-VL on HuggingFace](https://huggingface.co/Qwen/Qwen2-VL-7B-Instruct)
- [ComfyUI-QwenVL](https://github.com/1038lab/ComfyUI-QwenVL)
- [ComfyUI_Qwen3-VL-Instruct](https://github.com/IuvenisSapiens/ComfyUI_Qwen3-VL-Instruct)
- [OpenAI API](https://platform.openai.com/docs/guides/vision)
- [Anthropic API](https://docs.anthropic.com/en/docs/build-with-claude/vision)
