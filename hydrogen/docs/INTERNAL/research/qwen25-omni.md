# Qwen2.5-Omni Technical Report

## Paper Metadata

**Title:** Qwen2.5-Omni Technical Report

**Organization:** Qwen Team (Alibaba)

**Published:** March 2025

**arXiv:** arXiv:2503.20215v1 [cs.CL]

**Date:** March 26, 2025

**Resources:**
- HuggingFace: https://huggingface.co/Qwen
- ModelScope: https://modelscope.cn/organization/qwen
- GitHub: https://github.com/QwenLM/Qwen2.5-Omni

---

## Core Thesis

Qwen2.5-Omni is an end-to-end multimodal model designed to:
- **Perceive** diverse modalities (text, images, audio, video)
- **Generate** text and natural speech responses simultaneously
- **Stream** both outputs in real-time

Key innovation: Thinker-Talker architecture that separates understanding (brain) from generation (mouth) while maintaining end-to-end training.

---

## Key Innovations

### 1. Thinker-Talker Architecture

Inspired by human biology:
- **Thinker**: Transformer decoder responsible for understanding multimodal inputs, generating high-level representations and text
- **Talker**: Dual-track autoregressive model that generates streaming speech tokens using representations from Thinker

Both trained end-to-end jointly - shares all historical context.

### 2. TMRoPE (Time-aligned Multimodal RoPE)

Novel position embedding that explicitly incorporates temporal information for synchronizing audio and video:

- Extends M-RoPE (Multimodal Rotary Position Embedding) with absolute temporal positions
- Text: identical position IDs (1D-RoPE equivalent)
- Audio: 1 temporal ID = 40ms
- Images: constant temporal ID, distinct height/width IDs
- Video: temporal ID increments per frame, adjusted dynamically based on actual time
- Video with audio: time-interleaving method (2-second chunks, visual first, then audio)

### 3. Block-wise Streaming Processing

Modified all multimodal encoders for block-wise attention:
- Audio encoder: block attention of 2 seconds
- Vision encoder: merges 2×2 tokens, patch size 14
- Enables chunked prefills for efficient inference

### 4. Sliding Window DiT for Speech Codec

For streaming audio generation:
- Flow-Matching DiT with restricted receptive field
- Lookback: 2 blocks, Lookahead: 1 block
- Generates mel-spectrogram in chunks
- BigVGAN decoder with fixed receptive field for waveform

---

## Architecture Details

### Model Components

| Component | Description |
|-----------|-------------|
| Thinker | Transformer decoder (LLM backbone) |
| Audio Encoder | From Qwen2-Audio (Whisper-large-v3 init) |
| Vision Encoder | From Qwen2.5-VL (ViT ~675M params) |
| Talker | Dual-track autoregressive Transformer decoder |
| qwen-tts-tokenizer | Efficient speech codec |
| DiT | Flow-Matching for mel-spectrogram |
| BigVGAN | Modified for streaming waveform generation |

### Input Processing

| Modality | Processing |
|----------|------------|
| Text | Qwen tokenizer (151,643 tokens, byte-level BPE) |
| Audio | 16kHz resample → 128-channel mel-spectrogram (25ms window, 10ms hop) → ~40ms/frame |
| Image | ViT encoder, treated as 2 identical frames |
| Video | Dynamic frame rate sampling, interleaved with audio |

### Training Stages

| Stage | Focus | Data |
|-------|-------|------|
| Stage 1 | Train encoders (LLM frozen) | Image-text, audio-text pairs |
| Stage 2 | Unfreeze all, multimodal joint training | +800B image/video tokens, +300B audio tokens, +100B video-audio tokens |
| Stage 3 | Long sequence (32k tokens) | Extended data |

### Post-Training

**Thinker (SFT):**
- ChatML format
- Pure text, visual, audio, and mixed-modality dialogue data

**Talker (3-stage):**
1. **ICL Training**: Next-token prediction for speech continuation
2. **RL (DPO)**: Improve stability using WER-based rewards
3. **Speaker Fine-tuning**: Naturalness and controllability

---

## Results

### Text→Text (7B models)

| Benchmark | Qwen2.5-Omni | Qwen2.5-7B | Qwen2-7B |
|-----------|---------------|-------------|-----------|
| MMLU-Pro | 47.0 | 56.3 | 44.1 |
| MMLU-redux | 71.0 | 75.4 | 67.3 |
| MATH | 71.5 | 75.5 | 52.9 |
| GSM8K | 88.7 | 91.6 | 85.7 |
| MBPP | 73.2 | 79.2 | 67.2 |

### Audio→Text

| Task | Qwen2.5-Omni | Best Previous |
|------|---------------|----------------|
| ASR (LibriSpeech test-clean) | 1.8 | 1.3 (Qwen2-Audio) |
| ASR (CommonVoice zh) | 5.2 | 6.3 (MinMo) |
| S2TT (en-zh) | 41.4 | 45.2 (Qwen2-Audio) |
| VoiceChat (VoiceBench avg) | 74.12 | 71.69 (MiniCPM-o) |

### Image→Text

| Benchmark | Qwen2.5-Omni | Qwen2.5-VL-7B |
|-----------|---------------|-----------------|
| MMMUval | 59.2 | 58.6 |
| MathVistatestmini | 67.9 | 68.2 |
| MMBench-EN | 81.8 | 82.6 |
| DocVQA | 95.2 | 95.7 |

### Video→Text

| Benchmark | Qwen2.5-Omni | Qwen2.5-VL-7B |
|-----------|---------------|-----------------|
| Video-MME (w/ sub) | 72.4 | 71.6 |
| MVBench | 70.3 | 69.6 |
| EgoSchema | 68.6 | 65.0 |

### Multimodal→Text

| Benchmark | Qwen2.5-Omni | Previous Best |
|-----------|---------------|----------------|
| OmniBench (avg) | **56.13%** | 42.9% (Baichuan-Omni) |

### Speech Generation (X→Speech)

**Zero-shot TTS on SEED:**

| Model | WER (test-en) | WER (test-hard) | SIM (test-en) |
|-------|----------------|---------------------|------------------|
| Qwen2.5-Omni (RL) | **2.33** | **6.54** | 0.641 |
| MaskGCT | 2.62 | 10.27 | 0.714 |
| CosyVoice 2 | 2.57 | 6.83 | 0.652 |
| F5-TTS | 1.83 | 8.67 | 0.647 |

**Single-speaker naturalness (NMOS):**
- Human: 4.51 (en)
- Qwen2.5-Omni Speaker B: **4.62** (en)

---

## Key Findings

1. **Voice instruction following nearly matches text**
   - MMLU: 65.6 (voice) vs 69.3 (text) - only 5% gap
   - GSM8K: 85.4 (voice) vs 82.3 (text)

2. **Thinker-Talker separation works**
   - Talker uses Thinker's hidden representations directly
   - Enables concurrent text + speech generation
   - No interference between modalities

3. **TMRoPE enables video-audio sync**
   - Time-interleaving: 2-second chunks
   - Visual representation first, audio second
   - Dynamic temporal ID adjustment

4. **Block-wise processing reduces latency**
   - 2-second audio blocks
   - Vision: 2×2 token merging
   - Sliding window DiT: 4-block receptive field

---

## Relation to Hydrogen

### Multimodal Input Processing

- Block-wise streaming for audio/video
- Could apply to real-time UI interactions
- Time-interleaving for synchronized inputs

### Thinker-Talker Pattern

- Separate understanding from generation
- Could map to: Element understanding → Rendering generation
- Shared context between components

### Streaming Architecture

- Sliding window for audio codec
- Chunked prefills for efficiency
- Relevant for real-time rendering pipelines

### Position Embeddings

- TMRoPE for temporal alignment
- Could inform temporal coherence in animations
- Multi-modal position encoding for spatial-temporal data

---

## Technical Specifications

| Specification | Value |
|---------------|-------|
| Model Size | ~7B parameters |
| Audio Sample Rate | 16kHz |
| Audio Frame | 40ms |
| Mel Spectrogram | 128 channels |
| Vision Patch Size | 14 |
| Max Tokens (Stage 1-2) | 8,192 |
| Max Tokens (Stage 3) | 32,768 |
| Audio Block Size | 2 seconds |
| DiT Receptive Field | 4 blocks (2 lookback, 1 lookahead) |
| Vocabulary Size | 151,643 tokens |

---

## Summary

Qwen2.5-Omni demonstrates that a single model can:
1. **Understand** all modalities (text, image, audio, video)
2. **Generate** both text and speech simultaneously
3. **Stream** outputs with low latency

Key architectural innovations:
- Thinker-Talker separates understanding from generation
- TMRoPE synchronizes temporal information across modalities
- Block-wise processing enables efficient streaming
- Flow-matching DiT reduces speech generation latency

Results show competitive performance across all benchmarks, with particularly strong results in:
- Voice instruction following (nearly matching text)
- Multimodal reasoning (OmniBench SOTA)
- Speech generation quality (WER, naturalness)

---

**Citation:**
```
@article{qwen25omni2025,
  title={Qwen2.5-Omni Technical Report},
  author={Qwen Team},
  journal={arXiv preprint arXiv:2503.20215},
  year={2025}
}
```

---

*Document synthesized for Hydrogen research collection*
*Source: arXiv:2503.20215v1*
