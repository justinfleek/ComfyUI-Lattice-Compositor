# CosyVoice 2: Scalable Streaming Speech Synthesis with Large Language Models

**arXiv:** 2412.10117  
**Authors:** Zhihao Du, Yuxuan Wang, Qian Chen, Xian Shi, Xiang Lv, Tianyu Zhao, Zhifu Gao, Yexin Yang, Changfeng Gao, Hui Wang, Fan Yu, Huadai Liu, Zhengyan Sheng, Yue Gu, Chong Deng, Wen Wang, Shiliang Zhang, Zhijie Yan, Jingren Zhou (Alibaba)  
**Status:** DONE

---

## 1. Abstract

CosyVoice 2 is an improved streaming zero-shot TTS model with human-parity naturalness, minimal response latency, and nearly lossless synthesis quality in streaming mode.

Key contributions:
- Unified streaming and non-streaming synthesis in single framework
- Simplified LM architecture using pre-trained LLM as backbone
- Finite scalar quantization (FSQ) replacing VQ in speech tokenizer
- Chunk-aware causal flow matching model

---

## 2. Architecture Overview

### 2.1 Three-Component System

```
┌─────────────────┐     ┌──────────────────────┐     ┌─────────────┐
│ Text Tokenizer  │────▶│ Text-Speech LM      │────▶│ Flow Match │
│ (BPE-based)    │     │ (Qwen2.5-0.5B)     │     │ Model       │
└─────────────────┘     └──────────────────────┘     └──────┬──────┘
                                                            │
                                                            ▼
                                                   ┌─────────────┐
                                                   │   Vocoder   │
                                                   │ (Pre-trained)│
                                                   └─────────────┘
```

### 2.2 Pipeline

1. **Text Tokenizer:** Raw text → BPE tokens
2. **Speech Tokenizer:** Audio → Discrete tokens (25 Hz)
3. **Text-Speech LM:** Autoregressive token generation
4. **Flow Matching:** Tokens → Mel spectrogram
5. **Vocoder:** Mel → Waveform

---

## 3. Key Components

### 3.1 Text Tokenizer

- BPE-based tokenizer
- Masks one-to-many tokens (multi-char Chinese)
- Eliminates need for g2p frontend

### 3.2 Supervised Semantic Speech Tokenizer (FSQ)

**Definition 1 (Finite Scalar Quantization):**
```
H = Encoder1(speech)
H_quantized = ROUND(ProjDown(H))
H_reconstructed = ProjUp(H_quantized)
```

**Equation 1 (FSQ Forward):**
```
Ĥ = ProjUp(ROUND(ProjDown(H)))
```

**Equation 2 (Token Index Calculation):**
```
µ_i = Σ_{j=0}^{D-1} ĥ_{i,j} × (2K + 1)^j
```

Where:
- D = dimension of low-rank space
- K = quantization level (values in [-K, K])
- Token rate: 25 Hz

### 3.3 Unified Text-Speech Language Model

**Backbone:** Qwen2.5-0.5B (pre-trained LLM)

**Design changes from CosyVoice 1:**
- Removed speaker embedding (avoids info leaking)
- Removed text encoder (LLM handles alignment)
- Single model for streaming + non-streaming

**Sequence Construction:**

| Mode | Sequence |
|------|----------|
| Non-Streaming | S, text, T, speech, E |
| Streaming | [S, text_1...text_N, speech_1...speech_M] × k |

Where N=5, M=15 (pre-defined ratio)

---

## 4. Chunk-Aware Causal Flow Matching

### 4.1 Flow Matching Basics

**Definition 2 (Optimal Transport Flow):**
```
ω_t(φ_t(X_0, X_1) | X_1) = X_1 - X_0
```

**Equation 3 (OT Flow):**
```
φ_t(X_0, X_1) = (1 - t)X_0 + tX_1
```

Where t ∈ [0, 1] is the flow time.

### 4.2 Chunk-Aware Architecture

- Lookahead convolution: P = 4 (right-padded 1D conv)
- Causal Transformer blocks for alignment
- Upsampling: speech tokens (25 Hz) → Mel (50 Hz)

### 4.3 Masking Strategies

| Mask Type | Description |
|-----------|-------------|
| Full-causal | Standard autoregressive |
| Chunk-M | Generate M tokens at a time |
| Chunk-2M | Generate 2M tokens at a time |

---

## 5. Streaming vs Non-Streaming Modes

### 5.1 Inference Scenarios

| Scenario | Mode | Behavior |
|----------|------|----------|
| ICL, Non-Streaming | Prompt + text → speech | Full generation |
| ICL, Streaming | Mixed text/speech → generate every M tokens | Streaming output |
| SFT, Non-Streaming | S, text, T → speech | No prompt needed |
| SFT, Streaming | S, first N text → generate M tokens → repeat | Continuous |

### 5.2 Latency

- First packet: 150ms
- Real-time factor: Streaming mode nearly lossless

---

## 6. Key Definitions

1. **FSQ:** Finite Scalar Quantization - replaces VQ with bounded round operation
2. **Flow Matching:** Generative model predicting velocity fields
3. **Chunk-aware:** Processing tokens in fixed-size chunks for streaming
4. **OT Flow:** Optimal Transport flow - straight interpolation from noise to data

---

## 7. Relation to Hydrogen

### 7.1 Voice Interface

```purescript
-- Speech generation types
data SpeechToken
  = SemanticToken Int        -- 25 Hz discrete tokens
  | AcousticToken Tensor     -- Mel spectrogram

data TTSConfig
  = TTSConfig
      { sampleRate :: Hz 24000
      , melBins :: Int 80
      , frameRate :: Hz 50
      }

-- Streaming synthesis
streamTTS :: 
  forall msg. 
  TextInput -> 
  Stream (Element msg)
```

### 7.2 Zero-Shot Voice

```purescript
-- Voice cloning from reference
data VoiceReference
  = VoiceReference
      { audio :: ByteArray
      , duration :: Milliseconds
      }

zeroShotVoice ::
  VoiceReference ->
  TextInput ->
  SpeechToken
```

---

## 8. Bibliography

1. Du et al. "CosyVoice 2: Scalable Streaming Speech Synthesis with Large Language Models" 2024
2. Alibaba "FunAudioLLM" 2024

---

*Document generated: 2026-02-26*
