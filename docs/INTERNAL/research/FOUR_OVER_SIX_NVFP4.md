# Four Over Six: More Accurate NVFP4 Quantization with Adaptive Block Scaling

**Attestation:** clarity

**Source:** Jack Cook, Junxian Guo, Guangxuan Xiao, Yujun Lin, Song Han  
**Paper:** four_over_six_nvfp4.pdf  
**GitHub:** github.com/mit-han-lab/fouroversix

---

## Abstract

FourOverSix (4/6) is a modification to the block-scaled NVFP4 quantization algorithm that reduces quantization error. The key insight is that FP4's non-uniform step sizes create larger errors for larger values. By adaptively scaling some blocks to smaller FP4 values (4 instead of 6), the distribution of representable values becomes more uniform, reducing worst-case quantization error for near-maximal values.

---

## 1. Introduction

### 1.1 Background

- LLMs have grown increasingly capable through increases in size and training speed
- Progression: FP32 → FP16 → BF16 → FP8 → FP4
- NVFP4: Block-scaled quantization format with FP4 values + FP8 scale factors

### 1.2 NVFP4 Format

- Stores values in FP4 E2M1
- FP8 E4M3 scale factor for every 16 values
- Tensor-wide FP32 scale factor α

**Equations:**
```
α_FP32 = max(|X|) / (M_FP4 × M_FP8)
Δ_FP8_i = max(|X_16i:16(i+1)|) / (α × M_FP4)
```

### 1.3 Problem

Current NVFP4 training recipes require:
- Random Hadamard Transform (RHT)
- Stochastic Rounding (SR)
- Keeping some layers in high precision
- "Healing" the model near end of training

These introduce computational overhead that makes FP8 training preferable.

---

## 2. Problems with NVFP4 Quantization

### 2.1 FP4 Non-Uniform Stepsizes

Unlike integer formats, FP4 has dynamic stepsizes:
- 0.5 between 0-2
- 1 between 2-4
- 2 between 4-6

This enables wider range but creates larger quantization error for larger values.

### 2.2 Key Finding: Error from Near-Maximal Values

Experiments with Llama-3.1-8B show:
- Error from scale factors contributes relatively little to performance loss
- Error on values around 5 (where FP4 has no representable values) is primarily responsible for poor performance

---

## 3. Four Over Six Method

### 3.1 Core Insight

Instead of scaling all blocks to the same value M_FP4 = 6, 4/6 allows changing this scale for some blocks to 4:

- **M=6**: Values spread over range -6 to 6
- **M=4**: Values spread over range -4 to 4

This makes representation more uniform and reduces worst-case error for values at ~75% of max.

### 3.2 Algorithm

For each block:
1. Compute scales for both M=4 and M=6
2. Quantize values using both scales
3. Compare quantization errors
4. Select the scale with lower MSE

### 3.3 Scale Selection Rules

| Rule | Description |
|------|-------------|
| Max Error | Smallest maximum error |
| L1 | Lowest L1 norm of errors |
| **MSE** | **Lowest mean squared error** (works best) |

### 3.4 Results

**WikiText-2 Perplexity (Llama 3, Qwen 3):**

| Model | BF16 | NVFP4 | NVFP4 + 4/6 |
|-------|------|-------|--------------|
| Llama 3 1B | 11.98 | 14.27 | **13.84** |
| Llama 3 8B | 7.54 | 8.43 | **8.30** |
| Qwen3 1.7B | 21.06 | 23.06 | **21.67** |

4/6 improves perplexity 19.9% closer to BF16 when combined with AWQ.

---

## 4. Pre-Training Results

### 4.1 Setup

- Model: Nemotron 3 Nano (MoE hybrid: Mamba + Transformer)
- Parameters: 30B total, 3B active
- Training: 1 trillion tokens
- Hardware: 384 B200 GPUs

### 4.2 Results

4/6 brings training loss **22.3% closer to BF16** compared to standard NVFP4.

---

## 5. Post-Training Quantization

### 5.1 Combined with PTQ Methods

| Method | Improvement with 4/6 |
|--------|---------------------|
| RTN | Improved in most cases |
| GPTQ | Mixed results |
| **AWQ** | **Best overall** (19.9% closer to BF16) |
| SmoothQuant | 5.3% closer to BF16 |

### 5.2 Downstream Tasks

4/6 improves or matches average task performance in nearly all cases on:
- BoolQ, Arc-E, Arc-C, HellaSwag

---

## 6. Implementation

### 6.1 Computational Flow

1. **FPROP**: NVFP4 GEMM with fused transpose + RHT + Q(4/6)
2. **WGRAD**: Same operations
3. **DGRAD**: NVFP4 GEMM with stochastic rounding
4. Weights stored in FP32
5. Activations/gradients in BF16

### 6.2 Hardware Support

- 4/6 efficiently implemented on NVIDIA Blackwell GPUs
- No additional computational overhead beyond standard NVFP4

---

## 7. Limitations

- Would not work with MXFP4 (requires FP8 scale factors with enough precision)
- Block scaled to 4 requires scale factor 50% larger than block scaled to 6
- FP8 E4M3 provides sufficient precision for this

---

## 8. Related Work

### 8.1 FP4 Formats

- **MXFP4**: 32 FP4 values + 8-bit E8M0 scale factor
- **NVFP4**: 16 FP4 values + 8-bit E4M3 scale factor

### 8.2 PTQ Methods

- **GPTQ**: Layer-wise optimization
- **AWQ**: Activation-aware weight quantization
- **SmoothQuant**: Smooths activations for better quantization

### 8.3 FP4 Training

- Requires stochastic rounding, RHT, and "healing" the model
- 4/6 reduces the overhead needed for accurate FP4 training
