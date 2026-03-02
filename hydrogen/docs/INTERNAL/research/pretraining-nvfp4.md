# Pretraining Large Language Models with NVFP4

**Attestation:** clarity

**Source:** NVIDIA  
**Paper:** pretraining-fp4.pdf  
**Date:** September 2025

---

## Abstract

This technical report demonstrates successful large-scale pretraining of LLMs using NVFP4 (4-bit floating point) precision. A 12B-parameter model was trained on 10 trillion tokens—the longest publicly documented FP4 training run to date. Results show training loss and downstream task accuracies comparable to FP8 baselines (e.g., MMLU-pro: 62.58% vs 62.62% FP8).

---

## 1. Introduction

### 1.1 Motivation

- Training frontier models requires tens to hundreds of yottaflops
- Improving pretraining efficiency is essential for next-generation models
- FP8 training is widely adopted; FP4 could provide additional speedups
- Challenges: training stability, convergence, implementation at scale

### 1.2 Contributions

- Novel NVFP4 training methodology
- First successful demonstration of 4-bit pretraining at multi-trillion token scale
- Comparable downstream accuracy to FP8 baseline

---

## 2. NVFP4 Format

### 2.1 Microscaling Formats

MX formats use block-wise representation where groups of elements share a scale factor:

| Format | Elements per Block | Scale Factor | Precision |
|--------|------------------|--------------|-----------|
| MXFP8 | 32 | E8M0 | 8-bit |
| MXFP6 | 32 | E8M0 | 6-bit |
| MXFP4 | 32 | E8M0 | 4-bit |
| **NVFP4** | **16** | **E4M3** | **4-bit** |

### 2.2 NVFP4 vs MXFP4

**NVFP4 advantages:**
- Smaller block size (16 vs 32) → more precise scaling
- E4M3 scale factors → better outlier handling
- Maximizes FP4 dynamic range utilization
- Better training behavior consistently

### 2.3 Hardware Support

NVIDIA Blackwell Tensor Cores provide native support for:
- MXFP8, MXFP6, MXFP4, NVFP4
- 4-6× speedup vs BF16
- Native rounding modes (round-to-nearest, stochastic)

---

## 3. Training Results

### 3.1 Setup

- **Model**: 12B hybrid Mamba-Transformer (Nemotron-H family)
- **Training tokens**: 10 trillion
- **Architecture**: 62 blocks (6 Self-Attention, 28 FFN, 28 Mamba-2)
- **Hardware**: NVIDIA B200 GPUs
- **Schedule**: Warmup-Stable-Decay (WSD)

### 3.2 Validation Loss

- NVFP4 closely tracks FP8 throughout training
- Relative loss error <1% during stable phase
- Widens to ~1.5% during decay phase

### 3.3 Downstream Accuracy

| Task | FP8 | NVFP4 |
|------|-----|-------|
| MMLU-Pro | 62.62 | **62.58** |
| MMLU | 77.36 | 76.57 |
| MATH | 83.32 | 81.48 |
| HumanEval+ | 59.93 | 57.43 |
| MBPP+ | 59.11 | 55.91 |

---

## 4. Training Methodology

### 4.1 Key Techniques

1. **Mixed precision**: Keep 15% of numerically-sensitive layers in BF16
2. **Random Hadamard transforms (RHT)**: Bound block-level outliers
3. **2D scaling**: Consistent quantization across forward/backward passes
4. **Stochastic rounding**: Unbiased gradient estimation

### 4.2 Mixed Precision Strategy

- First 2 blocks + last 8 blocks in BF16 (16% of linear layers)
- Embeddings, attention, normalization in BF16/FP32
- Optimizer states in FP32
- Most gain from forward pass quantization

### 4.3 Random Hadamard Transform

- Applied to WGRAD inputs (weight gradient GEMMs)
- Matrix size: 16×16 (balance of cost and effectiveness)
- Random sign vector for outlier distribution
- Reduces structured outliers that harm FP4 accuracy

### 4.4 2D Weight Scaling

- **Forward pass**: 1×16 scaling along output channels
- **Backward pass**: 16×1 scaling along input channels
- Maintains consistent quantization for backpropagation

### 4.5 Stochastic Rounding

- Essential for gradient tensors (reduces bias)
- Round-to-nearest-even for weights/activations
- Applying SR to forward pass is detrimental

---

## 5. Ablation Studies

### 5.1 Component Importance

Each technique is essential:
- Removing SR: divergence
- Removing RHT: worse convergence
- Removing 2D scaling: worse loss
- Fewer BF16 layers: instability

### 5.2 Layer Sensitivity

- Final layers more sensitive to FP4 quantization
- First layers + last layers in BF16 provides stability
- Can reduce high-precision layers as methodology improves

### 5.3 Hadamard Matrix Size

- 16×16 optimal for 12B model
- 4×4: too small, harms distribution
- 128×128: marginal benefit but higher cost

---

## 6. NVFP4 vs MXFP4

### 6.1 Comparison Results

- NVFP4 reaches comparable loss with **fewer tokens** than MXFP4
- NVFP4: better outlier handling, more precise scaling
- MXFP4: limited by power-of-two scale factors

### 6.2 Scale Factor Precision

**MXFP4 limitation:**
- Power-of-two scale factors cannot map perfectly to FP4 range
- Results in saturation and wasted dynamic range

**NVFP4 advantage:**
- E4M3 allows precise mapping to FP4 maximum
- Better utilization of FP4 bins

---

## 7. Conclusions

- NVFP4 pretraining is stable and accurate with proper methodology
- 12B model trained on 10T tokens matches FP8 accuracy
- First public evidence of sustained 4-bit pretraining at scale
- NVFP4 more efficient than MXFP4
- Future work: quantize all layers, reduce high-precision layers, extend to attention/communication

---

## Appendix: Key Formulas

### Global Tensor Scaling
```
s_enc6 × 448) / am = (ax(x)
```

### Local Block Scaling
```
s_decode,b = amax(b) / 6
```

### Hadamard Transform
```
x' = q(xH · s)
```
