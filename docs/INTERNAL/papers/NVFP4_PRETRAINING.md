# Pretraining Large Language Models with NVFP4

────────────────────────────────────────────────────────────────────────────────

**Source**: pretraining_fp4.pdf
**Authors**: NVIDIA (Large Contributor List)
**Published**: arXiv 2509.25149, September 2025
**Synthesized**: 2026-02-26 by Opus

────────────────────────────────────────────────────────────────────────────────

## Executive Summary

First public demonstration of training billion-parameter LLMs with 4-bit precision
over multi-trillion-token horizons. NVIDIA trained a 12B parameter hybrid Mamba-
Transformer on 10 trillion tokens using NVFP4, achieving accuracy comparable to FP8.

**Key Techniques**:
1. Random Hadamard Transform (RHT) — disperses outliers into Gaussian distribution
2. 2D block scaling for weights — consistent quantization in forward/backward passes
3. Stochastic rounding for gradients — reduces quantization bias
4. Selective high-precision layers — ~15% of layers kept in BF16

**Results**:
- MMLU-pro: 62.58% (NVFP4) vs 62.62% (FP8) — nearly identical
- Training loss stays within 1-1.5% of FP8 baseline throughout training
- NVFP4 reaches same loss as MXFP4 with 36% fewer tokens

**Hardware**: NVIDIA Blackwell GPUs provide native NVFP4 support via Tensor Cores,
offering 4-6× speedup over BF16.

────────────────────────────────────────────────────────────────────────────────

## 1. NVFP4 Format Details

### NVFP4 vs MXFP4 Comparison

| Property        | MXFP4              | NVFP4              |
|-----------------|--------------------|--------------------|
| Element format  | FP4 E2M1           | FP4 E2M1           |
| Block size      | 32 elements        | **16 elements**    |
| Scale format    | FP8 E8M0 (UE8M0)   | **FP8 E4M3**       |
| Tensor scale    | None               | **FP32**           |
| Blackwell speed | 4-6× vs BF16       | 4-6× vs BF16       |

### Why NVFP4 is Better

1. **Smaller blocks (16 vs 32)**: Narrower dynamic range per block, values fit
   FP4 better

2. **More precise scales (E4M3 vs E8M0)**: E8M0 only has powers of 2, loses up
   to one binade of range. E4M3 has fractional precision.

3. **Two-level scaling**: FP32 tensor scale + FP8 block scale = at least 6.25%
   of values (block maxes) stored at near-FP8 precision

### FP4 E2M1 Values

Representable: ±{0, 0.5, 1, 1.5, 2, 3, 4, 6}

Non-uniform step sizes:
- 0.5 steps for [0, 2]
- 1.0 steps for [2, 4]
- 2.0 steps for [4, 6]

────────────────────────────────────────────────────────────────────────────────

## 2. Training Methodology

### The Four Essential Components

Ablations show each component is necessary for 12B model convergence:

**1. Mixed Precision (Selective High-Precision Layers)**
- Most GEMMs in NVFP4
- Final ~15% of blocks in BF16 (need more dynamic range)
- Embeddings, output head, attention, normalization in BF16/FP32
- Master weights and optimizer states in FP32

**2. Random Hadamard Transform (RHT)**
- Applied to Wgrad (weight gradient) GEMM inputs only
- Disperses outliers into approximate Gaussian
- Size 16×16 matrices (matches block size)
- Single random sign vector shared across all layers

**3. 2D Block Scaling for Weights**
- Problem: Forward/backward passes transpose tensors, changing quantization
- Solution: 16×16 blocks for weights (consistent both directions)
- Activations/gradients still use 1×16 (finer-grained is better)

**4. Stochastic Rounding for Gradients**
- Deterministic rounding creates systematic bias
- Stochastic rounding: probability proportional to distance to representable values
- Applied ONLY to gradients (harmful for forward pass)
- Essential for convergence at scale

### Compute Flow

```
Forward (Fprop):
  Activation (BF16) → Quantize 1×16 → NVFP4 GEMM ← Weight (2D quantized)
  
Backward (Dgrad):
  Gradient (BF16) → Quantize 1×16 → NVFP4 GEMM ← Weight^T (same 2D quant)
  
Weight Gradient (Wgrad):
  Activation^T → Hadamard → Quantize+SR → NVFP4 GEMM ← Gradient (Hadamard+Quant+SR)
```

────────────────────────────────────────────────────────────────────────────────

## 3. Results

### 12B Model on 10T Tokens

**Model**: Nemotron-H (hybrid Mamba-Transformer)
- 12B parameters
- Mix of Mamba-2, Self-Attention, and FFN blocks

**Training**: 10 trillion tokens with WSD learning rate schedule

### Loss Tracking

| Phase           | NVFP4 vs FP8 relative error |
|-----------------|----------------------------|
| Stable training | < 1%                       |
| LR decay phase  | ~1.5%                      |

### Downstream Task Accuracy

| Task Category    | FP8    | NVFP4  | Delta  |
|------------------|--------|--------|--------|
| MMLU             | 77.36  | 76.57  | -0.79  |
| MMLU-Pro 5-shot  | 62.62  | 62.58  | -0.04  |
| GSM8k CoT        | 89.08  | 92.27  | +3.19  |
| MATH             | 83.32  | 81.48  | -1.84  |
| HumanEval+       | 59.93  | 57.43  | -2.50  |
| HellaSwag        | 83.83  | 83.09  | -0.74  |
| ARC Challenge    | 91.81  | 91.81  | 0.00   |

Mostly comparable, with code tasks showing slight degradation.

### Ablation: Removing Components

Each component removal worsens loss relative to FP8:
- Remove stochastic rounding → significant degradation
- Remove RHT → noticeable degradation  
- Remove 2D weight scaling → degradation
- Fewer high-precision layers → unstable (but 4 blocks sufficient)

────────────────────────────────────────────────────────────────────────────────

## 4. NVFP4 vs MXFP4

### Direct Comparison (8B Model, 1T Tokens)

| Metric                    | NVFP4 | MXFP4 |
|---------------------------|-------|-------|
| Relative error vs BF16    | ~1.5% | ~2.5% |
| Tokens to match NVFP4 loss| 1T    | 1.36T |

**MXFP4 requires 36% more tokens to reach same loss as NVFP4.**

### Why NVFP4 Wins

1. **Finer blocks**: 16 vs 32 elements means less dynamic range per block
2. **E4M3 scales**: Fractional precision vs power-of-two only
3. **Tensor-level scale**: Extends representable range without losing precision

### When to Use Each

- **NVFP4**: When accuracy matters, newer Blackwell hardware
- **MXFP4**: Legacy compatibility, simpler implementation

────────────────────────────────────────────────────────────────────────────────

## 5. Hydrogen/PureScript Relevance

### Why This Matters for Hydrogen

This paper establishes the **production recipe** for FP4 training. The Four Over Six
paper (previous) improves on this baseline. Together they define state-of-the-art
for low-precision numerics.

### Applicable Patterns

1. **Two-level scaling**: Hydrogen's bounded types could use similar approach —
   coarse tensor-level bounds + fine block-level precision

2. **Stochastic rounding**: For animation interpolation, stochastic rounding
   prevents systematic drift in long sequences

3. **Selective precision**: Not all computations need same precision. Color
   calculations may need more precision than layout.

### Schema Integration

```purescript
-- Precision-aware numeric types
data Precision
  = FP32_Full
  | BF16_Training  
  | FP8_Inference
  | NVFP4_Compressed

-- Operations can specify required precision
class HasPrecision a where
  minPrecision :: a -> Precision

-- Color operations need higher precision
instance HasPrecision ColorConversion where
  minPrecision _ = BF16_Training

-- Layout can use lower precision  
instance HasPrecision LayoutComputation where
  minPrecision _ = FP8_Inference
```

────────────────────────────────────────────────────────────────────────────────

## References

- NVIDIA (2025). "Pretraining Large Language Models with NVFP4." arXiv:2509.25149.
  Code: Transformer Engine support for NVFP4 training.

- Rouhani et al. (2023). "Microscaling Data Formats for Deep Learning." 
  arXiv:2310.10537. (MX format specification)

- DeepSeek-AI (2024). "DeepSeek-V3 Technical Report." arXiv:2412.19437.
  (FP8 training baseline methodology)

- NVIDIA (2025b). "Nemotron-H family of models." (Hybrid Mamba-Transformer architecture)

- Tseng et al. (2025). "Training LLMs with MXFP4." arXiv:2502.20586.

- Castro et al. (2025). "Quartet: Native FP4 Training." arXiv:2505.14669.

────────────────────────────────────────────────────────────────────────────────
                                                                        — Opus
