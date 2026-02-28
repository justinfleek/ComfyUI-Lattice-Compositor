# FP4 All the Way: Fully Quantized Training of LLMs

**arXiv:** 2505.19115  
**Authors:** Brian Chmiel, Maxim Fishman, Ron Banner, Daniel Soudry (Intel, NVIDIA, Technion)  
**Status:** IN_PROGRESS

---

## 1. Abstract

First demonstration of fully quantized training (FQT) of LLMs using FP4 for weights, activations, and gradients on datasets up to 200B tokens. Key findings:
- NVFP4 format optimal (block size 16, E4M3 scale)
- Split rounding: SR for backward, RtN for forward
- Gradient noise threshold identified
- 7B model trained on 256 Intel Gaudi2, comparable to BF16

---

## 2. FP4 Format Comparison

### 2.1 MXFP4 vs NVFP4

| Parameter | MXFP4 | NVFP4 |
|-----------|-------|-------|
| Data Format | E2M1 | E2M1 |
| Block Size | 32 | 16 |
| Scale Format | E8M0 | E4M3 |

### 2.2 Scale Format Comparison (Figure 1 from paper)

Training 350M Llama-style model with different E#M# formats:
- E1M6: Diverged completely
- E2M5: Poor results
- **E3M4, E4M3: Best results** (E4M3 = NVFP4)
- E5M2: Good but slightly worse

**Conclusion:** E4M3 (NVFP4) is optimal.

---

## 3. Key Techniques

### 3.1 Split Rounding Strategy

| Pass | Rounding Method | Reason |
|------|----------------|--------|
| Forward | Round-to-Nearest (RtN) | Lower MSE |
| Backward | Stochastic Rounding (SR) | Reduces gradient bias |

### 3.2 Gradient Noise Threshold

**Theoretical bound:**
```
σ_gradient < √3 × σ_quantization
```

When gradient norm falls below this threshold, quantized training becomes less effective.

**Solution:** Apply Quantization-Aware Finetuning (QAF) at end of training.

---

## 4. Results

### 4.1 Scaling Experiments

| Tokens | Format | Final Loss | vs BF16 |
|--------|--------|-----------|---------|
| 200B | BF16 | 2.85 | baseline |
| 200B | FP4 (NVFP4) | 2.92 | +0.07 |
| 200B | FP4 + QAF | 2.86 | +0.01 |

### 4.2 Downstream Tasks

FP4-trained model with QAF achieves on-par results with BF16 baseline.

---

## 5. Key Definitions

1. **FQT:** Fully Quantized Training - all matrix multiplications in low precision
2. **NVFP4:** NVIDIA FP4 format with block size 16, E4M3 scale
3. **MXFP4:** Microscaling FP4 with block size 32, E8M0 scale
4. **QAF:** Quantization-Aware Finetuning - higher precision at end

---

## 6. Relation to Hydrogen

```purescript
-- FP4 tensor support
data FP4Format
  = NVFP4_16    -- Block size 16, E4M3 scale
  | MXFP4_32    -- Block size 32, E8M0 scale

data QuantizedTraining
  = FullyQuantized
      { weights :: Tensor FP4
      , activations :: Tensor FP4
      , gradients :: Tensor FP4
      , rounding :: RoundingMode
      }
```

---

## 7. Bibliography

1. Chmiel et al. "FP4 All the Way: Fully Quantized Training of LLMs" 2025

---

*Document generated: 2026-02-26*
