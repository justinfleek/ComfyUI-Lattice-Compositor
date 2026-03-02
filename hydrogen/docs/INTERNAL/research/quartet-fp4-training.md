# Quartet: Native FP4 Training Can Be Optimal for LLMs

**arXiv:** 2505.14669  
**Authors:** Roberto L. Castro, Andrei Panferov, Soroush Tabesh, Oliver Sieberling, Jiale Chen, Mahdi Nikdan, Saleh Ashkboos, Dan Alistarh  
**Institution:** ISTA, ETH Zürich  
**Date:** January 15, 2026  
**Domain:** Machine Learning / Training / Quantization

---

## Abstract

Quartet demonstrates that native FP4 training for LLMs can achieve optimal accuracy-efficiency trade-offs. The key insight is a scaling law that quantifies the trade-off between parameter efficiency (forward pass) and data efficiency (backward pass).

**Key Results:**
- First systematic study of hardware-supported MXFP4 training
- Introduces scaling law for quantized training comparison
- Achieves near-lossless pre-training in FP4
- 2× speedup over FP8 on NVIDIA RTX 5090

---

## 1. The Problem: Low-Precision Training

### 1.1 Motivation

Training frontier LLMs requires unprecedented compute. Lower-precision computation offers:
- Near-linear throughput gains
- Energy efficiency improvements
- Reduced memory footprint

### 1.2 Current State

| Precision | Status | Challenge |
|-----------|--------|-----------|
| FP16 | Mature | Baseline |
| FP8 | Emerging | DeepSeek-V3 uses it |
| FP4 | Underexplored | Accuracy degradation |

### 1.3 Hardware Support

NVIDIA Blackwell architecture provides native FP4 support:
- MXFP4: Group of 32 elements, shared E8M0 scale
- NVFP4: Group of 16 elements, shared E4M3 scale

**Key finding:** MXFP4 is the only format supporting all layouts for forward AND backward multiplications on Blackwell.

---

## 2. Scaling Laws for Quantized Training

### 2.1 The Key Insight

Standard scaling laws relate loss to model size (N) and data (D):
```
L(N, D) = (A/N^α + B/D^β)^γ + E
```

**Novel contribution:** Extend to include precision:
```
L(N, D, P_forward, P_backward) = 
  (A / (N · effN(P_forward))^α + 
   B / (D · effD(P_backward))^β)^γ + E
```

### 2.2 Efficiency Parameters

| Parameter | Description | What It Measures |
|-----------|-------------|------------------|
| **effN(P_forward)** | Parameter efficiency | How forward precision affects effective model capacity |
| **effD(P_backward)** | Data efficiency | How backward precision affects gradient quality |

### 2.3 Trade-off Analysis

| Precision Pair | Forward Speedup | Backward Speedup | Training Speedup |
|----------------|-----------------|------------------|------------------|
| FP8:FP8 | 1.0 | 1.0 | 1.0 |
| FP4:FP8 | 2.0 | 1.0 | 1.2 |
| FP8:FP4 | 1.0 | 2.0 | 1.5 |
| **FP4:FP4** | **2.0** | **2.0** | **2.0** |

### 2.4 Optimality Regions

Based on scaling law fitting:
- **Large models + limited data:** FP4:FP4 optimal
- **Small models + abundant data:** FP8:FP8 sufficient
- **Inference-heavy workloads:** FP4:FP8 preferred

---

## 3. Quartet: Four Ingredients

### 3.1 Ingredient 1: Scaling Law Comparison

Compare methods via induced scaling laws:
- Fit parameters for each quantization method
- Method A > Method B if both effD are higher

 effN and### 3.2 Ingredient 2: Forward-Backward Trade-offs

```
Forward pass:  Low precision → Reduced parameter efficiency + Faster inference
Backward pass: Low precision → Reduced data efficiency + Faster training
```

### 3.3 Ingredient 3: Error-Bias Trade-off

**Forward Pass:** Minimize MSE (error minimization)
- QuEST (Hadamard + RMSE) achieves best effN

**Backward Pass:** Balance error and gradient alignment
- RTN outperforms stochastic rounding for backward

| Method | effN | MSE | effD | Misalignment |
|--------|------|-----|------|--------------|
| Stochastic Rounding | 0.42 | 2.77e-2 | 0.88 | 0 |
| RTN AbsMax | 0.59 | 1.37e-2 | 0.93 | 9.3e-3 |
| QuEST | 0.64 | 1.32e-2 | 0.83 | 1.3e-2 |

**Key insight:** Forward uses QuEST (lowest MSE), backward uses RTN (best gradient alignment).

### 3.4 Ingredient 4: GPU Implementation

```
Forward:  W → Q(W H)  (Hadamard + quantization)
          X → Q(X H)  
          Y = Q(W H) × Q(X H)ᵀ

Backward: Same, but with RTN quantization
```

**Hardware support:**
- MXFP4 on Blackwell (32 elements, E8M0 scale)
- Fused Hadamard + quantization kernels
- Native FP4 tensor core operations

---

## 4. Technical Details

### 4.1 MXFP4 Format

```
Element:     1 sign + 2 exponent + 1 mantissa = 4 bits
Group:       32 elements share one scale
Scale:       E8M0 (8 exponent, 0 mantissa) — powers of 2
Total bits:  4×32 + 8 = 136 bits / 32 elements = 4.25 bits/element
```

### 4.2 Hadamard Transform

For outlier mitigation:
```
h(x) = H_d × x
```
Where H_d is normalized Hadamard matrix (±1 elements).

**Efficient computation:** FWHT in O(d log d)

### 4.3 Quantization Formulas

**Forward (QuEST):**
```python
# Normalize
x_norm = H(x) / ||x||

# Quantize with MSE-optimal clipping
ŵ = round(x_norm / s)  # s = MSE-optimal scale

# De-normalize  
x̂ = s × ŵ × H
```

**Backward (RTN):**
```python
# Simple round-to-nearest with absmax scaling
s = max(|x|)
ŵ = round(x / s)
x̂ = s × ŵ
```

---

## 5. Experimental Results

### 5.1 Scaling Law Fits

| Model Size | FP16 Loss | FP4:FP4 Loss | Gap |
|------------|-----------|--------------|-----|
| 30M | 2.6 | 2.65 | +0.05 |
| 50M | 2.4 | 2.44 | +0.04 |
| 100M | 2.2 | 2.23 | +0.03 |
| 200M | 2.0 | 2.02 | +0.02 |

### 5.2 Accuracy vs. Speedup

| Method | Accuracy | Speedup vs FP8 |
|--------|----------|----------------|
| FP16 Baseline | 100% | 0.5× |
| FP8 Training | ~99% | 1.0× |
| INT4-Transformers | ~97% | 1.8× |
| **Quartet (FP4:FP4)** | **~99%** | **2.0×** |

### 5.3 Key Findings

1. **Near-lossless FP4 training** achievable with Quartet
2. **2× speedup** over FP8 on RTX 5090
3. **Scaling law accurately predicts** optimal precision selection
4. **Forward QuEST + backward RTN** is optimal combination

---

## 6. Relation to Hydrogen

### 6.1 Schema Training vs. Inference

This paper focuses on **training** in FP4, while microscaling paper focuses on **inference**. Both are relevant for Hydrogen:

| Phase | Relevant Paper | Application |
|-------|---------------|-------------|
| **Training** | Quartet | Pre-computing schema weights |
| **Inference** | Microscaling | Runtime quantization |

### 6.2 Error Bound Composition

Combining both works:

```purescript
-- Training phase (Quartet)
trainSchema :: FP4Training ()  -- FP4 forward + backward

-- Inference phase (Microscaling)  
quantizeSchema :: Schema -> FP4Schema  -- Post-training quantization

-- End-to-end bound
theorem Schema_Error_Bound {s : Schema} :
  RP (inference (quantize (train s))) s ≤ ε_total
  where ε_total = ε_training + ε_quantization
```

### 6.3 Design System Weights

For Hydrogen's learned components (e.g., learned color spaces, neural rendering):
- Pre-train in FP4 using Quartet
- Quantize using MR-GPTQ
- End-to-end error bounds composable

### 6.4 Hardware Efficiency

| Operation | FP16 | FP4 | Speedup |
|-----------|------|-----|---------|
| Matrix multiply | 1× | 2× | 2× |
| Memory bandwidth | 1× | 2× | 2× |
| Energy | 1× | 0.5× | 2× |

For billion-agent scale, this is critical.

---

## 7. The Four Ingredients Summary

| Ingredient | Purpose | Technique |
|------------|---------|-----------|
| **1. Scaling Laws** | Compare methods | Fit effN, effD parameters |
| **2. Trade-off Analysis** | Optimal precision selection | Forward vs backward budget |
| **3. Error-Bias Balance** | Minimize loss | QuEST (fwd) + RTN (bwd) |
| **4. GPU Implementation** | Hardware support | MXFP4 on Blackwell |

---

## 8. Key Insights for Billion-Agent Systems

### 8.1 When FP4 is Optimal

Based on scaling laws:
- Large models (1B+ parameters): FP4:FP4 optimal
- Small models: FP8 sufficient
- Inference-heavy: FP4 forward preferred

### 8.2 Composability

At billion-agent scale:
- Individual agent training in FP4
- Composition preserves error bounds
- Scaling laws predict aggregate behavior

### 8.3 Hardware Alignment

NVIDIA Blackwell supports:
- MXFP4: All operations (forward + backward)
- NVFP4: Limited layout support

**Recommendation:** Use MXFP4 for full-stack FP4 support.

---

## 9. Citation

```bibtex
@article{castro2026quartet,
  title={Quartet: Native FP4 Training Can Be Optimal for Large Language Models},
  author={Castro, Roberto L. and Panferov, Andrei and Tabesh, Soroush and Sieberling, Oliver and Chen, Jiale and Nikdan, Mahdi and Ashkboos, Saleh and Alistarh, Dan},
  year={2026},
  eprint={2505.14669},
  archivePrefix={arXiv},
  primaryClass={cs.LG}
}
```

---

*Research Document: Hydrogen Research Collection*
*Completed: 2026-02-26*
*Attestation: clarity*
