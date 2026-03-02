# Microscaling FP4 Quantization: Bridging the Gap Between Promise and Performance

**arXiv:** 2509.23202  
**Authors:** Roberto L. Castro, Vage Egiazarian, Denis Kuznedelev, Andrei Panferov, Eldar Kurtić, Shubhra Pandit, Alexandre Marques, Mark Kurtz, Saleh Ashkboos, Torsten Hoefler, Dan Alistarh  
**Institution:** ISTA, Red Hat AI, ETH Zürich, Yandex Research  
**Date:** October 16, 2025  
**Domain:** Machine Learning / Model Compression / Quantization

---

## Abstract

This paper presents the first comprehensive study of MXFP4 and NVFP4 microscaling 4-bit floating-point formats for post-training quantization (PTQ) of large language models. Key findings:

1. **NVFP4's small group size** neutralizes traditional outlier mitigation
2. **MXFP4's power-of-two scale quantization** induces significant accuracy degradation
3. **MR-GPTQ** — a variant of GPTQ tailored to FP4's unique properties using block-wise Hadamard transforms

Results: Up to 3.6x layer-wise speedup on NVIDIA B200, 6x on RTX5090, with 98-99% accuracy recovery.

---

## 1. Background: Microscaling FP Formats

### 1.1 The Problem with LLM Quantization

LLMs have extreme size, requiring quantization for deployment. Key challenges:

| Challenge | Description |
|-----------|-------------|
| **Outlier features** | Elements up to 100× larger than average |
| **Heavy-tailed distributions** | Laplace-like rather than Gaussian |
| **Activation quantization** | Even harder than weight quantization |

### 1.2 Microscaling Formats

Microscaling uses hierarchical quantization with shared scales:

```
Tensor → Groups → Shared Scale → Quantized Elements
```

| Format | Group Size | Element Format | Scale Format | Bits/Element |
|--------|-----------|---------------|--------------|--------------|
| **MXFP4** | 32 | FP4 (E2M1) | E8M0 (powers-of-two) | 4.25 |
| **NVFP4** | 16 | FP4 (E2M1) | E4M3 (full FP8) | 4.5 |

### 1.3 Format Details

**MXFP4 (Microscaling FP4):**
- Group size: 32 elements
- Scale: E8M0 (8 exponent, 0 mantissa) — powers-of-two only
- Hardware: AMD GPUs
- Issue: Coarse scale quantization induces artifacts

**NVFP4 (NVIDIA FP4):**
- Group size: 16 elements  
- Scale: E4M3 (4 exponent, 3 mantissa) — full FP8
- Hardware: NVIDIA Blackwell GPUs
- Better precision but more bits

### 1.4 FP4 Value Representation

E2M1 format (1 sign, 2 exponent, 1 mantissa):
```
Positive values: {0.5, 1.0, 1.5, 2.0, 3.0, 4.0, 6.0}
+ zero + negatives
```

---

## 2. Quantization Error Analysis

### 2.1 Distribution Modeling

**Key insight:** LLM parameters follow different distributions:

| Distribution | Source | Kurtosis |
|-------------|--------|----------|
| **Laplace** | Native weights/activations | High (8.75) |
| **Normal** | After Hadamard rotation | Low (0.02) |

**Implications:**
- Heavy-tailed (Laplace) distributions need larger group sizes
- Rotation transforms distributions to Normal, improving quantization

### 2.2 MSE Analysis

**Key Results:**

| Format | Group Size | Without Rotation | With Rotation |
|--------|-----------|-----------------|---------------|
| **NVFP4** | 16 | Good outlier preservation | May hurt |
| **MXFP4** | 32 | Poor due to E8M0 scales | Helps significantly |

**Theorem (Simplified):**
For small G (group size):
- Native Laplace < Rotated Normal (LapFor large G:
lace better)

- Rotated Normal < Native Laplace (rotation becomes effective)

### 2.3 Scale Precision Impact

**Critical finding:**

1. **MXFP4**: Top values inherit precision from E2M1 (not E8M0 scales)
   - E8M0 is coarser than E2M1
   - Error doesn't improve with group size

2. **NVFP4**: Top values inherit precision from E4M3 scales
   - E4M3 is finer than E2M1
   - Constant relative error regardless of G

---

## 3. MR-GPTQ: FP4-Optimized Quantization

### 3.1 Standard GPTQ

GPTQ minimizes output reconstruction error:
```
minimize: ||XŴ - XW||²
```

Key innovations over Optimal Brain Quantization (OBQ):
- Fixed weight order (column-by-column)
- Shared Hessian information across rows
- Complexity: O(max{drow · dcol², dcol³})

### 3.2 FP4 Adaptations

**Three Ingredients:**

1. **MSE-Optimized Grids**
   ```python
   # Optimize per-tensor and per-group scales
   min_{sT, sG} Σ ||ŵi - wi||²
   
   # Alternating optimization
   for group in groups:
       optimize_scale(group)
   ```

2. **Static Activation Reordering**
   - Reorder columns BEFORE quantization
   - No runtime overhead vs. dynamic reordering
   - Same accuracy improvement

3. **Fused Online Rotations**
   ```python
   # Quantize: Q(W H) Q(X H)ᵀ
   # Where H = block-wise Hadamard
   ```

### 3.3 Format-Specific Strategies

| Format | Strategy | Rationale |
|--------|----------|-----------|
| **NVFP4** | GPTQ + absmax | Small G preserves outliers |
| **MXFP4** | GPTQ + Hadamard rotation | Normalizes distribution |
| **NVFP4 + Rot** | GPTQ + MSE grid | Compensates rotation overhead |

---

## 4. GPU Kernels: QuTLASS

### 4.1 Architecture

High-performance library for Blackwell GPUs (SM100, SM120):

```
Weight Pre-processing:
  W → Q(W Hk)  (rotation fused into weights)

Activation Processing:
  X → Q(X Hk)ᵀ  (online rotation with custom epilogue)

Matrix Multiplication:
  Q(W Hk) × Q(X Hk)ᵀ → FP4 accumulator
```

### 4.2 Key Optimizations

| Optimization | Impact |
|-------------|--------|
| **Block-wise Hadamard** | k × k diagonal blocks (k ∈ {16, 32, 64, 128}) |
| **Fused quantization** | Scales computed in transformation kernel |
| **Memory-bound exploitation** | Dense transforms at same cost as Hadamard |

### 4.3 Performance Results

| GPU | Layer-wise Speedup | End-to-end Speedup |
|-----|-------------------|-------------------|
| NVIDIA B200 | 3.6× | 2.2× |
| RTX5090 | 6× | 4× |

---

## 5. Experimental Results

### 5.1 Accuracy: Llama-3.1-8B-Instruct

| Format | Method | MMLU | GSM8K | HellaSwag | Avg | Recovery |
|--------|--------|------|-------|------------|-----|----------|
| **FP16** | Baseline | 72.76 | 85.06 | 80.01 | 78.93 | 100% |
| INT4 | GPTQ | 66.36 | 76.65 | 77.38 | 73.21 | 92.75% |
| **NVFP4** | RTN | 68.26 | 78.39 | 78.15 | 74.73 | 94.67% |
| **NVFP4** | GPTQ | 68.85 | 82.60 | 78.26 | 75.72 | **95.92%** |
| **MXFP4** | RTN | 62.21 | 67.85 | 73.99 | 69.32 | 87.83% |
| **MXFP4** | MR-GPTQ | ~67 | ~78 | ~77 | ~74 | ~94% |

### 5.2 Key Findings

1. **NVFP4 outperforms MXFP4** with standard methods (RTN)
2. **MR-GPTQ bridges the gap** — MXFP4 within 1-2% of NVFP4
3. **Hadamard rotation helps MXFP4** but hurts NVFP4 (with RTN)
4. **Both formats can achieve 98-99%** of FP16 accuracy with proper method

---

## 6. Relation to Hydrogen

### 6.1 Schema Bounded Types

This work directly informs Hydrogen's bounded type design:

| Hydrogen Need | FP4 Solution |
|---------------|--------------|
| **Bounded precision** | FP4 provides 4-bit bounds |
| **Quantization error** | MR-GPTQ-style bounds |
| **Group scales** | Per-group scaling for schema atoms |
| **Hardware support** | NVFP4/MXFP4 native on Blackwell |

### 6.2 Schema Atom Quantization

For Hydrogen's design primitives:

```
Hydrogen Atom      →  Quantization Format    →  Error Bound
─────────────────────────────────────────────────────────────
Pixel (0-255)     →  UINT8 (no quantization)  →  0
Normalized (0-1)  →  FP4 (group size 16)      →  ~0.01
Color (sRGB)      →  FP4 × 3 channels         →  ~0.02
Position          →  FP4 (NVFP4 preferred)    →  ~0.01
```

### 6.3 Type-Based Error Bounds

Combining with Bean/NumFuzz:

```purescript
-- Hydrogen Schema atom with FP4 quantization
type FP4Pixel
  = FP4 { value :: Bounded4 
        , scale :: E4M3Scale  -- Per-group scale
        , error :: ErrorBound  -- MR-GPTQ derived bound
        }

-- Quantization theorem
theorem FP4_Quantization_Bound {x : Float} :
  RP (dequantize (quantize x)) x ≤ ε_fp4
  
-- Where ε_fp4 depends on:
--   - Group size (16 for NVFP4)
--   - Distribution (Laplace vs Normal)
--   - Whether Hadamard rotation applied
```

### 6.4 Design System Quantization Pipeline

```
Hydrogen Schema (PureScript)
        │
        ▼
  Distribution Analysis
  (Laplace/Normal fitting)
        │
        ▼
  Format Selection
  (NVFP4 vs MXFP4)
        │
        ▼
  MR-GPTQ Optimization
  (Hadamard + scale search)
        │
        ▼
  Error Bound Derivation
        │
        ▼
  GPU Shader Compilation
  (QuTLASS kernels)
```

---

## 7. Technical Specifications

### 7.1 FP4 Format Parameters

| Parameter | E2M1 (FP4) | E4M3 (NVFP4 Scale) | E8M0 (MXFP4 Scale) |
|-----------|-------------|---------------------|---------------------|
| Sign bits | 1 | 1 | 1 |
| Exponent | 2 | 4 | 8 |
| Mantissa | 1 | 3 | 0 |
| Range | ±7 | ±240 | ±∞ (powers-of-2) |

### 7.2 Group Size Trade-offs

| Group Size | MSE (Laplace) | MSE (Normal) | Memory Overhead |
|------------|---------------|--------------|-----------------|
| 8 | High | Medium | High |
| 16 (NVFP4) | Medium | Medium | Medium |
| 32 (MXFP4) | Low | Low | Low |
| 64+ | Very Low | Very Low | Very Low |

### 7.3 Error Bounds by Format

```
NVFP4 (G=16, no rotation):
  MSE_rel ≈ 0.01  (1% relative error)
  
MXFP4 (G=32, with Hadamard):
  MSE_rel ≈ 0.02  (2% relative error)
  
INT4 (G=32, GPTQ):
  MSE_rel ≈ 0.01  (1% relative error)
```

---

## 8. Key Insights for Billion-Agent Systems

### 8.1 Format Selection Guidelines

| Use Case | Recommended Format | Reasoning |
|----------|-------------------|-----------|
| High precision UI | NVFP4 | Better scale precision |
| Memory-constrained | MXFP4 + MR-GPTQ | Lower bits, good recovery |
| Server deployment | NVFP4 | Hardware accelerated |
| Edge deployment | MXFP4 | AMD support, lower memory |

### 8.2 Compositional Quantization

At billion-agent scale, compositions require:
- Per-atom quantization bounds
- Propagation through transformations
- End-to-end error accumulation

This directly maps to NumFuzz/Bean type system!

### 8.3 Error Composition

```
Total Error = Σ (Local Error × Propagation Factor)

For composed transformations:
  T1: Float → FP4      → ε₁
  T2: FP4 → FP4        → ε₂  
  T3: FP4 → Float      → ε₃
  
Total: ε_total = ε₁ + ε₂ + ε₃
```

---

## 9. Citation

```bibtex
@article{castro2025microscaling,
  title={Bridging the Gap Between Promise and Performance for Microscaling FP4 Quantization},
  author={Castro, Roberto L. and Egiazarian, Vage and Kuznedelev, Denis and Panferov, Andrei and Kurti{\'c}, Eldar and Pandit, Shubhra and Marques, Alexandre and Kurtz, Mark and Ashkboos, Saleh and Hoefler, Torsten and Alistarh, Dan},
  year={2025},
  eprint={2509.23202},
  archivePrefix={arXiv},
  primaryClass={cs.LG}
}
```

---

*Research Document: Hydrogen Research Collection*
*Completed: 2026-02-26*
*Attestation: clarity*
