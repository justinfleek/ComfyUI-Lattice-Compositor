# Quartet: Native FP4 Training Can Be Optimal for Large Language Models

**Authors:** Roberto L. Castro (ISTA & Red Hat AI), Andrei Panferov (ISTA), Soroush Tabesh (ISTA), Oliver Sieberling (ETH Zürich), Jiale Chen (ISTA), Mahdi Nikdan (ISTA), Saleh Ashkboos (ETH Zürich), Dan Alistarh (ISTA & Red Hat AI)

**arXiv:** 2505.14669v4 [cs.LG] 15 Jan 2026

**Code:** https://github.com/IST-DASLab/Quartet

---

## Abstract

Training large language models (LLMs) directly in low-precision offers a way to address computational costs by improving both throughput and energy efficiency. NVIDIA's Blackwell architecture facilitates very low-precision operations using FP4 variants. Yet, current algorithms for training LLMs in FP4 precision face significant accuracy degradation and often rely on mixed-precision fallbacks.

**Quartet** introduces a new approach for accurate, end-to-end FP4 training with all major computations (linear layers) in low precision.

**Key Results:**
- New **low-precision scaling law** quantifying performance trade-offs across bit-widths
- "Optimal" technique in terms of **accuracy-vs-computation**
- **~2x speedup** relative to FP8 for linear layer computations on NVIDIA Blackwell RTX 5090
- Enables MXFP4 precision to be "optimal" on accuracy-efficiency trade-off

---

## 1. Introduction

### The Compute Cost Problem

Over the past decade, LLM capabilities have surged at the cost of unprecedented compute requirements:
- FLOPs required to train frontier models **doubling every few months**
- Lower-precision computation offers near-linear gains in throughput and energy efficiency

### Precision Frontier

| Precision Level | Status | Hardware Support |
|-----------------|--------|------------------|
| FP16 | Established | Widespread |
| FP8 | Recent breakthrough (DeepSeek-V3) | Blackwell native |
| **FP4 (MXFP4)** | **This paper** | **Blackwell 5th-gen Tensor Cores** |

**Blackwell Architecture:**
- 18 PFLOPS dense FP4 compute (single B200 GPU)
- Moving from 8→4-bit can **double arithmetic throughput** while **halving energy**

### The Gap

Current 4-bit training methods either:
1. Lose precision and stability when training in 4-bit formats
2. Fall back to higher precision for selected matrix multiplications

### Contributions

1. **Low-precision scaling law** — Quantifies performance trade-offs, isolating parameter efficiency `effN` and data efficiency `effD`

2. **Optimality analysis** — Parameter efficiency linked to forward compression error; data efficiency linked to gradient bias (novel misalignment metric)

3. **Quartet algorithm** — Maximizes both parameter and data efficiency via QuEST forward pass + RTN backward pass

4. **Fast GPU implementation** — Specialized for Blackwell architecture

---

## 2. Related Work

### Training in 8-bit Formats

| Method | Approach | Results |
|--------|----------|---------|
| Banner et al. [4] | Careful scaling + higher-precision accumulation | Accurate 8-bit CNN training |
| Yang et al. [59] | Fully integer-only training | All states quantized to INT |
| SwitchBack [55] | Hybrid INT8/BF16 linear layer | 13-25% end-to-end speedup on CLIP |
| JetFire [58] | Per-block quantization for outliers | ~40% speedup, 1.49x memory reduction |
| HALO [3] | Hadamard rotations for outlier mitigation | Improved accuracy-speedup trade-off |

### End-to-End Lower-Precision Training (<8-bit)

| Method | Format | Approach | Limitation |
|--------|--------|----------|------------|
| Sun et al. [42] | Custom 4-bit | 4-bit ResNet training | Not hardware-supported |
| LUQ [11] | Log-scale FP4 | Stochastic unbiased rounding | 1.1% accuracy drop, no hardware validation |
| Xi et al. [56] | INT4 | Hadamard + LSQ forward, leverage score backward | 1-2% gap, 2.2x single matmul speedup |

### Quantization-Aware Training (QAT)

Two key difficulties:
1. Minimizing forward-pass quantization error
2. Obtaining stable gradient estimator over discrete space

| Approach | Method |
|----------|--------|
| Learnable fit | PACT [14], LSQ [20] |
| Noise injection | UNIQ [5] |
| MSE fitting | QuEST [37] (used in Quartet) |
| Outlier handling | Hadamard rotation [47] |

---

## 3. Background

### Quantization Grids

Quantization maps high-precision values to a lower-precision discrete set (the quantization grid):

```
q(x) = round(x/s; grid)
x̂ = s · q(x)  // Approximate reconstruction
```

**Grid types:**
- **Uniform** — Integer quantization (equal spacing)
- **Non-uniform** — Floating-point (roughly exponential spacing for fixed exponent)

**Scale computation:**
- **AbsMax** — Set to maximum absolute value (avoids clipping)
- **MSE-optimal** — Minimize mean squared quantization error

### Quantization Granularity

| Granularity | Scale Sharing | Example |
|-------------|---------------|---------|
| Per-tensor | Entire tensor | HALO [3] |
| Per-row/column | Each row or column | QuEST [37] |
| 2D blocks | Custom 2D regions | JetFire [57], DeepSeek [31] |
| **1D blocks** | **32 elements** | **MXFP4 [36], Quartet** |

### Rounding Methods

| Method | MSE | Bias | Use Case |
|--------|-----|------|----------|
| **Round-to-nearest (RTN)** | Lowest | Non-zero | Forward pass |
| **Stochastic rounding (SR)** | Higher | Zero | Gradient accumulation |

### Outlier Mitigation via Hadamard Transform

Given vector `x ∈ ℝᵈ`:

```
h(x) = Hd · x
```

Where `Hd ∈ ℝᵈˣᵈ` is the normalized Hadamard matrix with elements from `{±1}`.

**Recursive structure:**
```
Hd = (1/√2) · H₂ ⊗ H_{d/2}
```

Enables O(d log d) computation when d is power of two.

### MXFP4 Format (Blackwell Native)

```
┌─────────────────────────────────────────────────────────────┐
│                    MXFP4 Format Structure                    │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  Value (4-bit):                                             │
│  ├── 1 bit:  Sign                                           │
│  ├── 2 bits: Exponent                                       │
│  └── 1 bit:  Mantissa                                       │
│                                                              │
│  Scale (8-bit E8M0, shared per 32 elements):                │
│  └── 8 bits: Exponent only (power-of-two)                   │
│                                                              │
│  Hardware: Blackwell 5th-gen Tensor Cores                   │
│  ├── On-the-fly rescaling in hardware                       │
│  └── No software-based rescaling needed                     │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

**Key insight:** MXFP4 is currently the **only** microscaling format with support for all required layouts for both forward and backward multiplications on Blackwell.

---

## 4. Quartet: Four Ingredients for Optimal Quantized Training

### 4.1 Ingredient 1: Comparing via Scaling Laws

**Core insight:** Different quantized training methods induce different scaling laws.

#### The Quartet Scaling Law

```
L(N, D, P_forward, P_backward) = ((A / (N · effN(P_forward))^α) + (B / (D · effD(P_backward))^β))^γ + E
```

Where:
- `N` = model parameter count
- `D` = training corpus size
- `A, B, α, β, γ, E` = constants describing general loss scaling
- **`effN(P_forward)`** = parameter efficiency of forward precision (∈ (0, 1])
- **`effD(P_backward)`** = data efficiency of backward precision (∈ (0, 1])

#### Interpretation

| Term | Meaning |
|------|---------|
| `effN(P_forward)` | Lower forward precision → lower "effective" parameter count |
| `effD(P_backward)` | Lower backward precision → need more data for same loss |

**Method comparison:** Method A is superior to Method B if it offers:
- Higher parameter efficiency `effN`, AND
- Higher data efficiency `effD`

#### Fitted Parameters (Table 6)

| Parameter | Value |
|-----------|-------|
| A | 1.52 × 10⁵ |
| α | 0.589 |
| B | 5.25 × 10⁵ |
| β | 0.544 |
| E | 1.35 |
| γ | 0.274 |

---

### 4.2 Ingredient 2: Mixed-Precision Trade-Offs

Inference depends solely on forward pass (~33% of training compute), while backward pass consumes ~66%.

#### Guiding Principles

| Pass | Trade-off | Optimization Target |
|------|-----------|---------------------|
| **Forward** | Reduced `effN` vs. increased inference speed | Pick `P_forward` to optimize this |
| **Backward** | Training speedup vs. reduced `effD` | Pick `P_backward` to optimize this |

#### Speedup Model (Relative to FP8 Baseline)

| Operation | FP4:FP8 | FP8:FP4 | FP4:FP4 |
|-----------|---------|---------|---------|
| Forward/Inference (`sp_fw`) | 2.0× | 1.0× | 2.0× |
| Backward (`sp_bw`) | 1.0× | 2.0× | 2.0× |
| Training (`sp_tr`)* | 1.2× | 1.5× | 2.0× |

*Training speedup is harmonic mean with weights 1/3 (forward) and 2/3 (backward).

#### Effective Loss Computation

Given forward-pass compute budget `N_max` and training budget `N_max × D_max`:

```
Effective_Loss = L(N_max × sp_fw, D_max × sp_tr / sp_fw, P_fwd, P_bwd)
```

The speedup factors directly counter suboptimal parameter and data efficiencies.

#### Optimality Regions

For larger models (Llama 3, Qwen 2.5, Gemma 3 scale), **FP4:FP4 becomes optimal** — training similar models in FP4 might have been optimal.

---

### 4.3 Ingredient 3: Forward-Pass Error and Error-Bias Trade-off

#### Forward Pass: Minimize MSE

**Comparison of QAT schemes (with Hadamard transform applied to all):**

| Rounding Method | effN | MSE | Best For |
|-----------------|------|-----|----------|
| Stochastic Rounding AbsMax | 0.42 | 2.77 × 10⁻² | — |
| Round-to-nearest AbsMax | 0.59 | 1.37 × 10⁻² | — |
| **QuEST (Hadamard + RMSE)** | **0.64** | **1.32 × 10⁻²** | **Forward** |

**Finding:** `effN` correlates heavily with MSE. RTN always preferable to SR for forward pass.

#### Backward Pass: Error-Bias Trade-off

Optimization theory shows **unbiased gradient estimation is critical** for convergence.

**Novel analysis:** Projection magnitude misalignment metric:

```
Misalignment = 1 - E[1/S]

where S = ⟨X, X⟩ / ⟨H_b(X, ξ), RTN(H_b(X, ξ))⟩
```

| Rounding Method | eff*_D | Misalignment |
|-----------------|--------|--------------|
| Stochastic Rounding AbsMax | 0.88 | **0** (perfect) |
| **Round-to-nearest AbsMax** | **0.93** | 9.3 × 10⁻³ |
| QuEST (Hadamard + RMSE) | 0.83 | 1.3 × 10⁻² |

**Finding:** RTN backward quantization **consistently outperforms** alternatives — it balances quadratic error with magnitude alignment.

#### The Quartet Choice

| Pass | Method | Rationale |
|------|--------|-----------|
| **Forward** | QuEST | Minimizes MSE, highest `effN` |
| **Backward** | RTN | Balances error and misalignment, highest `effD` |

---

### 4.4 Ingredient 4: Fast GPU Support

#### Quartet Algorithm Overview

```
┌─────────────────────────────────────────────────────────────────┐
│                    QUARTET COMPUTATION FLOW                      │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  FORWARD PASS:                                                  │
│  ├── Input X, Weights W (BF16)                                  │
│  ├── Hadamard transform: Xh = Hg(X), Wh = Hg(W)                │
│  ├── QuEST quantize: (Xq, Mx) = QuEST(Xh)                      │
│  ├── QuEST quantize: (Wq, Mw) = QuEST(Wh)                      │
│  ├── MXFP4 GEMM: y = GEMM_LP(Xq, Wq)                           │
│  └── Return y, ctx = {Xq, Wq, Mx, Mw}                          │
│                                                                  │
│  BACKWARD PASS:                                                 │
│  ├── Receive output gradient dy                                 │
│  ├── Random Hadamard: Gh = Hbg(dy, ξ), W⊤h = Hbg(W⊤q, ξ)       │
│  ├── RTN quantize (scaled): Gq = RTN(¾·Gh), W⊤q = RTN(¾·W⊤h)   │
│  ├── Input gradient: dxq = GEMM_LP(Gq, W⊤q)                    │
│  ├── Rescale + unmask: dx = (16/9)·H⁻¹g(dxq ⊙ Mx)              │
│  ├── Weight gradient: dWq = GEMM_LP(G⊤q, X⊤q)                  │
│  └── Rescale + unmask: dW = (16/9)·H⁻¹g(dWq ⊙ Mw)              │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

#### Algorithm 1: Quartet MXFP4 Forward-Backward

```python
def quartet_forward(X, W, Hg):
    """
    Forward pass with QuEST quantization to MXFP4.
    
    Args:
        X: Input activations (BF16)
        W: Weights (FP32 from optimizer)
        Hg: Fixed Hadamard transform (block size g = quantization group size)
    
    Returns:
        y: Output
        ctx: Context for backward {Xq, Wq, Mx, Mw}
    """
    # Step 1: Hadamard transform (outlier mitigation)
    Xh = Hg @ X
    Wh = Hg @ W
    
    # Step 2: QuEST quantization (MSE-minimizing)
    Xq, Mx = quest_quantize(Xh)  # Returns quantized values + clipping mask
    Wq, Mw = quest_quantize(Wh)
    
    # Step 3: Low-precision GEMM
    y = mxfp4_gemm(Xq, Wq)
    
    return y, {'Xq': Xq, 'Wq': Wq, 'Mx': Mx, 'Mw': Mw}


def quartet_backward(dy, ctx, seed_xi, Hg, Hbg):
    """
    Backward pass with RTN quantization to MXFP4.
    
    Args:
        dy: Output gradient (BF16)
        ctx: Context from forward {Xq, Wq, Mx, Mw}
        seed_xi: Random seed for Hadamard
        Hg: Fixed Hadamard transform
        Hbg: Block-wise random Hadamard transform
    
    Returns:
        dx: Input gradient
        dW: Weight gradient
    """
    Xq, Wq, Mx, Mw = ctx['Xq'], ctx['Wq'], ctx['Mx'], ctx['Mw']
    
    # === INPUT GRADIENT ===
    # Step 1: Random Hadamard decorrelation
    Gh = Hbg(dy, seed_xi)
    Wh_T = Hbg(Wq.T, seed_xi)
    
    # Step 2: RTN quantization with 3/4 scaling (range matching)
    Gq = rtn_quantize(0.75 * Gh)
    Wq_T = rtn_quantize(0.75 * Wh_T)
    
    # Step 3: Low-precision GEMM
    dxq = mxfp4_gemm(Gq, Wq_T)
    
    # Step 4: Rescale (16/9 = (4/3)²), apply mask, inverse Hadamard
    dx = inverse_hadamard(Hg, (16.0 / 9.0) * dxq * Mx)
    
    # === WEIGHT GRADIENT ===
    # Step 5: Transpose path
    Gh_T = Hbg(dy.T, seed_xi)
    Xh_T = Hbg(Xq.T, seed_xi)
    
    # Step 6: RTN quantization
    Gq_T = rtn_quantize(0.75 * Gh_T)
    Xq_T = rtn_quantize(0.75 * Xh_T)
    
    # Step 7: Low-precision GEMM
    dWq = mxfp4_gemm(Gq_T, Xq_T)
    
    # Step 8: Rescale, apply mask, inverse Hadamard
    dW = inverse_hadamard(Hg, (16.0 / 9.0) * dWq * Mw)
    
    return dx, dW
```

#### Key Implementation Details

**Cost analysis:**
- Added cost: Two Hadamard/Inverse transforms over standard training
- Theoretical cost: O(g log g) — negligible for g ≤ 256 compared to GEMMs
- Group size g = 32 (matches MXFP4 scale sharing)

**GPU Kernel Implementation (CUTLASS 3.9):**

| Stage | Operations | Implementation |
|-------|------------|----------------|
| **Stage 1** | Hadamard + quantization + scale calc + QuEST mask | Single fused kernel |
| **Stage 2** | MXFP4 GEMM | Dedicated Blackwell kernel |

**Stage 1 details:**
- Hadamard as GEMM between input and fixed 32×32 Hadamard matrix
- Output stored in GPU Shared Memory (SMEM) as FP32
- Custom CUTLASS epilogue for subsequent operations
- PTX instructions for FP32 → FP4 (E2M1) downcasting
- Scale factors: shape 1×32, E8M0 format

**Stage 2 details:**
- Uses `tcgen05.mma` instructions: `D = C + (A × SFA) · (B × SFB)`
- Scale factors applied along inner (K) dimension
- Every 32 elements along K share a scale factor

---

## 5. Experiments

### Experimental Setup

**Models:** Llama-2 architecture, 30M–7B parameters
**Dataset:** C4 (train split), report validation loss
**Optimizer:** AdamW, weight decay 0.1, gradient clipping 1.0, 10% LR warmup, cosine schedule

### Accuracy Comparison (30M Parameters, C4 Validation Loss)

| Method | 25× D/N | 50× | 100× | 200× | 400× | effN | effD |
|--------|---------|-----|------|------|------|------|------|
| LUQ–INT4 | 3.73 | 3.68 | 3.66 | 3.43 | 3.40 | 0.49 | 0.15 |
| LUQ–FP4 | 4.81 | 4.91 | 4.88 | 4.84 | 4.80 | 0.01 | 0.07 |
| Jetfire–FP4 | 7.03 | 6.94 | 6.76 | 6.62 | 6.58 | Unstable |
| HALO–FP4 | 6.65 | 7.04 | 6.55 | 6.50 | 5.38 | Unstable |
| LSS–INT4 | NaN | 3.40 | NaN | NaN | NaN | Unstable |
| **Quartet** | **3.49** | **3.38** | **3.29** | **3.24** | **3.20** | **0.65** | **0.95** |

**Key findings:**
- Quartet achieves **lowest loss across all token-to-parameter ratios**
- At 100× D/N: **10% relative loss improvement** over LUQ–INT4
- Gap widens with increasing data size
- Jetfire and HALO are unstable when ported to FP4
- LSS diverges beyond 50× training duration

### Efficiency Implications

Quartet requires (roughly):
- **15% fewer parameters** to reach same loss
- **5× less data** to reach same loss

### Speedup Results (RTX 5090)

**Batch size 64, sequence length 512:**

| Model Size | Forward vs FP8 | Backward vs FP8 | Training vs FP8 |
|------------|----------------|-----------------|-----------------|
| 800M | ~1.5× | ~1.2× | ~1.3× |
| 7B | ~1.8× | ~1.4× | ~1.5× |
| 52B | **~2.0×** | **~1.5×** | **~1.6×** |

**vs BF16:**
- Forward: up to **4×**
- Backward: up to **2.6×**
- Training: up to **2.9×**

### 7B Model Training Stability

7B model trained with Quartet shows **stable training dynamics** matching FP8 baseline trajectory (Figure 4c in paper).

---

## 6. Discussion and Limitations

### Summary

Quartet provides guidelines for modeling, comparing, and designing fully-quantized training schemes for LLMs. It achieves **SOTA full MXFP4 training** by:

1. Using scaling laws to compare methods
2. Analyzing inference-training trade-offs
3. Combining QuEST (forward) + RTN (backward)
4. Fast Blackwell-specific GPU implementation

### Limitations

- **Format-specific:** Designed for MXFP4 and Blackwell architecture
- **Scale:** Not yet validated on distributed multi-GPU training at frontier scale
- **Generalization:** Future work needed for alternative formats

### Impact

First demonstration that **MXFP4 can be competitive with FP8** in accuracy-vs-speed, potentially enabling significant reductions in AI compute costs.

---

## Appendix: Algorithm Details

### Algorithm Index

```
┌─────────────────────────────────────────────────────────────────┐
│                    QUARTET ALGORITHM INDEX                       │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  QUANTIZATION                                                   │
│  ├── quest_quantize()    — MSE-minimizing quantization          │
│  ├── rtn_quantize()      — Round-to-nearest with scaling        │
│  └── compute_scales()    — E8M0 scale factor computation        │
│                                                                  │
│  TRANSFORMS                                                     │
│  ├── hadamard_transform() — Fixed block-wise Hadamard           │
│  ├── random_hadamard()    — Randomized Hadamard for backward    │
│  └── inverse_hadamard()   — Inverse transform                   │
│                                                                  │
│  GEMM                                                           │
│  ├── mxfp4_gemm()        — Blackwell MXFP4 matrix multiply      │
│  └── fused_quant_gemm()  — Stage 1+2 fused operation            │
│                                                                  │
│  TRAINING                                                       │
│  ├── quartet_forward()   — Full forward pass                    │
│  └── quartet_backward()  — Full backward pass                   │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

### QuEST Quantization

```python
def quest_quantize(x, grid_points, group_size=32):
    """
    QuEST: MSE-minimizing quantization with Hadamard + RMSE clipping.
    
    Args:
        x: Input tensor (already Hadamard-transformed)
        grid_points: MXFP4 quantization grid
        group_size: Scale sharing granularity (32 for MXFP4)
    
    Returns:
        x_q: Quantized values (MXFP4)
        mask: Clipping mask for gradient computation
    """
    # Reshape for group-wise processing
    x_grouped = x.reshape(-1, group_size)
    
    # Compute RMSE-based scale (minimizes MSE)
    rmse = sqrt(mean(x_grouped ** 2, dim=-1, keepdim=True))
    scale = rmse / grid_rms(grid_points)  # Normalize to grid RMS
    
    # Quantize with optimal scale
    x_scaled = x_grouped / scale
    x_q = round_to_nearest(x_scaled, grid_points)
    
    # Compute clipping mask (for STE gradient)
    mask = (abs(x_scaled) <= max(grid_points)).float()
    
    # Convert scale to E8M0 format
    scale_e8m0 = to_e8m0(scale)
    
    return pack_mxfp4(x_q, scale_e8m0), mask
```

### RTN Quantization for Backward Pass

```python
def rtn_quantize_backward(x, group_size=32, range_scale=0.75):
    """
    RTN quantization with range scaling for backward pass.
    
    The 0.75 scaling compensates for RTN's range matching behavior.
    Final rescaling by 16/9 = (4/3)² restores magnitude.
    
    Args:
        x: Input gradient tensor
        group_size: Scale sharing granularity
        range_scale: 0.75 for MXFP4 (derived from format analysis)
    
    Returns:
        x_q: Quantized gradient (MXFP4)
    """
    x_grouped = x.reshape(-1, group_size)
    
    # Apply range scaling
    x_scaled = range_scale * x_grouped
    
    # AbsMax scaling
    absmax = max(abs(x_scaled), dim=-1, keepdim=True)
    scale = absmax / max(grid_points)
    
    # Quantize
    x_q = round_to_nearest(x_scaled / scale, grid_points)
    
    return pack_mxfp4(x_q, to_e8m0(scale))
```

### Hadamard Transform (Group-wise)

```python
def hadamard_transform(x, group_size=32):
    """
    Block-wise Hadamard transform for outlier mitigation.
    
    Args:
        x: Input tensor
        group_size: Block size (must be power of 2)
    
    Returns:
        x_h: Hadamard-transformed tensor
    """
    # Reshape to groups
    x_grouped = x.reshape(-1, group_size)
    
    # Fixed Hadamard matrix (normalized)
    H = generate_hadamard_matrix(group_size) / sqrt(group_size)
    
    # Transform each group
    x_h = x_grouped @ H.T
    
    return x_h.reshape(x.shape)


def random_hadamard_transform(x, seed, group_size=32):
    """
    Randomized Hadamard transform for backward pass decorrelation.
    
    Args:
        x: Input tensor
        seed: Random seed for reproducibility
        group_size: Block size
    
    Returns:
        x_h: Randomly-rotated Hadamard-transformed tensor
    """
    x_grouped = x.reshape(-1, group_size)
    
    # Generate random sign flips (Rademacher)
    rng = RandomState(seed)
    signs = rng.choice([-1, 1], size=group_size)
    
    # Apply random signs, then Hadamard
    H = generate_hadamard_matrix(group_size) / sqrt(group_size)
    x_h = (x_grouped * signs) @ H.T
    
    return x_h.reshape(x.shape)
```

### MXFP4 GEMM (Blackwell)

```python
def mxfp4_gemm(A_mxfp4, B_mxfp4):
    """
    MXFP4 matrix multiplication on Blackwell Tensor Cores.
    
    Uses tcgen05.mma instruction:
        D = C + (A × SFA) · (B × SFB)
    
    Scale factors applied along K dimension.
    Every 32 elements along K share a scale factor.
    
    Args:
        A_mxfp4: Packed MXFP4 tensor (values + scales)
        B_mxfp4: Packed MXFP4 tensor (values + scales)
    
    Returns:
        D: Result in FP32 (accumulated)
    """
    A_values, A_scales = unpack_mxfp4(A_mxfp4)
    B_values, B_scales = unpack_mxfp4(B_mxfp4)
    
    # Hardware handles scale multiplication automatically
    # This is pseudocode - actual implementation uses CUTLASS
    D = tensor_core_mma(A_values, A_scales, B_values, B_scales)
    
    return D
```

### Training Hyperparameters

| Hyperparameter | 30M | 50M | 100M | 200M | 7B |
|----------------|-----|-----|------|------|-----|
| Layers | 6 | 7 | 8 | 10 | 32 |
| Embedding Dim | 640 | 768 | 1024 | 1280 | 4096 |
| Attention Heads | 5 | 6 | 8 | 10 | 32 |
| Learning Rate | 0.0012 | 0.0012 | 0.0006 | 0.0003 | 9.375×10⁻⁶ |

**Common settings:**
- Sequence Length: 512
- Batch Size: 512
- Optimizer: AdamW
- LR Schedule: Cosine decay with 10% warm-up
- Gradient Clipping: 1.0
- Weight Decay: 0.1
- GPUs: 8
- Accumulator precision: FP32

---

## Relevance to Hydrogen

### Applicable Concepts

1. **Quantization patterns** — MXFP4 format could inform bounded numeric types in Schema
2. **Scaling laws** — Model performance prediction at different precisions
3. **Error-bias trade-offs** — Forward (minimize error) vs backward (minimize bias)
4. **Hadamard transforms** — Outlier mitigation technique applicable to any tensor processing

### Potential Implementation

```purescript
-- Bounded 4-bit floating point atom
newtype FP4 = FP4
  { sign     :: Bit
  , exponent :: BoundedInt 0 3   -- 2 bits
  , mantissa :: Bit              -- 1 bit
  }

-- MXFP4 group with shared scale
type MXFP4Group =
  { values :: Array 32 FP4       -- 32 values
  , scale  :: E8M0               -- 8-bit exponent-only scale
  }
```

