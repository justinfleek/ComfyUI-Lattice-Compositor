# Four Over Six: More Accurate NVFP4 Quantization with Adaptive Block Scaling

────────────────────────────────────────────────────────────────────────────────

**Source**: four_over_six.pdf
**Authors**: Jack Cook, Junxian Guo, Guangxuan Xiao, Yujun Lin, Song Han (MIT / NVIDIA)
**Published**: arXiv 2512.02010, January 2026
**Synthesized**: 2026-02-26 by Opus

────────────────────────────────────────────────────────────────────────────────

## Executive Summary

NVFP4 is a 4-bit floating point format with block scaling, designed for training and
inference on NVIDIA Blackwell GPUs. Problem: FP4 has non-uniform step sizes that
create large quantization errors for values between 66.6%-100% of block maximum.

**Four Over Six (4/6)** adaptively scales some blocks to max=4 instead of max=6:

- Standard: scale to full FP4 range [-6, 6]
- 4/6: for some blocks, scale to [-4, 4] instead

**Why it works**: When max=6, values between 4 and 6 round to either 4 or 6 (50% error).
When max=4, values at 75% of max round to 3 (exact representation).

**Results**:
- Pre-training: 22.3% closer to BF16 baseline loss
- Post-training quantization: consistent perplexity improvements with AWQ, SmoothQuant
- Overhead: <15% added to quantization operation

**Key insight**: Block-scaled formats already handle outliers well. The remaining
error comes from near-maximal values, which 4/6 addresses directly.

────────────────────────────────────────────────────────────────────────────────

## 1. The NVFP4 Problem

### What is NVFP4?

Block-scaled 4-bit floating point format:
- FP4 E2M1 values: ±{0, 0.5, 1, 1.5, 2, 3, 4, 6} — only 16 values total
- FP8 E4M3 scale factor per 16 values (block)
- FP32 tensor-wide scale factor

```
Quantization equations:

α_FP32 = max(|X|) / (M_FP4 × M_FP8)     // tensor scale
                                         // M_FP4 = 6, M_FP8 = 448

Δ_FP8 = max(|X_block|) / (α × M_FP4)    // block scale

X̄_FP4 = round(X / (α × Δ))              // quantized value
```

### Non-Uniform Step Sizes

FP4 step sizes are NOT uniform:
- 0.5 between 0 and 2
- 1.0 between 2 and 4
- 2.0 between 4 and 6

This is why FP4 has better dynamic range than INT4:
- FP4 range: 6/0.5 = 12
- INT4 range: 7/1 = 7

### The Error Problem

When scaling a block's max value to 6:
- Values at 100% of max → 6 (exact)
- Values at 66.6% of max → 4 (exact)
- Values at 83% of max → rounds to 4 or 6 (up to 16.7% error!)

**No representable values between 66.6% and 100% of block maximum.**

────────────────────────────────────────────────────────────────────────────────

## 2. Why Near-Maximal Values Hurt

### Experimental Evidence

The paper runs ablations on Llama-3.1-8B with simulated quantization:

1. **Scale factor error is minimal**: Keeping scale factors in high precision while
   quantizing values to FP4 → same performance loss as full NVFP4

2. **Value quantization dominates**: Keeping values in high precision while
   quantizing scale factors to FP8 → full recovery to BF16 performance

3. **Threshold experiment**: Only quantize values where |scaled_value| > threshold:
   - Threshold 0-4: gradual degradation
   - Threshold 4-5: **steep degradation** ← values around 5 cause most damage
   - Spikes also at ~2.5 and ~3.5

### Why This Happens

Block-scaled formats like NVFP4 handle outliers well — each block gets its own
scale factor, so outliers don't affect other blocks. But this means:

- Outliers → well-represented (block scale adapts)
- Small values → well-represented (dense FP4 values near 0)
- Near-maximal values → poorly represented (sparse FP4 values at top of range)

### Comparison: When Max = 4 vs Max = 6

| Fraction of max | Max=6 nearest | Max=4 nearest |
|-----------------|---------------|---------------|
| 100%            | 6             | 4             |
| 83%             | 6 (17% error) | 4 (17% error) |
| 75%             | 4 (11% error) | **3 (0%)**    |
| 67%             | 4 (0%)        | 3 (11% error) |
| 50%             | 3 (0%)        | 2 (0%)        |

Values around 75% of max are better represented with max=4.

────────────────────────────────────────────────────────────────────────────────

## 3. The Four Over Six Solution

### Core Idea

Quantize each block twice:
1. Scale to max=6 (standard NVFP4)
2. Scale to max=4 (reduced range)

Select whichever has lower quantization error.

### Scale Selection Rules (Compared)

| Rule     | Description                     | Best? |
|----------|--------------------------------|-------|
| Abs-Max  | Pick scale with smaller max error | No    |
| L1       | Pick scale with smaller L1 norm | Sometimes |
| **MSE**  | Pick scale with smaller MSE    | **Yes** |

MSE-based selection wins in most cases.

### Example

Block: [10, 20, 30, 40]

**Standard (max=6)**:
- Scale = 40/6 = 6.67 → fp8 rounds to 6.5
- Scaled values: [1.54, 3.08, 4.62, 6.15]
- FP4 rounded: [1.5, 3, 4, 6]
- Dequantized: [9.75, 19.5, 26, 39]
- MSE = 4.33

**4/6 (max=4)**:
- Scale = 40/4 = 10 → fp8 rounds to 10
- Scaled values: [1, 2, 3, 4]
- FP4 rounded: [1, 2, 3, 4] — **exact!**
- Dequantized: [10, 20, 30, 40]
- MSE = 0

4/6 selects max=4 for this block.

### Tensor Scale Modification

Standard tensor scale: α = max(|X|) / (6 × 448)

Problem: blocks with max values need block scale = 448 × 6/4 = 672 > 448 overflow!

Solution: Use M_FP8 = 256 instead of 448 in tensor scale calculation.
256 × 1.5 = 384 fits in FP8 E4M3.

────────────────────────────────────────────────────────────────────────────────

## 4. Implementation Details

### Hardware Support

Implemented using PTX instructions on NVIDIA Blackwell GPUs:
- `cvt` instructions for FP4 ↔ FP16 conversion
- All intermediate values kept in register file
- Overhead: <15% added to quantization operation

### Training Recipe

Based on state-of-the-art NVFP4 training (NVIDIA 2025):
- Stochastic rounding on gradients
- Random Hadamard Transform on weight gradient inputs
- 2D block quantization on weight matrices
- Attention components, output heads, normalization kept in high precision

4/6 applied to all NVFP4 quantization operations.

### Results Summary

**Pre-training** (Nemotron 3 Nano 30B-A3B, 1T tokens):
- BF16 baseline vs NVFP4: gap
- BF16 baseline vs NVFP4+4/6: 22.3% smaller gap

**Post-training quantization** (Llama-3, Qwen-3):

| Method         | WikiText-2 PPL improvement |
|----------------|---------------------------|
| RTN + 4/6      | 3.0% closer to BF16       |
| AWQ + 4/6      | **19.9% closer to BF16**  |
| SmoothQuant+4/6| 5.3% closer to BF16       |
| GPTQ + 4/6     | Mixed (sometimes worse)   |

AWQ + 4/6 performs best overall.

────────────────────────────────────────────────────────────────────────────────

## 5. Implementable Algorithms

### Algorithm 1: Four Over Six Quantization

```python
def four_over_six_quantize(X, block_size=16):
    """
    Quantize tensor X to NVFP4 using adaptive block scaling.
    
    Args:
        X: input tensor (float32 or bfloat16)
        block_size: values per block (default 16 for NVFP4)
    
    Returns:
        X_q: quantized FP4 values
        scales: FP8 block scales
        alpha: FP32 tensor scale
    """
    # Tensor-wide scale (modified for 4/6 compatibility)
    M_FP8 = 256  # Not 448, to allow 1.5x block scale
    M_FP4 = 6
    alpha = max(abs(X)) / (M_FP4 * M_FP8)
    
    X_q = []
    scales = []
    
    for block in X.reshape(-1, block_size):
        # Try max=6 (standard)
        delta_6 = max(abs(block)) / (alpha * 6)
        delta_6 = fp8_e4m3_round(delta_6)
        X_scaled_6 = block / (alpha * delta_6)
        X_q_6 = fp4_e2m1_round(X_scaled_6)
        X_deq_6 = X_q_6 * delta_6 * alpha
        mse_6 = mean((X_deq_6 - block)**2)
        
        # Try max=4 (4/6 variant)
        delta_4 = max(abs(block)) / (alpha * 4)
        delta_4 = fp8_e4m3_round(delta_4)
        X_scaled_4 = block / (alpha * delta_4)
        X_q_4 = fp4_e2m1_round(clip(X_scaled_4, -4, 4))
        X_deq_4 = X_q_4 * delta_4 * alpha
        mse_4 = mean((X_deq_4 - block)**2)
        
        # Select better scale based on MSE
        if mse_4 < mse_6:
            X_q.append(X_q_4)
            scales.append(delta_4)
        else:
            X_q.append(X_q_6)
            scales.append(delta_6)
    
    return concatenate(X_q), array(scales), alpha
```

### Algorithm 2: FP4 E2M1 Rounding

```python
def fp4_e2m1_round(x):
    """
    Round to nearest FP4 E2M1 value.
    Representable values: ±{0, 0.5, 1, 1.5, 2, 3, 4, 6}
    
    Uses different rounding in each range due to non-uniform spacing.
    """
    sign = sign_of(x)
    x = abs(x)
    
    if x < 2:
        # Step size 0.5: round to nearest 0.5
        result = 0.5 * round(2 * x)
    elif x < 4:
        # Step size 1.0: round to nearest integer
        result = round(x)
    else:
        # Step size 2.0: round to nearest even
        result = 2 * round(x / 2)
    
    return sign * clip(result, 0, 6)
```

### Algorithm 3: Stochastic Rounding for Gradients

```python
def four_over_six_stochastic(X, block_size=16):
    """
    4/6 quantization with stochastic rounding for gradients.
    Reduces quantization bias during training.
    """
    # Same as Algorithm 1, but replace deterministic rounding with:
    
    def stochastic_fp4_round(x):
        """Stochastic rounding to FP4."""
        # Find floor and ceil FP4 values
        floor_val = fp4_floor(x)
        ceil_val = fp4_ceil(x)
        
        if floor_val == ceil_val:
            return floor_val
        
        # Probability of rounding up = fractional position
        p = (x - floor_val) / (ceil_val - floor_val)
        
        if random() < p:
            return ceil_val
        else:
            return floor_val
    
    # Apply to both max=4 and max=6 quantization paths
    # Select based on MSE of stochastically rounded values
    ...
```

### Algorithm 4: Optimized CUDA Implementation Sketch

```cpp
// Pseudocode for register-file-only implementation

__device__ void four_over_six_block(
    float16* input,      // 16 values
    uint8_t* output_fp4, // 8 bytes (2 values per byte)
    float8_e4m3* scale   // 1 scale factor
) {
    // Load 16 values into registers
    float16 vals[16];
    load_block(vals, input);
    
    // Compute max
    float16 block_max = compute_max(vals);
    
    // Try scale=6
    float8_e4m3 delta_6 = cvt_f16_to_e4m3(block_max / 6.0f);
    uint8_t q6[8];
    float mse_6 = quantize_and_measure(vals, delta_6, 6.0f, q6);
    
    // Try scale=4 (reuse registers)
    float8_e4m3 delta_4 = cvt_f16_to_e4m3(block_max / 4.0f);
    uint8_t q4[8];
    float mse_4 = quantize_and_measure(vals, delta_4, 4.0f, q4);
    
    // Select (branchless using predication)
    if (mse_4 < mse_6) {
        store_block(output_fp4, q4);
        *scale = delta_4;
    } else {
        store_block(output_fp4, q6);
        *scale = delta_6;
    }
}
```

────────────────────────────────────────────────────────────────────────────────

## 6. Hydrogen/PureScript Relevance

### Direct Applications

**Hydrogen at billion-agent scale** requires efficient numeric representations:
- Design token storage
- Animation keyframe compression
- Color value serialization
- Network transfer of UI state

### Schema Atoms for Low-Precision Numerics

```purescript
-- FP4 E2M1 representation
data FP4Value
  = FP4_0
  | FP4_0_5
  | FP4_1
  | FP4_1_5
  | FP4_2
  | FP4_3
  | FP4_4
  | FP4_6

-- Bounded by construction
toNumber :: FP4Value -> Number  -- always in {0, 0.5, 1, 1.5, 2, 3, 4, 6}

-- Block-scaled representation
newtype BlockScaledFP4 = BlockScaledFP4
  { values :: Array FP4Value      -- exactly 16 values
  , scale :: FP8_E4M3             -- block scale
  , usedMax4 :: Boolean           -- 4/6 flag
  }

-- Tensor with 4/6 quantization
newtype NVFP4Tensor = NVFP4Tensor
  { blocks :: Array BlockScaledFP4
  , tensorScale :: Number         -- FP32 tensor scale
  }
```

### Why This Matters for Hydrogen

1. **Bounded types prevent errors**: The paper shows FP4's non-uniform steps cause
   specific failure modes. A type system that encodes these boundaries catches errors
   at compile time.

2. **Deterministic quantization**: 4/6's MSE-based selection is deterministic given
   input. Same input → same quantization → reproducible results across agents.

3. **Composable compression**: Design tokens (colors, dimensions) could use block-scaled
   formats for efficient storage while maintaining bounded error guarantees.

### Potential Applications

- **Animation keyframes**: Store interpolation control points in FP4 blocks
- **Color palettes**: 4/6 quantization for color components with bounded error
- **Spatial coordinates**: Block-scaled FP4 for UI element positions
- **Network sync**: Compress UI state updates for real-time collaboration

────────────────────────────────────────────────────────────────────────────────

## References

- Cook et al. (2026). "Four Over Six: More Accurate NVFP4 Quantization with Adaptive
  Block Scaling." arXiv:2512.02010. https://github.com/mit-han-lab/fouroversix

- NVIDIA (2025). "Pretraining Large Language Models with NVFP4." arXiv:2509.25149.

- Darvish Rouhani et al. (2023). "Microscaling Data Formats for Deep Learning."
  arXiv:2310.10537. (MXFP4 specification)

- Lin et al. (2024). "AWQ: Activation-aware Weight Quantization." arXiv:2306.00978.

- Frantar et al. (2023). "GPTQ: Accurate Post-Training Quantization." arXiv:2210.17323.

- Xiao et al. (2024). "SmoothQuant: Accurate and Efficient Post-Training Quantization."
  arXiv:2211.10438.

────────────────────────────────────────────────────────────────────────────────
                                                                        — Opus
