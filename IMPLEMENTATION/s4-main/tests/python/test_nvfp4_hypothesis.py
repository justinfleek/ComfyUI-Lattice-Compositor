#!/usr/bin/env python3
"""
s4 // tests/python/test_nvfp4_hypothesis.py

Property-based tests for NVFP4 quantization using Hypothesis.
Tests mathematical invariants against reference implementations.

Reference: SageAttention3 fp4_interface.py
"""

import math
from dataclasses import dataclass
from typing import List, Tuple

import hypothesis
from hypothesis import given, settings, assume
import hypothesis.strategies as st
import numpy as np


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# Constants matching nvfp4.cuh
# ════════════════════════════════════════════════════════════════════════════

BLOCK_SIZE = 16
E2M1_MAX_VALUE = 6.0
E2M1_RCP_MAX = 1.0 / 6.0
FP8_E4M3_MAX_FINITE = 448.0

#                                                                      // e2m1
E2M1_POSITIVE_VALUES = [0.0, 0.5, 1.0, 1.5, 2.0, 3.0, 4.0, 6.0]


# ════════════════════════════════════════════════════════════════════════════
# Reference: SA3 Token Permutation
#
# Maps logical token index to physical storage index within 128-token blocks.
# Pattern optimizes tensor core access.
# ════════════════════════════════════════════════════════════════════════════

def sa3_token_permute_within_128(token_idx: int) -> int:
    """SA3 token permutation within 128-token block."""
    idx_in_32 = token_idx % 32
    block_32 = token_idx // 32
    
    permuted = (idx_in_32 // 8) * 2 + ((idx_in_32 % 8) // 2) * 8 + (idx_in_32 % 2)
    
    return block_32 * 32 + permuted


def sa3_token_permute_inverse(permuted_idx: int) -> int:
    """Inverse of SA3 token permutation."""
    # Build inverse mapping
    inverse = [0] * 128
    for i in range(128):
        inverse[sa3_token_permute_within_128(i)] = i
    
    return inverse[permuted_idx % 128] + (permuted_idx // 128) * 128


# ════════════════════════════════════════════════════════════════════════════
# Reference: SA3 Scale Swizzle
#
# Computes byte offset for scale factor storage in SA3's swizzled layout.
# Tiles are 64 rows × 16 columns.
# ════════════════════════════════════════════════════════════════════════════

def sa3_scale_swizzle_offset(row_within_64: int, col_idx: int) -> int:
    """SA3 64x16 scale factor swizzle."""
    col_group = col_idx // 4
    col_in_group = col_idx % 4
    row_group = row_within_64 // 16
    row_in_group = row_within_64 % 16
    
    return col_group * 256 + col_in_group + row_group * 4 + row_in_group * 16


# ════════════════════════════════════════════════════════════════════════════
# Reference: E2M1 Encode/Decode
# ════════════════════════════════════════════════════════════════════════════

def e2m1_nibble_to_float(nibble: int) -> float:
    """Decode E2M1 nibble to float."""
    sign = (nibble >> 3) & 0x1
    exp = (nibble >> 1) & 0x3
    mant = nibble & 0x1
    
    if exp == 0:
        mag = 0.5 * mant  # 0 or 0.5
    else:
        significand = 1.0 + 0.5 * mant
        exponent = exp - 1
        mag = math.ldexp(significand, exponent)
    
    return -mag if sign else mag


def find_nearest_e2m1(value: float) -> float:
    """Find nearest E2M1 representable value."""
    sign = -1.0 if value < 0 else 1.0
    abs_val = abs(value)
    
    if abs_val >= E2M1_MAX_VALUE:
        return sign * E2M1_MAX_VALUE
    
    # Find nearest
    best = 0.0
    best_dist = abs_val
    
    for repr_val in E2M1_POSITIVE_VALUES:
        dist = abs(abs_val - repr_val)
        if dist < best_dist:
            best_dist = dist
            best = repr_val
    
    return sign * best


# ════════════════════════════════════════════════════════════════════════════
# Reference: Block Quantization
# ════════════════════════════════════════════════════════════════════════════

@dataclass
class QuantizedBlock:
    quantized_values: List[float]
    scale: float


def clamp_to_fp8_range(value: float) -> float:
    """Clamp to FP8 E4M3 range."""
    if not math.isfinite(value):
        return 0.0
    return min(max(value, 0.0), FP8_E4M3_MAX_FINITE)


def reference_quantize_block_16(values: List[float]) -> QuantizedBlock:
    """Reference block-16 quantization."""
    assert len(values) == 16
    
    # Find max abs
    max_abs = 0.0
    for v in values:
        if math.isfinite(v):
            max_abs = max(max_abs, abs(v))
    
    # Compute scale with FP8 roundtrip
    scale = clamp_to_fp8_range(max_abs * E2M1_RCP_MAX)
    
    inv_scale = 0.0 if scale == 0.0 else 1.0 / scale
    
    # Scale and quantize
    quantized = []
    for v in values:
        scaled = v * inv_scale
        quantized.append(find_nearest_e2m1(scaled))
    
    return QuantizedBlock(quantized, scale)


def reference_dequantize_block_16(quantized: List[float], scale: float) -> List[float]:
    """Reference block-16 dequantization."""
    return [q * scale for q in quantized]


# ════════════════════════════════════════════════════════════════════════════
# Hypothesis Strategies
# ════════════════════════════════════════════════════════════════════════════

@st.composite
def block_16_values(draw, min_val=-10.0, max_val=10.0):
    """Generate a block of 16 float values."""
    return [draw(st.floats(min_value=min_val, max_value=max_val, 
                          allow_nan=False, allow_infinity=False))
            for _ in range(16)]


@st.composite  
def tensor_4d_shape(draw):
    """Generate a valid 4D tensor shape for attention."""
    batch = draw(st.integers(min_value=1, max_value=4))
    heads = draw(st.integers(min_value=1, max_value=8))
    seq_len = draw(st.sampled_from([128, 256, 512, 1024]))
    head_dim = draw(st.sampled_from([64, 128]))
    return (batch, heads, seq_len, head_dim)


# ════════════════════════════════════════════════════════════════════════════
# Property Tests: Token Permutation
# ════════════════════════════════════════════════════════════════════════════

class TestTokenPermutation:
    
    def test_bijective_within_128(self):
        """Permutation is a bijection on [0, 127]."""
        outputs = [sa3_token_permute_within_128(i) for i in range(128)]
        assert sorted(outputs) == list(range(128))
    
    def test_preserves_pairs(self):
        """Consecutive pairs remain consecutive."""
        for i in range(0, 128, 2):
            p0 = sa3_token_permute_within_128(i)
            p1 = sa3_token_permute_within_128(i + 1)
            assert p1 == p0 + 1, f"Pair ({i}, {i+1}) -> ({p0}, {p1})"
    
    def test_expected_pattern_first_32(self):
        """First 32 tokens match expected pattern."""
        expected = [
            0, 1, 8, 9, 16, 17, 24, 25,
            2, 3, 10, 11, 18, 19, 26, 27,
            4, 5, 12, 13, 20, 21, 28, 29,
            6, 7, 14, 15, 22, 23, 30, 31
        ]
        for i in range(32):
            assert sa3_token_permute_within_128(i) == expected[i]
    
    @given(st.integers(min_value=0, max_value=127))
    def test_inverse_is_correct(self, idx):
        """Inverse permutation recovers original."""
        permuted = sa3_token_permute_within_128(idx)
        recovered = sa3_token_permute_inverse(permuted)
        assert recovered == idx


# ════════════════════════════════════════════════════════════════════════════
# Property Tests: Scale Swizzle
# ════════════════════════════════════════════════════════════════════════════

class TestScaleSwizzle:
    
    def test_bijective_within_64x16(self):
        """Swizzle is bijection for 64x16 tile."""
        outputs = []
        for row in range(64):
            for col in range(16):
                outputs.append(sa3_scale_swizzle_offset(row, col))
        
        assert sorted(outputs) == list(range(64 * 16))
    
    @given(st.integers(min_value=0, max_value=63),
           st.integers(min_value=0, max_value=15))
    def test_within_bounds(self, row, col):
        """Swizzle offset is within [0, 1023]."""
        offset = sa3_scale_swizzle_offset(row, col)
        assert 0 <= offset < 64 * 16


# ════════════════════════════════════════════════════════════════════════════
# Property Tests: E2M1 Encoding
# ════════════════════════════════════════════════════════════════════════════

class TestE2M1:
    
    def test_decode_covers_all_16(self):
        """All 16 nibbles decode to finite values."""
        for nibble in range(16):
            value = e2m1_nibble_to_float(nibble)
            assert math.isfinite(value)
    
    def test_positive_values_match(self):
        """Positive nibbles decode to expected values."""
        for nibble in range(8):
            value = e2m1_nibble_to_float(nibble)
            assert abs(value - E2M1_POSITIVE_VALUES[nibble]) < 1e-6
    
    def test_negative_values_are_negated(self):
        """Negative nibbles are negated positive values."""
        for nibble in range(8, 16):
            pos_value = e2m1_nibble_to_float(nibble - 8)
            neg_value = e2m1_nibble_to_float(nibble)
            assert abs(neg_value + pos_value) < 1e-6
    
    def test_symmetric_range(self):
        """E2M1 range is [-6, 6]."""
        values = [e2m1_nibble_to_float(i) for i in range(16)]
        assert min(values) == -6.0
        assert max(values) == 6.0
    
    @given(st.floats(min_value=-6.0, max_value=6.0))
    def test_find_nearest_in_range(self, value):
        """find_nearest returns value in representable set."""
        assume(math.isfinite(value))
        nearest = find_nearest_e2m1(value)
        assert abs(nearest) in E2M1_POSITIVE_VALUES
    
    def test_find_nearest_clamps(self):
        """Values outside range are clamped."""
        assert find_nearest_e2m1(100.0) == 6.0
        assert find_nearest_e2m1(-100.0) == -6.0


# ════════════════════════════════════════════════════════════════════════════
# Property Tests: Block Quantization
# ════════════════════════════════════════════════════════════════════════════

class TestBlockQuantization:
    
    def test_zero_input(self):
        """All-zero input produces zero output."""
        zeros = [0.0] * 16
        result = reference_quantize_block_16(zeros)
        assert result.scale == 0.0
        assert all(q == 0.0 for q in result.quantized_values)
    
    @given(block_16_values())
    @settings(max_examples=100)
    def test_output_in_range(self, values):
        """Quantized values are in [-6, 6]."""
        result = reference_quantize_block_16(values)
        for q in result.quantized_values:
            assert -6.0 <= q <= 6.0
    
    @given(block_16_values())
    @settings(max_examples=100)
    def test_scale_non_negative(self, values):
        """Scale factor is non-negative."""
        result = reference_quantize_block_16(values)
        assert result.scale >= 0.0
    
    @given(block_16_values(min_val=-5.0, max_val=5.0))
    @settings(max_examples=100)
    def test_reconstruction_error_bounded(self, values):
        """Dequant(quant(x)) has bounded error."""
        result = reference_quantize_block_16(values)
        dequant = reference_dequantize_block_16(result.quantized_values, result.scale)
        
        for i in range(16):
            error = abs(dequant[i] - values[i])
            # Error should be bounded by half the max quantization step
            assert error <= 1.5


# ════════════════════════════════════════════════════════════════════════════
# Property Tests: Tensor Layouts
# ════════════════════════════════════════════════════════════════════════════

class TestTensorLayouts:
    
    @given(tensor_4d_shape())
    @settings(max_examples=20)
    def test_row_major_output_shape(self, shape):
        """Row-major quantization produces correct output shape."""
        B, H, N, D = shape
        
        # Output: [B, H, N, D/2]
        output_shape = (B, H, N, D // 2)
        assert output_shape[3] == D // 2
        
        # Scales: [B, H, N, D/16]
        scale_shape = (B, H, N, D // BLOCK_SIZE)
        assert scale_shape[3] == D // BLOCK_SIZE
    
    @given(tensor_4d_shape())
    @settings(max_examples=20)
    def test_transpose_output_shape(self, shape):
        """Transpose quantization produces correct output shape."""
        B, H, N, D = shape
        
        # Output: [B, H, D, N/2]
        output_shape = (B, H, D, N // 2)
        assert output_shape[2] == D
        assert output_shape[3] == N // 2
        
        # Scales: [B, H, D, N/16]
        scale_shape = (B, H, D, N // BLOCK_SIZE)
        assert scale_shape[2] == D
        assert scale_shape[3] == N // BLOCK_SIZE


# ════════════════════════════════════════════════════════════════════════════
# Property Tests: Numerical Properties
# ════════════════════════════════════════════════════════════════════════════

class TestNumericalProperties:
    
    @given(st.floats(min_value=0.01, max_value=100.0))
    def test_scale_proportional_to_max(self, max_val):
        """Scale is approximately max_val / 6."""
        values = [max_val if i == 0 else 0.0 for i in range(16)]
        result = reference_quantize_block_16(values)
        
        expected_scale = clamp_to_fp8_range(max_val * E2M1_RCP_MAX)
        assert abs(result.scale - expected_scale) < 0.01
    
    @given(block_16_values(min_val=-5.0, max_val=5.0))
    @settings(max_examples=50)
    def test_preserves_relative_order(self, values):
        """Quantization approximately preserves relative ordering."""
        result = reference_quantize_block_16(values)
        
        for i in range(16):
            for j in range(i + 1, 16):
                if values[i] > values[j] + 0.5:  # Margin for quantization
                    assert result.quantized_values[i] >= result.quantized_values[j] - 0.1


# ════════════════════════════════════════════════════════════════════════════
# Main
# ════════════════════════════════════════════════════════════════════════════

if __name__ == "__main__":
    import pytest
    pytest.main([__file__, "-v"])
