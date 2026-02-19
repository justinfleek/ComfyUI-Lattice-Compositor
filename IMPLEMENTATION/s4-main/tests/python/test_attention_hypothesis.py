"""s4 // tests/python/test_attention_hypothesis.py

Hypothesis property tests for attention kernel mathematical invariants.
These verify the mathematical properties without requiring CUDA.
"""
import math
from typing import Tuple

import numpy as np
import pytest
from hypothesis import given, settings, assume
from hypothesis import strategies as st


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# Reference implementations
# ════════════════════════════════════════════════════════════════════════════

def reference_key_centering(
    key: np.ndarray,  # [batch, heads, seq, dim]
) -> np.ndarray:
    """Center keys by subtracting mean along sequence dimension."""
    # mean shape: [batch, heads, 1, dim]
    mean = key.mean(axis=2, keepdims=True)
    return key - mean


def reference_query_group_mean(
    query: np.ndarray,  # [batch, heads, seq, dim]
    group_size: int,
) -> Tuple[np.ndarray, np.ndarray]:
    """
    Compute per-group means and centered queries.
    
    Returns:
        centered: [batch, heads, seq, dim] - query with group mean subtracted
        group_means: [batch, heads, groups, dim] - mean vector per group
    """
    batch, heads, seq, dim = query.shape
    group_count = (seq + group_size - 1) // group_size
    
    centered = np.zeros_like(query)
    group_means = np.zeros((batch, heads, group_count, dim), dtype=query.dtype)
    
    for g in range(group_count):
        start = g * group_size
        end = min(start + group_size, seq)
        
        # Compute mean for this group
        group_mean = query[:, :, start:end, :].mean(axis=2, keepdims=True)
        group_means[:, :, g:g+1, :] = group_mean
        
        # Subtract mean from group members
        centered[:, :, start:end, :] = query[:, :, start:end, :] - group_mean
    
    return centered, group_means


def reference_score_correction(
    key_centered: np.ndarray,    # [batch, heads, key_seq, dim]
    query_group_mean: np.ndarray,  # [batch, heads, groups, dim]
) -> np.ndarray:
    """
    Compute score correction: delta_S = query_group_mean @ key_centered^T
    
    Returns: [batch, heads, groups, key_seq]
    """
    # Transpose key: [batch, heads, dim, key_seq]
    key_t = np.transpose(key_centered, (0, 1, 3, 2))
    # Matmul: [batch, heads, groups, dim] @ [batch, heads, dim, key_seq]
    # Result: [batch, heads, groups, key_seq]
    return np.matmul(query_group_mean, key_t)


# ════════════════════════════════════════════════════════════════════════════
# Hypothesis strategies
# ════════════════════════════════════════════════════════════════════════════

@st.composite
def attention_dims(draw, max_batch=4, max_heads=8, max_seq=64, max_dim=32):
    """Generate valid attention dimensions."""
    batch = draw(st.integers(1, max_batch))
    heads = draw(st.integers(1, max_heads))
    seq = draw(st.integers(1, max_seq))
    dim = draw(st.integers(1, max_dim))
    return batch, heads, seq, dim


@st.composite
def attention_tensor(draw, shape):
    """Generate a random attention tensor."""
    # Use moderate values to avoid numerical issues
    return draw(st.from_type(np.ndarray).filter(
        lambda x: x.shape == shape
    ).map(lambda _: np.random.randn(*shape).astype(np.float32) * 0.1))


def random_tensor(shape, scale=0.1):
    """Create a random tensor for testing."""
    return np.random.randn(*shape).astype(np.float32) * scale


# ════════════════════════════════════════════════════════════════════════════
# Property tests: Key centering
# ════════════════════════════════════════════════════════════════════════════

class TestKeyCentering:
    """Property tests for key centering operation."""
    
    @given(
        batch=st.integers(1, 4),
        heads=st.integers(1, 8),
        seq=st.integers(2, 64),
        dim=st.integers(1, 32),
    )
    @settings(max_examples=100, deadline=1000)
    def test_output_has_zero_mean(self, batch, heads, seq, dim):
        """Centered keys should have zero mean along sequence dimension."""
        key = random_tensor((batch, heads, seq, dim))
        centered = reference_key_centering(key)
        
        # Check mean along sequence dimension is ~0
        means = centered.mean(axis=2)
        assert np.allclose(means, 0, atol=1e-5)
    
    @given(
        batch=st.integers(1, 2),
        heads=st.integers(1, 4),
        seq=st.integers(2, 32),
        dim=st.integers(1, 16),
    )
    @settings(max_examples=100, deadline=1000)
    def test_preserves_relative_differences(self, batch, heads, seq, dim):
        """Differences between positions are preserved after centering."""
        key = random_tensor((batch, heads, seq, dim))
        centered = reference_key_centering(key)
        
        # For any two positions, difference should be the same
        for s1 in range(min(seq, 5)):
            for s2 in range(s1 + 1, min(seq, 5)):
                input_diff = key[:, :, s1, :] - key[:, :, s2, :]
                output_diff = centered[:, :, s1, :] - centered[:, :, s2, :]
                assert np.allclose(input_diff, output_diff, atol=1e-5)
    
    @given(
        batch=st.integers(1, 4),
        heads=st.integers(1, 8),
        seq=st.integers(1, 64),
        dim=st.integers(1, 32),
    )
    @settings(max_examples=50, deadline=1000)
    def test_idempotent(self, batch, heads, seq, dim):
        """Centering already-centered keys should be identity."""
        key = random_tensor((batch, heads, seq, dim))
        centered = reference_key_centering(key)
        double_centered = reference_key_centering(centered)
        
        assert np.allclose(centered, double_centered, atol=1e-5)
    
    @given(
        batch=st.integers(1, 4),
        heads=st.integers(1, 8),
        seq=st.integers(1, 64),
        dim=st.integers(1, 32),
        scalar=st.floats(-10, 10, allow_nan=False, allow_infinity=False),
    )
    @settings(max_examples=50, deadline=1000)
    def test_translation_invariance(self, batch, heads, seq, dim, scalar):
        """Adding constant along sequence dimension doesn't change centered result."""
        key = random_tensor((batch, heads, seq, dim))
        key_shifted = key + scalar
        
        centered1 = reference_key_centering(key)
        centered2 = reference_key_centering(key_shifted)
        
        assert np.allclose(centered1, centered2, atol=1e-5)


# ════════════════════════════════════════════════════════════════════════════
# Property tests: Query group mean
# ════════════════════════════════════════════════════════════════════════════

class TestQueryGroupMean:
    """Property tests for query group mean operation."""
    
    @given(
        batch=st.integers(1, 2),
        heads=st.integers(1, 4),
        seq=st.integers(1, 32),
        dim=st.integers(1, 16),
        group_size=st.integers(1, 16),
    )
    @settings(max_examples=100, deadline=1000)
    def test_group_means_are_correct(self, batch, heads, seq, dim, group_size):
        """Group means should equal average of group members."""
        query = random_tensor((batch, heads, seq, dim))
        centered, group_means = reference_query_group_mean(query, group_size)
        
        group_count = (seq + group_size - 1) // group_size
        
        for g in range(group_count):
            start = g * group_size
            end = min(start + group_size, seq)
            
            expected_mean = query[:, :, start:end, :].mean(axis=2)
            actual_mean = group_means[:, :, g, :]
            
            assert np.allclose(expected_mean, actual_mean, atol=1e-5)
    
    @given(
        batch=st.integers(1, 2),
        heads=st.integers(1, 4),
        seq=st.integers(1, 32),
        dim=st.integers(1, 16),
        group_size=st.integers(1, 16),
    )
    @settings(max_examples=100, deadline=1000)
    def test_centered_queries_have_zero_group_mean(self, batch, heads, seq, dim, group_size):
        """Centered queries should sum to zero within each group."""
        query = random_tensor((batch, heads, seq, dim))
        centered, _ = reference_query_group_mean(query, group_size)
        
        group_count = (seq + group_size - 1) // group_size
        
        for g in range(group_count):
            start = g * group_size
            end = min(start + group_size, seq)
            
            group_mean = centered[:, :, start:end, :].mean(axis=2)
            assert np.allclose(group_mean, 0, atol=1e-5)
    
    @given(
        batch=st.integers(1, 2),
        heads=st.integers(1, 4),
        seq=st.integers(1, 32),
        dim=st.integers(1, 16),
    )
    @settings(max_examples=50, deadline=1000)
    def test_group_size_one_equals_centering(self, batch, heads, seq, dim):
        """Group size 1 means each query is its own mean, so centered = 0."""
        query = random_tensor((batch, heads, seq, dim))
        centered, group_means = reference_query_group_mean(query, group_size=1)
        
        # Centered should be all zeros
        assert np.allclose(centered, 0, atol=1e-5)
        
        # Group means should equal original queries
        assert np.allclose(group_means, query, atol=1e-5)
    
    @given(
        batch=st.integers(1, 2),
        heads=st.integers(1, 4),
        seq=st.integers(1, 32),
        dim=st.integers(1, 16),
    )
    @settings(max_examples=50, deadline=1000)
    def test_group_size_seq_equals_full_centering(self, batch, heads, seq, dim):
        """Group size >= seq means single group, equivalent to key centering."""
        query = random_tensor((batch, heads, seq, dim))
        
        centered_group, group_means = reference_query_group_mean(query, group_size=seq)
        centered_full = reference_key_centering(query)
        
        assert np.allclose(centered_group, centered_full, atol=1e-5)
        
        # Should have exactly one group mean equal to full mean
        assert group_means.shape[2] == 1
        expected_mean = query.mean(axis=2, keepdims=True)
        assert np.allclose(group_means, expected_mean, atol=1e-5)


# ════════════════════════════════════════════════════════════════════════════
# Property tests: Score correction identity
# ════════════════════════════════════════════════════════════════════════════

class TestScoreCorrection:
    """Property tests for the score correction mathematical identity."""
    
    @given(
        batch=st.integers(1, 2),
        heads=st.integers(1, 2),
        query_seq=st.integers(1, 16),
        key_seq=st.integers(1, 16),
        dim=st.integers(1, 8),
        group_size=st.integers(1, 8),
    )
    @settings(max_examples=100, deadline=2000)
    def test_attention_score_identity(self, batch, heads, query_seq, key_seq, dim, group_size):
        """
        Verify: Q @ K^T = Q' @ K'^T + expand(Q_mean @ K'^T)
        
        Where:
        - K' = K - mean(K, dim=seq)
        - Q' = Q - group_mean(Q)
        - Q_mean = group_mean(Q)
        """
        query = random_tensor((batch, heads, query_seq, dim))
        key = random_tensor((batch, heads, key_seq, dim))
        
        # Original scores: Q @ K^T -> [batch, heads, query_seq, key_seq]
        original_scores = np.matmul(query, np.transpose(key, (0, 1, 3, 2)))
        
        # Centered versions
        key_centered = reference_key_centering(key)
        query_centered, query_group_mean = reference_query_group_mean(query, group_size)
        
        # Centered scores: Q' @ K'^T
        centered_scores = np.matmul(
            query_centered, 
            np.transpose(key_centered, (0, 1, 3, 2))
        )
        
        # Score correction: Q_mean @ K'^T -> [batch, heads, groups, key_seq]
        delta_s = reference_score_correction(key_centered, query_group_mean)
        
        # Expand delta_s to [batch, heads, query_seq, key_seq]
        group_count = (query_seq + group_size - 1) // group_size
        expanded_delta = np.zeros_like(original_scores)
        for q in range(query_seq):
            g = q // group_size
            expanded_delta[:, :, q, :] = delta_s[:, :, g, :]
        
        # Reconstruct: Q' @ K'^T + delta_S
        reconstructed = centered_scores + expanded_delta
        
        # Should match original
        assert np.allclose(original_scores, reconstructed, atol=1e-4)
    
    @given(
        batch=st.integers(1, 2),
        heads=st.integers(1, 2),
        seq=st.integers(1, 16),
        dim=st.integers(1, 8),
    )
    @settings(max_examples=50, deadline=1000)
    def test_self_attention_symmetry(self, batch, heads, seq, dim):
        """For self-attention with full sequence as one group, delta_S = 0."""
        # When K is centered and group_size = seq, the correction is just
        # mean(Q) @ K'^T, and since K' has zero mean, this should work out
        x = random_tensor((batch, heads, seq, dim))
        
        key_centered = reference_key_centering(x)
        query_centered, query_mean = reference_query_group_mean(x, group_size=seq)
        
        delta_s = reference_score_correction(key_centered, query_mean)
        
        # Original self-attention: X @ X^T
        original = np.matmul(x, np.transpose(x, (0, 1, 3, 2)))
        
        # Centered: X' @ X'^T + delta_S
        centered = np.matmul(
            query_centered,
            np.transpose(key_centered, (0, 1, 3, 2))
        )
        # delta_s is [batch, heads, 1, seq], expand to [batch, heads, seq, seq]
        reconstructed = centered + delta_s  # Broadcasting handles expansion
        
        assert np.allclose(original, reconstructed, atol=1e-4)


# ════════════════════════════════════════════════════════════════════════════
# Property tests: Workspace requirements
# ════════════════════════════════════════════════════════════════════════════

class TestWorkspaceRequirements:
    """Property tests for workspace size computation."""
    
    @given(
        batch1=st.integers(1, 8),
        batch2=st.integers(1, 8),
        heads=st.integers(1, 32),
        seq=st.integers(128, 512),
        dim=st.sampled_from([64, 128, 256]),
    )
    @settings(max_examples=50, deadline=1000)
    def test_monotonic_in_batch(self, batch1, batch2, heads, seq, dim):
        """Larger batch size requires more workspace."""
        # This is a logical property test - actual computation would use C++ bindings
        # For now, just verify the mathematical relationship
        def estimate_workspace(b, h, s, d):
            # Simplified estimate based on the workspace components
            group_count = (s + 127) // 128
            s_pad = ((s + 127) // 128) * 128
            
            bf16_size = 2
            fp32_size = 4
            fp8_size = 1
            
            key_centered = b * h * s_pad * d * bf16_size
            query_centered = b * h * s_pad * d * bf16_size
            query_mean = b * h * group_count * d * bf16_size
            score_corr = b * h * group_count * s * fp32_size
            query_fp4 = b * h * s_pad * (d // 2)
            key_fp4 = b * h * s_pad * (d // 2)
            value_fp4 = b * h * d * (s_pad // 2)
            scale_q = b * h * s_pad * (d // 16) * fp8_size
            scale_k = b * h * s_pad * (d // 16) * fp8_size
            scale_v = b * h * d * (s_pad // 16) * fp8_size
            
            return sum([key_centered, query_centered, query_mean, score_corr,
                       query_fp4, key_fp4, value_fp4, scale_q, scale_k, scale_v])
        
        ws1 = estimate_workspace(batch1, heads, seq, dim)
        ws2 = estimate_workspace(batch2, heads, seq, dim)
        
        if batch1 <= batch2:
            assert ws1 <= ws2
        if batch1 >= batch2:
            assert ws1 >= ws2


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
