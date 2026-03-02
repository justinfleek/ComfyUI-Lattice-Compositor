# MonarchRT: Architecture

**Parent:** [monarch-rt-real-time-video.md](monarch-rt-real-time-video.md)

---

## 2. Core Insight: Monarch Matrices

### 2.1 The Attention Bottleneck in Video DiTs

Standard self-attention computes:

```
Attention(Q, K, V) = softmax(QK^T / √d) V

Where:
  Q, K, V ∈ ℝ^{N×d}   — Query, Key, Value matrices
  N = T × H × W       — Number of tokens (frames × height × width)
  d                   — Head dimension
```

For video generation with T=21 frames at 480×832 resolution:
- N = 21 × 30 × 52 = 32,760 tokens per attention layer
- Attention matrix: 32,760² ≈ 1 billion elements
- Memory: O(N²) = prohibitive for consumer GPUs
- Compute: O(N²d) = bottleneck for real-time inference

### 2.2 Monarch Matrix Factorization

**Key insight:** Many matrices can be efficiently represented as products of **block-diagonal matrices** interleaved with **permutations**.

A Monarch matrix M factors as:

```
M = L · P · R

Where:
  L ∈ ℝ^{n×n}  — Left block-diagonal matrix (b₁ blocks of size n/b₁)
  P            — Fixed permutation matrix
  R ∈ ℝ^{n×n}  — Right block-diagonal matrix (b₂ blocks of size n/b₂)
```

**Block Structure:**

```python
def monarch_factorization(n, b1, b2):
    """
    Factor matrix M = L @ P @ R with block-diagonal L and R.
    
    Complexity: O(n * (n/b1 + n/b2)) = O(n²/b) for b1 = b2 = b
    vs O(n²) for dense attention
    """
    # Left factor: b1 diagonal blocks of size (n/b1 × n/b1)
    L_blocks = [torch.randn(n//b1, n//b1) for _ in range(b1)]
    L = torch.block_diag(*L_blocks)
    
    # Permutation: interleave tokens across blocks
    P = create_interleave_permutation(n, b1, b2)
    
    # Right factor: b2 diagonal blocks of size (n/b2 × n/b2)  
    R_blocks = [torch.randn(n//b2, n//b2) for _ in range(b2)]
    R = torch.block_diag(*R_blocks)
    
    return L, P, R
```

### 2.3 Monarch Attention

Apply Monarch factorization to attention's softmax(QK^T):

```python
def monarch_attention(Q, K, V, b1, b2):
    """
    Approximate attention using Monarch matrix structure.
    
    Standard: A = softmax(QK^T/√d)
    Monarch:  A ≈ softmax(aL · aR^T) where aL, aR are low-rank factors
    """
    B, N, H, d = Q.shape
    block_b1 = N // b1
    block_b2 = N // b2
    
    # Reshape for block-wise processing
    Q_blocked = Q.view(B, b1, block_b1, H, d)
    K_blocked = K.view(B, b2, block_b2, H, d)
    V_blocked = V.view(B, b2, block_b2, H, d)
    
    # Stage 1: Compute aL (left factor attention) and y (partial output)
    # For each query block i, for each key block j:
    #   aL[i,j] = softmax(Q[i] @ K[j]^T) @ K[j]   — attended keys
    #   y[i,j]  = softmax(Q[i] @ K[j]^T) @ V[j]   — partial values
    #   cL[i,j] = logsumexp(Q[i] @ K[j]^T)        — normalization factors
    
    aL = torch.zeros(B, b1, b2, block_b1, H, d)
    y = torch.zeros(B, b1, b2, block_b1, H, d)
    cL = torch.zeros(B, b1, b2, block_b1, H)
    
    for i in range(b1):
        for j in range(b2):
            scores = torch.einsum('bqhd,bkhd->bqkh', 
                                  Q_blocked[:, i], K_blocked[:, j]) / math.sqrt(d)
            max_scores = scores.max(dim=2, keepdim=True).values
            exp_scores = torch.exp(scores - max_scores)
            sum_exp = exp_scores.sum(dim=2, keepdim=True)
            attn = exp_scores / sum_exp
            cL[:, i, j] = (max_scores.squeeze() + torch.log(sum_exp.squeeze()))
            aL[:, i, j] = torch.einsum('bqkh,bkhd->bqhd', attn, K_blocked[:, j])
            y[:, i, j] = torch.einsum('bqkh,bkhd->bqhd', attn, V_blocked[:, j])
    
    # Stage 2: Combine across key blocks
    # ... see full implementation in monarch-rt-implementation.md
    return output
```

### 2.4 Why Monarch Works for Video Attention

**Spatial-Temporal Structure:** Video attention has natural block structure:
- Tokens within a frame attend strongly to nearby spatial neighbors
- Tokens across frames attend to temporal correspondences
- Long-range interactions are often sparse

**Approximation Quality:** Monarch matrices can exactly represent:
- Butterfly transforms (FFT-like patterns)
- Block-sparse matrices  
- Low-rank + sparse decompositions

**Video-Specific Observations:**
1. **Temporal dimension is compressible:** Consecutive frames share structure
2. **Spatial attention is local-ish:** Most attention weight is within local patches
3. **Cross-frame attention is sparse:** Only motion-relevant regions need full attention

### 2.5 Complexity Analysis

| Operation | Standard Attention | Monarch Attention |
|-----------|-------------------|-------------------|
| Memory | O(N²) | O(N × b₁ × b₂) |
| Compute | O(N²d) | O(N^{3/2}d) for b = √N |
| Optimal Block Size | N/A | b₁ = b₂ = √N |

For N = 32,760 tokens:
- Standard: 32,760² = 1.07B attention entries
- Monarch (b=181): 32,760 × 181 × 181 ≈ 5.9M effective entries
- **Speedup: ~180× memory reduction**

## 3. Architecture

### 3.1 Two-Stage Monarch Attention

MonarchRT replaces standard attention with a two-stage computation:

```
Stage 1 (aL, cL, y): Block-local attention
  For each query block i ∈ [1, A] and key block j ∈ [1, F]:
    aL[i,j] = softmax(Q[i] @ K[j]^T) @ K[j]    — Attended keys
    y[i,j]  = softmax(Q[i] @ K[j]^T) @ V[j]    — Partial values  
    cL[i,j] = logsumexp(Q[i] @ K[j]^T)          — Log-sum-exp for combining

Stage 2 (z): Cross-block combination  
  For each query position:
    z = softmax(Q @ aL^T - cL) @ y             — Final output weighted by cL
```

Memory: O(A × F × block_b1 × block_b2) vs O(N²) standard
Compute: O(A × F × block_b1 × block_b2 × d) — sub-quadratic

### 3.2 Video-Specific Block Assignment

For video DiTs, MonarchRT assigns blocks along the **temporal** dimension:

```python
def video_block_assignment(T, H, W, f_tied=1, h_reduce=1, w_reduce=1):
    """
    Compute Monarch block parameters for video attention.
    
    Default: each frame is one block
      A = F = T (number of frames)
      block_b1 = block_b2 = H × W (tokens per frame)
    
    With tied frames: multiple frames share a block
      Reduces A, F by f_tied factor
    """
    A = T // f_tied
    F = T // f_tied
    spatial_tokens = (H // h_reduce) * (W // w_reduce)
    block_b1 = f_tied * spatial_tokens
    block_b2 = f_tied * spatial_tokens
    return A, F, block_b1, block_b2

# Example: Wan2.1-1.3B at 480×832, 21 frames
# T=21, H=30, W=52 → A=F=21, block_b1=block_b2=1560
```

### 3.3 Causal Monarch Attention for Autoregressive Video

For Self-Forcing style autoregressive generation, MonarchRT supports **causal block masking**:

```python
def causal_monarch_attention(Q, K, V, A, F, causal_block_size):
    """
    Masking: Query block a can only attend to key blocks f where:
      (a // causal_block_size) >= (f // causal_block_size)
    
    This enforces that frame groups can only see current and past.
    """
    for a in range(A):
        for f in range(F):
            a_block = a // causal_block_size
            f_block = f // causal_block_size
            if a_block < f_block:
                continue  # Skip future blocks
            # ... compute attention as before ...
```

### 3.4 Integration with Wan2.1 DiT Architecture

MonarchRT integrates into Wan2.1 by replacing the attention module:

```python
class WanAttentionWithMonarch(nn.Module):
    """
    Drop-in replacement for Wan2.1 attention.
    
    Config (self_forcing_monarch_dmd.yaml):
      monarch_args:
        enable: true
        num_iters: 1
        f_tied: 1
        h_reduce: 1
        w_reduce: 1
    """
    def __init__(self, dim, num_heads, monarch_args=None):
        super().__init__()
        self.num_heads = num_heads
        self.head_dim = dim // num_heads
        self.scale = self.head_dim ** -0.5
        self.qkv = nn.Linear(dim, dim * 3)
        self.proj = nn.Linear(dim, dim)
        self.monarch_enabled = monarch_args.get('enable', False) if monarch_args else False
        self.f_tied = monarch_args.get('f_tied', 1) if monarch_args else 1
    
    def forward(self, x, image_or_video_shape, is_causal=False):
        B, N, C = x.shape
        T, H, W = image_or_video_shape
        qkv = self.qkv(x).reshape(B, N, 3, self.num_heads, self.head_dim)
        Q, K, V = qkv.permute(2, 0, 1, 3, 4).unbind(0)
        
        if self.monarch_enabled:
            A, F, block_b1, block_b2 = video_block_assignment(T, H, W, self.f_tied)
            out = monarch_attention_triton(Q, K, V, A, F, block_b1, block_b2,
                                           sm_scale=self.scale, causal=is_causal)
        else:
            out = F.scaled_dot_product_attention(Q, K, V, is_causal=is_causal)
        
        return self.proj(out.reshape(B, N, C))
```

---

*Part of MonarchRT paper synthesis.*
