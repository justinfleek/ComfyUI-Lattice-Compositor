# MonarchRT: Efficient Attention for Real-Time Video Generation

**arXiv:** 2602.12271  
**Authors:** Krish Agarwal, Zhuoming Chen, Cheng Luo, Yongqi Chen, Haizhong Zheng, Xun Huang, Atri Rudra, Beidi Chen (CMU, Buffalo, Morpheus AI)  
**Status:** COMPLETE

---

## Document Structure

This paper synthesis is split across multiple files for maintainability:

| Document | Contents | Lines |
|----------|----------|-------|
| **monarch-rt-real-time-video.md** (this file) | Abstract, overview, navigation | ~100 |
| [monarch-rt-architecture.md](monarch-rt-architecture.md) | Sections 2-3: Math foundations, two-stage attention | ~350 |
| [monarch-rt-implementation.md](monarch-rt-implementation.md) | Sections 4-5: Triton kernels, training pipeline | ~300 |
| [monarch-rt-integration.md](monarch-rt-integration.md) | Sections 6-8: Performance, Lattice integration, bibliography | ~300 |

---

## Abstract

Video diffusion transformers (DiTs) achieve state-of-the-art quality but are computationally prohibitive for real-time generation due to the quadratic complexity of self-attention. MonarchRT introduces **Monarch matrix factorization** to sparsely parameterize attention maps in video DiTs, achieving minimal quality degradation while enabling true real-time inference.

**Core Contributions:**

1. **Monarch Attention** — Factor attention matrices as products of block-diagonal matrices interleaved with permutations, reducing complexity from O(N²) to O(N^{3/2})

2. **Training-Free and Fine-Tuned Variants** — Works both as a drop-in replacement (training-free) and with brief fine-tuning for quality recovery

3. **Efficient Triton Kernels** — Fused implementation exploiting the Monarch structure for memory-efficient computation on consumer GPUs

4. **First True Real-Time Video DiT** — Achieves **16 FPS on RTX 5090** with Self-Forcing autoregressive generation, matching dense model quality

**Key Results:**
- 2.1× speedup over dense FlashAttention with training-free MonarchRT
- 3.5× speedup with fine-tuned MonarchRT at equivalent quality
- Compatible with few-step distillation (DMD) and autoregressive generation (Self-Forcing)

---

## Quick Reference

### Complexity Comparison

| Operation | Standard Attention | Monarch Attention |
|-----------|-------------------|-------------------|
| Memory | O(N²) | O(N × b₁ × b₂) |
| Compute | O(N²d) | O(N^{3/2}d) for b = √N |

### Key Hyperparameters

| Parameter | Default | Purpose |
|-----------|---------|---------|
| f_tied | 1 | Frames per Monarch block |
| h_reduce | 1 | Spatial height reduction |
| w_reduce | 1 | Spatial width reduction |
| BLOCK_J | 16-128 | Query tile size (autotuned) |
| BLOCK_L | 16-128 | Key tile size (autotuned) |

### Performance Summary

| Configuration | Hardware | FPS | vs Dense |
|--------------|----------|-----|----------|
| MonarchRT (TF) | RTX 5090 | 16.7 | 2.1× |
| MonarchRT (FT) | RTX 5090 | 27.8 | 3.5× |
| MonarchRT (FT) | RTX 4090 | 15.4 | 2.8× |

---

## Section Overview

### 2. Core Insight: Monarch Matrices
→ See [monarch-rt-architecture.md](monarch-rt-architecture.md)

- The attention bottleneck in video DiTs
- Monarch matrix factorization (M = L · P · R)
- Why Monarch works for video attention
- Complexity analysis

### 3. Architecture  
→ See [monarch-rt-architecture.md](monarch-rt-architecture.md)

- Two-stage Monarch attention algorithm
- Video-specific block assignment
- Causal Monarch attention for autoregressive generation
- Integration with Wan2.1 DiT

### 4. Triton Kernel Implementation
→ See [monarch-rt-implementation.md](monarch-rt-implementation.md)

- Stage 1 kernel: `_al_cl_y_fwd`
- Stage 2 kernel: `_z_fwd`
- Memory layout and tensor descriptors
- Autotuning configuration

### 5. Training Pipeline
→ See [monarch-rt-implementation.md](monarch-rt-implementation.md)

- Training-free application
- Fine-tuning for quality recovery
- Self-Forcing integration
- Causal initialization

### 6. Performance
→ See [monarch-rt-integration.md](monarch-rt-integration.md)

- Latency benchmarks
- Quality metrics (VBench)
- Memory usage
- Scaling analysis

### 7. Relation to Lattice
→ See [monarch-rt-integration.md](monarch-rt-integration.md)

- Lattice video generation pipeline
- Hydrogen state management integration
- libevring event pattern mapping
- Real-time preview architecture

### 8. Bibliography
→ See [monarch-rt-integration.md](monarch-rt-integration.md)

---

*Document synthesized from MonarchRT implementation and paper.*
*Lattice integration patterns derived from Hydrogen architecture.*

*Generated: 2026-03-02*
