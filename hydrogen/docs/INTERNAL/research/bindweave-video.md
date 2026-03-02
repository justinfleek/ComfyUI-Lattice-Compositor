# BindWeave: Subject-Consistent Video Generation via Cross-Modal Integration

**arXiv:** 2510.00438  
**Authors:** Zhaoyang Li, Wenfei Yang, Tianzhu Zhang (USTC), Dongjun Qian, Kai Su, Qishuai Diao, Xiangyang Xia, Chang Liu, Zehuan Yuan (ByteDance)  
**Date:** October 1, 2025  
**Domain:** Computer Vision / Video Generation / Multimodal AI

---

## Abstract

BindWeave solves **subject-consistent video generation**—ensuring one or more subjects maintain identity and appearance throughout generated videos.

**Key Problem:** Existing models use "shallow fusion" (separate encoders → simple concatenation), failing to understand complex spatial relationships and interactions among multiple subjects.

**Key Solution:** Use a **Multimodal Large Language Model (MLLM)** as intelligent instruction parser to perform deep cross-modal reasoning, binding textual commands to visual entities before generation.

---

## 1. Problem: Subject Consistency in Video Generation

### 1.1 Challenge

| Issue | Description |
|-------|-------------|
| **Identity Confusion** | Which subject in prompt maps to which reference image? |
| **Action Misplacement** | Spatial relationships lost in generation |
| **Attribute Blending** | Features bleed between subjects |
| **Multi-Subject Complexity** | Heterogeneous entities with interactions |

### 1.2 Previous Approach: Shallow Fusion

```
Reference Images → Separate Encoder → Concatenate → Cross-Attention → Generation
Text Prompt    → Separate Encoder ─────────↗
```

**Limitation:** No deep semantic understanding of multimodal inputs.

---

## 2. Methodology: MLLM-DiT Framework

### 2.1 Architecture Overview

```
┌─────────────────────────────────────────────────────────────────────┐
│                    BindWeave Architecture                             │
├─────────────────────────────────────────────────────────────────────┤
│                                                                      │
│  Reference Images + Text Prompt                                      │
│           │                                                          │
│           ▼                                                          │
│  ┌─────────────────┐                                                │
│  │  Qwen2.5-VL    │  (MLLM for cross-modal reasoning)             │
│  │  Multimodal LLM │                                                │
│  └────────┬────────┘                                                │
│           │                                                         │
│           ▼  Hidden States (H_mllm)                                 │
│  ┌─────────────────┐                                                │
│  │  Connector      │  (Project to DiT space)                        │
│  │  (MLP)         │                                                │
│  └────────┬────────┘                                                │
│           │                                                         │
│           ▼  c_mllm (semantic reasoning)                            │
│  ┌────────────────────────────────────────────┐                     │
│  │         Diffusion Transformer (DiT)         │                     │
│  │  - Temporal Self-Attention                  │                     │
│  │  - Text Cross-Attention                     │                     │
│  │  - CLIP Image Cross-Attention              │                     │
│  │  - MLLM Cross-Attention (new!)             │                     │
│  └─────────────────────┬──────────────────────┘                     │
│                        │                                             │
│                        ▼                                             │
│               Subject-Consistent Video                               │
│                                                                      │
└─────────────────────────────────────────────────────────────────────┘
```

### 2.2 Intelligent Instruction Planning (MLLM)

**Input Construction:**
```
X = [T, ⟨img⟩₁, ⟨img⟩₂, ..., ⟨img⟩ₖ]  (multimodal sequence)
I = [I₁, I₂, ..., Iₖ]                   (reference images)
```

Where ⟨img⟩ₖ is a special placeholder token aligned with image Iₖ.

**Processing:**
```
H_mllm = MLLM(X, I)
c_mllm = Connector(H_mllm)  -- Project to DiT conditioning space
```

**Output:** Hidden states encoding:
- Subject identity
- Spatial relationships
- Temporal logic
- Role disentanglement

### 2.3 Joint Conditioning Signal

Combine MLLM reasoning with traditional text encoding:

```python
c_text = T5_Encoder(text_prompt)
c_joint = Concat(c_mllm, c_text)
```

This provides:
- **Deep semantic reasoning** (MLLM)
- **Fine-grained textual semantics** (T5)

### 2.4 Collective Conditioning in DiT

Three conditioning streams:

1. **VAE Features** (low-level appearance)
   ```python
   c_vae = VAE_Encoder(reference_images)
   H_vid = PatchEmbed(concat(noise_video, c_vae, mask))
   ```

2. **CLIP Features** (semantic identity)
   ```python
   c_clip = CLIP_Encoder(reference_images)
   ```

3. **MLLM Reasoning** (complex relationships)
   ```python
   c_joint = MLLM_Connector(hidden_states)
   ```

### 2.5 Cross-Attention Fusion

```python
# Traditional: text + image
H_out = H_vid + Attn(Q_vid, K_text, V_text) + γ * Attn(Q_vid, K_img, V_img)

# BindWeave: + MLLM reasoning
H_out = H_vid + Attn(Q_vid, K_joint, V_joint) + Attn(Q_vid, K_clip, V_clip)
```

---

## 3. Training

### 3.1 Dataset

- **OpenS2V-5M**: 5 million video-text pairs
- **Curated**: ~1 million high-quality pairs after filtering

### 3.2 Two-Stage Curriculum

| Stage | Iterations | Purpose |
|-------|-----------|---------|
| Stabilization | 1,000 | Core identity preservation |
| Full Scale | 5,000 | Generalization |

### 3.3 Training Objective

```python
L_mse = ||u_θ(z_t, t, c_joint, c_clip, c_vae) - v_t||²
```

Using **Rectified Flow** (Flow Matching) for stable training.

### 3.4 Inference

- 50 denoising steps
- CFG scale ω = 5
- Prompt rephraser for accuracy

---

## 4. Results

### 4.1 Benchmark: OpenS2V-Eval

180 prompts in 7 categories:
- Single-face-to-video
- Single-entity-to-video
- Single-body-to-video
- Human-entity-to-video
- Multi-face-to-video
- Multi-entity-to-video
- Multi-body-to-video

### 4.2 Metrics

| Metric | Measures |
|--------|----------|
| **NexusScore** | Subject consistency |
| **NaturalScore** | Temporal naturalness |
| **GmeScore** | Text-video alignment |
| FaceSim | Identity preservation |
| Aesthetics | Visual quality |
| MotionSmoothness | Temporal coherence |

### 4.3 Performance

BindWeave achieves **state-of-the-art** on:
- ✓ Subject consistency (NexusScore)
- ✓ Naturalness
- ✓ Text alignment
- ✓ Outperforms open-source and commercial models

---

## 5. Relation to Hydrogen

### 5.1 Video Generation for UI

For **billion-agent swarms** generating video content:

| Need | BindWeave Solution |
|------|-------------------|
| **Subject consistency** | MLLM reasoning before generation |
| **Multi-entity scenes** | Unified cross-modal parsing |
| **Identity preservation** | CLIP + VAE + MLLM triple conditioning |

### 5.2 Complementary Papers

- **AnchorWeave** (2602.14941): World consistency via local memories
- **Spatia**: Spatial memory video generation
- **Wan/Animate**: Character animation

### 5.3 Not Directly Applicable

- DOM manipulation
- 2D layout
- WebGPU compute

---

## 6. References

1. Qwen2.5-VL (MLLM backbone)
2. Wan (Video DiT foundation)
3. DiT (Diffusion Transformer)
4. Rectified Flow / Flow Matching
5. CLIP (semantic features)
6. T5 (text encoding)
7. OpenS2V benchmark

---

## 7. Citation

```bibtex
@misc{li2025bindweave,
  title={BindWeave: Subject-Consistent Video Generation via Cross-Modal Integration},
  author={Zhaoyang Li and Dongjun Qian and Kai Su and Qishuai Diao and Xiangyang Xia and Chang Liu and Wenfei Yang and Tianzhu Zhang and Zehuan Yuan},
  year={2025},
  eprint={2510.00438},
  archivePrefix={arXiv},
  primaryClass={cs.CV}
}
```

---
*Research Document: Hydrogen Research Collection*
*Completed: 2026-02-26*
*Attestation: clarity*
