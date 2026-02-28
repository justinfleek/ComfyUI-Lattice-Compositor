# DreaMontage: Arbitrary Frame-Guided One-Shot Video Generation

**arXiv:** 2512.21252  
**Authors:** Jiawei Liu, Junqiao Li, Jiangfan Deng, Gen Li, Siyu Zhou, et al. (ByteDance Intelligence Creation Team)  
**Date:** December 25, 2025  
**Domain:** Computer Vision / Video Generation / One-Shot Video

---

## Abstract

DreaMontage generates **seamless, expressive, long-duration one-shot videos** from diverse user-provided inputs (keyframes, video clips).

**Key Innovation:** Three-dimension approach:
1. Lightweight intermediate-conditioning in DiT with Adaptive Tuning
2. Visual Expression SFT + Tailored DPO for quality
3. Segment-wise Auto-Regressive (SAR) inference

---

## 1. Problem: One-Shot Video Generation

### 1.1 Challenge

"The one-shot technique" (long take) is a cinematic aesthetic with:
- High production costs
- Complex real-world constraints
- Physical space limitations

### 1.2 Previous Approaches

| Method | Limitation |
|--------|------------|
| Clip concatenation | Fails visual smoothness |
| First-last frame | No temporal coherence |
| Naïve conditioning | Disjointed transitions |

---

## 2. Methodology

### 2.1 Intermediate-Conditioning Mechanism

- Integrates into DiT architecture
- **Adaptive Tuning:** Leverages base training data
- Unlocks arbitrary-frame control

### 2.2 Visual Expression SFT

- Curated high-quality dataset
- Enhanced visual fidelity
- Cinematic expressiveness

### 2.3 Tailored DPO

- Addresses subject motion rationality
- Improves transition smoothness
- Better success rate

### 2.4 Segment-wise Auto-Regressive (SAR) Inference

- Memory-efficient
- Extended sequences
- Seamless coherence

---

## 3. Results

- ✓ Arbitrary frame guidance
- ✓ Long-form coherent videos
- ✓ Cinematic quality
- ✓ Computational efficiency

---

## 4. Relation to Hydrogen

### 4.1 Video Generation

Complementary to:
- **Wan-Animate:** Character animation
- **BindWeave:** Subject consistency
- **AnchorWeave:** World consistency
- **ATI:** Trajectory control

### 4.2 Agent Applications

For **billion-agent swarms**:
- Generate coherent video narratives
- Seamless scene transitions
- Cinematic content creation

---
*Research Document: Hydrogen Research Collection*
*Completed: 2026-02-26*
*Attestation: clarity*
