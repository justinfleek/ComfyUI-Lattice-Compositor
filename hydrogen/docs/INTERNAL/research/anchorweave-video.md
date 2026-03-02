# AnchorWeave: World-Consistent Video Generation with Retrieved Local Spatial Memories

**arXiv:** 2602.14941  
**Authors:** Zun Wang, Han Lin, Yue Zhang, Mohit Bansal (UNC Chapel Hill), Jaehong Yoon (NTU), Jaemin Cho (AI2)  
**Date:** February 17, 2026  
**Domain:** Computer Vision / Video Generation / 3D Reconstruction

---

## Abstract

AnchorWeave solves the problem of maintaining **spatial world consistency over long horizons** in camera-controllable video generation. 

**Key Problem:** Existing memory-based approaches condition generation on globally reconstructed 3D scenes, but reconstruction errors accumulate causing cross-view misalignment and ghosting artifacts.

**Key Insight:** Replace a single noisy global 3D memory with multiple clean **local geometric memories**, then learn to reconcile cross-view inconsistencies through a multi-anchor weaving controller.

---

## 1. Problem: Global 3D Memory Degradation

### 1.1 Previous Approach: Global Point Cloud Memory

```
Historical Frames → 3D Estimator → Global Point Cloud → Render Anchor → Generation
```

**Problem:** 
- Pose and depth estimation errors cause surfaces to reconstruct at **different 3D locations** across views
- These inconsistencies accumulate → noisy geometry → ghosting/drift artifacts

### 1.2 AnchorWeave Solution: Local Memory + Multi-Anchor Reconciliation

```
Historical Frames → Per-frame Local Point Clouds → Coverage-driven Retrieval 
                                                        ↓
                                          Multiple Clean Anchors
                                                        ↓
                                          Multi-Anchor Weaving Controller
                                                        ↓
                                              Consistent Generation
```

---

## 2. Methodology

### 2.1 Local Geometric Memory

Instead of fusing into one global point cloud, maintain **per-frame local point clouds**:
- Each frame has its own local geometry
- No accumulation of cross-view misalignment
- Cleaner geometric signals for rendering

### 2.2 Coverage-Driven Memory Retrieval

Given target camera trajectory, iteratively select local memories that **maximize additional visibility coverage**:

```
For each step in trajectory:
  1. Compute uncovered regions along trajectory
  2. Select local memory maximizing coverage
  3. Add to anchor set
  4. Update coverage
  5. Repeat until coverage threshold
```

### 2.3 Multi-Anchor Weaving Controller

Three components:

1. **Shared Cross-Anchor Attention**
   - Reason over multiple retrieved anchors jointly
   - Attend to consistent spatial features

2. **Pose-Guided Fusion**
   - Use camera poses to align anchor geometries
   - Resolve residual misalignment

3. **Learned Reconciliation**
   - Treat residual misalignment as learnable problem
   - Train controller to handle inconsistencies

### 2.4 Iterative Update-Retrieve-Generate Loop

```
1. Generate new frames
2. Convert to local geometric memory
3. Add to memory bank
4. Retrieve for next generation step
5. Repeat
```

---

## 3. Architecture

### 3.1 Video Diffusion Backbone

Using DiT-based Latent Diffusion Models (LDMs):
- Input: RGB video x ∈ R^(F×3×H×W)
- Encode to latent: z = E(x) ∈ R^(F×C'×H'×W')
- Diffusion: DDPM or Flow Matching
- Condition on: timestep, text, camera parameters, anchor videos

### 3.2 Training Objective

```
L_LDM = E_{z, ε~N(0,I), t} [||ε - ε_θ(z_t, t, c_text + c_cam)||²]
```

---

## 4. Experiments

### 4.1 Datasets

| Dataset | Description |
|---------|-------------|
| RealEstate10K | Indoor scenes, camera trajectories |
| DL3DV | Diverse 3D videos |

### 4.2 Results

AnchorWeave significantly improves:
- **Long-term scene consistency** (ghost-free revisit)
- **Visual quality** (cleaner geometry)
- **Generalization** to open-domain images/scenes

### 4.3 Ablation Study

Each component contributes:
- ✓ Local geometric memory (vs global)
- ✓ Coverage-driven retrieval
- ✓ Multi-anchor weaving controller

---

## 5. Relation to Hydrogen

### 5.1 World Models

For **billion-agent swarms** building 3D world models:

| Need | AnchorWeave Solution |
|------|---------------------|
| **Long-horizon consistency** | Local memory avoids drift |
| **Spatial coherence** | Multi-anchor reconciliation |
| **Efficient retrieval** | Coverage-driven selection |

### 5.2 Not Directly Applicable

- UI rendering
- DOM manipulation
- 2D layout

### 5.3 Complementary Papers

- **Spatia** (2512.15716): Video generation with spatial memory
- **WorldGen** (2511.16825): Text to traversable 3D
- **GAIA-2** (2503.20523): Multi-view world model

---

## 6. References

1. Wu et al. "SPMem" - Global point cloud memory
2. Zhao et al. "Spatia" - Spatial memory video generation
3. Li et al. "MagicWorld" - 3D-based memory
4. Rombach et al. "Latent Diffusion Models" (SD)
5. Ho et al. "DDPM"
6. Lipman et al. "Flow Matching"

---

## 7. Citation

```bibtex
@misc{wang2026anchorweave,
  title={AnchorWeave: World-Consistent Video Generation with Retrieved Local Spatial Memories},
  author={Zun Wang and Han Lin and Jaehong Yoon and Jaemin Cho and Yue Zhang and Mohit Bansal},
  year={2026},
  eprint={2602.14941},
  archivePrefix={arXiv},
  primaryClass={cs.CV}
}
```

---
*Research Document: Hydrogen Research Collection*
*Completed: 2026-02-26*
*Attestation: clarity*
