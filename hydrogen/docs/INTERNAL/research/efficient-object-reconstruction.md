# Efficient Object Reconstruction with Differentiable Area Light Shading

**Authors:** Yaoan Gao, Jiamin Xu, James Tompkin, Qi Wang, Zheng Dong, Hujun Bao, Yujun Shen, Huamin Wang, Changqing Zou, Weiwei Xu (Zhejiang University, Brown University, Ant Group, Style3D)  
**Publication:** SIGGRAPH Asia 2025  
**Date:** December 2025  
**Domain:** Computer Graphics / 3D Reconstruction / Inverse Rendering

---

## Abstract

Proposes **active area lighting in inverse rendering** to capture BRDF material and geometry of real-world objects.

**Key Results:**
- +3 dB relighting PSNR over point lights
- Need only 1/5 of photos for same quality
- Works with mesh or 3D Gaussian splatting pipelines

---

## 1. Problem: Material Reconstruction

### 1.1 Challenge

Estimating material properties (BRDF) from photographs is challenging.

### 1.2 Solution: Area Lighting

- Provides wider range of lighting angles per photo
- Better material roughness estimation
- More accurate reconstruction

---

## 2. Methodology

### 2.1 Area Light vs Point Light

| Approach | Coverage | Photos Required |
|---------|----------|-----------------|
| Point light | Narrow | More |
| Area light | Broad | 1/5 |

### 2.2 Differentiable Rendering

- Monte Carlo ray tracing
- **LTC (Linearly Transformed Cosines)** - faster alternative

### 2.3 Pipeline Support

- Mesh-based
- 3D Gaussian Splatting

---

## 3. Results

- ✓ +3 dB relighting PSNR
- ✓ 5× fewer photos needed
- ✓ Both mesh and GS pipelines

---

## 4. Relation to Hydrogen

### 4.1 3D Reconstruction

Complementary to:
- **3D Gaussian Splatting** papers
- **Path tracing SDF grids**
- **Material segmentation**

### 4.2 Agent Applications

For **billion-agent swarms**:
- Efficient object capture
- Material property inference
- Real-world digitization

---
*Research Document: Hydrogen Research Collection*
*Completed: 2026-02-26*
*Attestation: clarity*
