# Learning Zero-Shot Material States Segmentation

## Paper Metadata

**Title:** Learning Zero-Shot Material States Segmentation, by Implanting Natural Image Patterns in Synthetic Data

**Authors:**
- Sagi Eppel¹'²* (*Equal contributions)
- Jolina Yining Li²*
- Manuel S. Drehwald²
- Alan Aspuru-Guzik¹'²

**Affiliations:**
1. Vector Institute
2. University of Toronto

**Published:** NeurIPS 2024 (38th Conference on Neural Information Processing Systems)

**arXiv:** arXiv:2403.03309v6 [cs.CV]

**Date:** August 1, 2025

**Artifact URLs:** Dataset, code, trained models, 300,000+ extracted textures and PBR materials

---

## Core Thesis

Visual recognition of materials and their states is essential for understanding the physical world. Material states include:
- Wet regions on surfaces
- Stains on fabrics
- Infected areas on plants
- Minerals in rocks
- Dust on surfaces
- Cooked/burned food
- Rust on metals
- Foam in liquids

**Problem:** No comprehensive dataset exists for general material state segmentation. Manual annotation is costly and imprecise for soft boundaries and gradual transitions. Synthetic data lacks real-world diversity.

**Solution:** Infuse patterns automatically extracted from real-world images into synthetic data to bridge the gap between synthetic precision and real-world complexity.

---

## Key Contributions

### 1. First General Zero-Shot Material State Benchmark (MatSeg)

- **1,220 real-world images** covering diverse domains
- Point-based and similarity-based annotations
- Handles partial similarity between similar (but not identical) materials
- Captures gradual transitions and scattered shapes
- Hard segmentation + soft similarity measures

### 2. Procedural Imitation: Pattern Infusion Method

Unsupervised method to extract patterns from real images and infuse into synthetic scenes:
- Extract simple image properties (RGB, HSV channels)
- Use as material property maps in synthetic 3D/2D scenes
- Captures complexity of real world while maintaining precise annotations

### 3. Large-Scale Training Data Generation

- 2D synthetic scenes with mapped materials
- 3D synthetic scenes with PBR materials
- 300,000+ extracted textures and SVBRDF/PBR materials shared

### 4. Trained Segmentation Network

- Class-agnostic soft material segmentation
- Outperforms SAM and Materialistic on benchmark
- Handles scattered shapes, soft boundaries, gradual transitions

---

## Domains Covered in Benchmark

| Domain | Examples |
|--------|----------|
| Food | Cooked, burned, frozen, spoiled |
| Plants | Infected, dry, wilted, healthy |
| Rocks/Soils | Minerals, sediment, dust, moisture |
| Construction | Rusted, worn, cracked, wet |
| Metals | Corroded, oxidized, polished |
| Liquids | Foam, precipitate, contamination |
| Fabrics | Stained, worn, damp |
| Laboratory | Chemical phases, reactions |

---

## Key Algorithms

### Algorithm 1: Unsupervised Map Extraction

```
1. Pick random image from dataset
2. Select random channel: R, G, B, H, S, or V
3. Apply random ramp threshold:
   - Pick two random threshold values t_low, t_high
   - Values below t_low → 0
   - Values above t_high → 1
   - Values in between → linear interpolation
4. Result: Soft binary map for material positioning
```

**Key Insight:** Simple image properties often correlate with material regions:
- Darker = wet/dense/stained
- Brighter = dry/light/scattered
- Hue changes = material type transitions

### Algorithm 2: Texture Extraction

```
1. Split image into 40x40 pixel cells
2. For each cell, compute:
   - RGB color distribution
   - Gradient distribution
3. Identify uniform texture regions:
   - Jensen-Shannon distance < 0.5 between cells
   - Minimum 6x6 cells
4. Filter out:
   - Too uniform (smooth/blank)
   - Extreme values (over/underexposed)
5. Output: Texture image patches
```

### Algorithm 3: PBR Material Generation

```
1. Take extracted texture image
2. For each material property (albedo, roughness, metallic, etc.):
   a. Randomly select one channel: RGB or HSV
   b. Apply random augmentation
   c. Apply thresholding (optional)
   d. Apply random scaling/shifting
3. Generate normal map from height/bumpiness gradient
4. Output: Full SVBRDF/PBR material maps
```

### Algorithm 4: 3D Scene Generation

```
1. Load random 3D objects (ShapeNet)
2. Generate UV map from extracted soft map
3. Assign PBR material to each map region
4. Load panoramic HDRI for background/lighting
5. Add random ground plane, objects
6. Set random camera position
7. Render with Cycles (Blender)
```

### Algorithm 5: 2D Scene Generation

```
1. Define map regions as material segments
2. Map different textures to different regions
3. Overlay on random background image
4. Apply shadow effects using secondary soft map
5. Blend materials in transition zones (value 0-1)
```

---

## Network Architecture

### Material Descriptor Network

```
Input: RGB Image
  ↓
Encoder: Pre-trained ConvNext
  ↓
PSP Layer (Pyramid Pooling)
  ↓
Upsampling (3 skip connections)
  ↓
Output: 128-dimensional descriptor per pixel
```

### Training Procedure

```
1. Batch: Multiple images with material annotations
2. Forward pass → 128-d descriptor map per image
3. Average descriptors in GT material regions
4. Compute cosine similarity:
   - Each pixel descriptor vs. each material average
5. Stack similarity maps → softmax (temp=0.2)
6. Cross-entropy loss with one-hot GT masks
```

**Key:** Material similarity = cosine similarity of 128-d descriptors

---

## Benchmark Details

### Annotation Format

**Point-based sampling:**
- Sample points representing each material state distribution
- Group points by exact material (same color = same material)
- Define partial similarity groups (boxes in figures)

**Triplet Evaluation:**
```
1. Select three points: anchor, pos, neg
2. Compare anchor-pos similarity vs anchor-neg similarity
3. Prediction correct if matches GT ordering
4. Average over all triplets per image
```

### Evaluation Metrics

| Metric | Description |
|--------|-------------|
| Triplet Accuracy | Correct triplet ordering |
| Soft Triplets | Triplets with partial similarity |
| IOU | For hard segmentation (optimal threshold) |

---

## Results

### MatSeg Benchmark (Triplet Accuracy)

| Method | 1 Point | Hard | Soft |
|--------|---------|------|------|
| **MatSeg (Ours) 2D** | 0.91 | - | 0.84 |
| **MatSeg (Ours) 3D** | 0.90 | - | 0.83 |
| **MatSeg (Ours) Mixed** | 0.92 | - | 0.84 |
| Materialistic | 0.76 | - | 0.72 |
| SAM (1 point) | 0.69 | - | 0.63 |
| SAM (8 points) | 0.74 | - | 0.65 |

### Related Benchmarks (IOU)

| Dataset | MatSeg | Materialistic | SAM (4pts) |
|--------|--------|---------------|------------|
| Cu Ore | 0.52 | 0.36 | 0.51 |
| FeM Ore | 0.62 | 0.37 | 0.50 |
| Corrosion | 0.69 | 0.49 | 0.54 |
| Leaf Disease | 0.56 | 0.47 | 0.51 |
| Dust (URDE) | 0.50 | 0.47 | 0.49 |
| Soil States | 0.62 | 0.53 | 0.68 |
| NuInsSeg | 0.38 | 0.17 | 0.29 |
| Materialistic | 0.75 | 0.87 | 0.80 |

---

## Key Findings

### 1. Foundation Models Struggle

- SAM trained on 11M images with 1B segments
- Materialistic trained on synthetic PBR data
- Both fail on scattered shapes and soft boundaries
- Neither handles gradual transitions well

### 2. Synthetic + Real Infusion Works

- Net trained on infused synthetic data generalizes to real
- Outperforms both real-trained (SAM) and synthetic-trained (Materialistic)
- Supports hypothesis: simple correlations → general learning

### 3. Shape Distribution Matters

- MatSeg excels at scattered/sparse/soft shapes
- SAM/Materialistic excel at bulk smooth shapes
- Different data = different inductive biases

---

## Relation to Hydrogen

### Material Representation

The paper's material representation aligns with Hydrogen's goals:

```
Material Properties:
- Albedo (color)
- Roughness
- Metallic
- Normal/Height
- Transparency
- Ambient Occlusion

Each as 2D map → PBR material
```

### Pattern Infusion for Rendering

Hydrogen could use similar techniques:
- Extract patterns from real images
- Use as material property maps
- Generate diverse synthetic training data
- Train networks for material prediction

### Zero-Shot Segmentation

Similar to Hydrogen's view functions:
- Input: Element + Query point
- Output: Material similarity to query
- Enables class-agnostic material detection

### Texture/Pattern Matching

The cosine similarity descriptor approach:
- 128-d embedding per pixel
- Compare to prototype material
- Soft similarity for mixtures/transitions

Could inform:
- Color space interpolation
- Texture similarity metrics
- Material state gradients

---

## Technical Specifications

### Hardware
- 2D generation: CPU (i7)
- 3D rendering: RTX 3090 GPU
- Blender 4.0 with Cycles

### Data Sources
- Open Images v7 (Apache License)
- ShapeNet 3D objects (GNU license)
- HDRI Haven (CC0 license)
- Custom extracted textures

### Training Parameters
- Optimizer: AdamW
- Learning rate: 1e-5
- Image size: 250-900 px (random crop)
- Descriptor dimension: 128
- Temperature: 0.2 (softmax)

---

## References (Paper-Specific)

### Dataset Benchmarks Referenced
- [17] Cu Dataset - Copper ore segmentation
- [18] FeM Dataset - Iron ore segmentation
- [48] Corrosion-segment - Rust on metals
- [5] Leaf disease segmentation
- [18] URDE - Dust on roads
- [49, 50] Soil type datasets
- [39, 40] NuInsSeg, CryoNuSeg - Microscopy
- [53] Materialistic benchmark
- [24] LabPics - Chemistry materials

### Technical References
- [6] BSDF/BRDF theory
- [43] PBR rendering (Pharr et al.)
- [21] One-shot material recognition
- [34] SAM (Segment Anything)
- [38] ConvNeXt architecture
- [8] Blender rendering

---

## Appendix: Asset Licenses

| Asset | License |
|-------|---------|
| MatSeg Dataset | CC0 1.0 Universal |
| Extracted Textures | CC0 1.0 Universal |
| Code | CC0 1.0 Universal |
| Open Images | Apache 2.0 |
| ShapeNet | GNU |
| HDRI Haven | CC0 |

---

## Summary

This paper demonstrates:

1. **Pattern infusion** - Extract simple image correlations → use as material maps in synthetic scenes
2. **Benchmark** - First zero-shot material state segmentation benchmark
3. **Network** - Class-agnostic material segmentation trained on infused synthetic data
4. **Outperformance** - Beats SAM and Materialistic on scattered/soft shapes
5. **Resources** - 300K+ textures and PBR materials shared

The key insight: **simple image properties often correlate with material states in real images. By extracting these patterns and using them to generate synthetic training data, we can train networks that generalize to real-world material states without manual annotation.**

---

**Citation:**
```
@article{eppel2024matseg,
  title={Learning Zero-Shot Material States Segmentation},
  author={Eppel, Sagi and Li, Jolina Yining and Drehwald, Manuel S and Aspuru-Guzik, Alan},
  journal={NeurIPS 2024},
  year={2024}
}
```

---

*Document synthesized for Hydrogen research collection*
*Source: arXiv:2403.03309v6*
