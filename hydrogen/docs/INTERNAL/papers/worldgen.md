━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                              // worldgen // paper
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

**Title**: WorldGen: From Text to Traversable and Interactive 3D Worlds
**Authors**: Dilin Wang et al. (Reality Labs, Meta)
**Date**: November 24, 2025
**arXiv**: 2511.16825v1 [cs.CV]
**Source PDF**: world-gen-from-text.pdf

────────────────────────────────────────────────────────────────────────────────
                                                                     // abstract
────────────────────────────────────────────────────────────────────────────────

## Summary

WorldGen enables automatic creation of large-scale, interactive 3D worlds from
text prompts. Outputs are traversable, fully textured environments compatible
with standard game engines (Unreal, Unity).

**Key Innovation**: Combines LLM-driven scene layout reasoning, procedural
generation, diffusion-based 3D generation, and object-aware scene decomposition.

**Output Format**: Compositional textured meshes with navigation mesh (navmesh).

────────────────────────────────────────────────────────────────────────────────
                                                                    // pipeline
────────────────────────────────────────────────────────────────────────────────

## Four-Stage Pipeline

```
Text Prompt y
     │
     ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│ STAGE I: Scene Planning                                                     │
│   • LLM parses prompt → JSON parameters                                     │
│   • Procedural generator creates blockout B                                 │
│   • Extract navmesh S from blockout                                         │
│   • Depth-conditioned image generator → reference image R                   │
│   Output: L = (B, R, S)                                                     │
└─────────────────────────────────────────────────────────────────────────────┘
     │
     ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│ STAGE II: Scene Reconstruction                                              │
│   • AssetGen2 (image-to-3D) conditioned on R and S                          │
│   • VecSet latent diffusion for SDF generation                              │
│   • Navmesh encoder provides spatial constraints                            │
│   • TRELLIS volumetric texture generation                                   │
│   Output: Holistic textured mesh M                                          │
└─────────────────────────────────────────────────────────────────────────────┘
     │
     ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│ STAGE III: Scene Decomposition                                              │
│   • AutoPartGen extracts parts autoregressively                             │
│   • Accelerated via connectivity-degree ordering (PartPacker)               │
│   • Ground/terrain extracted first as pivot                                 │
│   • Connected-component analysis for remaining geometry                     │
│   Output: Xˆ = {(xˆᵢ, gᵢ)}ᴺᵢ₌₁ (low-res parts with poses)                   │
└─────────────────────────────────────────────────────────────────────────────┘
     │
     ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│ STAGE IV: Scene Enhancement                                                 │
│   • Per-object image enhancement via LLM-VLM                                │
│   • Mesh refinement model (conditioned on coarse geometry + enhanced image) │
│   • Multi-view texture generation with disentangled attention               │
│   Output: X = ({(xᵢ, gᵢ)}ᴺᵢ₌₁, S) (high-res scene)                          │
└─────────────────────────────────────────────────────────────────────────────┘
```

────────────────────────────────────────────────────────────────────────────────
                                                         // stage-i // planning
────────────────────────────────────────────────────────────────────────────────

## Stage I: Scene Planning

### Procedural Blockout Generation

LLM maps text prompt to structured JSON parameters:
- terrain type ("flat", "steep")
- surface roughness
- elevation range
- object density
- verticality
- placement regularity

**Three-step procedural pipeline:**

1. **Terrain Generation**
   - Perlin noise or rule-based heightmap
   - Configured by JSON specification

2. **Spatial Partitioning**
   - Structured environments: BSP, uniform grids, k-d trees
   - Natural/irregular: Voronoi diagrams, noise partitions, Drunkard's Walk

3. **Hierarchical Asset Placement**
   - Pass 1: Hero assets (major landmarks/buildings)
   - Pass 2: Medium-scale (trees, walls, bridges)
   - Pass 3: Small decorative assets
   - Final: Terrain smoothing to prevent collisions

### Navmesh Extraction

Uses **Recast** algorithm on blockout geometry B.
Identifies exterior traversable surfaces, excludes indoor areas.

### Reference Image Generation

- Render blockout B as isometric depth map (45° elevation)
- Apply Gaussian perturbation to non-terrain depth values
- Feed to depth-conditioned image generator

────────────────────────────────────────────────────────────────────────────────
                                                   // stage-ii // reconstruction
────────────────────────────────────────────────────────────────────────────────

## Stage II: Scene Reconstruction

### AssetGen2 Base Model

**VecSet Latent Representation:**
- 3D object encoded as unordered set of K latent vectors z ∈ R^(K×D)
- Encoder: FPS downsampling → cross-attention → transformer layers
- Decoder: Query point q → SDF value D(q | z)
- Mesh extraction via Marching Cubes

**Image-to-3D Diffusion:**
- Denoising diffusion transformer Φ
- Samples p(z | I; Φ) conditioned on input image
- Produces SDF latent → watertight triangular mesh

### Navmesh Conditioning

Extended AssetGen2 to sample p(z | R, S; Φ):

**Navmesh Encoder:**
1. Uniform random sampling from navmesh surface → point cloud P
2. FPS downsample to Pˆ ∈ R^(K×3)
3. Coordinate positional encoding → D-dimensional features
4. Cross-attention: sparse points attend to dense points
5. Positional encoding reinforced in output

**Integration:** Navmesh embeddings added via cross-attention layers in diffusion transformer.

**Training:** End-to-end fine-tuning (not just new cross-attention layers).

**Data Normalization:**
- All meshes rescaled to [-1, 1]³ cube
- Navmesh ground plane centered at (0, 0, 0)

### Scene Texture Generation

Uses **TRELLIS** volumetric texture generator:
- Generates texture in 3D directly (handles self-occlusions)
- Retrained on internal object + scene dataset
- Lower resolution but complete coverage

────────────────────────────────────────────────────────────────────────────────
                                                  // stage-iii // decomposition
────────────────────────────────────────────────────────────────────────────────

## Stage III: Scene Decomposition

### AutoPartGen (Modified)

Original: Autoregressive part extraction in lexicographical z-x-y order.

**Problem:** Slow for complex scenes with many parts.

### Acceleration via Connectivity-Degree Ordering

Inspired by **PartPacker**:
- Generate parts by decreasing connectivity degree
- High-connectivity parts (e.g., ground) are "pivots"
- Once pivots extracted, remaining parts via connected-component analysis

**Five-step schedule:**
1. Generate 4 pivot parts autoregressively
2. Generate "remainder" part (all remaining geometry)
3. Decompose remainder via connected-component analysis

**Result:** 10 minutes → 1 minute inference time.

### Scene Decomposition Data

No existing dataset of 3D scenes with part annotations.

**Data creation pipeline:**
1. Mine scene-like assets from internal repository using VLM
2. Connectivity-based part splitting + vertex welding
3. Ground detection and thin overlay merging
4. De-duplicate and merge small parts to neighbors
5. Filter by part count, imbalance, ground confidence

────────────────────────────────────────────────────────────────────────────────
                                                    // stage-iv // enhancement
────────────────────────────────────────────────────────────────────────────────

## Stage IV: Scene Enhancement

### Per-Object Image Enhancement

**Input to LLM-VLM:**
1. Global reference image R
2. Top-down view of scene M with target object highlighted in red
3. Coarse render Îᵢ of object xˆᵢ

**Output:** High-resolution detailed image Iᵢ

**Verification:** IoU check between enhanced and coarse renders.
Iterative refinement if IoU below threshold.

### Per-Object Mesh Enhancement

**Architecture:** Extended AssetGen2 with coarse shape conditioning.

**Process:**
1. Encode coarse mesh via VAE → latent zˆᵢ
2. Add positional embeddings + zero-initialized projection
3. Concatenate with noise latent along sequence dimension
4. Diffusion denoising
5. Discard zˆᵢ, output refined mesh xᵢ

**Training Data Curation:**
- Create synthetic "scenes" by arranging objects in 2×2 and 3×3 grids
- Feed to AssetGen2 to simulate degradation
- Extract degraded objects by grid location
- Augment with floaters, masked regions, broken surfaces

### Per-Object Texture Enhancement

**Multi-View Generation:**
- 10 orthographic views: 8 side views (45° spacing) + top + bottom
- Sequential generation: frontal → side → top/bottom

**Disentangled Multi-View Attention:**
1. **In-plane self-attention:** Each view attends to own features
2. **Reference attention:** Generated views cross-attend to reference (view 0)
3. **Multi-view attention:** Generated views attend to each other

**Delighting:** Diffusion model removes baked lighting from conditioning image.

**Texture Post-processing:** UV back-projection + inpainting for gaps.

────────────────────────────────────────────────────────────────────────────────
                                                        // key // architectures
────────────────────────────────────────────────────────────────────────────────

## Key Model Architectures

### VecSet (3D Latent Representation)

```
Point Cloud P = {(pᵢ, nᵢ)}ᴹᵢ₌₁
        │
        ▼ FPS(K)
Sparse Points Pˆ = {pˆ₁, ..., pˆₖ}
        │
        ▼ Sinusoidal Encoding + Cross-Attention + Transformer
Latent Code z ∈ R^(K×D)
        │
        ▼ Query Decoder
SDF Value D(q | z) for any point q ∈ R³
```

### Navmesh Encoder

```
Navmesh S
    │
    ▼ Uniform Random Sampling
Point Cloud P ∈ R^(M×3)
    │
    ▼ FPS(K)
Sparse Points Pˆ ∈ R^(K×3)
    │
    ▼ Coordinate Positional Encoding
Features ∈ R^(K×D)
    │
    ▼ Cross-Attention (sparse attend to dense)
    │
    + Positional Encoding (reinforced)
    │
    ▼
Navmesh Embeddings E'(S)
```

### Mesh Refinement Model

```
Coarse Mesh xˆᵢ ──► VAE Encoder ──► zˆᵢ
                                      │
                    ┌─────────────────┘
                    │ + Positional Embeddings
                    │ + Zero-init Linear Projection
                    ▼
              [zˆᵢ || Noise Latent xₜ]  (concatenate along sequence)
                    │
                    ▼
           Diffusion Transformer (+ image cross-attention)
                    │
                    ▼
              Refined Latent z
                    │
                    ▼ VAE Decoder
              Refined Mesh xᵢ
```

────────────────────────────────────────────────────────────────────────────────
                                                               // quantitative
────────────────────────────────────────────────────────────────────────────────

## Quantitative Results

### Navmesh Alignment (Chamfer Distance, lower = better)

| Model                    | NavMesh CD |
|--------------------------|------------|
| Top Image-to-3D Model A  | 0.038      |
| Baseline AssetGen2       | 0.042      |
| Baseline* (scene-tuned)  | 0.038      |
| **WorldGen (Ours)**      | **0.022**  |

**40-50% improvement** over baselines.

### Scene Decomposition (50 synthetic scenes)

| Model               | Chamfer | F@0.01 | F@0.02 | F@0.03 | F@0.05 | Time   |
|---------------------|---------|--------|--------|--------|--------|--------|
| Top PartGen Model A | 0.171   | 0.090  | 0.215  | 0.307  | 0.443  | 1 min  |
| Top PartGen Model B | 0.136   | 0.155  | 0.357  | 0.481  | 0.633  | 3 min  |
| AutoPartGen         | 0.144   | 0.281  | 0.526  | 0.613  | 0.683  | 10 min |
| **Ours**            | **0.061** | **0.322** | **0.644** | **0.761** | **0.853** | **1 min** |

────────────────────────────────────────────────────────────────────────────────
                                                                 // limitations
────────────────────────────────────────────────────────────────────────────────

## Limitations

1. **Single reference view** — limits scene scale (~50×50m currently)
2. **No multi-floor/interior-exterior** — can't model dungeons, seamless transitions
3. **No geometry/texture reuse** — each object independent, rendering overhead
4. **Region stitching artifacts** — for larger scenes requiring multiple passes

────────────────────────────────────────────────────────────────────────────────
                                                      // implementation // notes
────────────────────────────────────────────────────────────────────────────────

## Implementation Notes for Hydrogen

### Relevant Components

1. **Procedural Generation (Stage I)**
   - Perlin noise terrain: `Hydrogen.Schema.Geometry.Noise`
   - BSP/Voronoi partitioning: `Hydrogen.Schema.Geometry.Partition`
   - JSON schema for LLM output: `Hydrogen.Schema.WorldGen.Layout`

2. **Navmesh Representation**
   - Triangle mesh with walkability metadata
   - Recast algorithm binding (FFI to C++ library)
   - `Hydrogen.Schema.Spatial.Navmesh`

3. **Scene Graph**
   - Compositional scene: `Hydrogen.Schema.Spatial.SceneGraph`
   - Object poses SE(3): `Hydrogen.Schema.Geometry.Transform3D`

4. **VecSet Latent Space**
   - Point cloud representation: `Hydrogen.Schema.Geometry.PointCloud`
   - SDF queries: `Hydrogen.Schema.Geometry.SDF`

### Dependencies

- **Recast Navigation** — navmesh generation
- **Marching Cubes** — mesh extraction from SDF
- **DINO** — image feature extraction for conditioning

────────────────────────────────────────────────────────────────────────────────
                                                                  // references
────────────────────────────────────────────────────────────────────────────────

## Full Attribution

### This Paper

**WorldGen: From Text to Traversable and Interactive 3D Worlds**

Dilin Wang, Hyunyoung Jung, Tom Monnier, Kihyuk Sohn, Chuhang Zou, Xiaoyu Xiang,
Yu-Ying Yeh, Di Liu, Zixuan Huang, Thu Nguyen-Phuoc, Yuchen Fan, Sergiu Oprea,
Ziyan Wang, Roman Shapovalov, Nikolaos Sarafianos, Thibault Groueix, Antoine Toisoul,
Prithviraj Dhar, Xiao Chu, Minghao Chen, Geon Yeong Park, Mahima Gupta, Yassir Azziz,
Rakesh Ranjan, Andrea Vedaldi

Reality Labs, Meta
arXiv:2511.16825v1 [cs.CV], November 2025

### Key Dependencies Cited

**AssetGen2**
Rakesh Ranjan, Andrea Vedaldi, Mahima Gupta, Christopher Ocampo, Ocean Quigley.
"Introducing Meta 3D AssetGen 2.0: A New Foundation Model for 3D Content Creation."
Meta Developers Blog, 2025.

**AutoPartGen**
Minghao Chen, Jianyuan Wang, Roman Shapovalov, Tom Monnier, Hyunyoung Jung,
Dilin Wang, Rakesh Ranjan, Iro Laina, Andrea Vedaldi.
"AutoPartGen: Autoregressive 3D Part Generation and Discovery."
NeurIPS 2025.

**PartPacker**
Jiaxiang Tang, Ruijie Lu, Zhaoshuo Li, Zekun Hao, Xuan Li, Fangyin Wei, Shuran Song,
Gang Zeng, Ming-Yu Liu, Tsung-Yi Lin.
"Efficient Part-Level 3D Object Generation via Dual Volume Packing."
arXiv:2506.09980, 2025.

**TRELLIS**
Jianfeng Xiang, Zelong Lv, Sicheng Xu, Yu Deng, Ruicheng Wang, Bowen Zhang,
Dong Chen, Xin Tong, Jiaolong Yang.
"Structured 3D Latents for Scalable and Versatile 3D Generation."
CVPR 2025.

**VecSet (3DShape2VecSet)**
Biao Zhang, Jiapeng Tang, Matthias Niessner, Peter Wonka.
"3DShape2VecSet: A 3D Shape Representation for Neural Fields and Generative
Diffusion Models."
ACM Transactions on Graphics (TOG), 2023.

**Recast Navigation**
Mikko Mononen and contributors.
"Recast Navigation." https://github.com/recastnavigation/recastnavigation
2016-2026. State-of-the-art navmesh generation for games.

**Perlin Noise**
Ken Perlin.
"An Image Synthesizer."
ACM SIGGRAPH Computer Graphics, 19(3):287-296, 1985.

**Marching Cubes**
William E. Lorensen, Harvey E. Cline.
"Marching Cubes: A High Resolution 3D Surface Construction Algorithm."
ACM Computer Graphics, 21(24), 1987.

**DUSt3R / MASt3R**
Shuzhe Wang, Vincent Leroy, Yohann Cabon, Boris Chidlovskii, Jerome Revaud.
"DUSt3R: Geometric 3D Vision Made Easy."
CVPR 2024.

**3D Gaussian Splatting**
Bernhard Kerbl, Georgios Kopanas, Thomas Leimkühler, George Drettakis.
"3D Gaussian Splatting for Real-Time Radiance Field Rendering."
SIGGRAPH 2023.

### Acknowledgements (from paper)

Ocean Quigley, Zack Dawson, Alexander Dawson, Vladimir Mironov, Kam Zambel,
Vu Ha, Yoav Goldstein, Dhwaj Agrawal, Scott Nagy, Stephen Madsen, John Niehuss,
Chin Fong, Christopher Ocampo, Milton Cadogan, Sandy Kao, Ryan Cameron,
Barrett Meeker.

────────────────────────────────────────────────────────────────────────────────

                                                         — extracted 2026-02-26
