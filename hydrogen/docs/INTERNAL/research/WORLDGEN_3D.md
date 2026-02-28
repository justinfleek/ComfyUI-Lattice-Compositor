# WorldGen: From Text to Traversable and Interactive 3D Worlds

**arXiv:** 2511.16825  
**Authors:** Dilin Wang, Hyunyoung Jung, Tom Monnier, Kihyuk Sohn, et al. (Meta Reality Labs)  
**Status:** IN_PROGRESS

---

## 1. Abstract

WorldGen enables automatic creation of large-scale, interactive 3D worlds directly from text prompts. Pipeline combines:
- LLM-driven scene layout reasoning
- Procedural generation
- Diffusion-based 3D generation
- Object-aware scene decomposition

Output: Traversable, fully textured environments for game engines.

---

## 2. Architecture

### 2.1 Four-Stage Pipeline

```
Text Prompt
     │
     ▼
┌──────────────────────────────────────────────────┐
│ Stage I: Scene Planning                            │
│  • LLM interprets prompt                          │
│  • Procedural blockout generation               │
│  • Navmesh extraction                           │
│  • Reference image generation                  │
└──────────────────────────────────────────────────┘
     │
     ▼
┌──────────────────────────────────────────────────┐
│ Stage II: Scene Reconstruction                   │
│  • Image-to-3D base model                     │
│  • Navmesh-based scene generation             │
│  • Scene texture generation                    │
└──────────────────────────────────────────────────┘
     │
     ▼
┌──────────────────────────────────────────────────┐
│ Stage III: Scene Decomposition                  │
│  • AutoPartGen for scenes                     │
│  • Object decomposition                       │
└──────────────────────────────────────────────────┘
     │
     ▼
┌──────────────────────────────────────────────────┐
│ Stage IV: Scene Enhancement                     │
│  • Per-object image enhancement               │
│  • Per-object mesh enhancement                │
│  • Per-object texture enhancement            │
└──────────────────────────────────────────────────┘
     │
     ▼
3D World (Game Engine Compatible)
```

---

## 3. Stage Details

### 3.1 Stage I: Scene Planning

**Procedural Blockout:**
- LLM maps text → procedural parameters
- Generates basic layout (blockout)
- Extracts navigation mesh (navmesh)
- Creates reference image

**Key insight:** PG guarantees functional constraints while image generator provides detail.

### 3.2 Stage II: Reconstruction

- **Image-to-3D:** AssetGen2 (state-of-the-art)
- Navmesh-conditioned reconstruction
- Maintains traversability

### 3.3 Stage III: Decomposition

- AutoPartGen for scene decomposition
- Extracts objects: buildings, trees, etc.
- Handles large number of parts

### 3.4 Stage IV: Enhancement

- Per-object high-res image generation
- Individual mesh/texture regeneration
- Preserves geometric consistency

---

## 4. Key Innovations

### 4.1 Hybrid Generation

| Component | Method | Purpose |
|-----------|--------|---------|
| Layout | Procedural Generation | Functional constraints |
| Details | Diffusion Model | Visual richness |
| Objects | Compositional | Editability |

### 4.2 Traversability Guarantee

- Navmesh extraction ensures walkable regions
- Image generator interprets semantic layout
- Hybrid approach balances flexibility + function

---

## 5. Capabilities

- **Input:** Single text prompt
- **Output:** Full 3D world (mesh + textures)
- **Compatibility:** Standard game engines
- **Control:** Fine-grained layout, scale, style

---

## 6. Key Definitions

1. **Blockout:** Basic 3D layout defining volumes and connectivity
2. **Navmesh:** Navigation mesh for character movement
3. **AssetGen2:** Meta's image-to-3D model
4. **AutoPartGen:** Automated 3D part discovery

---

## 7. Relation to Hydrogen

```purescript
-- World generation
data World3D
  = World3D
      { mesh :: Mesh
      , textures :: Map ObjectId Texture
      , navmesh :: NavMesh
      , objects :: Array SceneObject
      }

-- Generate from prompt
generateWorld ::
  TextPrompt ->
  Config ->
  World3D

-- Interactive exploration
exploreWorld ::
  World3D ->
  PlayerPosition ->
  Viewport
```

---

## 8. Bibliography

1. Wang et al. "WorldGen: From Text to Traversable and Interactive 3D Worlds" Meta 2025

---

*Document generated: 2026-02-26*
