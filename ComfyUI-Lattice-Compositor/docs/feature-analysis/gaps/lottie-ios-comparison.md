# Lottie iOS vs Lattice: Feature Comparison

**Analysis Date:** 2026-01-26
**Verdict:** Lattice has complete parity + extensive additional capabilities

---

## Executive Summary

Lottie iOS is a **playback-only** engine for After Effects animations exported via bodymovin. Lattice is a **full motion graphics system** with authoring, generation, and advanced simulation capabilities.

**Result:** No features to back-port. Lattice should implement Lottie JSON import/export for interoperability.

---

## Feature Parity Table

### Layer Types

| Feature | Lottie | Lattice | Status |
|---------|--------|---------|--------|
| Pre-composition (nested) | Yes | Yes | PARITY |
| Solid color | Yes | Yes | PARITY |
| Image | Yes | Yes | PARITY |
| Null/Control | Yes | Yes | PARITY |
| Shape (vector) | Yes | Yes | PARITY |
| Text | Yes | Yes | PARITY |
| **Particle** | No | Yes | LATTICE+ |
| **3D Model** | No | Yes | LATTICE+ |
| **Audio** | No | Yes | LATTICE+ |
| **Depth** | No | Yes | LATTICE+ |
| **Generated (AI)** | No | Yes | LATTICE+ |

### Shape Items

| Feature | Lottie | Lattice | Status |
|---------|--------|---------|--------|
| Ellipse | Yes | Yes | PARITY |
| Rectangle | Yes | Yes | PARITY |
| Star/Polygon | Yes | Yes | PARITY |
| Path (bezier) | Yes | Yes | PARITY |
| Fill | Yes | Yes | PARITY |
| Stroke | Yes | Yes | PARITY |
| Gradient fill | Yes | Yes | PARITY |
| Gradient stroke | Yes | Yes | PARITY |
| Group | Yes | Yes | PARITY |
| Merge paths | Yes | Yes | PARITY |
| Trim paths | Yes | Yes | PARITY |
| Repeater | Yes | Yes | PARITY |
| Rounded corners | Yes | Yes | PARITY |
| **Offset paths** | No | Yes | LATTICE+ |
| **Pucker/Bloat** | No | Yes | LATTICE+ |
| **Wiggle paths** | No | Yes | LATTICE+ |
| **Zig-zag** | No | Yes | LATTICE+ |
| **Twist** | No | Yes | LATTICE+ |

### Transform

| Feature | Lottie | Lattice | Status |
|---------|--------|---------|--------|
| Position | Yes | Yes | PARITY |
| Scale | Yes | Yes | PARITY |
| Rotation | Yes | Yes | PARITY |
| Anchor point | Yes | Yes | PARITY |
| Opacity | Yes | Yes | PARITY |
| Skew | Yes | Yes | PARITY |
| 3D rotation (X/Y/Z) | Yes | Yes | PARITY |

### Text Animation

| Feature | Lottie | Lattice | Status |
|---------|--------|---------|--------|
| Text content | Yes | Yes | PARITY |
| Font styling | Yes | Yes | PARITY |
| Per-character animation | Yes | Yes | PARITY |
| Range selector | Yes | Yes | PARITY |
| **Wiggly selector** | No | Yes | LATTICE+ |
| **Expression selector** | No | Yes | LATTICE+ |
| Path text | Yes | Yes | PARITY |

### Keyframes

| Feature | Lottie | Lattice | Status |
|---------|--------|---------|--------|
| Linear | Yes | Yes | PARITY |
| Bezier/eased | Yes | Yes | PARITY |
| Hold | Yes | Yes | PARITY |
| Spatial bezier | Yes | Yes | PARITY |
| **Spring physics** | No | Planned | LATTICE+ |

### Effects

| Feature | Lottie | Lattice | Status |
|---------|--------|---------|--------|
| Drop shadow | Yes | Yes | PARITY |
| **Blur (5 types)** | No | Yes | LATTICE+ |
| **Distortion (8 types)** | No | Yes | LATTICE+ |
| **Stylize (12 types)** | No | Yes | LATTICE+ |
| **Color correction** | No | Yes | LATTICE+ |
| **Generate (noise, etc.)** | No | Yes | LATTICE+ |
| **Time effects** | No | Yes | LATTICE+ |

---

## Lattice-Exclusive Capabilities

These features exist in Lattice but have **no equivalent** in Lottie:

### Particle System
- 2D/3D emitters (point, line, box, sphere, mesh surface)
- Force fields (gravity, turbulence, vortex, drag)
- Behaviors (flocking, SPH fluid, springs)
- Audio-reactive particles
- Deterministic frame caching

### Physics Simulation
- Rigid body dynamics
- Soft body simulation
- Cloth simulation
- Collision detection

### 3D Rendering
- GLTF/OBJ model import
- Point cloud rendering
- PBR materials
- Camera depth of field
- Ray-traced shadows

### Expression System
- Safe DSL (not JavaScript)
- Property drivers
- Audio-reactive expressions
- Inter-property linking

### Generative AI Integration
- Image generation (FLUX, Stable Diffusion)
- Video generation (Wan 2.1, LTX)
- Depth estimation
- Pose detection
- Layer decomposition

### Mesh Warp
- Pin-based deformation (puppet tool)
- Weighted influence
- Bend/rotation pins
- Path morphing

### Audio
- Waveform visualization
- Frequency band extraction
- Beat detection
- Audio-reactive properties

### Camera Tracking
- Import tracking data
- 3D camera reconstruction
- Point tracking

### Depth Flow
- 2.5D depth-based parallax
- Depth-aware composition
- Depth-based blur

---

## Integration Recommendations

### 1. Lottie JSON Import (HIGH PRIORITY)

Allow Lattice to open Lottie JSON files:
- Parse bodymovin format
- Map to Lattice layer model
- Full fidelity for supported features

**Benefits:**
- Import from LottieFiles marketplace
- Import from After Effects
- Use existing animations

### 2. Lottie JSON Export (HIGH PRIORITY)

Allow Lattice to export to Lottie format:
- Export compositions to JSON
- Feature subset (Lottie-compatible only)
- Clear warnings for unsupported features

**Benefits:**
- Use animations in web/mobile apps
- Share on LottieFiles
- Integrate with Lottie ecosystem

### 3. Feature Degradation Handling

When exporting to Lottie:
- Particles: Bake to shape sequences
- Expressions: Pre-evaluate keyframes
- 3D: Flatten to 2D
- Effects: Apply and rasterize

---

## Conclusion

**Lottie iOS provides no features that Lattice lacks.**

The value of analyzing Lottie is in **interoperability**, not feature extraction. Implementing Lottie import/export makes Lattice compatible with the broader animation ecosystem.

Lattice should be positioned as:
- A **superset** of Lottie capabilities
- A **professional** motion graphics tool
- An **AI-native** animation platform
