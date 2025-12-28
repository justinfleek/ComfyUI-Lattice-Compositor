# LATTICE COMPOSITOR - DEPENDENCY GRAPH
Understanding what depends on what

---

## WHY THIS MATTERS

If you fix a bug in Layer System, you might break Text Animators.
If Keyframe System is broken, ALL animation is broken.
Audit upstream before downstream.

---

## FOUNDATION DEPENDENCIES
````
┌─────────────────────────────────────────────────────────────────┐
│                        FOUNDATION                                │
│  (Everything depends on these - audit FIRST)                    │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌──────────────┐    ┌──────────────┐    ┌──────────────┐       │
│  │ Layer System │───▶│ Render Loop  │───▶│ Export       │       │
│  └──────────────┘    └──────────────┘    └──────────────┘       │
│         │                   │                                    │
│         ▼                   ▼                                    │
│  ┌──────────────┐    ┌──────────────┐                           │
│  │ Keyframes    │───▶│ Interpolation│                           │
│  └──────────────┘    └──────────────┘                           │
│         │                                                        │
│         ▼                                                        │
│  ┌──────────────┐                                               │
│  │ Expressions  │                                               │
│  └──────────────┘                                               │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
````

**Audit Order:** Layer System → Keyframes → Interpolation → Expressions → Render Loop → Export

---

## LAYER TYPE DEPENDENCIES
````
BaseLayer (MUST BE CORRECT)
    │
    ├── SolidLayer
    ├── ImageLayer
    ├── VideoLayer
    ├── TextLayer ────────────▶ Text Animators
    │                          Text on Path
    │
    ├── ShapeLayer ───────────▶ Shape Modifiers
    │                          Path Booleans
    │                          Path Morphing
    │
    ├── AudioLayer ───────────▶ Audio Analysis
    │                          Beat Detection
    │                          Property Mapping
    │
    ├── CameraLayer ──────────▶ DOF
    │                          Two-Node
    │                          Camera Tracking
    │
    ├── LightLayer
    ├── ControlLayer
    ├── GroupLayer
    ├── NestedCompLayer
    │
    ├── ParticleLayer ────────▶ Particle System (12 subsystems)
    │
    ├── PathLayer
    ├── SplineLayer
    │
    ├── ModelLayer ───────────▶ GLTF Loader
    ├── PointCloudLayer
    │
    ├── DepthLayer
    ├── DepthflowLayer
    ├── NormalLayer
    ├── PoseLayer
    │
    └── GeneratedLayer
````

**Key Insight:** If BaseLayer.ts has a bug, ALL 24 layer types are affected.

---

## ANIMATION DEPENDENCIES
````
Keyframe System
    │
    ├── Interpolation Engine (45 easings)
    │       │
    │       └── Bezier Math
    │
    ├── Expression System
    │       │
    │       ├── Motion Expressions (wiggle, bounce)
    │       ├── Loop Expressions (cycle, pingPong)
    │       ├── Audio Expressions
    │       └── Text Animator Expressions
    │
    ├── Roving Keyframes
    │
    └── Time Warp/Remapping
````

---

## PARTICLE SYSTEM DEPENDENCIES
````
GPUParticleSystem (Core)
    │
    ├── ParticleEmitterLogic
    │       │
    │       └── ParticleSubEmitter
    │
    ├── ParticleForceCalculator
    │
    ├── SpatialHashGrid
    │       │
    │       ├── ParticleCollisionSystem
    │       └── ParticleConnectionSystem
    │
    ├── ParticleFlockingSystem
    │
    ├── ParticleTrailSystem
    │
    ├── ParticleTextureSystem
    │
    ├── ParticleModulationCurves
    │
    ├── ParticleFrameCache (Determinism)
    │
    └── ParticleAudioReactive ──▶ Audio System
````

**Key Insight:** GPUParticleSystem must work before testing any particle feature.

---

## EFFECTS DEPENDENCIES
````
Effect System Core
    │
    ├── Effect Registration
    ├── Effect Application (addEffectToLayer)
    ├── Effect Ordering
    │
    └── Individual Effects (102)
            │
            ├── TypeScript Effects (77)
            │       │
            │       └── Shader Compilation
            │
            └── GLSL Effects (25)
                    │
                    └── GLSLEngine
````

---

## AUDIO DEPENDENCIES
````
Audio Loading
    │
    ├── FFT Analysis
    │       │
    │       ├── Beat Detection
    │       └── Stem Separation
    │
    ├── Property Mapping
    │       │
    │       └── Audio Expressions
    │
    ├── MIDI Import
    │
    └── Waveform Display
````

---

## 3D SYSTEM DEPENDENCIES
````
Three.js Scene
    │
    ├── CameraLayer
    │       │
    │       ├── DOF System
    │       ├── Two-Node Camera
    │       └── Camera Tracking
    │
    ├── LightLayer
    │
    ├── 3D Layer Mode (BaseLayer)
    │
    ├── ModelLayer
    │       │
    │       └── GLTF/GLB Loader
    │
    └── PointCloudLayer
            │
            └── PLY/PCD Loader
````

---

## EXPORT DEPENDENCIES
````
Export Pipeline
    │
    ├── Frame Sequence Exporter
    │       │
    │       └── Render Loop (must be correct)
    │
    ├── Video Encoder
    │       │
    │       └── Frame Sequences
    │
    ├── Depth Renderer
    │       │
    │       └── Depth Estimation
    │
    ├── Camera Export
    │       │
    │       └── Camera System
    │
    ├── Pose Export
    │       │
    │       └── Pose System
    │
    └── ComfyUI Export
            │
            └── All Systems
````

---

## AUDIT ORDER RECOMMENDATION

Based on dependencies, audit in this order:

### Week 1: Foundation
1. Layer System (1.1, 1.2)
2. Keyframe System (1.3, 1.4)
3. Expression System (1.5)
4. Render Loop (1.6)
5. Save/Load (1.7)

### Week 2: Core Layer Types
6. SolidLayer (2.1)
7. ImageLayer (2.2)
8. VideoLayer (2.3)
9. TextLayer + Text Animators (2.4, 3.1, 3.2)
10. ShapeLayer + Modifiers (2.5, 3.3, 3.4, 3.5)

### Week 3: Advanced Features
11. AudioLayer + Audio System (2.6, 6.x)
12. CameraLayer + 3D (2.7, 7.x)
13. ParticleLayer + System (2.13, 5.x)
14. Effects System (4.x)

### Week 4: Export & Polish
15. Export System (10.x)
16. Layer Styles (9.x)
17. AI Integrations (11.x)
18. Templates (12.x)
19. Remaining Layer Types (2.8-2.23)

---

## CASCADING RISK

If these break, everything downstream breaks:

| Component | Risk Level | Downstream Impact |
|-----------|------------|-------------------|
| BaseLayer.ts | 🔴 CRITICAL | All 24 layer types |
| KeyframeEvaluator.ts | 🔴 CRITICAL | All animation |
| LatticeEngine.ts | 🔴 CRITICAL | All rendering |
| interpolation.ts | 🟠 HIGH | All easing/tweening |
| expressions/index.ts | 🟠 HIGH | All expressions |
| GPUParticleSystem.ts | 🟡 MEDIUM | All particle features |
| exportPipeline.ts | 🟡 MEDIUM | All exports |