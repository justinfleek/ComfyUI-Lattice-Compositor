# WEYL COMPOSITOR - SYSTEM ARCHITECTURE

**Version:** 1.0.0
**Last Updated:** December 23, 2025
**Purpose:** Complete architectural documentation for developers

---

## TABLE OF CONTENTS

1. [High-Level Overview](#1-high-level-overview)
2. [Data Flow Diagrams](#2-data-flow-diagrams)
3. [Component Architecture](#3-component-architecture)
4. [State Management](#4-state-management)
5. [Render Pipeline](#5-render-pipeline)
6. [Engine Architecture](#6-engine-architecture)
7. [Service Layer](#7-service-layer)
8. [Event Flow](#8-event-flow)
9. [File Structure](#9-file-structure)
10. [Integration Points](#10-integration-points)

---

## 1. HIGH-LEVEL OVERVIEW

### 1.1 System Layers

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                           PRESENTATION LAYER                                 │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────┐ │
│  │   Canvas    │  │   Timeline  │  │   Panels    │  │   Property Editor   │ │
│  │ ThreeCanvas │  │ TimelinePanel│ │ LayerPanel  │  │ TransformProperties │ │
│  │ SplineEditor│  │ LayerTrack  │  │ EffectsPanel│  │ TextProperties      │ │
│  │ MaskEditor  │  │ CurveEditor │  │ AssetsPanel │  │ ParticleProperties  │ │
│  └──────┬──────┘  └──────┬──────┘  └──────┬──────┘  └──────────┬──────────┘ │
│         │                │                │                     │            │
└─────────┼────────────────┼────────────────┼─────────────────────┼────────────┘
          │                │                │                     │
          ▼                ▼                ▼                     ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                            STATE LAYER (Pinia)                               │
│  ┌─────────────────────┐  ┌──────────────┐  ┌────────────┐  ┌────────────┐  │
│  │   compositorStore   │  │ playbackStore│  │ audioStore │  │assetStore  │  │
│  │   (90KB - Main)     │  │  (Timeline)  │  │  (Audio)   │  │ (Assets)   │  │
│  ├─────────────────────┤  └──────────────┘  └────────────┘  └────────────┘  │
│  │ • Project state     │  ┌──────────────┐  ┌────────────┐  ┌────────────┐  │
│  │ • Layer management  │  │selectionStore│  │historyStore│  │  uiStore   │  │
│  │ • Keyframe data     │  │ (Selection)  │  │(Undo/Redo) │  │ (UI state) │  │
│  │ • Composition info  │  └──────────────┘  └────────────┘  └────────────┘  │
│  └──────────┬──────────┘                                                     │
│             │                                                                │
└─────────────┼────────────────────────────────────────────────────────────────┘
              │
              ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                           ENGINE LAYER (Three.js)                            │
│  ┌─────────────────────────────────────────────────────────────────────┐    │
│  │                        WeylEngine.ts (2400+ lines)                   │    │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐  ┌────────────┐  │    │
│  │  │   Scene     │  │  Renderer   │  │   Camera    │  │  Composer  │  │    │
│  │  │  (Graph)    │  │  (WebGL2)   │  │ (Controller)│  │  (Effects) │  │    │
│  │  └─────────────┘  └─────────────┘  └─────────────┘  └────────────┘  │    │
│  └──────────────────────────────────────────────────────────────────────┘    │
│  ┌──────────────────────────────────────────────────────────────────────┐   │
│  │                        Layer Manager                                  │   │
│  │  ┌────────┐ ┌────────┐ ┌────────┐ ┌────────┐ ┌────────┐ ┌────────┐  │   │
│  │  │ Image  │ │ Video  │ │  Text  │ │ Spline │ │Particle│ │ Camera │  │   │
│  │  │ Layer  │ │ Layer  │ │ Layer  │ │ Layer  │ │ Layer  │ │ Layer  │  │   │
│  │  └────────┘ └────────┘ └────────┘ └────────┘ └────────┘ └────────┘  │   │
│  │  ┌────────┐ ┌────────┐ ┌────────┐ ┌────────┐ ┌────────┐ ┌────────┐  │   │
│  │  │ Solid  │ │  Null  │ │ Shape  │ │Precomp │ │Adjust- │ │ Light  │  │   │
│  │  │ Layer  │ │ Layer  │ │ Layer  │ │ Layer  │ │ment    │ │ Layer  │  │   │
│  │  └────────┘ └────────┘ └────────┘ └────────┘ └────────┘ └────────┘  │   │
│  │  ┌────────┐ ┌────────┐ ┌────────┐ ┌────────┐ ┌────────┐             │   │
│  │  │ Model  │ │ Point  │ │Depth-  │ │Proced- │ │ More   │             │   │
│  │  │ Layer  │ │ Cloud  │ │ flow   │ │ural   │ │ ...    │             │   │
│  │  └────────┘ └────────┘ └────────┘ └────────┘ └────────┘             │   │
│  └──────────────────────────────────────────────────────────────────────┘   │
└─────────────────────────────────────────────────────────────────────────────┘
              │
              ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                           SERVICE LAYER (42 Services)                        │
│  ┌──────────────────────┐  ┌──────────────────────┐  ┌────────────────────┐ │
│  │     ANIMATION        │  │       AUDIO          │  │      EFFECTS       │ │
│  │  • interpolation.ts  │  │  • audioFeatures.ts  │  │  • blurRenderer    │ │
│  │  • easing.ts         │  │  • audioReactive.ts  │  │  • colorRenderer   │ │
│  │  • expressions.ts    │  │  • audioPathAnim.ts  │  │  • distortRenderer │ │
│  │  • propertyDriver.ts │  │  • audioWorker.ts    │  │  • generateRenderer│ │
│  └──────────────────────┘  └──────────────────────┘  └────────────────────┘ │
│  ┌──────────────────────┐  ┌──────────────────────┐  ┌────────────────────┐ │
│  │      3D/CAMERA       │  │      PARTICLES       │  │      EXPORT        │ │
│  │  • cameraTrajectory  │  │  • particleSystem    │  │  • matteExporter   │ │
│  │  • cameraEnhance.ts  │  │  • gpuParticleRender │  │  • modelExport     │ │
│  │  • camera3DViz.ts    │  │  • meshParticle.ts   │  │  • cameraExport    │ │
│  │  • math3d.ts         │  │  • spriteSheet.ts    │  │  • projectStorage  │ │
│  └──────────────────────┘  └──────────────────────┘  └────────────────────┘ │
│  ┌──────────────────────┐  ┌──────────────────────┐  ┌────────────────────┐ │
│  │       GEOMETRY       │  │       CACHING        │  │     UTILITIES      │ │
│  │  • arcLength.ts      │  │  • frameCache.ts     │  │  • fontService.ts  │ │
│  │  • textOnPath.ts     │  │  • layerEvalCache.ts │  │  • gpuDetection.ts │ │
│  │  • shapeOperations   │  │  • effectProcessor   │  │  • workerPool.ts   │ │
│  │  • depthflow.ts      │  │                      │  │  • lazyLoader.ts   │ │
│  └──────────────────────┘  └──────────────────────┘  └────────────────────┘ │
└─────────────────────────────────────────────────────────────────────────────┘
              │
              ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                          INTEGRATION LAYER                                   │
│  ┌─────────────────────────────────────────────────────────────────────┐    │
│  │                    ComfyUI Extension                                 │    │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────────────┐  │    │
│  │  │extension.js │  │ Python Nodes│  │       HTTP Routes           │  │    │
│  │  │ (Sidebar)   │  │compositor.py│  │  /weyl/compositor/*         │  │    │
│  │  └─────────────┘  └─────────────┘  └─────────────────────────────┘  │    │
│  └─────────────────────────────────────────────────────────────────────┘    │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 1.2 Technology Stack

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  FRONTEND                                                                    │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────┐ │
│  │  Vue 3.5    │  │  Pinia 2.2  │  │ PrimeVue 4  │  │    TypeScript 5     │ │
│  │  (UI)       │  │  (State)    │  │  (Components)│ │    (Language)       │ │
│  └─────────────┘  └─────────────┘  └─────────────┘  └─────────────────────┘ │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────┐ │
│  │ Three.js    │  │  Vite 5     │  │  Vitest     │  │    Bezier.js        │ │
│  │ r170 (3D)   │  │  (Build)    │  │  (Testing)  │  │    (Curves)         │ │
│  └─────────────┘  └─────────────┘  └─────────────┘  └─────────────────────┘ │
├─────────────────────────────────────────────────────────────────────────────┤
│  BACKEND                                                                     │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────────────────────┐  │
│  │  Python 3   │  │  ComfyUI    │  │    aiohttp (HTTP)                   │  │
│  └─────────────┘  └─────────────┘  └─────────────────────────────────────┘  │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## 2. DATA FLOW DIAGRAMS

### 2.1 Main Render Loop

```
┌──────────────────────────────────────────────────────────────────────────────┐
│                           RENDER LOOP DATA FLOW                              │
└──────────────────────────────────────────────────────────────────────────────┘

     User Input                    State Change                  Render
    ┌─────────┐                   ┌─────────┐                  ┌─────────┐
    │ Scrub   │                   │ Update  │                  │ Request │
    │Timeline │──────────────────▶│ Store   │─────────────────▶│ Frame   │
    │         │                   │         │                  │         │
    └─────────┘                   └─────────┘                  └────┬────┘
                                                                    │
                                                                    ▼
┌──────────────────────────────────────────────────────────────────────────────┐
│                              WEYL ENGINE                                      │
│                                                                               │
│  ┌────────────────────────────────────────────────────────────────────────┐  │
│  │  STEP 1: Property Evaluation                                           │  │
│  │  ┌──────────────┐    ┌──────────────┐    ┌──────────────┐             │  │
│  │  │  Keyframe    │    │ Interpolate  │    │  Apply       │             │  │
│  │  │  Lookup      │───▶│  Values      │───▶│  Expressions │             │  │
│  │  │              │    │  (Bezier)    │    │              │             │  │
│  │  └──────────────┘    └──────────────┘    └──────────────┘             │  │
│  └────────────────────────────────────────────────────────────────────────┘  │
│                                    │                                          │
│                                    ▼                                          │
│  ┌────────────────────────────────────────────────────────────────────────┐  │
│  │  STEP 2: Layer Evaluation                                              │  │
│  │  ┌──────────────┐    ┌──────────────┐    ┌──────────────┐             │  │
│  │  │  Transform   │    │  Content     │    │  Effects     │             │  │
│  │  │  Matrix      │───▶│  Render      │───▶│  Stack       │             │  │
│  │  │              │    │              │    │              │             │  │
│  │  └──────────────┘    └──────────────┘    └──────────────┘             │  │
│  └────────────────────────────────────────────────────────────────────────┘  │
│                                    │                                          │
│                                    ▼                                          │
│  ┌────────────────────────────────────────────────────────────────────────┐  │
│  │  STEP 3: Composition                                                   │  │
│  │  ┌──────────────┐    ┌──────────────┐    ┌──────────────┐             │  │
│  │  │  Z-Sort      │    │  Blend       │    │  Post        │             │  │
│  │  │  Layers      │───▶│  Modes       │───▶│  Process     │             │  │
│  │  │              │    │              │    │              │             │  │
│  │  └──────────────┘    └──────────────┘    └──────────────┘             │  │
│  └────────────────────────────────────────────────────────────────────────┘  │
│                                    │                                          │
│                                    ▼                                          │
│  ┌────────────────────────────────────────────────────────────────────────┐  │
│  │  STEP 4: Output                                                        │  │
│  │  ┌──────────────┐    ┌──────────────┐    ┌──────────────┐             │  │
│  │  │  Frame       │    │  Cache       │    │  Display     │             │  │
│  │  │  Buffer      │───▶│  Store       │───▶│  Canvas      │             │  │
│  │  │              │    │              │    │              │             │  │
│  │  └──────────────┘    └──────────────┘    └──────────────┘             │  │
│  └────────────────────────────────────────────────────────────────────────┘  │
│                                                                               │
└──────────────────────────────────────────────────────────────────────────────┘
```

### 2.2 Keyframe Animation Flow

```
┌──────────────────────────────────────────────────────────────────────────────┐
│                        KEYFRAME EVALUATION FLOW                              │
└──────────────────────────────────────────────────────────────────────────────┘

  Frame N Request
       │
       ▼
  ┌─────────────────────┐
  │ Find Surrounding    │
  │ Keyframes           │
  │ (prev, next)        │
  └──────────┬──────────┘
             │
             ▼
  ┌─────────────────────┐      ┌─────────────────────┐
  │ Calculate Local T   │      │ Check if cached     │
  │ t = (frame - prev)  │─────▶│ in layerEvalCache   │
  │ / (next - prev)     │      │                     │
  └──────────┬──────────┘      └──────────┬──────────┘
             │                            │
             │ (cache miss)               │ (cache hit)
             ▼                            │
  ┌─────────────────────┐                 │
  │ Get Interpolation   │                 │
  │ Type                │                 │
  │ linear/bezier/hold  │                 │
  └──────────┬──────────┘                 │
             │                            │
             ▼                            │
  ┌─────────────────────────────────────┐ │
  │     INTERPOLATION TYPE              │ │
  ├─────────────────────────────────────┤ │
  │                                     │ │
  │  LINEAR:                            │ │
  │  value = lerp(prev.value,           │ │
  │               next.value, t)        │ │
  │                                     │ │
  │  BEZIER:                            │ │
  │  1. Get ease handles (in/out)       │ │
  │  2. Build cubic bezier curve        │ │
  │  3. Sample curve at t               │ │
  │  4. Map to value range              │ │
  │                                     │ │
  │  HOLD:                              │ │
  │  value = prev.value (no interp)     │ │
  │                                     │ │
  └──────────┬──────────────────────────┘ │
             │                            │
             ▼                            ▼
  ┌─────────────────────────────────────────┐
  │           EVALUATED VALUE               │
  │  Store in cache, return to engine       │
  └─────────────────────────────────────────┘
```

### 2.3 Particle System Flow

```
┌──────────────────────────────────────────────────────────────────────────────┐
│                       PARTICLE EVALUATION FLOW                               │
└──────────────────────────────────────────────────────────────────────────────┘

  Frame N Request
       │
       ▼
  ┌─────────────────────┐
  │ Check Frame Cache   │
  │ (every 30 frames)   │
  └──────────┬──────────┘
             │
     ┌───────┴───────┐
     │               │
     ▼               ▼
  (cache hit)    (cache miss)
     │               │
     │               ▼
     │     ┌─────────────────────┐
     │     │ Find Nearest        │
     │     │ Checkpoint          │
     │     │ (frame ÷ 30) × 30   │
     │     └──────────┬──────────┘
     │                │
     │                ▼
     │     ┌─────────────────────┐
     │     │ Initialize RNG      │
     │     │ Mulberry32(seed)    │◀── Deterministic!
     │     └──────────┬──────────┘
     │                │
     │                ▼
     │     ┌─────────────────────┐
     │     │ Simulate Frames     │
     │     │ checkpoint → target │
     │     └──────────┬──────────┘
     │                │
     │                ▼
     │     ┌─────────────────────────────────────────────┐
     │     │  FOR EACH SIMULATION STEP:                  │
     │     │                                             │
     │     │  1. Emit new particles (based on rate)      │
     │     │  2. Apply forces:                           │
     │     │     • Gravity (vec3)                        │
     │     │     • Wind (vec3 + turbulence)              │
     │     │     • Vortex (position, strength)           │
     │     │     • Turbulence (simplex noise)            │
     │     │  3. Update positions (physics integration)  │
     │     │  4. Check collisions                        │
     │     │  5. Update lifetime, kill dead particles    │
     │     │  6. Update visual properties (color, size)  │
     │     │                                             │
     │     └──────────┬──────────────────────────────────┘
     │                │
     │                ▼
     │     ┌─────────────────────┐
     │     │ Store Checkpoint    │
     │     │ (if frame % 30 = 0) │
     │     └──────────┬──────────┘
     │                │
     └───────┬────────┘
             │
             ▼
  ┌─────────────────────────────────┐
  │    PARTICLE STATE AT FRAME N    │
  │  • positions: Float32Array      │
  │  • velocities: Float32Array     │
  │  • colors: Float32Array         │
  │  • sizes: Float32Array          │
  │  • ages: Float32Array           │
  │  • alive: Uint8Array            │
  └─────────────────────────────────┘
             │
             ▼
  ┌─────────────────────────────────┐
  │    GPU INSTANCED RENDERING      │
  │  • Upload to GPU buffers        │
  │  • Instance attributes          │
  │  • Draw call (single)           │
  └─────────────────────────────────┘
```

### 2.4 Audio Reactivity Flow

```
┌──────────────────────────────────────────────────────────────────────────────┐
│                        AUDIO REACTIVITY FLOW                                 │
└──────────────────────────────────────────────────────────────────────────────┘

        IMPORT TIME (Once)                    EVALUATION TIME (Per Frame)
        ─────────────────                     ──────────────────────────

  ┌─────────────────────┐            Frame N
  │  Load Audio File    │               │
  │  (MP3, WAV, etc)    │               ▼
  └──────────┬──────────┘        ┌─────────────────────┐
             │                   │ Get AudioAnalysis   │
             ▼                   │ from project        │
  ┌─────────────────────┐        └──────────┬──────────┘
  │  Decode to PCM      │                   │
  │  (Web Audio API)    │                   ▼
  └──────────┬──────────┘        ┌─────────────────────┐
             │                   │ Lookup Features     │
             ▼                   │ at Frame N          │
  ┌─────────────────────┐        │ O(1) array access   │
  │  Compute Features   │        └──────────┬──────────┘
  │  Per-Frame:         │                   │
  │  • amplitude        │                   ▼
  │  • RMS              │        ┌─────────────────────┐
  │  • spectrum (FFT)   │        │ Apply Mappings      │
  │  • beats            │        │ • feature → property│
  │  • onsets           │        │ • transform func    │
  │  • chroma           │        │ • smoothing         │
  │  • centroid         │        └──────────┬──────────┘
  └──────────┬──────────┘                   │
             │                              ▼
             ▼                   ┌─────────────────────┐
  ┌─────────────────────┐        │ Animated Value      │
  │  Store as           │        │ (drives layer prop) │
  │  Float32Array[]     │        └─────────────────────┘
  │  (Immutable)        │
  └─────────────────────┘

  Example Mapping:

  ┌─────────────────────────────────────────────────────────────────────┐
  │  Audio Feature: amplitude[frame] = 0.8                              │
  │                         │                                           │
  │                         ▼                                           │
  │  Transform: (v, f) => 1 + v * 0.5                                   │
  │                         │                                           │
  │                         ▼                                           │
  │  Target: layer.transform.scale.x = 1.4                              │
  └─────────────────────────────────────────────────────────────────────┘
```

---

## 3. COMPONENT ARCHITECTURE

### 3.1 Vue Component Hierarchy

```
App.vue
├── WorkspaceLayout.vue (Main container)
│   ├── Toolbar
│   │   ├── ToolSelector
│   │   ├── PlaybackControls
│   │   └── ZoomControls
│   │
│   ├── Canvas Area
│   │   ├── ThreeCanvas.vue (Main 3D viewport)
│   │   ├── SplineEditor.vue (Overlay for path editing)
│   │   ├── MaskEditor.vue (Overlay for mask editing)
│   │   └── PathPreview.vue (Motion path visualization)
│   │
│   ├── Timeline Area
│   │   ├── TimelinePanel.vue (Container)
│   │   │   ├── TimeRuler.vue
│   │   │   ├── Playhead.vue
│   │   │   └── EnhancedLayerTrack.vue (per layer)
│   │   │       ├── LayerBar.vue
│   │   │       ├── KeyframeDiamond.vue (per keyframe)
│   │   │       └── MarqueeSelect.vue
│   │   │
│   │   └── CurveEditor.vue (Curve editing)
│   │       ├── CurveEditor.vue
│   │       └── KeyframeHandles.vue
│   │
│   ├── Side Panels
│   │   ├── LayerPanel.vue (Layer list)
│   │   ├── EffectsPanel.vue (Effect stack)
│   │   ├── AssetsPanel.vue (Asset browser)
│   │   ├── AudioPanel.vue (Waveform + controls)
│   │   ├── TrajectoryPanel.vue (Camera presets)
│   │   └── ParticlePanel.vue (Particle controls)
│   │
│   └── Property Area
│       ├── TransformProperties.vue
│       ├── TextProperties.vue
│       ├── ParticleProperties.vue
│       ├── CameraProperties.vue
│       ├── LightProperties.vue
│       ├── ShapeProperties.vue
│       ├── VideoProperties.vue
│       ├── EffectProperties.vue
│       ├── MaterialProperties.vue
│       └── AudioReactiveProperties.vue
│
└── Dialogs
    ├── CompositionSettings.vue
    ├── ExportDialog.vue
    ├── FontPicker.vue
    ├── KeyboardShortcuts.vue
    └── PresetSaveDialog.vue
```

### 3.2 Component Communication

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                        COMPONENT COMMUNICATION                               │
└─────────────────────────────────────────────────────────────────────────────┘

                    ┌─────────────────────────────────────┐
                    │           PINIA STORES              │
                    │  (Single Source of Truth)           │
                    └─────────────────────────────────────┘
                               ▲           │
                               │           │ Reactive
                           Actions         │ State
                               │           ▼
    ┌──────────────────────────┼───────────────────────────────────────────┐
    │                          │                                           │
    │   ┌─────────────┐   ┌────┴────────┐   ┌─────────────┐               │
    │   │  Timeline   │   │   Canvas    │   │  Properties │               │
    │   │  Panel      │   │   Panel     │   │   Panel     │               │
    │   └──────┬──────┘   └──────┬──────┘   └──────┬──────┘               │
    │          │                 │                 │                       │
    │          └─────────────────┼─────────────────┘                       │
    │                            │                                         │
    │                   ┌────────▼────────┐                                │
    │                   │  Event Bus      │                                │
    │                   │  (provide/inject)│                               │
    │                   └─────────────────┘                                │
    │                                                                       │
    │   Props Down (parent → child):                                       │
    │   • Layer data                                                        │
    │   • Selection state                                                   │
    │   • Current frame                                                     │
    │                                                                       │
    │   Events Up (child → parent):                                        │
    │   • @select-layer                                                     │
    │   • @update-keyframe                                                  │
    │   • @tool-change                                                      │
    │                                                                       │
    └───────────────────────────────────────────────────────────────────────┘
```

---

## 4. STATE MANAGEMENT

### 4.1 Store Structure

```
┌──────────────────────────────────────────────────────────────────────────────┐
│                           PINIA STORE STRUCTURE                              │
└──────────────────────────────────────────────────────────────────────────────┘

compositorStore (90KB) ─── MAIN STORE
│
├── State
│   ├── project: WeylProject | null
│   │   ├── id: string
│   │   ├── name: string
│   │   ├── composition: Composition
│   │   │   ├── width: number
│   │   │   ├── height: number
│   │   │   ├── frameRate: number
│   │   │   ├── frameCount: number
│   │   │   └── backgroundColor: Color
│   │   ├── layers: Layer[]
│   │   ├── assets: Asset[]
│   │   └── audioAnalysis?: AudioAnalysis
│   │
│   ├── currentFrame: number
│   └── selectedLayerIds: string[]
│
├── Getters
│   ├── selectedLayers: Layer[]
│   ├── visibleLayers: Layer[]
│   ├── sortedLayers: Layer[]  (by z-index)
│   └── compositionDuration: number
│
└── Actions
    ├── Layer Management
    │   ├── addLayer(type, options)
    │   ├── removeLayer(id)
    │   ├── duplicateLayer(id)
    │   ├── reorderLayers(ids)
    │   └── updateLayer(id, updates)
    │
    ├── Keyframe Management
    │   ├── addKeyframe(layerId, property, frame, value)
    │   ├── removeKeyframe(layerId, property, frame)
    │   ├── moveKeyframe(layerId, property, from, to)
    │   └── updateKeyframeValue(layerId, property, frame, value)
    │
    ├── Selection
    │   ├── selectLayer(id)
    │   ├── selectLayers(ids)
    │   ├── deselectAll()
    │   └── toggleSelection(id)
    │
    └── Project
        ├── newProject(settings)
        ├── loadProject(data)
        ├── saveProject()
        └── exportProject(config)

─────────────────────────────────────────────────────────────────────────────

playbackStore ─── TIMELINE PLAYBACK
│
├── State
│   ├── isPlaying: boolean
│   ├── playbackSpeed: number
│   ├── loopEnabled: boolean
│   └── workAreaStart/End: number
│
└── Actions
    ├── play()
    ├── pause()
    ├── togglePlayback()
    ├── setFrame(frame)
    └── stepFrame(direction)

─────────────────────────────────────────────────────────────────────────────

selectionStore ─── SELECTION STATE
│
├── State
│   ├── selectedLayerIds: Set<string>
│   ├── selectedKeyframes: KeyframeSelection[]
│   └── hoveredLayerId: string | null
│
└── Actions
    ├── selectLayers(ids)
    ├── selectKeyframes(keyframes)
    └── clearSelection()

─────────────────────────────────────────────────────────────────────────────

historyStore ─── UNDO/REDO
│
├── State
│   ├── undoStack: HistoryEntry[]
│   ├── redoStack: HistoryEntry[]
│   └── maxHistory: number (50)
│
└── Actions
    ├── pushState(state, description)
    ├── undo()
    ├── redo()
    └── clearHistory()

─────────────────────────────────────────────────────────────────────────────

audioStore ─── AUDIO STATE
│
├── State
│   ├── audioContext: AudioContext | null
│   ├── currentTrack: AudioTrack | null
│   ├── isPlaying: boolean
│   └── volume: number
│
└── Actions
    ├── loadAudio(file)
    ├── analyzeAudio()
    ├── playAudio()
    └── stopAudio()

─────────────────────────────────────────────────────────────────────────────

assetStore ─── ASSET MANAGEMENT
│
├── State
│   ├── assets: Map<string, Asset>
│   ├── loading: Set<string>
│   └── thumbnails: Map<string, string>
│
└── Actions
    ├── importAsset(file)
    ├── removeAsset(id)
    └── getAsset(id)
```

### 4.2 State Flow Diagram

```
┌──────────────────────────────────────────────────────────────────────────────┐
│                            STATE FLOW                                        │
└──────────────────────────────────────────────────────────────────────────────┘

User Action                State Change                    Side Effects
──────────                 ────────────                    ────────────

┌─────────────┐
│ Click Play  │
└──────┬──────┘
       │
       ▼
┌─────────────────────┐
│ playbackStore       │
│ .play()             │
└──────────┬──────────┘
           │
           ├─────────────────────────────────────────┐
           │                                         │
           ▼                                         ▼
┌─────────────────────┐                   ┌─────────────────────┐
│ isPlaying = true    │                   │ Start RAF loop      │
└─────────────────────┘                   │ (requestAnimation   │
                                          │  Frame)             │
                                          └──────────┬──────────┘
                                                     │
                                                     ▼
                                          ┌─────────────────────┐
                                          │ Every frame:        │
                                          │ currentFrame++      │
                                          │ ▼                   │
                                          │ WeylEngine          │
                                          │ .renderFrame()      │
                                          └─────────────────────┘
```

---

## 5. RENDER PIPELINE

### 5.1 Frame Render Pipeline

```
┌──────────────────────────────────────────────────────────────────────────────┐
│                         FRAME RENDER PIPELINE                                │
└──────────────────────────────────────────────────────────────────────────────┘

                          ┌─────────────────────┐
                          │   REQUEST FRAME N   │
                          └──────────┬──────────┘
                                     │
                                     ▼
    ┌────────────────────────────────────────────────────────────────────┐
    │                    PHASE 1: EVALUATION                              │
    │                                                                     │
    │   For each layer (sorted by depth):                                │
    │   ┌─────────────────────────────────────────────────────────────┐  │
    │   │  1. Check visibility (enabled, inPoint <= frame <= outPoint) │  │
    │   │  2. Evaluate all animated properties at frame N              │  │
    │   │  3. Build transform matrix (TRS)                             │  │
    │   │  4. Evaluate layer-specific content                          │  │
    │   │     • Image: load texture                                    │  │
    │   │     • Text: shape glyphs                                     │  │
    │   │     • Particle: simulate to frame N                          │  │
    │   │     • Spline: evaluate curve                                 │  │
    │   │  5. Process effect stack                                     │  │
    │   └─────────────────────────────────────────────────────────────┘  │
    │                                                                     │
    └────────────────────────────────────────────────────────────────────┘
                                     │
                                     ▼
    ┌────────────────────────────────────────────────────────────────────┐
    │                    PHASE 2: SCENE SETUP                            │
    │                                                                     │
    │   ┌─────────────────────────────────────────────────────────────┐  │
    │   │  1. Update Three.js scene graph                              │  │
    │   │  2. Update camera matrices (view, projection)                │  │
    │   │  3. Update light positions and parameters                    │  │
    │   │  4. Upload textures to GPU                                   │  │
    │   │  5. Update uniform buffers                                   │  │
    │   └─────────────────────────────────────────────────────────────┘  │
    │                                                                     │
    └────────────────────────────────────────────────────────────────────┘
                                     │
                                     ▼
    ┌────────────────────────────────────────────────────────────────────┐
    │                    PHASE 3: RENDER PASSES                          │
    │                                                                     │
    │   Pass 1: Opaque Geometry                                          │
    │   ┌─────────────────────────────────────────────────────────────┐  │
    │   │  • Render solid layers front-to-back                         │  │
    │   │  • Depth buffer enabled                                      │  │
    │   │  • No blending                                               │  │
    │   └─────────────────────────────────────────────────────────────┘  │
    │                                                                     │
    │   Pass 2: Transparent Geometry                                     │
    │   ┌─────────────────────────────────────────────────────────────┐  │
    │   │  • Render transparent layers back-to-front                   │  │
    │   │  • Depth test enabled, depth write disabled                  │  │
    │   │  • Blend mode per layer                                      │  │
    │   └─────────────────────────────────────────────────────────────┘  │
    │                                                                     │
    │   Pass 3: Particles                                                │
    │   ┌─────────────────────────────────────────────────────────────┐  │
    │   │  • GPU instanced rendering                                   │  │
    │   │  • Additive blending                                         │  │
    │   │  • Soft particles (depth-based fade)                         │  │
    │   └─────────────────────────────────────────────────────────────┘  │
    │                                                                     │
    └────────────────────────────────────────────────────────────────────┘
                                     │
                                     ▼
    ┌────────────────────────────────────────────────────────────────────┐
    │                    PHASE 4: POST-PROCESSING                        │
    │                                                                     │
    │   ┌─────────────────────────────────────────────────────────────┐  │
    │   │  EffectComposer pipeline:                                    │  │
    │   │  1. Render pass (scene to texture)                           │  │
    │   │  2. Bloom pass (optional)                                    │  │
    │   │  3. Color correction (optional)                              │  │
    │   │  4. Motion blur (optional)                                   │  │
    │   │  5. FXAA (antialiasing)                                      │  │
    │   │  6. Output to canvas                                         │  │
    │   └─────────────────────────────────────────────────────────────┘  │
    │                                                                     │
    └────────────────────────────────────────────────────────────────────┘
                                     │
                                     ▼
    ┌────────────────────────────────────────────────────────────────────┐
    │                    PHASE 5: OUTPUT                                 │
    │                                                                     │
    │   ┌─────────────────────────────────────────────────────────────┐  │
    │   │  • Display on canvas                                         │  │
    │   │  • Cache frame if needed                                     │  │
    │   │  • Trigger export capture if exporting                       │  │
    │   └─────────────────────────────────────────────────────────────┘  │
    │                                                                     │
    └────────────────────────────────────────────────────────────────────┘
```

### 5.2 Blend Mode Pipeline

```
┌──────────────────────────────────────────────────────────────────────────────┐
│                          BLEND MODE PIPELINE                                 │
└──────────────────────────────────────────────────────────────────────────────┘

  Layer Stack              Blend Operation              Result
  ───────────              ───────────────              ──────

  ┌─────────────┐
  │  Layer 3    │  Blend: Multiply
  │  (Top)      │  ─────────────────────────────────────────────────────┐
  └─────────────┘                                                       │
        │                                                               │
        ▼                                                               │
  ┌─────────────┐    ┌───────────────────────────────────────┐         │
  │  Layer 2    │───▶│  result = layer2 × layer3              │         │
  │  (Middle)   │    │  (per-channel multiplication)         │         │
  └─────────────┘    └───────────────────────────────────────┘         │
        │                         │                                     │
        │                         ▼                                     │
        │            ┌───────────────────────────────────────┐         │
        │            │  Apply layer 2 opacity                 │         │
        │            │  result = lerp(layer2, result, opacity)│         │
        │            └───────────────────────────────────────┘         │
        │                         │                                     │
        ▼                         ▼                                     ▼
  ┌─────────────┐    ┌───────────────────────────────────────────────────┐
  │  Layer 1    │───▶│  Composite onto background                        │
  │  (Bottom)   │    │  Apply layer 1 blend mode                         │
  └─────────────┘    └───────────────────────────────────────────────────┘
                                  │
                                  ▼
                     ┌───────────────────────────────────────┐
                     │          FINAL COMPOSITE              │
                     └───────────────────────────────────────┘

  Supported Blend Modes (27):
  ┌────────────────────────────────────────────────────────────────────┐
  │ Normal    │ Dissolve  │ Darken    │ Multiply  │ Color Burn│ Linear│
  │ Lighten   │ Screen    │ Color     │ Dodge     │ Linear    │ Dodge │
  │ Overlay   │ Soft Light│ Hard Light│ Vivid     │ Light     │ Pin   │
  │ Light     │ Hard Mix  │ Difference│ Exclusion │ Subtract  │ Divide│
  │ Hue       │ Saturation│ Color     │ Luminosity│           │       │
  └────────────────────────────────────────────────────────────────────┘
```

---

## 6. ENGINE ARCHITECTURE

### 6.1 WeylEngine Class Structure

```
┌──────────────────────────────────────────────────────────────────────────────┐
│                        WEYL ENGINE STRUCTURE                                 │
│                        (2400+ lines)                                         │
└──────────────────────────────────────────────────────────────────────────────┘

class WeylEngine {

  // ═══════════════════════════════════════════════════════════════════════════
  // CORE COMPONENTS
  // ═══════════════════════════════════════════════════════════════════════════

  private scene: THREE.Scene                    // Main scene graph
  private renderer: THREE.WebGLRenderer         // WebGL2 renderer
  private camera: THREE.PerspectiveCamera       // Active camera
  private composer: EffectComposer              // Post-processing
  private layerManager: LayerManager            // Layer management
  private cameraController: CameraController    // Camera controls

  // ═══════════════════════════════════════════════════════════════════════════
  // CACHING
  // ═══════════════════════════════════════════════════════════════════════════

  private frameCache: FrameCache                // Rendered frame cache
  private textureCache: Map<string, Texture>    // Loaded textures
  private geometryCache: Map<string, Geometry>  // Reusable geometries

  // ═══════════════════════════════════════════════════════════════════════════
  // PUBLIC METHODS
  // ═══════════════════════════════════════════════════════════════════════════

  constructor(canvas: HTMLCanvasElement, options: EngineOptions)

  // Lifecycle
  initialize(): Promise<void>
  dispose(): void
  resize(width: number, height: number): void

  // Rendering
  renderFrame(frame: number): void
  renderToTexture(frame: number): THREE.Texture
  exportFrame(frame: number, format: 'png' | 'exr'): Blob

  // Layer Management
  addLayer(layer: Layer): void
  removeLayer(id: string): void
  updateLayer(id: string, updates: Partial<Layer>): void
  getLayerAtPoint(x: number, y: number): Layer | null

  // Camera
  setActiveCamera(cameraId: string | null): void
  getCameraState(): CameraState

  // Selection
  selectLayers(ids: string[]): void
  getSelectedLayers(): Layer[]

  // ═══════════════════════════════════════════════════════════════════════════
  // PRIVATE METHODS
  // ═══════════════════════════════════════════════════════════════════════════

  // Evaluation
  private evaluateLayer(layer: Layer, frame: number): EvaluatedLayer
  private evaluateTransform(transform: LayerTransform, frame: number): Matrix4
  private evaluateEffects(effects: Effect[], frame: number): EffectResult

  // Rendering
  private setupRenderPass(): void
  private renderOpaquePass(): void
  private renderTransparentPass(): void
  private renderParticlePass(): void
  private applyPostProcessing(): void

  // Utilities
  private createThreeObject(layer: Layer): THREE.Object3D
  private updateThreeObject(object: THREE.Object3D, evaluated: EvaluatedLayer): void
  private disposeObject(object: THREE.Object3D): void
}
```

### 6.2 Layer Manager Structure

```
┌──────────────────────────────────────────────────────────────────────────────┐
│                        LAYER MANAGER STRUCTURE                               │
└──────────────────────────────────────────────────────────────────────────────┘

class LayerManager {

  // Storage
  private layers: Map<string, BaseLayer>        // Layer instances by ID
  private layerOrder: string[]                  // Z-order (bottom to top)
  private threeObjects: Map<string, Object3D>   // Three.js objects

  // Layer Operations
  addLayer(data: LayerData): BaseLayer
  removeLayer(id: string): void
  getLayer(id: string): BaseLayer | undefined
  getLayers(): BaseLayer[]
  reorderLayers(ids: string[]): void

  // Evaluation
  evaluateAt(frame: number): EvaluatedLayer[]
  getVisibleLayers(frame: number): BaseLayer[]

  // Three.js Integration
  getThreeObject(id: string): Object3D | undefined
  syncToScene(scene: Scene): void
}

// Layer Type Implementations:

┌─────────────────────────────────────────────────────────────────────────────┐
│  BaseLayer (abstract)                                                        │
│  ├── id, name, type, enabled, locked                                        │
│  ├── transform: LayerTransform                                               │
│  ├── blendMode: BlendMode                                                   │
│  ├── effects: Effect[]                                                       │
│  ├── masks: Mask[]                                                           │
│  ├── inPoint, outPoint                                                       │
│  └── abstract methods: createThreeObject(), evaluate(), dispose()            │
├─────────────────────────────────────────────────────────────────────────────┤
│  ImageLayer extends BaseLayer                                                │
│  └── source: string, fit: 'fill' | 'fit' | 'stretch'                        │
├─────────────────────────────────────────────────────────────────────────────┤
│  VideoLayer extends BaseLayer                                                │
│  └── source: string, loop: boolean, frameBlending: boolean                   │
├─────────────────────────────────────────────────────────────────────────────┤
│  TextLayer extends BaseLayer                                                 │
│  └── content: string, fontId: string, fontSize: number, alignment: string    │
├─────────────────────────────────────────────────────────────────────────────┤
│  SplineLayer extends BaseLayer                                               │
│  └── points: ControlPoint[], closed: boolean, strokeWidth: number            │
├─────────────────────────────────────────────────────────────────────────────┤
│  ParticleLayer extends BaseLayer                                             │
│  └── emitter: EmitterConfig, physics: PhysicsConfig, rendering: RenderConfig │
├─────────────────────────────────────────────────────────────────────────────┤
│  CameraLayer extends BaseLayer                                               │
│  └── fov: number, near: number, far: number, dof: DOFConfig                  │
├─────────────────────────────────────────────────────────────────────────────┤
│  LightLayer extends BaseLayer                                                │
│  └── lightType: 'ambient'|'point'|'spot'|'directional', intensity: number    │
├─────────────────────────────────────────────────────────────────────────────┤
│  ... and 10 more layer types                                                 │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## 7. SERVICE LAYER

### 7.1 Service Categories

```
┌──────────────────────────────────────────────────────────────────────────────┐
│                         SERVICE LAYER ORGANIZATION                           │
└──────────────────────────────────────────────────────────────────────────────┘

services/
│
├── ANIMATION (5 services)
│   ├── interpolation.ts      ─ Keyframe value interpolation
│   ├── easing.ts             ─ 35 easing functions
│   ├── expressions.ts        ─ Expression language & presets
│   ├── propertyDriver.ts     ─ Property linking (pickwhip)
│   └── layerEvaluationCache.ts ─ Evaluation result caching
│
├── AUDIO (4 services)
│   ├── audioFeatures.ts      ─ Audio analysis (FFT, beats, etc)
│   ├── audioReactiveMapping.ts ─ Audio-to-property mapping
│   ├── audioPathAnimator.ts  ─ Audio-driven path animation
│   └── audioWorkerClient.ts  ─ Web Worker for audio processing
│
├── 3D/CAMERA (5 services)
│   ├── cameraTrajectory.ts   ─ 22 camera movement presets
│   ├── cameraEnhancements.ts ─ Shake, rack focus, DOF
│   ├── camera3DVisualization.ts ─ Camera frustum visualization
│   ├── cameraExport.ts       ─ Camera animation export
│   └── math3d.ts             ─ 3D math utilities
│
├── PARTICLES (4 services)
│   ├── particleSystem.ts     ─ CPU particle simulation (76KB)
│   ├── gpuParticleRenderer.ts ─ GPU instanced rendering
│   ├── meshParticleManager.ts ─ Mesh-based particles
│   └── spriteSheet.ts        ─ Sprite animation
│
├── GEOMETRY (5 services)
│   ├── arcLength.ts          ─ Arc-length parameterization
│   ├── textOnPath.ts         ─ Text along spline path
│   ├── shapeOperations.ts    ─ Path boolean operations
│   ├── imageTrace.ts         ─ Image to vector tracing
│   └── svgExtrusion.ts       ─ SVG to 3D mesh
│
├── EFFECTS (6 services)
│   ├── effectProcessor.ts    ─ Effect stack processing
│   └── effects/
│       ├── blurRenderer.ts   ─ Blur effects (5 types)
│       ├── colorRenderer.ts  ─ Color effects (13 types)
│       ├── distortRenderer.ts ─ Distortion effects
│       ├── generateRenderer.ts ─ Generator effects
│       └── maskRenderer.ts   ─ Mask operations
│
├── RENDERING (4 services)
│   ├── depthflow.ts          ─ 2.5D parallax rendering
│   ├── motionBlur.ts         ─ Motion blur effect
│   ├── materialSystem.ts     ─ PBR material management
│   └── webgpuRenderer.ts     ─ WebGPU acceleration
│
├── CACHING (2 services)
│   ├── frameCache.ts         ─ Rendered frame caching
│   └── layerEvaluationCache.ts ─ Property evaluation cache
│
├── EXPORT (3 services)
│   ├── matteExporter.ts      ─ Matte sequence export
│   ├── modelExport.ts        ─ 3D model/trajectory export
│   └── projectStorage.ts     ─ Project save/load
│
├── UTILITIES (6 services)
│   ├── fontService.ts        ─ Font loading & enumeration
│   ├── gpuDetection.ts       ─ GPU capability detection
│   ├── workerPool.ts         ─ Web Worker pool
│   ├── lazyLoader.ts         ─ Lazy loading system
│   ├── segmentation.ts       ─ Image segmentation
│   └── segmentToMask.ts      ─ Segmentation to mask
│
└── AI (1 service)
    └── aiGeneration.ts       ─ AI model integration
```

---

## 8. EVENT FLOW

### 8.1 User Interaction Event Flow

```
┌──────────────────────────────────────────────────────────────────────────────┐
│                        USER INTERACTION EVENT FLOW                           │
└──────────────────────────────────────────────────────────────────────────────┘

Example: Dragging a keyframe in the timeline

┌─────────────┐     ┌─────────────┐     ┌─────────────┐     ┌─────────────┐
│  @mousedown │     │  @mousemove │     │  @mouseup   │     │  Store      │
│  (start)    │────▶│  (drag)     │────▶│  (end)      │────▶│  Update     │
└─────────────┘     └─────────────┘     └─────────────┘     └─────────────┘
      │                   │                   │                   │
      ▼                   ▼                   ▼                   ▼
┌─────────────┐     ┌─────────────┐     ┌─────────────┐     ┌─────────────┐
│ Capture     │     │ Update      │     │ Commit      │     │ Push to     │
│ initial     │     │ preview     │     │ change      │     │ history     │
│ position    │     │ position    │     │             │     │             │
└─────────────┘     └─────────────┘     └─────────────┘     └─────────────┘
                          │                   │                   │
                          │                   │                   │
                          ▼                   ▼                   ▼
                    ┌─────────────┐     ┌─────────────┐     ┌─────────────┐
                    │ Throttled   │     │ compositorStore│   │ Engine      │
                    │ render      │     │ .moveKeyframe()│   │ re-render   │
                    │ update      │     │              │     │             │
                    └─────────────┘     └─────────────┘     └─────────────┘
```

### 8.2 Keyboard Shortcut Flow

```
┌──────────────────────────────────────────────────────────────────────────────┐
│                        KEYBOARD SHORTCUT FLOW                                │
└──────────────────────────────────────────────────────────────────────────────┘

document.addEventListener('keydown')
           │
           ▼
┌─────────────────────────────────────────┐
│  Check if input field has focus         │
│  (skip if typing in text input)         │
└──────────────────────┬──────────────────┘
                       │
                       ▼
┌─────────────────────────────────────────┐
│  Match key combination                  │
│  ┌───────────────────────────────────┐  │
│  │ Space      → togglePlayback()     │  │
│  │ Delete     → deleteSelected()     │  │
│  │ Ctrl+Z     → undo()               │  │
│  │ Ctrl+Y     → redo()               │  │
│  │ Ctrl+S     → saveProject()        │  │
│  │ V          → selectTool()         │  │
│  │ P          → penTool()            │  │
│  │ ← / →      → stepFrame()          │  │
│  │ Home / End → goToStart/End()      │  │
│  └───────────────────────────────────┘  │
└──────────────────────┬──────────────────┘
                       │
                       ▼
┌─────────────────────────────────────────┐
│  Execute action                         │
│  Prevent default browser behavior       │
└─────────────────────────────────────────┘
```

---

## 9. FILE STRUCTURE

### 9.1 Complete File Tree

```
ui/
├── src/
│   ├── main.ts                           # Application entry point
│   ├── App.vue                           # Root Vue component
│   │
│   ├── components/                       # Vue components (57 files)
│   │   ├── canvas/
│   │   │   ├── ThreeCanvas.vue           # Main Three.js viewport
│   │   │   ├── SplineEditor.vue          # Path editing overlay
│   │   │   ├── MaskEditor.vue            # Mask drawing overlay
│   │   │   └── PathPreview.vue           # Motion path visualization
│   │   │
│   │   ├── controls/
│   │   │   ├── AngleDial.vue             # Rotation input
│   │   │   ├── ColorPicker.vue           # RGBA color picker
│   │   │   ├── CurveEditor.vue           # Bezier curve handles
│   │   │   ├── PropertyLink.vue              # Property linking UI
│   │   │   ├── NumberInput.vue           # Numeric input with scrub
│   │   │   ├── VectorInput.vue           # XYZ vector input
│   │   │   ├── Stopwatch.vue             # Animation toggle
│   │   │   └── ExpressionEditor.vue      # Expression input
│   │   │
│   │   ├── dialogs/
│   │   │   ├── CompositionSettings.vue   # Project dimensions
│   │   │   ├── ExportDialog.vue          # Export options
│   │   │   ├── FontPicker.vue            # Font selection
│   │   │   ├── KeyboardShortcuts.vue     # Shortcut reference
│   │   │   └── PresetSaveDialog.vue      # Save presets
│   │   │
│   │   ├── layout/
│   │   │   └── WorkspaceLayout.vue       # Main layout container
│   │   │
│   │   ├── panels/
│   │   │   ├── AssetsPanel.vue           # Asset management
│   │   │   ├── AudioPanel.vue            # Audio waveform
│   │   │   ├── EffectsPanel.vue          # Effect stack
│   │   │   ├── LayerPanel.vue            # Layer list
│   │   │   ├── PreviewPanel.vue          # Render preview
│   │   │   ├── ProjectPanel.vue          # Project settings
│   │   │   ├── TrajectoryPanel.vue       # Camera presets
│   │   │   ├── ParticlePanel.vue         # Particle controls
│   │   │   └── PresetsPanel.vue          # Effect presets
│   │   │
│   │   ├── properties/
│   │   │   ├── TransformProperties.vue   # Position/scale/rotation
│   │   │   ├── TextProperties.vue        # Font/style settings
│   │   │   ├── ParticleProperties.vue    # Emitter settings
│   │   │   ├── CameraProperties.vue      # Camera/DOF
│   │   │   ├── LightProperties.vue       # Light parameters
│   │   │   ├── ShapeProperties.vue       # Path fill/stroke
│   │   │   ├── VideoProperties.vue       # Playback controls
│   │   │   ├── EffectProperties.vue      # Effect parameters
│   │   │   ├── MaterialProperties.vue    # PBR materials
│   │   │   └── AudioReactiveProperties.vue # Audio mapping
│   │   │
│   │   └── timeline/
│   │       ├── TimelinePanel.vue         # Timeline container
│   │       ├── EnhancedLayerTrack.vue    # Layer with keyframes
│   │       ├── KeyframeDiamond.vue       # Keyframe marker
│   │       ├── Playhead.vue              # Current frame indicator
│   │       ├── TimeRuler.vue             # Frame numbers
│   │       ├── CurveEditor.vue           # Speed/value curves
│   │       ├── MarqueeSelect.vue         # Box selection
│   │       └── TimelineContextMenu.vue   # Right-click menu
│   │
│   ├── engine/                           # Three.js engine
│   │   ├── WeylEngine.ts                 # Main engine class (2400+ lines)
│   │   │
│   │   ├── animation/
│   │   │   ├── EasingFunctions.ts        # Easing implementations
│   │   │   └── KeyframeEvaluator.ts      # Keyframe evaluation
│   │   │
│   │   ├── core/
│   │   │   ├── CameraController.ts       # Camera controls
│   │   │   ├── LayerManager.ts           # Layer management
│   │   │   └── RenderPipeline.ts         # Render pass management
│   │   │
│   │   ├── layers/                       # Layer implementations (17 files)
│   │   │   ├── BaseLayer.ts              # Abstract base class (54KB)
│   │   │   ├── ImageLayer.ts
│   │   │   ├── VideoLayer.ts
│   │   │   ├── TextLayer.ts
│   │   │   ├── SolidLayer.ts
│   │   │   ├── SplineLayer.ts
│   │   │   ├── ShapeLayer.ts
│   │   │   ├── NullLayer.ts
│   │   │   ├── ParticleLayer.ts
│   │   │   ├── CameraLayer.ts
│   │   │   ├── LightLayer.ts
│   │   │   ├── PrecompLayer.ts
│   │   │   ├── AdjustmentLayer.ts
│   │   │   ├── ModelLayer.ts
│   │   │   ├── PointCloudLayer.ts
│   │   │   ├── DepthflowLayer.ts
│   │   │   └── ProceduralMatteLayer.ts
│   │   │
│   │   └── particles/
│   │       ├── GPUParticleSystem.ts      # GPU particle rendering
│   │       ├── shaders/                  # Particle shaders
│   │       └── types.ts                  # Particle types
│   │
│   ├── services/                         # Business logic (42 files)
│   │   ├── [See Service Layer section above]
│   │   └── effects/                      # Effect renderers
│   │
│   ├── stores/                           # Pinia stores (7 files)
│   │   ├── compositorStore.ts            # Main store (90KB)
│   │   ├── playbackStore.ts
│   │   ├── selectionStore.ts
│   │   ├── historyStore.ts
│   │   ├── audioStore.ts
│   │   ├── assetStore.ts
│   │   └── uiStore.ts
│   │
│   ├── types/                            # TypeScript types
│   │   ├── project.ts                    # Project types
│   │   ├── effects.ts                    # Effect types
│   │   └── particles.ts                  # Particle types
│   │
│   └── __tests__/                        # Test files (28 files)
│       ├── services/
│       └── engine/
│
├── public/                               # Static assets
├── vite.config.ts                        # Vite configuration
├── vitest.config.ts                      # Test configuration
└── tsconfig.json                         # TypeScript configuration
```

---

## 10. INTEGRATION POINTS

### 10.1 ComfyUI Integration

```
┌──────────────────────────────────────────────────────────────────────────────┐
│                        COMFYUI INTEGRATION                                   │
└──────────────────────────────────────────────────────────────────────────────┘

ComfyUI
│
├── Extension Registration
│   └── web/js/extension.js
│       │
│       ├── Register sidebar tab "Compositor"
│       ├── Load weyl-compositor.js bundle
│       └── Initialize Vue application
│
├── Python Nodes
│   └── nodes/
│       ├── __init__.py (node registration)
│       └── compositor_node.py
│           │
│           ├── CompositorNode
│           │   ├── INPUT: image, depth, settings
│           │   └── OUTPUT: composited frames
│           │
│           ├── MatteExportNode
│           │   ├── INPUT: project, frame range
│           │   └── OUTPUT: matte sequence
│           │
│           └── AudioInputNode
│               ├── INPUT: audio file
│               └── OUTPUT: audio analysis
│
└── HTTP Routes
    └── /weyl/compositor/*
        │
        ├── POST /set_output
        │   └── Send rendered frame to workflow
        │
        ├── POST /save_project
        │   └── Save project to disk
        │
        ├── GET /load_project
        │   └── Load project from disk
        │
        └── GET /assets/:id
            └── Stream asset file


Communication Flow:
┌─────────────┐      ┌─────────────┐      ┌─────────────┐
│   ComfyUI   │◀────▶│   Python    │◀────▶│   Frontend  │
│   Workflow  │      │   Backend   │      │   (Vue)     │
└─────────────┘      └─────────────┘      └─────────────┘
     │                     │                     │
     │                     │                     │
     ▼                     ▼                     ▼
  Execute              HTTP/WS              Render
  workflow            messages              frames
```

### 10.2 Export Integration

```
┌──────────────────────────────────────────────────────────────────────────────┐
│                        EXPORT INTEGRATION                                    │
└──────────────────────────────────────────────────────────────────────────────┘

Export Targets:

┌─────────────────────────────────────────────────────────────────────────────┐
│  TARGET: Wan Video Generation                                                │
│                                                                              │
│  Outputs:                                                                    │
│  ├── RGBA frames (PNG)                                                       │
│  ├── Depth maps (PNG normalized)                                             │
│  ├── Motion vectors (optional)                                               │
│  └── Camera trajectory (JSON)                                                │
│                                                                              │
│  Usage:                                                                      │
│  └── Load in ComfyUI → Feed to Wan model                                     │
└─────────────────────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────────────────────┐
│  TARGET: Regional Prompting                                                  │
│                                                                              │
│  Outputs:                                                                    │
│  ├── Per-layer masks (PNG)                                                   │
│  ├── ID maps (uint16)                                                        │
│  └── Layer metadata (JSON)                                                   │
│                                                                              │
│  Usage:                                                                      │
│  └── Load in ComfyUI → Regional conditioning                                 │
└─────────────────────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────────────────────┐
│  TARGET: ATI (Audio-to-Image)                                                │
│                                                                              │
│  Outputs:                                                                    │
│  ├── Audio features (NPZ)                                                    │
│  │   ├── amplitude per frame                                                 │
│  │   ├── spectrum per frame                                                  │
│  │   └── beat markers                                                        │
│  └── Composition frames (PNG)                                                │
│                                                                              │
│  Usage:                                                                      │
│  └── Load in ComfyUI → ATI model conditioning                                │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## QUICK REFERENCE

### Key Files for Common Tasks

| Task | Primary Files |
|------|--------------|
| Add new layer type | `engine/layers/`, `stores/compositorStore.ts` |
| Add new effect | `services/effects/`, `services/effectProcessor.ts` |
| Modify animation | `services/interpolation.ts`, `services/easing.ts` |
| Change UI layout | `components/layout/WorkspaceLayout.vue` |
| Add keyboard shortcut | `components/layout/WorkspaceLayout.vue` |
| Modify timeline | `components/timeline/TimelinePanel.vue` |
| Change camera behavior | `engine/core/CameraController.ts` |
| Add export format | `services/matteExporter.ts`, `services/modelExport.ts` |
| Modify particle system | `services/particleSystem.ts`, `engine/particles/` |

### Performance-Critical Paths

1. **Render loop** - `WeylEngine.renderFrame()`
2. **Property evaluation** - `interpolation.ts`
3. **Particle simulation** - `particleSystem.ts`
4. **Frame caching** - `frameCache.ts`
5. **Effect processing** - `effectProcessor.ts`

---

**Document End**
**Total Lines: ~1500**
**Last Updated: December 19, 2025**
