# CLAUDE.md - WEYL COMPOSITOR COMPLETE GUIDE

**Version:** 5.0 FINAL | **Last Updated:** December 19, 2024

---

## TABLE OF CONTENTS

1. [Executive Summary](#executive-summary)
2. [Project Metrics](#project-metrics)
3. [Build Commands](#build-commands)
4. [Architecture Deep Dive](#architecture-deep-dive)
5. [The Determinism Rule (CRITICAL)](#the-determinism-rule-critical)
6. [Layer System](#layer-system)
7. [Animation System](#animation-system)
8. [Particle System](#particle-system)
9. [Audio Reactivity](#audio-reactivity)
10. [3D Camera System](#3d-camera-system)
11. [Effect Pipeline](#effect-pipeline)
12. [Key File Locations](#key-file-locations)
13. [Common Tasks Guide](#common-tasks-guide)
14. [Troubleshooting](#troubleshooting)
15. [Known Issues & Workarounds](#known-issues--workarounds)
16. [Documentation Index](#documentation-index)
17. [Git Status & Recent Changes](#git-status--recent-changes)
18. [Tech Stack Reference](#tech-stack-reference)

---

## EXECUTIVE SUMMARY

### What is Weyl Compositor?

Weyl is an **After Effects-caliber motion graphics compositor** built for the **ComfyUI ecosystem**. Think of it as:

- **Adobe After Effects** (timeline, keyframes, graph editor, layers, precomps)
- **+ Trapcode Particular** (deterministic particle systems)
- **+ TouchDesigner** (audio reactivity, property linking)
- **+ ComfyUI Integration** (matte export for AI video generation)

### Why Does It Exist?

ComfyUI users need to create **conditioning data** (depth maps, masks, motion vectors) for AI video generation models like Wan 2.1. Weyl lets you:

1. Draw splines on depth maps
2. Animate text along paths
3. Create particle effects
4. Control 3D cameras with presets
5. Export frame sequences for AI processing

### Target Output

- **81 frames** at **16fps** = 5.0625 seconds
- Dimensions **divisible by 8** (for AI model compatibility)
- Deterministic output (same input = same output, always)

---

## PROJECT METRICS

| Metric | Current | Target | Notes |
|--------|---------|--------|-------|
| **Lines of Code** | 128,114 | - | TypeScript + Vue |
| **Source Files** | 215 | - | .ts + .vue |
| **Test Files** | 29 | - | Vitest framework |
| **Tests Passing** | 1011/1055 | 1055/1055 | 96% pass rate |
| **TypeScript Errors** | 26 | 0 | All in test files |
| **Services** | 42 | - | Business logic modules |
| **Vue Components** | 55 | - | UI components |
| **Layer Types** | 17 | - | More than AE! |
| **Effects** | 22 | - | 4 categories |
| **Easing Functions** | 35 | - | All Penner + custom |
| **Camera Presets** | 22 | - | Trajectory presets |
| **Feature Completion** | 87% | 95% | See HANDOFF.md |

---

## BUILD COMMANDS

```bash
# Navigate to UI directory
cd ui

# Install dependencies (first time only)
npm install

# Development server with hot reload
npm run dev
# Opens at http://localhost:5173

# Production build
npm run build
# Outputs to: ../web/js/
#   weyl-compositor.js (2.2MB)
#   weyl-compositor.css (146KB)
#   weyl-three-vendor.js (2.4MB)
#   weyl-vue-vendor.js (210KB)

# Run all tests
npm test

# Run tests with verbose output
npm test -- --reporter=verbose

# Run specific test file
npm test -- audioFeatures.test.ts

# Type check (shows 26 errors in test files)
npx tsc --noEmit

# Watch mode for development
npm test -- --watch
```

### Build Output Structure

```
web/js/
├── extension.js              # ComfyUI sidebar registration
├── weyl-compositor.js        # Main application bundle
├── weyl-compositor.css       # All styles
├── weyl-three-vendor.js      # Three.js chunk
├── weyl-vue-vendor.js        # Vue chunk
├── weyl-ui-vendor.js         # PrimeVue chunk
├── weyl-export-vendor.js     # Export libraries
├── worker-audioWorker.js     # Web Worker for audio
└── assets/                   # Static assets
```

---

## ARCHITECTURE DEEP DIVE

### System Layers

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                           PRESENTATION LAYER                                 │
│                                                                              │
│  Vue 3.5 Components (55 total)                                              │
│  ├── Canvas Area: ThreeCanvas, SplineEditor, MaskEditor, PathPreview        │
│  ├── Timeline: TimelinePanel, LayerTrack, GraphEditor, Playhead             │
│  ├── Panels: LayerPanel, EffectsPanel, AudioPanel, AssetsPanel              │
│  ├── Properties: TransformProps, TextProps, ParticleProps, CameraProps      │
│  ├── Controls: ColorPicker, AngleDial, Pickwhip, CurveEditor                │
│  └── Dialogs: ExportDialog, FontPicker, CompositionSettings                 │
│                                                                              │
│  PrimeVue 4 provides: Buttons, Inputs, Dropdowns, Tabs, Splitters           │
└──────────────────────────────────────────────────────────────────────────────┘
                                       │
                                       ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                            STATE LAYER (Pinia 2.2)                          │
│                                                                              │
│  compositorStore (90KB) - THE MAIN STORE                                    │
│  ├── project: WeylProject         # All project data                        │
│  ├── compositions: Composition[]  # All compositions                        │
│  ├── activeCompositionId: string  # Currently editing                       │
│  ├── currentFrame: number         # Playhead position                       │
│  └── selectedLayerIds: string[]   # Selected layers                         │
│                                                                              │
│  Modular Sub-Stores (delegated from compositorStore):                       │
│  ├── playbackStore   → play(), pause(), setFrame(), isPlaying              │
│  ├── selectionStore  → selectLayer(), selectKeyframes(), clearSelection    │
│  ├── historyStore    → push(), undo(), redo(), canUndo, canRedo            │
│  ├── audioStore      → loadAudio(), playAudio(), audioContext              │
│  └── assetStore      → importAsset(), getAsset(), thumbnails               │
└──────────────────────────────────────────────────────────────────────────────┘
                                       │
                                       ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                           ENGINE LAYER (Three.js r170)                      │
│                                                                              │
│  WeylEngine.ts (2400+ lines) - Main Engine Facade                           │
│  ├── scene: THREE.Scene              # Scene graph                          │
│  ├── renderer: THREE.WebGLRenderer   # WebGL2 renderer                      │
│  ├── camera: THREE.PerspectiveCamera # Active camera                        │
│  ├── composer: EffectComposer        # Post-processing                      │
│  └── layerManager: LayerManager      # Layer management                     │
│                                                                              │
│  MotionEngine.ts - PURE FRAME EVALUATION (Single Source of Truth)           │
│  └── evaluate(frame, project, audio) → FrameState                           │
│                                                                              │
│  LayerManager.ts - Layer CRUD and Scene Sync                                │
│  CameraController.ts - Orbit, Pan, Dolly, View Presets                      │
│                                                                              │
│  Layer Implementations (17 types):                                           │
│  ├── ImageLayer, VideoLayer, SolidLayer, NullLayer                          │
│  ├── TextLayer, SplineLayer, ShapeLayer                                     │
│  ├── ParticleLayer, CameraLayer, LightLayer                                 │
│  ├── PrecompLayer, AdjustmentLayer, ProceduralMatteLayer                    │
│  └── ModelLayer, PointCloudLayer, DepthflowLayer                            │
└──────────────────────────────────────────────────────────────────────────────┘
                                       │
                                       ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                           SERVICE LAYER (42 services)                       │
│                                                                              │
│  ANIMATION (5 services):                                                     │
│  ├── interpolation.ts (21KB)    # Keyframe interpolation, Bezier curves    │
│  ├── easing.ts (8KB)            # 35 easing functions                       │
│  ├── expressions.ts (35KB)      # Expression language, AE-style            │
│  ├── propertyDriver.ts (25KB)   # Pickwhip property linking                │
│  └── layerEvaluationCache.ts    # Evaluation result caching                │
│                                                                              │
│  AUDIO (4 services):                                                         │
│  ├── audioFeatures.ts (36KB)    # FFT, beat detection, BPM                 │
│  ├── audioReactiveMapping.ts    # Audio → property mapping                 │
│  ├── audioPathAnimator.ts       # Audio-driven path animation              │
│  └── audioWorkerClient.ts       # Web Worker communication                 │
│                                                                              │
│  PARTICLES (4 services):                                                     │
│  ├── particleSystem.ts (76KB)   # CPU simulation, SeededRNG               │
│  ├── gpuParticleRenderer.ts     # WebGL2 Transform Feedback               │
│  ├── meshParticleManager.ts     # Mesh-based particles                    │
│  └── spriteSheet.ts             # Sprite animation                        │
│                                                                              │
│  3D/CAMERA (5 services):                                                     │
│  ├── math3d.ts (14KB)           # Vec3, Mat4, Quat operations             │
│  ├── cameraTrajectory.ts        # 22 camera presets                       │
│  ├── cameraEnhancements.ts      # Shake, rack focus, DOF                  │
│  ├── camera3DVisualization.ts   # Frustum visualization                   │
│  └── cameraExport.ts            # Camera animation export                 │
│                                                                              │
│  EFFECTS (6 services):                                                       │
│  ├── effectProcessor.ts         # Effect stack pipeline                    │
│  └── effects/                   # Individual effect renderers              │
│      ├── blurRenderer.ts        # Gaussian, Directional, Radial           │
│      ├── colorRenderer.ts       # 13 color effects                        │
│      ├── distortRenderer.ts     # Transform, Warp                         │
│      └── generateRenderer.ts    # Fill, Gradient, Noise                   │
│                                                                              │
│  GEOMETRY (5 services):                                                      │
│  ├── arcLength.ts               # Arc-length parameterization             │
│  ├── textOnPath.ts              # Text along spline                       │
│  ├── shapeOperations.ts (43KB)  # Path booleans (simplified)              │
│  ├── imageTrace.ts              # Image to vector                         │
│  └── svgExtrusion.ts            # SVG to 3D mesh                          │
│                                                                              │
│  EXPORT (3 services):                                                        │
│  ├── matteExporter.ts (15KB)    # Matte sequence export                   │
│  ├── modelExport.ts (34KB)      # 3D model export                         │
│  └── projectStorage.ts          # Project save/load                       │
│                                                                              │
│  CACHING (2 services):                                                       │
│  ├── frameCache.ts              # Rendered frame cache                    │
│  └── layerEvaluationCache.ts    # Property evaluation cache               │
│                                                                              │
│  UTILITIES (8+ services):                                                    │
│  ├── fontService.ts             # Font loading & enumeration              │
│  ├── gpuDetection.ts            # GPU capability detection                │
│  ├── workerPool.ts              # Web Worker pool                         │
│  ├── lazyLoader.ts              # Lazy loading system                     │
│  ├── motionBlur.ts (21KB)       # Motion blur post-process               │
│  ├── depthflow.ts (47KB)        # 2.5D parallax                          │
│  └── timelineSnap.ts            # Snap to beats/keyframes                 │
└──────────────────────────────────────────────────────────────────────────────┘
                                       │
                                       ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                          INTEGRATION LAYER                                   │
│                                                                              │
│  ComfyUI Extension:                                                          │
│  ├── web/js/extension.js   # Sidebar registration, loads Vue app           │
│  └── nodes/*.py            # Python nodes for ComfyUI workflows            │
│                                                                              │
│  HTTP Routes: /weyl/compositor/*                                             │
│  ├── POST /set_output      # Send rendered frame to workflow               │
│  ├── POST /save_project    # Save project to disk                          │
│  ├── GET /load_project     # Load project from disk                        │
│  └── GET /assets/:id       # Stream asset file                             │
└──────────────────────────────────────────────────────────────────────────────┘
```

### Data Flow Diagram

```
User Action (e.g., scrub timeline)
        │
        ▼
┌──────────────────┐
│   Vue Component  │  TimelinePanel.vue detects scrub
│   (UI Layer)     │  Calls: compositorStore.setFrame(newFrame)
└────────┬─────────┘
         │
         ▼
┌──────────────────┐
│   Pinia Store    │  compositorStore updates currentFrame
│   (State Layer)  │  Triggers: playbackStore.setFrame()
└────────┬─────────┘
         │
         ▼
┌──────────────────┐
│   MotionEngine   │  MotionEngine.evaluate(frame, project, audio)
│   (Engine Layer) │  PURE FUNCTION - Same input = Same output
└────────┬─────────┘
         │
         ├──────────────────────────────────────────────────────┐
         │                                                      │
         ▼                                                      ▼
┌──────────────────┐                               ┌──────────────────┐
│   Interpolation  │                               │  ParticleSystem  │
│   Service        │                               │  Service         │
│                  │                               │                  │
│ For each layer:  │                               │ 1. Find nearest  │
│ 1. Find keyframes│                               │    checkpoint    │
│ 2. Calculate t   │                               │ 2. Restore RNG   │
│ 3. Apply easing  │                               │ 3. Simulate to   │
│ 4. Interpolate   │                               │    target frame  │
└────────┬─────────┘                               └────────┬─────────┘
         │                                                  │
         └──────────────────────┬───────────────────────────┘
                                │
                                ▼
                   ┌──────────────────┐
                   │    FrameState    │  Immutable, frozen object
                   │    (Output)      │  Contains: layers, camera,
                   │                  │  particles, audio features
                   └────────┬─────────┘
                            │
                            ▼
                   ┌──────────────────┐
                   │   WeylEngine     │  engine.applyFrameState(state)
                   │   (Render)       │  Updates Three.js scene
                   └────────┬─────────┘
                            │
                            ▼
                   ┌──────────────────┐
                   │   WebGL Canvas   │  Displayed to user
                   └──────────────────┘
```

---

## THE DETERMINISM RULE (CRITICAL)

### Why Determinism Matters

For AI video generation, every frame must be **reproducible**. If you render frame 50, then scrub to frame 10, then back to frame 50, **you MUST get identical output**. This is non-negotiable.

### The Golden Rule

> **`evaluate(frame, project)` must ALWAYS return identical results for identical inputs.**

### Forbidden Patterns (NEVER USE IN EVALUATION)

```typescript
// ❌ FORBIDDEN - Non-deterministic
Date.now()                    // Time-dependent
performance.now()             // Time-dependent
Math.random()                 // Non-deterministic
requestAnimationFrame()       // For evaluation logic
this.state += delta           // Accumulation
particle.age += dt            // Accumulation
camera.position += velocity   // Accumulation
previousFrame                 // Frame order dependent
lastFrame                     // Frame order dependent
```

### Required Patterns (ALWAYS USE)

```typescript
// ✅ CORRECT - Deterministic
const state = evaluate(frame, project)           // Pure function
const position = interpolate(keyframes, frame)   // Frame-based
const random = seededRNG(seed, frame, id)        // Seeded RNG
Object.freeze(result)                            // Immutable output
```

### Seeded Random Number Generator

We use **Mulberry32** for deterministic randomness:

```typescript
// From particleSystem.ts
export class SeededRandom {
  private state: number;

  constructor(seed: number) {
    this.state = seed;
  }

  next(): number {
    // Mulberry32 algorithm - DETERMINISTIC
    let t = this.state += 0x6D2B79F5;
    t = Math.imul(t ^ t >>> 15, t | 1);
    t ^= t + Math.imul(t ^ t >>> 7, t | 61);
    return ((t ^ t >>> 14) >>> 0) / 4294967296;
  }

  nextRange(min: number, max: number): number {
    return min + this.next() * (max - min);
  }
}
```

### Particle Checkpointing

Particles use a checkpoint system for scrub-safe playback:

```
Frame:     0    30    60    90    120
           │     │     │     │     │
Checkpoints: ●─────●─────●─────●─────●

User scrubs to frame 75:
1. Find nearest checkpoint: frame 60
2. Load checkpoint state (RNG seed, particle positions)
3. Simulate frames 61, 62, 63... 75
4. Result is IDENTICAL regardless of scrub order
```

---

## LAYER SYSTEM

### Layer Types (17 Total)

| Type | Class | Description | Completion |
|------|-------|-------------|------------|
| `image` | ImageLayer | Static images (PNG, JPG, WebP) | 100% |
| `solid` | SolidLayer | Solid color rectangles | 100% |
| `null` | NullLayer | Invisible parent for grouping | 100% |
| `text` | TextLayer | Animated text with fonts | 95% |
| `spline` | SplineLayer | Bezier curves with stroke/fill | 95% |
| `video` | VideoLayer | Video files with frame control | 90% |
| `camera` | CameraLayer | 3D cameras with DOF | 95% |
| `light` | LightLayer | Point, spot, directional lights | 90% |
| `particle` | ParticleLayer | Particle emitters | 90% |
| `precomp` | PrecompLayer | Nested compositions | 90% |
| `adjustment` | AdjustmentLayer | Effect-only layer | 85% |
| `procedural_matte` | ProceduralMatteLayer | Generated masks | 85% |
| `shape` | ShapeLayer | Vector shapes | 80% |
| `model` | ModelLayer | 3D models (glTF, OBJ) | 75% |
| `depthflow` | DepthflowLayer | 2.5D parallax | 70% |
| `point_cloud` | PointCloudLayer | Point cloud data | 60% |

### Layer Properties

Every layer has these standard properties:

```typescript
interface Layer {
  id: string;                    // Unique identifier
  name: string;                  // Display name
  type: LayerType;               // One of 17 types
  enabled: boolean;              // Visibility toggle
  locked: boolean;               // Edit lock
  solo: boolean;                 // Solo mode

  // Timing
  inPoint: number;               // First visible frame
  outPoint: number;              // Last visible frame

  // Transform (all animatable)
  transform: {
    position: AnimatableProperty<Vec3>;
    rotation: AnimatableProperty<Vec3>;
    scale: AnimatableProperty<Vec3>;
    anchor: AnimatableProperty<Vec3>;
    opacity: AnimatableProperty<number>;
  };

  // Rendering
  blendMode: BlendMode;          // 27 modes
  effects: EffectInstance[];     // Effect stack
  masks: Mask[];                 // Mask stack

  // Layer-specific data
  data: LayerSpecificData;
}
```

### Transform Order

Transforms are applied in this order (matching After Effects):

```
1. Translate by -anchor (move origin to anchor point)
2. Scale
3. Rotate Z
4. Rotate Y
5. Rotate X
6. Translate by position
```

```typescript
// From math3d.ts
function composeTransformMatrix(
  position: Vec3,
  rotation: Vec3,
  scale: Vec3,
  anchor: Vec3
): Mat4 {
  const m = mat4.create();
  mat4.translate(m, m, [position.x, position.y, position.z]);
  mat4.rotateX(m, m, rotation.x * DEG_TO_RAD);
  mat4.rotateY(m, m, rotation.y * DEG_TO_RAD);
  mat4.rotateZ(m, m, rotation.z * DEG_TO_RAD);
  mat4.scale(m, m, [scale.x, scale.y, scale.z]);
  mat4.translate(m, m, [-anchor.x, -anchor.y, -anchor.z]);
  return m;
}
```

---

## ANIMATION SYSTEM

### Keyframe Structure

```typescript
interface Keyframe<T> {
  frame: number;                 // Frame number (0-based)
  value: T;                      // Value at this frame
  interpolation: 'linear' | 'bezier' | 'hold';

  // Bezier handles (for 'bezier' interpolation)
  inHandle?: Vec2;               // Incoming tangent
  outHandle?: Vec2;              // Outgoing tangent

  // Handle linking mode
  controlMode: 'linked' | 'free' | 'auto';

  // For spatial properties (position)
  spatialInTangent?: Vec3;
  spatialOutTangent?: Vec3;
}
```

### Interpolation Process

```
Frame 30 with keyframes at 0 and 60:

1. Find surrounding keyframes
   prev = keyframe at frame 0
   next = keyframe at frame 60

2. Calculate local t
   t = (30 - 0) / (60 - 0) = 0.5

3. Apply easing (if bezier)
   easedT = cubicBezier(t, prev.outHandle, next.inHandle)

4. Interpolate value
   value = lerp(prev.value, next.value, easedT)
```

### Easing Functions (35 Total)

```typescript
// Categories
const EASING_PRESETS = {
  // Linear
  'linear': (t) => t,

  // Sine
  'easeInSine': (t) => 1 - Math.cos((t * Math.PI) / 2),
  'easeOutSine': (t) => Math.sin((t * Math.PI) / 2),
  'easeInOutSine': (t) => -(Math.cos(Math.PI * t) - 1) / 2,

  // Quad
  'easeInQuad': (t) => t * t,
  'easeOutQuad': (t) => 1 - (1 - t) * (1 - t),
  'easeInOutQuad': (t) => t < 0.5 ? 2 * t * t : 1 - (-2 * t + 2) ** 2 / 2,

  // Cubic, Quart, Quint, Expo, Circ, Back, Elastic, Bounce...
  // See easing.ts for full list
};
```

### Expression System

Expressions are JavaScript snippets that dynamically calculate values:

```typescript
// Example expressions
const EXPRESSION_PRESETS = {
  // Wiggle
  'wiggleSubtle': 'wiggle(2, 10)',
  'wiggleMedium': 'wiggle(4, 25)',
  'wiggleIntense': 'wiggle(8, 50)',

  // Time-based
  'pulse': 'Math.sin(time * 2 * Math.PI) * 0.5 + 0.5',
  'sawtooth': '(time % 1)',
  'triangle': 'Math.abs((time * 2) % 2 - 1)',

  // Looping
  'loopCycle': 'loopOut("cycle")',
  'loopPingPong': 'loopOut("pingpong")',

  // Inertia
  'inertiaLight': 'inertia(0.5, 0.3)',
  'inertiaHeavy': 'inertia(0.9, 0.1)',
};

// Expression context provides these functions:
interface ExpressionContext {
  time: number;                  // Current time in seconds
  frame: number;                 // Current frame
  value: T;                      // Current property value

  // Interpolation
  linear(t: number, a: T, b: T): T;
  ease(t: number, a: T, b: T): T;

  // Time functions
  loopIn(type?: string, numKf?: number): T;
  loopOut(type?: string, numKf?: number): T;

  // Motion
  wiggle(freq: number, amp: number): T;
  inertia(friction?: number, elasticity?: number): T;
  bounce(): T;

  // Math
  clamp(val: number, min: number, max: number): number;
  random(seed?: number): number;  // SEEDED - deterministic!
}
```

---

## PARTICLE SYSTEM

### Overview

The particle system is **fully deterministic** using:
- Seeded RNG (Mulberry32 algorithm)
- Checkpoint system every 30 frames
- Pure evaluation function

### Configuration

```typescript
interface ParticleLayerData {
  emitter: EmitterConfig;
  physics: PhysicsConfig;
  forces: ForceConfig[];
  rendering: RenderConfig;
  collision: CollisionConfig;
  subEmitters: SubEmitterConfig[];
}

interface EmitterConfig {
  shape: 'point' | 'line' | 'circle' | 'box' | 'sphere' | 'ring' | 'spline';
  emissionRate: number;          // Particles per frame
  burstCount: number;            // Particles per burst
  maxParticles: number;          // Pool size

  lifetime: { min: number; max: number };
  speed: { min: number; max: number };
  direction: Vec3;
  spread: number;                // Cone angle in degrees

  sizeStart: { min: number; max: number };
  sizeEnd: { min: number; max: number };

  colorStart: RGBA;
  colorEnd: RGBA;
}
```

### Evaluation Flow

```typescript
// From particleSystem.ts
class ParticleSystem {
  evaluate(targetFrame: number): Particle[] {
    // 1. Find nearest checkpoint
    const checkpointFrame = this.getNearestCheckpoint(targetFrame);

    // 2. Restore state from checkpoint
    if (checkpointFrame !== null) {
      this.loadCheckpoint(checkpointFrame);
    } else {
      this.reset();  // Start from frame 0
    }

    // 3. Simulate forward to target frame
    const startFrame = checkpointFrame ?? 0;
    for (let f = startFrame; f <= targetFrame; f++) {
      this.simulateFrame(f);

      // Save checkpoint every 30 frames
      if (f % 30 === 0 && f > 0) {
        this.saveCheckpoint(f);
      }
    }

    // 4. Return current particles (immutable)
    return Object.freeze([...this.particles]);
  }
}
```

### Forces

```typescript
interface ForceConfig {
  // Global forces
  gravity: Vec3;                 // Default: [0, -9.8, 0]
  wind: Vec3;                    // Constant wind
  damping: number;               // Velocity damping (0-1)

  // Gravity wells (attractors)
  gravityWells: Array<{
    position: Vec3;
    strength: number;
    radius: number;
    falloff: 'linear' | 'quadratic' | 'none';
  }>;

  // Vortices
  vortices: Array<{
    position: Vec3;
    axis: Vec3;
    strength: number;
    radius: number;
  }>;

  // Turbulence (Simplex noise)
  turbulence: {
    strength: number;
    scale: number;               // Noise frequency
    speed: number;               // Animation speed
    octaves: number;
  };
}
```

---

## AUDIO REACTIVITY

### Audio Analysis Pipeline

```
Audio File (MP3, WAV, etc.)
        │
        ▼
┌──────────────────┐
│  Web Audio API   │  Decode to PCM samples
│  (OfflineContext)│
└────────┬─────────┘
         │
         ▼
┌──────────────────┐
│  audioWorker.js  │  Heavy processing in background
│  (Web Worker)    │
└────────┬─────────┘
         │
         ▼
┌──────────────────┐
│  Per-Frame Data  │  Pre-computed for all frames
│  (Float32Arrays) │
└────────┬─────────┘
         │
         ├── amplitude[frame]      # Overall loudness (0-1)
         ├── rms[frame]            # Root Mean Square energy
         ├── frequencyBands[frame] # Bass, mid, high
         │   ├── bass              # 20-250 Hz
         │   ├── lowMid            # 250-500 Hz
         │   ├── mid               # 500-2000 Hz
         │   ├── highMid           # 2000-4000 Hz
         │   └── high              # 4000-20000 Hz
         ├── spectralCentroid[frame] # "Brightness"
         ├── beats[frame]          # Beat detection (0 or 1)
         ├── onsets[frame]         # Note onsets (0 or 1)
         └── bpm                   # Detected tempo
```

### Audio-to-Property Mapping

```typescript
interface AudioMapping {
  id: string;
  enabled: boolean;

  // Source
  sourceFeature: 'amplitude' | 'bass' | 'mid' | 'high' | 'beat' | 'spectralCentroid';

  // Target
  targetLayerId: string;
  targetPropertyPath: string;   // e.g., 'transform.scale.x'

  // Transform
  sensitivity: number;          // Multiplier
  smoothing: number;            // Smoothing factor (0-1)
  min: number;                  // Output minimum
  max: number;                  // Output maximum

  // Optional curve
  responseCurve?: 'linear' | 'exponential' | 'logarithmic';
}

// Example: Scale layer based on bass
const bassToScale: AudioMapping = {
  id: 'bass-scale',
  enabled: true,
  sourceFeature: 'bass',
  targetLayerId: 'layer-123',
  targetPropertyPath: 'transform.scale.x',
  sensitivity: 2.0,
  smoothing: 0.3,
  min: 1.0,
  max: 2.0,
  responseCurve: 'exponential'
};
```

---

## 3D CAMERA SYSTEM

### Camera Properties

```typescript
interface CameraLayerData {
  cameraType: 'perspective' | 'orthographic';

  // Lens
  fov: AnimatableProperty<number>;        // Field of view (degrees)
  near: number;                            // Near clip plane
  far: number;                             // Far clip plane

  // Depth of Field
  dof: {
    enabled: boolean;
    focusDistance: AnimatableProperty<number>;
    aperture: AnimatableProperty<number>;
    focalLength: number;
    bokehScale: number;
  };

  // Trajectory
  trajectory?: {
    preset: string;              // e.g., 'orbit', 'dolly', 'crane'
    progress: AnimatableProperty<number>;  // 0-1 along path
  };
}
```

### Camera Trajectory Presets (22 Total)

| Category | Presets |
|----------|---------|
| **Orbital** | orbit, orbitTilt, orbitVertical, figurEight |
| **Linear** | dollyIn, dollyOut, truckLeft, truckRight, pedestalUp, pedestalDown |
| **Crane** | craneUp, craneDown, craneArc |
| **Cinematic** | reveal, pushIn, pullBack, whipPan |
| **Dynamic** | spiral, zigzag, bounce, shake |
| **Custom** | Custom bezier path |

### Usage Example

```typescript
// Apply camera trajectory
const camera = compositorStore.getLayer(cameraId);
camera.data.trajectory = {
  preset: 'orbit',
  progress: {
    defaultValue: 0,
    animated: true,
    keyframes: [
      { frame: 0, value: 0, interpolation: 'bezier' },
      { frame: 80, value: 1, interpolation: 'bezier' }
    ]
  }
};
```

---

## EFFECT PIPELINE

### Effect Stack Processing

Effects are processed top-to-bottom on each layer:

```
Layer Content (e.g., image)
        │
        ▼
┌──────────────────┐
│   Effect 1       │  e.g., Brightness/Contrast
│   (Top of stack) │
└────────┬─────────┘
         │
         ▼
┌──────────────────┐
│   Effect 2       │  e.g., Gaussian Blur
└────────┬─────────┘
         │
         ▼
┌──────────────────┐
│   Effect 3       │  e.g., Drop Shadow
│   (Bottom)       │
└────────┬─────────┘
         │
         ▼
Final Layer Output
```

### Available Effects (22 Total)

| Category | Effects |
|----------|---------|
| **Blur** | Gaussian, Directional, Radial, Box, Sharpen |
| **Color** | Brightness/Contrast, Hue/Saturation, Levels, Tint, Curves, Glow, Drop Shadow, Color Balance, Exposure, Vibrance, Invert, Posterize, Threshold |
| **Distort** | Transform, Warp, Displacement Map |
| **Generate** | Fill, Gradient Ramp, Fractal Noise |

### Effect Parameter Animation

All effect parameters are animatable:

```typescript
interface EffectInstance {
  id: string;
  effectKey: string;             // e.g., 'gaussian-blur'
  enabled: boolean;
  category: 'blur' | 'color' | 'distort' | 'generate';

  parameters: {
    [key: string]: AnimatableProperty<number | Vec2 | Vec3 | Color>;
  };
}

// Example: Animated blur
const blurEffect: EffectInstance = {
  id: 'blur-1',
  effectKey: 'gaussian-blur',
  enabled: true,
  category: 'blur',
  parameters: {
    radius: {
      defaultValue: 0,
      animated: true,
      keyframes: [
        { frame: 0, value: 0, interpolation: 'linear' },
        { frame: 30, value: 20, interpolation: 'bezier' },
        { frame: 60, value: 0, interpolation: 'linear' }
      ]
    },
    direction: { defaultValue: 0, animated: false }
  }
};
```

---

## KEY FILE LOCATIONS

### Engine Files

| File | Size | Purpose |
|------|------|---------|
| `engine/WeylEngine.ts` | 2400+ lines | Main engine facade |
| `engine/MotionEngine.ts` | 800 lines | Pure frame evaluation |
| `engine/core/CameraController.ts` | 600 lines | Camera controls |
| `engine/core/LayerManager.ts` | 500 lines | Layer management |
| `engine/layers/BaseLayer.ts` | 54KB | Abstract base class |

### Service Files (Top 10 by Importance)

| File | Size | Purpose |
|------|------|---------|
| `services/interpolation.ts` | 21KB | Keyframe interpolation |
| `services/particleSystem.ts` | 76KB | Particle simulation |
| `services/audioFeatures.ts` | 36KB | Audio analysis |
| `services/expressions.ts` | 35KB | Expression language |
| `services/propertyDriver.ts` | 25KB | Property linking |
| `services/effectProcessor.ts` | 13KB | Effect pipeline |
| `services/cameraTrajectory.ts` | 17KB | Camera presets |
| `services/matteExporter.ts` | 15KB | Export pipeline |
| `services/arcLength.ts` | 8KB | Path parameterization |
| `services/easing.ts` | 8KB | 35 easing functions |

### Store Files

| File | Size | Purpose |
|------|------|---------|
| `stores/compositorStore.ts` | 90KB | Main store |
| `stores/playbackStore.ts` | 5KB | Playback state |
| `stores/selectionStore.ts` | 4KB | Selection state |
| `stores/historyStore.ts` | 6KB | Undo/redo |

---

## COMMON TASKS GUIDE

### Adding a New Layer Type

1. Create layer class in `engine/layers/`:
```typescript
// engine/layers/MyLayer.ts
export class MyLayer extends BaseLayer {
  type = 'my-layer' as const;

  createThreeObject(): THREE.Object3D {
    // Create Three.js representation
  }

  evaluate(frame: number): EvaluatedLayer {
    // Evaluate at frame
  }

  dispose(): void {
    // Cleanup resources
  }
}
```

2. Register in LayerManager
3. Add to compositorStore.addLayer()
4. Create properties component

### Adding a New Effect

1. Create renderer in `services/effects/`:
```typescript
// services/effects/myEffect.ts
export function renderMyEffect(
  input: ImageData,
  params: MyEffectParams,
  frame: number
): ImageData {
  // Process image
  return output;
}
```

2. Register in effectProcessor.ts
3. Add to EFFECT_DEFINITIONS
4. Create parameter controls in EffectProperties.vue

### Adding a Keyboard Shortcut

In `components/layout/WorkspaceLayout.vue`:
```typescript
function handleKeyDown(e: KeyboardEvent) {
  // Check for text input focus
  if (isInputFocused()) return;

  switch (e.key) {
    case 'Delete':
      e.preventDefault();
      deleteSelectedLayers();
      break;
    case ' ':
      e.preventDefault();
      playbackStore.togglePlayback();
      break;
    // Add your shortcut here
  }
}
```

---

## TROUBLESHOOTING

### Common Issues

#### "Animation not playing"
1. Check `playbackStore.isPlaying` is true
2. Verify `currentFrame < frameCount`
3. Ensure composition has layers
4. Check browser tab is focused (RAF pauses in background)

#### "Layer not visible"
1. Check `layer.visible === true`
2. Verify `currentFrame` between `inPoint` and `outPoint`
3. Check opacity is not 0
4. Verify layer is not behind other layers

#### "Particle positions change on scrub"
1. Ensure using `SeededRandom`, not `Math.random()`
2. Check checkpoint system is working
3. Verify seed is consistent

#### "Audio reactivity not working"
1. Load audio file in AudioPanel
2. Wait for analysis to complete
3. Check audio mapping is enabled
4. Verify target property path is correct

#### "WebGL context lost"
1. Too many contexts open - close other tabs
2. GPU memory exhausted - reduce texture sizes
3. Add context loss handler

### Debug Commands (Browser Console)

```javascript
// Get store state
const store = useCompositorStore();
console.log('currentFrame:', store.currentFrame);
console.log('layers:', store.activeComposition?.layers);

// Force re-render
store.markAllDirty();
store.requestRender();

// Check cache stats
const stats = getEvaluationCacheStats();
console.log('cache hits:', stats.hits, 'misses:', stats.misses);
```

---

## KNOWN ISSUES & WORKAROUNDS

### TypeScript Errors (26 in test files)

All errors are in test files due to missing required fields:

| File | Fix |
|------|-----|
| `effectProcessor.test.ts` | Add `category: 'blur'` to effect instances |
| `interpolation.test.ts` | Add `controlMode: 'linked'` to keyframes |
| `matteExporter.test.ts` | Use `ControlPoint` import, add required fields |

### Security Issues (6 total)

| Issue | Location | Fix |
|-------|----------|-----|
| API keys in client | MotionIntentResolver.ts | Move to backend proxy |
| Extension-only file validation | AssetUploader.vue | Add MIME type check |
| Unsanitized font URLs | fontService.ts | Whitelist font families |

### Performance Issues (5 critical)

| Issue | Location | Fix |
|-------|----------|-----|
| JSON.parse for history | historyStore.ts | Use structuredClone() |
| O(n) LRU eviction | frameCache.ts | Use Set + LinkedList |
| setInterval leak | WorkspaceLayout.vue | Add clearInterval |

---

## DOCUMENTATION INDEX

### Primary Documents

| Document | Purpose |
|----------|---------|
| **CLAUDE.md** | This file - complete guide |
| **HANDOFF.md** | Detailed knowledge transfer (20 parts) |
| **README.md** | Project overview |

### Architecture & API

| Document | Purpose |
|----------|---------|
| `docs/ARCHITECTURE.md` | System diagrams, data flow |
| `docs/SERVICE_API_REFERENCE.md` | Service API index |
| `docs/SERVICE_API_*.md` (10 files) | Category-specific APIs |
| `docs/EFFECT_PARAMETERS.md` | Effect documentation |

### Reference & Troubleshooting

| Document | Purpose |
|----------|---------|
| `docs/GLOSSARY.md` | 150+ term definitions |
| `docs/DEBUG_TROUBLESHOOTING.md` | Common issues & solutions |
| `docs/TEST_COVERAGE_MAP.md` | Test documentation |
| `docs/COMPONENT_STORE_SERVICE_MAP.md` | Component dependencies |

### Specifications

| Document | Purpose |
|----------|---------|
| `docs/00_MASTER_GROUND_TRUTH.md` | Core requirements |
| `docs/01_TYPE_DEFINITIONS.md` | TypeScript types |
| `docs/02_MOTION_ENGINE.md` | Engine spec |
| `docs/03_LAYER_SYSTEM.md` - `16_*.md` | System specs |

---

## GIT STATUS & RECENT CHANGES

### Current Branch: master

### Recent Commits
```
cfead8f CLAUDE.md v4.0: Comprehensive update with accurate metrics
5e19f17 Split SERVICE_API_REFERENCE.md and add comprehensive handoff documentation
d4300de Add comprehensive documentation suite for handoff
08efce1 3D System and Particle Overhaul
e7044be Sprint 2: Store refactoring, testing infrastructure
```

### Modified (Uncommitted)
```
ui/src/engine/WeylEngine.ts
ui/src/engine/core/CameraController.ts
ui/src/engine/core/LayerManager.ts
ui/src/engine/layers/BaseLayer.ts
ui/src/services/audioFeatures.ts
ui/src/services/effects/blurRenderer.ts
ui/src/services/interpolation.ts
ui/src/services/particleSystem.ts
ui/src/stores/compositorStore.ts
```

### Untracked (New Files)
```
ui/src/engine/MotionEngine.ts
ui/src/engine/ParticleSimulationController.ts
ui/src/__tests__/engine/MotionEngine.test.ts
ui/src/__tests__/engine/ParticleSimulationController.test.ts
```

---

## TECH STACK REFERENCE

| Category | Technology | Version | Purpose |
|----------|------------|---------|---------|
| **Framework** | Vue | 3.5.x | UI framework |
| **State** | Pinia | 2.2.x | State management |
| **UI Components** | PrimeVue | 4.2.x | Component library |
| **3D Rendering** | Three.js | r170 | WebGL rendering |
| **Build Tool** | Vite | 5.x | Build & dev server |
| **Testing** | Vitest | 1.x | Test framework |
| **Language** | TypeScript | 5.x | Type safety |
| **Curves** | Bezier.js | 6.1.x | Bezier math |
| **3D Text** | troika-three-text | 0.52.x | Text rendering |
| **Noise** | simplex-noise | 4.0.x | Procedural noise |
| **Video Export** | mp4-muxer | 5.2.x | MP4 encoding |
| **Archive** | JSZip | 3.10.x | ZIP creation |

---

## FINAL NOTES

### For Next Claude Session

1. **Read this file completely** - It contains everything you need
2. **Check HANDOFF.md** for detailed issue lists and fixes
3. **Run `npm test`** to verify current state
4. **Run `npx tsc --noEmit`** to see TypeScript errors (all in tests)
5. **Focus on determinism** - This is the #1 priority

### For Human Developers

This project is for the **open source ComfyUI community**. The goal is professional-grade motion graphics accessible to everyone.

**Repository**: `https://github.com/justinfleek/weyl-compositor`

**Local Path**: `/mnt/c/Users/justi/Desktop/Compositor`

---

**Document Version:** 5.0 FINAL
**Last Updated:** December 19, 2024
**Total Lines:** ~1200
**Estimated Reading Time:** 30-45 minutes
