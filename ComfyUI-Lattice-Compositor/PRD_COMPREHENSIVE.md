# Lattice Compositor - Comprehensive Product Requirements Document

**Version:** 2.0  
**Status:** Pre-Release (Alpha)  
**Last Updated:** February 2026  
**Document Type:** Consolidated PRD (merges PRD.md, specs/, PROJECT_STATUS.md, SECURITY_ASSESSMENT.md)

---

## Table of Contents

1. [Executive Summary](#1-executive-summary)
2. [Vision & Philosophy](#2-vision--philosophy)
3. [Target Users & Use Cases](#3-target-users--use-cases)
4. [Feature Specifications](#4-feature-specifications)
5. [API & Data Contracts](#5-api--data-contracts)
6. [Technical Requirements](#6-technical-requirements)
7. [Security Requirements](#7-security-requirements)
8. [Roadmap & Milestones](#8-roadmap--milestones)
9. [Appendices](#9-appendices)

---

# 1. Executive Summary

## 1.1 What is Lattice?

Lattice Compositor is a **professional motion graphics engine** built as a **ComfyUI extension**. It brings industry-standard animation tools directly into AI video generation workflows, enabling creators to produce conditioning data (depth maps, motion trajectories, attention masks) that AI video models consume.

## 1.2 The Problem

AI video creators need conditioning data for models like Wan 2.1, AnimateDiff, MotionCtrl, and VACE. Creating this data currently requires:
- Jumping between multiple tools (professional compositors, 3D software, custom scripts)
- Manual export/import workflows
- Technical knowledge of each model's input format
- No real-time preview of how animations will affect AI output

## 1.3 The Solution

Lattice provides:
- **One-click export** to 20+ AI-native formats
- **Industry-standard tools** (keyframes, bezier curves, particles, expressions)
- **Direct ComfyUI integration** (no export/import dance)
- **AI agent** for natural language animation ("fade in the title over 1 second")
- **Deterministic rendering** (every frame reproducible for AI workflows)

## 1.4 Current Status

| Metric | Value |
|--------|-------|
| Lines of Code | 290,000+ |
| TypeScript Files | 476 |
| Vue Components | 157 |
| Service Files | 181 |
| Python Files | 26 |
| Tests Passing | 4,275+ |
| Layer Types | 17 |
| Effects | 22 categories |
| Export Formats | 20+ |

## 1.5 Release Status

| Phase | Status | Notes |
|-------|--------|-------|
| Alpha | **CURRENT** | Core compositor functional, basic exports working |
| Beta | Pending | Security Phase 1+2 required (7-10 weeks) |
| v1.0 | Pending | Production hardening, documentation complete |

---

# 2. Vision & Philosophy

## 2.1 Core Principles

### Determinism by Design
Every frame MUST be reproducible. This is critical for AI video workflows.

```
evaluate(frame, project) === evaluate(frame, project)  // ALWAYS TRUE
```

Implementation:
- **Seeded RNG** - Mulberry32 algorithm for all randomness
- **Checkpoint System** - Particles restore state on scrub
- **Pure Evaluation** - No `Math.random()`, no `Date.now()`, no accumulation

### AI-Native Export
One-click export to formats AI models actually consume:
- Matte sequences for IP Adapter attention masks
- Camera trajectories for MotionCtrl
- Point paths for Wan Move
- 20+ formats total

### Professional Tools, Zero Cost
The full professional toolkit, open source:
- Keyframe animation with 35 easing functions
- Bezier curve editor with handle manipulation
- Particle systems with 24 presets
- Expression language (wiggle, bounce, inertia)
- 3D camera with depth of field

### Math-First Rendering
Splines, curves, particles are fundamentally mathematical. Compute on GPU where possible using shaders, not rasterization.

### No Unnecessary Dependencies
The compositor works with zero AI models loaded if the user just wants to draw splines and animate text. AI features are opt-in.

## 2.2 The Frame Count Formula

AI video models require frame counts following `frames = (seconds × 16) + 1`:

| Duration | Frames |
|----------|--------|
| 1 second | 17 |
| 2 seconds | 33 |
| 3 seconds | 49 |
| 5 seconds | **81 (default)** |
| 10 seconds | 161 |

---

# 3. Target Users & Use Cases

## 3.1 User Personas

### Persona 1: AI Video Creator (Primary)
**Name:** Alex  
**Background:** Creates AI-generated videos using Stable Diffusion workflows  
**Technical Level:** Intermediate (comfortable with ComfyUI, not a programmer)  
**Goals:**
- Create motion trajectories for Wan 2.1 without learning complex software
- Generate attention masks for IP Adapter
- Iterate quickly on camera movements

**Pain Points:**
- Current workflow requires 5+ tools
- Export formats are confusing
- Can't preview how animation affects AI output

### Persona 2: Motion Designer
**Name:** Maya  
**Background:** Professional motion graphics designer, experienced with industry tools  
**Technical Level:** Advanced (knows animation principles deeply)  
**Goals:**
- Use familiar tools in AI workflows
- Create complex particle effects for AI video
- Maintain precise control over timing

**Pain Points:**
- Traditional compositors don't export to AI formats
- AI video tools lack professional animation features
- Can't use expressions in current AI workflows

### Persona 3: VFX Artist
**Name:** Jordan  
**Background:** Visual effects for film/TV, uses Nuke/Fusion  
**Technical Level:** Expert  
**Goals:**
- Create depth-based compositing with AI segmentation
- Generate mattes for rotoscoping workflows
- Integrate AI models into existing pipeline

**Pain Points:**
- AI segmentation tools are disconnected from compositing
- No depth-aware animation tools
- Export format compatibility issues

### Persona 4: Content Creator
**Name:** Sam  
**Background:** YouTube/TikTok creator, self-taught  
**Technical Level:** Beginner  
**Goals:**
- Create animated titles without learning complex software
- Use AI to speed up video production
- Quick motion graphics for social media

**Pain Points:**
- Professional tools too expensive/complex
- Free tools lack features
- AI tools have steep learning curve

## 3.2 User Stories

### US-001: Create Motion Trajectory for Wan 2.1
**As** an AI video creator  
**I want** to draw a motion path and export it as Wan Move coordinates  
**So that** I can control object movement in my AI-generated video

**Acceptance Criteria:**
- [ ] Can draw bezier spline on canvas
- [ ] Can animate object along spline path
- [ ] Can export to Wan Move JSON format
- [ ] Export matches Wan 2.1 coordinate system exactly

### US-002: Generate Attention Mask Sequence
**As** an AI video creator  
**I want** to create animated shapes that export as matte sequences  
**So that** IP Adapter knows which areas to focus on per frame

**Acceptance Criteria:**
- [ ] Can create shape/text layers
- [ ] Can animate opacity, position, scale
- [ ] Can export as PNG sequence (white on black)
- [ ] Resolution matches composition settings

### US-003: Animate Camera for MotionCtrl
**As** a motion designer  
**I want** to create 3D camera movements and export to MotionCtrl format  
**So that** my AI video has cinematic camera motion

**Acceptance Criteria:**
- [ ] Can create 3D camera with position/rotation keyframes
- [ ] Can use camera presets (orbit, dolly, crane)
- [ ] Can export to MotionCtrl JSON format
- [ ] Camera matrices are mathematically correct

### US-004: Create Particle Effect for AI Video
**As** a VFX artist  
**I want** to create deterministic particle effects  
**So that** I can scrub the timeline without particles changing

**Acceptance Criteria:**
- [ ] Particles render identically on each scrub
- [ ] Can export particle layer as matte sequence
- [ ] Particle state checkpoints every 30 frames
- [ ] Performance maintains 30fps with 10,000 particles

### US-005: Use Natural Language for Animation
**As** a content creator  
**I want** to describe animations in plain English  
**So that** I can create motion graphics without learning keyframes

**Acceptance Criteria:**
- [ ] Can type "fade in the title over 1 second"
- [ ] AI agent creates appropriate keyframes
- [ ] Can refine with "make it faster"
- [ ] Agent uses correct easing functions

### US-006: Import Depth Map and Create Parallax
**As** an AI video creator  
**I want** to load a depth map and create 2.5D parallax animation  
**So that** my still image has depth-based movement

**Acceptance Criteria:**
- [ ] Can load depth map from ComfyUI node
- [ ] Layers parallax based on depth values
- [ ] Camera movement creates realistic depth effect
- [ ] Can export camera trajectory for AI model

### US-007: Sync Animation to Music
**As** a content creator  
**I want** to make my animations react to music beats  
**So that** my motion graphics feel connected to the audio

**Acceptance Criteria:**
- [ ] Can load audio file
- [ ] Beat detection identifies beats automatically
- [ ] Can map beat intensity to any property
- [ ] Can snap keyframes to detected beats

### US-008: Create Text Animation Along Path
**As** a motion designer  
**I want** to animate text along a curved path  
**So that** I can create professional title sequences

**Acceptance Criteria:**
- [ ] Can draw bezier path
- [ ] Text follows path with correct orientation
- [ ] Can animate text offset along path
- [ ] Supports Google Fonts and system fonts

---

# 4. Feature Specifications

## 4.1 Layer System (17 Types)

### 4.1.1 Layer Type Reference

| Layer Type | Description | Key Properties | Status |
|------------|-------------|----------------|--------|
| **image** | Static images (PNG, JPG, WebP, GIF) | source, opacity, blendMode | ✅ Complete |
| **video** | Video files with frame-accurate playback | source, startFrame, playbackSpeed | ✅ Complete |
| **solid** | Solid color rectangles | color, width, height | ✅ Complete |
| **text** | Animated text with fonts | text, fontFamily, fontSize, pathLayerId | ✅ Complete |
| **spline** | Bezier curves with stroke/fill | controlPoints, stroke, strokeWidth, fill | ✅ Complete |
| **shape** | Vector shapes with boolean operations | pathData, fill, stroke, booleanOp | ⚠️ Simplified |
| **particle** | Deterministic particle emitters | emitter, physics, rendering, texture | ✅ Complete |
| **camera** | 3D cameras with depth-of-field | focalLength, aperture, focusDistance | ✅ Complete |
| **light** | Point, spot, directional lights | type, color, intensity, range | ✅ Complete |
| **null** | Invisible parent for grouping | (transform only) | ✅ Complete |
| **precomp** | Nested compositions | compositionId | ✅ Complete |
| **adjustment** | Effect-only layers | effects[] | ✅ Complete |
| **procedural_matte** | Generated masks | mode, parameters | ✅ Complete |
| **depthflow** | Depth map with 2.5D parallax | depthSource, parallaxStrength | ✅ Complete |
| **model** | 3D model import (glTF, OBJ, FBX) | modelSource, materials | ⚠️ Partial |
| **point_cloud** | Point cloud visualization | pointData, pointSize | ⚠️ Partial |
| **generated** | AI-generated content layers | generationType, prompt | ✅ Complete |

### 4.1.2 Common Layer Properties

Every layer has these base properties:

```typescript
interface Layer {
  id: string;                    // UUID v5
  name: string;                  // User-visible name
  type: LayerType;               // One of 17 types
  visible: boolean;              // Visibility toggle
  locked: boolean;               // Lock for editing
  solo: boolean;                 // Solo mode
  inPoint: number;               // Start frame (0-based)
  outPoint: number;              // End frame (inclusive)
  parentId: string | null;       // Parent layer for hierarchy
  blendMode: BlendMode;          // One of 27 blend modes
  opacity: AnimatableProperty<number>;  // 0-100
  transform: LayerTransform;     // Position, scale, rotation, anchor
  effects: EffectInstance[];     // Effect stack
}
```

### 4.1.3 Transform System (3D)

```typescript
interface LayerTransform {
  position: AnimatableProperty<Vector3>;      // XYZ position
  anchor: AnimatableProperty<Vector3>;        // XYZ anchor point
  scale: AnimatableProperty<Vector3>;         // XYZ scale (100 = 100%)
  rotation: AnimatableProperty<Vector3>;      // XYZ rotation (Euler degrees)
  orientation?: AnimatableProperty<Vector3>;  // 3D orientation (quaternion-based)
}

interface Vector3 {
  x: number;
  y: number;
  z: number;
}
```

### 4.1.4 Blend Modes (27 Total)

Full industry-standard compatibility:

| Category | Modes |
|----------|-------|
| Normal | normal, dissolve |
| Darken | darken, multiply, colorBurn, linearBurn, darkerColor |
| Lighten | lighten, screen, colorDodge, linearDodge, lighterColor |
| Contrast | overlay, softLight, hardLight, vividLight, linearLight, pinLight, hardMix |
| Inversion | difference, exclusion, subtract, divide |
| Component | hue, saturation, color, luminosity |

## 4.2 Animation System

### 4.2.1 Keyframe System

```typescript
interface Keyframe<T> {
  id: string;
  frame: number;                           // 0-based frame index
  value: T;                                // Property value at this frame
  interpolation: InterpolationType;        // linear, bezier, hold, auto-bezier, continuous-bezier
  inHandle: BezierHandle;                  // Incoming tangent
  outHandle: BezierHandle;                 // Outgoing tangent
  controlMode: 'linked' | 'split';         // Handle linking
  temporalEase: EaseValue[];               // Per-axis ease
  spatialTangent?: Vector3;                // Motion path tangents
}

interface BezierHandle {
  x: number;  // 0-1, time influence (cannot go backwards)
  y: number;  // Unbounded, value influence (can overshoot)
}
```

### 4.2.2 Easing Functions (35 Total)

| Category | Functions |
|----------|-----------|
| Linear | linear |
| Quad | easeInQuad, easeOutQuad, easeInOutQuad |
| Cubic | easeInCubic, easeOutCubic, easeInOutCubic |
| Quart | easeInQuart, easeOutQuart, easeInOutQuart |
| Quint | easeInQuint, easeOutQuint, easeInOutQuint |
| Sine | easeInSine, easeOutSine, easeInOutSine |
| Expo | easeInExpo, easeOutExpo, easeInOutExpo |
| Circ | easeInCirc, easeOutCirc, easeInOutCirc |
| Back | easeInBack, easeOutBack, easeInOutBack |
| Elastic | easeInElastic, easeOutElastic, easeInOutElastic |
| Bounce | easeInBounce, easeOutBounce, easeInOutBounce |
| Spring | spring (custom damping/stiffness) |

### 4.2.3 Expression Language

Expressions run in SES (Secure EcmaScript) sandbox:

```javascript
// Available functions
wiggle(frequency, amplitude)           // Random oscillation
bounce(elasticity, gravity)            // Bounce physics
inertia(friction)                      // Momentum after keyframe
repeatAfter(startFrame, duration)      // Loop section
elastic(amplitude, frequency, decay)   // Elastic motion
noise(t, seed)                         // Perlin noise
random(min, max, seed)                 // Seeded random (deterministic!)

// Available properties
time                    // Current time in seconds
frame                   // Current frame number
value                   // Current property value
thisProperty            // Reference to this property
thisLayer               // Reference to this layer
comp                    // Reference to composition
```

### 4.2.4 Property Linking (PropertyLink)

Connect properties across layers:

```typescript
interface PropertyLink {
  id: string;
  sourceLayerId: string;
  sourcePropertyPath: string;    // e.g., "transform.position.x"
  targetLayerId: string;
  targetPropertyPath: string;
  expression?: string;           // Optional transform: "value * 0.5"
}
```

## 4.3 Particle System

### 4.3.1 Architecture

- **CPU Simulation**: SeededRandom (Mulberry32) for determinism
- **GPU Rendering**: WebGL2 Transform Feedback for performance
- **Checkpoint System**: State saved every 30 frames for instant scrubbing

### 4.3.2 Emitter Types

| Type | Description | Key Parameters |
|------|-------------|----------------|
| point | Single emission point | position |
| line | Emit along line segment | start, end |
| circle | Emit from circle edge | center, radius |
| box | Emit within rectangle | position, width, height |
| sphere | Emit from sphere surface | center, radius |
| ring | Emit from ring | center, innerRadius, outerRadius |
| spline | Emit along bezier path | pathLayerId |

### 4.3.3 Physics Forces

| Force | Description | Parameters |
|-------|-------------|------------|
| gravity | Constant downward force | strength, direction |
| wind | Constant directional force | strength, direction, turbulence |
| turbulence | Perlin noise displacement | strength, scale, speed |
| attractor | Pull toward point | position, strength, falloff |
| vortex | Spiral around axis | position, strength, axis |
| drag | Air resistance | coefficient |

### 4.3.4 Presets (24 Built-in)

| Category | Presets |
|----------|---------|
| Fire | fire, campfire, torch, explosion |
| Smoke | smoke, steam, fog, mist |
| Weather | rain, snow, hail, leaves |
| Magic | sparkle, fairy_dust, magic_trail, portal |
| Celebration | confetti, fireworks, bubbles, balloons |
| Nature | fireflies, dust, pollen, embers |

## 4.4 3D Camera System

### 4.4.1 Camera Properties

```typescript
interface CameraSettings {
  focalLength: AnimatableProperty<number>;      // mm (default: 50)
  aperture: AnimatableProperty<number>;         // f-stop (default: 2.8)
  focusDistance: AnimatableProperty<number>;    // units (default: 1000)
  depthOfField: boolean;                        // Enable DOF blur
  projection: 'perspective' | 'orthographic';
  near: number;                                 // Near clip plane
  far: number;                                  // Far clip plane
}
```

### 4.4.2 Camera Presets (22 Total)

| Category | Presets |
|----------|---------|
| Orbit | orbit_cw, orbit_ccw, orbit_tilt |
| Dolly | dolly_in, dolly_out, dolly_left, dolly_right |
| Crane | crane_up, crane_down, crane_arc |
| Pan/Tilt | pan_left, pan_right, tilt_up, tilt_down |
| Reveal | reveal_left, reveal_right, reveal_up |
| Spiral | spiral_in, spiral_out |
| Shake | handheld, earthquake, subtle |
| Custom | bezier_path |

### 4.4.3 Camera Enhancements

| Feature | Description |
|---------|-------------|
| Depth of Field | Bokeh blur based on focus distance |
| Camera Shake | Procedural shake with frequency/amplitude |
| Rack Focus | Animated focus distance |
| Motion Blur | Per-frame motion blur |
| Lens Distortion | Barrel/pincushion distortion |

## 4.5 Effect Pipeline (22+ Categories)

### 4.5.1 Effect Categories

| Category | Effects |
|----------|---------|
| **Blur** | gaussian, directional, radial, box, sharpen |
| **Color** | brightness, contrast, hue/saturation, levels, curves, colorBalance, exposure, vibrance |
| **Stylize** | glow, dropShadow, emboss, findEdges, mosaic, posterize |
| **Distort** | transform, warp, displacementMap, turbulentDisplace, meshWarp |
| **Generate** | fill, gradientRamp, fractalNoise, checkerboard |
| **Perspective** | 3dTransform, cornerPin |
| **Time** | motionBlur, echo, pixelMotion |
| **Matte** | matteChoker, simpleChoker, refineMatte |
| **Audio** | audioSpectrum, audioWaveform |

### 4.5.2 Effect Stack Processing

Effects process in order (top to bottom). Each effect receives the output of the previous:

```
Layer → Effect 1 → Effect 2 → Effect 3 → Output
```

### 4.5.3 GPU Effect Dispatch

Effects automatically route to optimal renderer:

| Tier | Renderer | Performance |
|------|----------|-------------|
| WebGPU | Compute shaders | Fastest |
| WebGL2 | Fragment shaders | Fast |
| Canvas2D | CPU fallback | Slowest |

## 4.6 Audio Reactivity

### 4.6.1 Audio Features

| Feature | Description | Use Case |
|---------|-------------|----------|
| amplitude | Overall volume level | Scale, opacity |
| bass | Low frequency energy | Heavy hits |
| mid | Mid frequency energy | Vocals, instruments |
| treble | High frequency energy | Hi-hats, cymbals |
| onset | Attack detection | Trigger events |
| beat | Beat detection | Sync to rhythm |
| spectralCentroid | Brightness measure | Color mapping |
| spectralFlux | Change detection | Motion intensity |
| chroma | Pitch class energy | Musical mapping |

### 4.6.2 Audio-to-Property Mapping

```typescript
interface AudioReactiveMapping {
  audioFeature: AudioFeature;
  targetLayerId: string;
  targetPropertyPath: string;
  sensitivity: number;      // 0-10 (default: 1)
  smoothing: number;        // 0-1 (default: 0.5)
  min: number;              // Output range minimum
  max: number;              // Output range maximum
}
```

### 4.6.3 Stem Separation (Demucs)

Separate audio into stems for independent reactivity:

| Stem | Description |
|------|-------------|
| drums | Percussion elements |
| bass | Bass instruments |
| vocals | Voice/singing |
| other | Everything else |

## 4.7 AI Agent Integration

### 4.7.1 Capabilities

| Capability | Description |
|------------|-------------|
| Layer Creation | "Add a text layer that says Hello" |
| Animation | "Fade in over 1 second" |
| Effects | "Add a glow effect" |
| Keyframing | "Make it bounce at frame 30" |
| Property Editing | "Change the font to Roboto" |
| Composition | "Set resolution to 1080p" |

### 4.7.2 Tool Actions (30+)

| Category | Tools |
|----------|-------|
| Layer | createLayer, deleteLayer, duplicateLayer, renameLayer |
| Transform | setPosition, setScale, setRotation, setAnchor |
| Animation | addKeyframe, removeKeyframe, setEasing |
| Effects | addEffect, removeEffect, setEffectParam |
| Timeline | setInPoint, setOutPoint, moveLayer |
| Composition | setResolution, setFrameCount, setFps |

### 4.7.3 API Support

| Provider | Model | Status |
|----------|-------|--------|
| OpenAI | GPT-4o | ✅ Supported |
| Anthropic | Claude 3.5 | ✅ Supported |

Requires environment variable: `OPENAI_API_KEY` or `ANTHROPIC_API_KEY`


---

# 5. API & Data Contracts

## 5.1 Export Formats (20+)

### 5.1.1 Point/Motion Trajectory Formats

| Format | Target Model | Output Structure |
|--------|--------------|------------------|
| **wan-move** | Wan 2.1 | `{ trackCoords: "[[[x,y],...],...]", metadata: {...} }` |
| **ati** | ATI AudioReactive | `{ tracks: "[[{x,y},...],...]", width, height }` |
| **ttm** | Time-to-Move | `{ layers: [{ motionMask, trajectory }] }` |
| **ttm-wan** | TTM for Wan | Same as ttm with Wan-specific params |
| **ttm-cogvideox** | TTM for CogVideoX | Same as ttm with CogVideoX params |

### 5.1.2 Camera Trajectory Formats

| Format | Target Model | Output Structure |
|--------|--------------|------------------|
| **motionctrl** | MotionCtrl | `{ camera_poses: [{ RT: [[4x4 matrix]] }] }` |
| **motionctrl-svd** | MotionCtrl SVD | `{ motion_camera: "preset_name" }` |
| **animatediff-cameractrl** | AnimateDiff | `{ poses: [{ position, rotation, focal_length }] }` |
| **wan22-fun-camera** | Wan 2.2 | `{ poses: [...], metadata: {...} }` |
| **camera-comfyui** | Generic ComfyUI | `{ frames: [{ view_matrix, projection_matrix }] }` |

### 5.1.3 Matte/Mask Formats

| Format | Use Case | Output |
|--------|----------|--------|
| **png-sequence** | IP Adapter, ControlNet | Folder of PNG files |
| **webm** | Preview/Web | WebM video file |
| **mp4** | Standard video | MP4 video file |

## 5.2 Project File Schema

```typescript
interface LatticeProject {
  version: string;           // Schema version "1.0.0"
  meta: {
    name: string;
    created: string;         // ISO 8601
    modified: string;        // ISO 8601
    author?: string;
  };
  composition: {
    width: number;           // Divisible by 8
    height: number;          // Divisible by 8
    frameCount: number;      // Default 81
    fps: number;             // Default 16
    backgroundColor: string; // Hex color
  };
  assets: Record<string, AssetReference>;
  layers: Layer[];
  audio?: AudioTrack[];
  propertyLinks?: PropertyLink[];
}
```

## 5.3 ComfyUI Integration API

### HTTP Routes

| Route | Method | Purpose |
|-------|--------|---------|
| `/lattice/compositor/set_output` | POST | Send matte data to ComfyUI node |
| `/lattice/compositor/save_project` | POST | Save project state |
| `/lattice/compositor/load_project/{id}` | GET | Load project state |
| `/lattice/generate/depth` | POST | Generate depth map |
| `/lattice/generate/normal` | POST | Generate normal map |
| `/lattice/generate/texture` | POST | Generate SDXL texture |

### WebSocket Events

| Event | Direction | Purpose |
|-------|-----------|---------|
| `lattice.compositor.inputs_ready` | Server→Client | Image/depth data ready |
| `lattice.compositor.export_complete` | Server→Client | Export finished |
| `lattice.compositor.error` | Server→Client | Error notification |

## 5.4 Naming Convention by Export Target

| Export Target | Convention | Examples |
|---------------|------------|----------|
| WanMove | camelCase | `trackCoords`, `numPoints` |
| ATI | camelCase | `tracks`, `numTracks` |
| MotionCtrl | snake_case | `camera_poses`, `focal_length` |
| CameraCtrl | Mixed | `poses`, `focal_length` |
| TTM | camelCase | `layers`, `layerId`, `motionMask` |
| SCAIL | snake_case | `reference_image`, `pose_video` |

---

# 6. Technical Requirements

## 6.1 Technology Stack

| Component | Technology | Version |
|-----------|------------|---------|
| UI Framework | Vue | 3.5.x |
| State Management | Pinia | 2.2.x |
| UI Components | PrimeVue | 4.x |
| 3D Rendering | Three.js | r170 |
| Type Safety | TypeScript | 5.x |
| Build Tool | Vite | 5.x |
| Backend | Python | 3.10+ |
| Testing | Vitest | Latest |

## 6.2 Browser Support

| Browser | Minimum Version | Status |
|---------|-----------------|--------|
| Chrome | 90+ | Primary |
| Firefox | 90+ | Supported |
| Edge | 90+ | Supported |
| Safari | 15+ | Supported |

**Required:** WebGL2 support

## 6.3 Performance Requirements

| Metric | Target | Current |
|--------|--------|---------|
| Preview FPS (100 layers @ 1080p) | 30+ fps | ~30 fps |
| Particle count (realtime) | 10,000 | 10,000 |
| Export speed (1080p frame) | < 100ms | ~80ms |
| Memory usage (large project) | < 2GB | ~1.5GB |
| Initial load time | < 3s | ~2s |

## 6.4 Determinism Requirements

**CRITICAL:** All rendering must be deterministic for AI workflows.

| Requirement | Implementation |
|-------------|----------------|
| No Math.random() | SeededRandom (Mulberry32) |
| No Date.now() | Frame-based timing |
| Particle reproducibility | Checkpoint every 30 frames |
| Expression isolation | SES sandbox |

## 6.5 Dependencies

### Python (requirements.txt)
```
numpy
Pillow
scipy
aiohttp
```

### Optional Python (AI features)
```
torch
torchvision
transformers  # For DepthAnything
```

### Node.js (package.json)
- Vue 3.5+
- Pinia 2.2+
- Three.js r170+
- PrimeVue 4+
- Vitest (dev)

---

# 7. Security Requirements

## 7.1 Current Security Status

**RECOMMENDATION: NOT APPROVED FOR PRODUCTION**

Risk Rating: **CRITICAL**

The engineering foundation is solid, but 8 critical security gaps must be addressed before production deployment.

## 7.2 Critical Security Gaps (Must Fix)

### Gap 1: No Template Validation (CRITICAL)
- **Risk:** Remote code execution from untrusted template/project files
- **Current:** Untrusted files processed with `as Type` casts
- **Required:** Zod schema validation for all external data

### Gap 2: No LLM Scope Boundaries (CRITICAL)
- **Risk:** Arbitrary actions via prompt injection attacks
- **Current:** Autonomous LLM agent lacks scope validation
- **Required:** Tool allowlist, action limits, confirmation for destructive ops

### Gap 3: No Path Traversal Prevention (CRITICAL)
- **Risk:** Read/write arbitrary files on user's machine
- **Current:** File system operations lack path sanitization
- **Required:** Path validation, sandbox to project directory

### Gap 4: No ComfyUI Output Validation (HIGH)
- **Risk:** Data injection from malicious third-party nodes
- **Current:** ComfyUI node outputs trusted without validation
- **Required:** Schema validation for all ComfyUI data

### Gap 5: No JSON Bomb Protection (MEDIUM)
- **Risk:** DoS via resource exhaustion
- **Required:** Depth/size limits on JSON parsing

### Gap 6: No Prototype Pollution Prevention (HIGH)
- **Risk:** Security bypass, property injection attacks
- **Required:** Object.create(null), __proto__ filtering

### Gap 7: No Prompt Injection Detection (MEDIUM)
- **Risk:** LLM hijacking via layer names/content
- **Required:** Input sanitization, boundary enforcement

### Gap 8: Main-thread Expression DoS (MEDIUM)
- **Risk:** Application freeze from infinite loops
- **Required:** Web Worker isolation, CPU time limits

## 7.3 Existing Security Measures

| Measure | Status | Notes |
|---------|--------|-------|
| Expression Sandbox (SES) | ✅ Implemented | Blocks fetch, global access |
| URL Validation | ⚠️ Partial | urlValidator exists |
| Template Signatures | ✅ Implemented | Ed25519 for official templates |
| NaN/Infinity Validation | ⚠️ Partial | Some numeric checks |

## 7.4 Security Implementation Plan

### Phase 1 (Weeks 1-2): 120-165 hours
1. Complete missing Zod schemas (6 directories)
2. Implement safeJsonParse with all protections
3. Replace all `as Type` casts with schema validation
4. Implement path traversal prevention
5. Implement LLM scope system
6. Add prompt injection detection

### Phase 2 (Weeks 3-4): 90-130 hours
7. ComfyUI output validation
8. File system security wrapper
9. Resource exhaustion limits
10. Error boundaries
11. Fix TypeScript errors

### Phase 3 (Weeks 5-6): 60-90 hours (Optional)
12-17. Advanced mitigations (Nix signing, audit logging, worker limits)

**Total Estimate:** 210-295 hours (7-10 weeks)

## 7.5 Attack Surface Summary

| Entry Point | Trust Level | Current Validation |
|-------------|-------------|-------------------|
| Template/Project files | UNTRUSTED | None |
| Preset files | UNTRUSTED | Partial |
| Expression strings | UNTRUSTED | SES sandbox |
| Layer names/properties | UNTRUSTED | None |
| Asset files | UNTRUSTED | None |
| ComfyUI node outputs | UNTRUSTED | None |
| URL imports | UNTRUSTED | Partial |

---

# 8. Roadmap & Milestones

## 8.1 Release Phases

### Alpha (CURRENT)
- [x] Core compositor functional
- [x] 17 layer types implemented
- [x] Basic export working
- [x] AI agent integrated
- [x] 4,275+ tests passing
- [ ] Security gaps unaddressed

### Beta (Target: +10 weeks)
- [ ] Security Phase 1+2 complete
- [ ] All export formats validated
- [ ] Performance optimized
- [ ] Documentation complete
- [ ] TypeScript errors fixed

### v1.0 (Target: +16 weeks)
- [ ] Production security hardening
- [ ] Edge cases handled
- [ ] Community feedback incorporated
- [ ] Tutorial content available

## 8.2 Outstanding TODOs (from codebase audit)

### High Priority - Backend/FFI
| File | TODO | Effort |
|------|------|--------|
| featureFlagsStore.ts | Wire to DuckDB via FFI | Medium |
| chatDatabase.ts | Implement search_chat_history FFI | Medium |
| lattice_api_proxy.py | Actual depth estimation impl | High |
| lattice_api_proxy.py | Actual normal map generation | High |
| lattice_api_proxy.py | Actual segmentation impl | High |
| visual_generation.py | Integrate ComfyUI workflow execution | High |

### Medium Priority - UI/Features
| File | TODO | Effort |
|------|------|--------|
| preprocessorService.ts | renderLayerToCanvas in LatticeEngine | Medium |
| ColorProfileService.ts | Implement deflate decompression | Low |
| WorkspaceLayout.vue | Allow user to save frames | Low |
| ExportPanel.vue | Check ComfyUI backend availability | Low |

### Low Priority - Tests
| File | TODO | Effort |
|------|------|--------|
| memory.test.ts | Effect processing API, canvas pool API | Low |
| benchmarks.test.ts | Effect processing API, export API | Low |
| workflowTemplates.contract.test.ts | validateWorkflowParams() function | Low |

## 8.3 Feature Roadmap

### Near Term (v1.x)
- Complete 3D model import pipeline (ModelLayer)
- Improve point cloud visualization
- Additional particle presets
- UI wiring for 15-20 backend features

### Medium Term (v2.x)
- Real-time collaboration
- Cloud project storage
- Plugin system for custom effects
- Mobile companion app

### Long Term (v3.x)
- Native desktop application
- Hardware acceleration improvements
- VR/AR preview support

## 8.4 Milestones & Success Metrics

| Milestone | Target Date | Success Criteria |
|-----------|-------------|------------------|
| Security Phase 1 | +2 weeks | All CRITICAL gaps closed |
| Security Phase 2 | +4 weeks | All HIGH gaps closed |
| Beta Release | +10 weeks | Security complete, docs ready |
| v1.0 Release | +16 weeks | Production ready |

| Metric | Target |
|--------|--------|
| Installation success rate | > 95% |
| Build without errors | 100% |
| Test pass rate | > 99% |
| Export format coverage | 20+ AI formats |
| Performance (100 layers @ 1080p) | > 30 FPS |

---

# 9. Appendices

## 9.1 Document References

| Document | Location | Purpose |
|----------|----------|---------|
| Architecture | docs/ARCHITECTURE.md | System architecture |
| Security Threat Model | docs/SECURITY_THREAT_MODEL.md | Detailed threat analysis |
| Service API Reference | docs/SERVICE_API_REFERENCE.md | Service documentation |
| Export Property Mapping | docs/EXPORT_PROPERTY_MAPPING.md | Export format details |
| Specs | specs/*.md | Technical specifications |

## 9.2 Keyboard Shortcuts

| Key | Action |
|-----|--------|
| Space | Play/Pause |
| Home/End | Go to start/end |
| Arrow Left/Right | Previous/Next frame |
| Shift+Arrow | Jump 10 frames |
| Ctrl+Z | Undo |
| Ctrl+Shift+Z | Redo |
| Delete | Delete selected |
| V | Selection tool |
| P | Pen tool |
| T | Text tool |
| Ctrl+S | Save project |
| Ctrl+E | Export |

## 9.3 Glossary

| Term | Definition |
|------|------------|
| Composition | A timeline containing layers |
| Precomp | Nested composition |
| Matte | Grayscale mask image |
| Trajectory | Path of motion over time |
| Keyframe | Specific value at specific frame |
| Expression | Code that generates property values |
| PropertyLink | Connection between two properties |
| Deterministic | Same input always produces same output |

## 9.4 Version History

| Version | Date | Changes |
|---------|------|---------|
| 2.0 | February 2026 | Comprehensive consolidation |
| 1.0 | January 2026 | Initial PRD |

---

*This document consolidates PRD.md, specs/, PROJECT_STATUS.md, and SECURITY_ASSESSMENT.md into a single comprehensive reference.*
