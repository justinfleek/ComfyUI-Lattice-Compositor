# GLOSSARY

**Weyl Compositor - Terminology Reference**

**HYPER-CRITICAL FOR HANDOFF**: Understanding these terms is essential for working with the codebase.

---

## Core Concepts

### Animation Terms

| Term | Definition |
|------|------------|
| **Keyframe** | A specific value at a specific frame that defines animation waypoints |
| **Interpolation** | The process of calculating values between keyframes |
| **Easing** | A function that controls the rate of change during interpolation |
| **Bezier Handle** | Control points that define the curve shape between keyframes |
| **Expression** | JavaScript code that dynamically calculates property values |
| **Property Driver** | A link that makes one property follow another (pickwhip) |
| **Frame** | A single point in time, typically 1/30th of a second at 30fps |
| **In Point** | The first frame where a layer is active |
| **Out Point** | The last frame where a layer is active |

### Composition Terms

| Term | Definition |
|------|------------|
| **Composition** | A collection of layers with shared settings (dimensions, duration) |
| **Precomp** | A composition used as a layer inside another composition |
| **Work Area** | The portion of the timeline selected for preview/export |
| **Playhead** | The current frame indicator on the timeline |
| **Markers** | User-defined points on the timeline for reference |
| **Frame Count** | Total number of frames in a composition (default: 81) |

### Layer Terms

| Term | Definition |
|------|------------|
| **Layer** | A visual element in the composition (image, shape, text, etc.) |
| **Transform** | Position, rotation, scale, anchor point properties |
| **Opacity** | Transparency level (0 = invisible, 1 = fully visible) |
| **Blend Mode** | How a layer combines with layers below it |
| **Track Matte** | Using one layer's alpha/luma to mask another |
| **Adjustment Layer** | A layer that applies effects to all layers below |
| **Null Layer** | An invisible layer used as a parent for other layers |
| **3D Layer** | A layer with Z-axis position and XYZ rotation |

### Effect Terms

| Term | Definition |
|------|------------|
| **Effect Stack** | Ordered list of effects applied to a layer |
| **Effect Instance** | A specific effect with its parameter values |
| **Effect Parameter** | A controllable value within an effect (e.g., blur radius) |
| **Animatable Parameter** | An effect parameter that can have keyframes |

---

## Technical Terms

### Engine Terms

| Term | Definition |
|------|------------|
| **WeylEngine** | The main rendering engine class |
| **MotionEngine** | The animation evaluation engine |
| **Evaluate** | To calculate the state of all properties at a given frame |
| **Render** | To draw the evaluated state to a canvas/WebGL |
| **Deterministic** | Producing identical output for identical input every time |
| **Frame-Independent** | Working correctly regardless of evaluation order |

### State Management

| Term | Definition |
|------|------------|
| **compositorStore** | The central Pinia store for all application state |
| **Action** | A function that modifies store state |
| **Getter** | A computed property derived from store state |
| **Mutation** | A synchronous state change (implicit in Pinia) |
| **History** | The undo/redo stack of state snapshots |

### Cache Terms

| Term | Definition |
|------|------------|
| **Frame Cache** | Stores rendered ImageData by frame number |
| **Layer Evaluation Cache** | Stores evaluated layer states by layer+frame |
| **Version** | A counter that increments when a layer changes |
| **State Hash** | A hash of relevant state for cache validation |
| **LRU** | Least Recently Used - cache eviction strategy |
| **Checkpoint** | A saved particle system state for scrub restoration |

### Particle Terms

| Term | Definition |
|------|------------|
| **Emitter** | Configuration for spawning particles |
| **Particle** | A single simulated point with position, velocity, etc. |
| **SeededRandom** | A deterministic random number generator |
| **Mulberry32** | The specific seeded RNG algorithm used |
| **Force** | Gravity, wind, vortex, turbulence affecting particles |
| **Collision** | When particles hit boundaries or objects |
| **Sub-Emitter** | An emitter triggered by particle events |

### Audio Terms

| Term | Definition |
|------|------------|
| **AudioAnalysis** | Pre-computed audio features for all frames |
| **Amplitude** | Overall loudness at a frame |
| **RMS** | Root Mean Square - a measure of signal energy |
| **Frequency Band** | A range of frequencies (bass, mid, high) |
| **Spectral Centroid** | The "center of mass" of the frequency spectrum |
| **Beat** | A detected rhythmic pulse in the audio |
| **Onset** | The start of a musical note or sound event |
| **BPM** | Beats Per Minute - the tempo of the audio |

### 3D/Camera Terms

| Term | Definition |
|------|------------|
| **Vec3** | A 3D vector [x, y, z] |
| **Mat4** | A 4x4 transformation matrix |
| **Quat** | A quaternion for rotation representation |
| **FOV** | Field of View - camera viewing angle |
| **Frustum** | The 3D viewing volume of a camera |
| **DOF** | Depth of Field - focus blur effect |
| **Trajectory** | A predefined camera movement path |

### Path/Spline Terms

| Term | Definition |
|------|------------|
| **Bezier** | A curve defined by control points |
| **Control Point** | A point that defines spline shape |
| **Handle** | Tangent control extending from a control point |
| **Arc Length** | The actual distance along a curve |
| **Parameterization** | Mapping parameter t to curve distance |
| **Tangent** | The direction of the curve at a point |
| **Normal** | Perpendicular to the tangent |

---

## File/Format Terms

| Term | Definition |
|------|------------|
| **Matte** | A grayscale image defining transparency |
| **NPZ** | NumPy compressed archive format (for ComfyUI) |
| **Uni3C** | Camera trajectory format for video generation |
| **GLTF/GLB** | 3D model format (text/binary) |
| **Sprite Sheet** | Multiple animation frames in one image |

---

## UI Terms

| Term | Definition |
|------|------------|
| **Timeline** | The horizontal panel showing time and layers |
| **Curve Editor** | Visual editor for animation curves (renamed from Graph Editor) |
| **Properties Panel** | Editor for selected layer/effect properties |
| **Canvas** | The main viewport showing the composition |
| **Scrubbing** | Dragging the playhead to preview animation |
| **PropertyLink** | A draggable connector for linking properties (renamed from Pickwhip) |

---

## Abbreviations

| Abbrev | Full Form |
|--------|-----------|
| **AE** | After Effects |
| **FPS** | Frames Per Second |
| **GPU** | Graphics Processing Unit |
| **LUT** | Lookup Table |
| **RGB/RGBA** | Red Green Blue (Alpha) |
| **UV** | Texture coordinates |
| **VFX** | Visual Effects |
| **VLM** | Vision Language Model |
| **WebGL** | Web Graphics Library |
| **WebGPU** | Next-gen Web GPU API |

---

## Layer Type Reference

| Type | Description | Key Properties |
|------|-------------|----------------|
| `solid` | A solid color rectangle | color |
| `image` | A raster image | source, fit |
| `video` | A video file | source, playbackRate |
| `text` | Rendered text | text, font, fontSize |
| `shape` / `spline` | Vector path | controlPoints, fill, stroke |
| `null` | Invisible parent | transform only |
| `camera` | 3D camera | fov, near, far, dof |
| `light` | 3D light source | type, intensity, color |
| `particle` | Particle emitter | emitter config, forces |
| `precomp` | Nested composition | compositionId, timeRemap |
| `adjustment` | Effect-only layer | effects (no content) |
| `depthflow` | Depth parallax | depthSource, parallax |
| `model` | 3D model | modelUrl, materials |
| `point_cloud` | Point cloud data | points, colors |

---

## Effect Category Reference

| Category | Effects |
|----------|---------|
| **Blur** | Gaussian, Directional, Radial, Box, Sharpen |
| **Color** | Brightness/Contrast, Hue/Saturation, Levels, Tint, Curves, Glow, Drop Shadow, Color Balance, Exposure, Vibrance, Invert, Posterize, Threshold |
| **Distort** | Transform, Warp, Displacement Map |
| **Generate** | Fill, Gradient Ramp, Fractal Noise |

---

## Code Conventions

| Convention | Meaning |
|------------|---------|
| `useXxxStore()` | Pinia store hook |
| `xxxService` | Singleton service instance |
| `createDefaultXxx()` | Factory for default config |
| `evaluateXxx()` | Calculate value at frame |
| `interpolateXxx()` | Calculate between keyframes |
| `Xxx.ts` | TypeScript service file |
| `Xxx.vue` | Vue component |
| `xxxStore.ts` | Pinia store |
| `xxxActions.ts` | Store action module |

---

## Version Compatibility

| Term | Version |
|------|---------|
| **Vue** | 3.x |
| **Pinia** | 2.x |
| **Three.js** | 0.160+ |
| **Vitest** | 1.x |
| **TypeScript** | 5.x |
| **Node** | 18+ |

---

**See also**:
- [ARCHITECTURE.md](./ARCHITECTURE.md) - System architecture
- [SERVICE_API_REFERENCE.md](./SERVICE_API_REFERENCE.md) - Service APIs
- [EFFECT_PARAMETERS.md](./EFFECT_PARAMETERS.md) - Effect documentation

*Generated: December 23, 2025*
