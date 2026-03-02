# SPEC_08: Particle, Point Cloud, Camera & Depth Systems

## Executive Summary

This specification documents the complete state of Lattice's particle ecosystem including particles, point clouds, camera trajectories, and depth-based effects. The goal is production-grade software competitive with Adobe After Effects plugins.

**Overall Assessment: 70% Feature Parity, 50% UI-Wired**

| System | Implementation | UI Wiring | Industry Parity |
|--------|----------------|-----------|-----------------|
| Particles | 75% | 40% | 55% |
| Point Cloud | 60% | 70% | 40% |
| Camera Trajectory | 85% | 80% | 70% |
| Camera Controller | 90% | 85% | 80% |
| Depthflow | 80% | 70% | 65% |

**Critical Finding:** The backend is solid. The UI is the bottleneck. We have ~15-20 features implemented in code with zero UI exposure.

---

## Architecture Overview

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  UI LAYER                                                                   │
│  ├── ParticleProperties.vue      - Main particle control panel (1550 lines)│
│  ├── AssetsPanel.vue             - Sprite/mesh import, emitter shape       │
│  ├── WorkspaceLayout.vue         - Mesh emitter wiring                     │
│  ├── CameraProperties.vue        - Camera controls                         │
│  └── DepthflowProperties.vue     - 2.5D parallax controls                  │
├─────────────────────────────────────────────────────────────────────────────┤
│  ENGINE LAYER                                                               │
│  ├── ParticleLayer.ts            - Three.js particle layer (1150 lines)    │
│  ├── GPUParticleSystem.ts        - WebGL2 Transform Feedback (1200+ lines) │
│  ├── PointCloudLayer.ts          - Point cloud visualization               │
│  ├── CameraController.ts         - Camera management                       │
│  └── particleShaders.ts          - GLSL vertex/fragment shaders            │
├─────────────────────────────────────────────────────────────────────────────┤
│  SERVICE LAYER                                                              │
│  ├── particleSystem.ts           - CPU particle simulation (2400+ lines)   │
│  ├── cameraTrajectory.ts         - 22 camera motion presets                │
│  ├── depthflow.ts                - 2.5D parallax rendering                 │
│  └── audioFeatures.ts            - Audio reactivity extraction             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### Key Source Files

| File | Purpose | Lines | Complexity |
|------|---------|-------|------------|
| `ui/src/services/particleSystem.ts` | CPU particle simulation with full physics | ~2415 | High |
| `ui/src/engine/particles/GPUParticleSystem.ts` | GPU-accelerated simulation | ~1200 | High |
| `ui/src/engine/particles/types.ts` | TypeScript type definitions | ~600 | Medium |
| `ui/src/engine/layers/ParticleLayer.ts` | Three.js integration layer | ~1147 | High |
| `ui/src/engine/layers/PointCloudLayer.ts` | Point cloud visualization | ~800 | Medium |
| `ui/src/services/cameraTrajectory.ts` | Camera motion presets | ~600 | Medium |
| `ui/src/services/depthflow.ts` | 2.5D parallax system | ~1200 | High |
| `ui/src/engine/core/CameraController.ts` | Camera management | ~500 | Medium |
| `ui/src/components/properties/ParticleProperties.vue` | UI controls | ~1550 | Medium |

---

# PART 1: PARTICLE SYSTEM

## 1.1 Current Implementation Status

### Emitter System

#### Emitter Shapes

| Shape | Backend Status | UI Wired | Config Properties | Notes |
|-------|----------------|----------|-------------------|-------|
| Point | `particleSystem.ts:1342-1344` | Default only | `x`, `y` | No shape selector in UI |
| Line | `particleSystem.ts:1346-1358` | **No** | `shapeWidth`, `direction` | Perpendicular to direction |
| Circle | `particleSystem.ts:1360-1378` | **No** | `shapeRadius`, `emitFromEdge` | Uniform area distribution via sqrt |
| Ring | `particleSystem.ts:1380-1391` | **No** | `shapeRadius`, `shapeInnerRadius` | Donut shape |
| Box | `particleSystem.ts:1393-1420` | **No** | `shapeWidth`, `shapeHeight`, `emitFromEdge` | Edge or filled |
| Sphere | `particleSystem.ts:1422-1447` | **No** | `shapeRadius`, `emitFromEdge`, `emitFromVolume` | 3D with rejection sampling |
| Spline | `particleSystem.ts:1449-1452` | **No** | `splinePath.layerId`, `emitMode`, `alignToPath` | Path-based emission |
| Mesh | `WorkspaceLayout.vue:820-847` | **Yes** | `meshVertices`, `meshNormals` | Via AssetsPanel button |
| Cone | GPU only (`GPUParticleSystem.ts`) | **No** | `coneRadius`, `coneLength`, `coneAngle` | GPU-only shape |

**Critical UI Gap:** Need emitter shape type dropdown in ParticleProperties.vue

#### Emitter Parameters

| Parameter | Backend Property | Range | UI Control | UI Location |
|-----------|------------------|-------|------------|-------------|
| Position X | `emitter.x` | 0-1 normalized | Slider | ParticleProperties.vue:123-132 |
| Position Y | `emitter.y` | 0-1 normalized | Slider | ParticleProperties.vue:133-145 |
| Direction | `emitter.direction` | 0-360 degrees | Slider | ParticleProperties.vue:146-156 |
| Spread | `emitter.spread` | 0-360 degrees | Slider | ParticleProperties.vue:157-168 |
| Speed | `emitter.speed` | 1-1000 | Slider | ParticleProperties.vue:169-180 |
| Speed Variance | `emitter.speedVariance` | 0-500 | Slider | ParticleProperties.vue:181-192 |
| Size | `emitter.size` | 1-400 px | Slider | ParticleProperties.vue:193-204 |
| Size Variance | `emitter.sizeVariance` | 0-100 | Slider | ParticleProperties.vue:205-216 |
| Color | `emitter.color` | RGB array | Color picker | ParticleProperties.vue:217-224 |
| Emission Rate | `emitter.emissionRate` | 0.1-100/s | Slider | ParticleProperties.vue:225-236 |
| Lifetime | `emitter.particleLifetime` | 1-300 frames | Slider | ParticleProperties.vue:237-248 |
| Lifetime Variance | `emitter.lifetimeVariance` | 0-50 | Not exposed | Backend only |
| Initial Burst | `emitter.initialBurst` | 0-1 (%) | Slider | ParticleProperties.vue:249-260 |
| Burst on Beat | `emitter.burstOnBeat` | boolean | Checkbox | ParticleProperties.vue:262-271 |
| Burst Count | `emitter.burstCount` | 1-100 | Slider | ParticleProperties.vue:272-283 |

#### Emitter Shape Parameters (ALL UNWIRED)

| Parameter | Backend Property | Range | Purpose |
|-----------|------------------|-------|---------|
| Shape Radius | `emitter.shapeRadius` | 0.01-1 | Circle, sphere, ring outer radius |
| Shape Width | `emitter.shapeWidth` | 0.01-1 | Box width, line length |
| Shape Height | `emitter.shapeHeight` | 0.01-1 | Box height |
| Shape Depth | `emitter.shapeDepth` | 0.01-1 | Box depth (3D) |
| Inner Radius | `emitter.shapeInnerRadius` | 0-0.5 | Ring inner radius |
| Emit From Edge | `emitter.emitFromEdge` | boolean | Surface-only emission |
| Emit From Volume | `emitter.emitFromVolume` | boolean | 3D volume emission |

#### Spline Path Emission Parameters (ALL UNWIRED)

| Parameter | Backend Property | Values | Purpose |
|-----------|------------------|--------|---------|
| Layer ID | `splinePath.layerId` | string | SplineLayer to emit along |
| Emit Mode | `splinePath.emitMode` | `'uniform'`, `'random'`, `'start'`, `'end'`, `'sequential'` | Distribution along path |
| Parameter | `splinePath.parameter` | 0-1 | Mode-specific parameter |
| Align to Path | `splinePath.alignToPath` | boolean | Emission direction follows tangent |
| Offset | `splinePath.offset` | -1 to 1 | Perpendicular offset from path |
| Bidirectional | `splinePath.bidirectional` | boolean | Emit both directions |

### Force Fields

#### Implemented Force Types

| Force Type | Backend Location | UI Wired | Parameters |
|------------|------------------|----------|------------|
| Gravity Wells | `particleSystem.ts:904-933` | **Yes** | position (x,y), strength, radius, falloff (linear/quadratic/constant) |
| Vortices | `particleSystem.ts:935-961` | **Yes** | position, strength, radius, rotationSpeed, inwardPull |
| Turbulence | `particleSystem.ts:1668-1680` | **Yes** | scale, strength, evolutionSpeed |
| Global Gravity | `particleSystem.ts:897` | **Yes** | Single value in system config |
| Global Wind | `particleSystem.ts:872-880` | **Yes** | windStrength, windDirection |
| Global Friction | `particleSystem.ts:967-969` | **Yes** | Single friction value |

**Gravity Wells UI** (ParticleProperties.vue:316-403):
- Position X/Y sliders (0-1 normalized)
- Strength slider (-1000 to 1000)
- Radius slider (0.01-1)
- Falloff dropdown (linear/quadratic/constant)
- Enable checkbox
- Name input
- Add/remove buttons

**Vortices UI** (ParticleProperties.vue:406-506):
- Position X/Y sliders
- Strength slider (0-1000)
- Radius slider (0.01-1)
- Rotation Speed slider (0-50 degrees/frame)
- Inward Pull slider (0-100)
- Enable checkbox

**Turbulence UI** (ParticleProperties.vue:511-580):
- Scale slider (0.001-0.02)
- Strength slider (0-500)
- Evolution Speed slider (0-1)
- Enable checkbox
- Add/remove buttons

#### GPU-Only Force Types (Not in CPU Fallback)

| Force Type | Backend Location | UI Wired | Description |
|------------|------------------|----------|-------------|
| Linear Drag | `GPUParticleSystem.ts:151` | **No** | Velocity-proportional resistance |
| Quadratic Drag | `GPUParticleSystem.ts:152` | **No** | Velocity-squared resistance |
| Wind with Gusts | `GPUParticleSystem.ts:155-158` | **No** | Directional wind with randomized gusts |
| Lorenz Attractor | `GPUParticleSystem.ts:159-161` | **No** | Chaotic attractor (sigma, rho, beta) |
| Flocking/Swarming | `GPUParticleSystem.ts:types.ts:252-274` | **No** | Separation, alignment, cohesion |
| Point Attractor | `GPUParticleSystem.ts:134-137` | **No** | Simple radial attraction/repulsion |

### Collision System

**Backend Implementation:** `particleSystem.ts:1077-1227`, `CollisionConfig` interface

| Feature | Backend Property | Default | UI Wired |
|---------|------------------|---------|----------|
| Enable Collision | `collision.enabled` | false | **No** |
| Floor Collision | `collision.floorEnabled` | false | **No** |
| Floor Y Position | `collision.floorY` | 1.0 | **No** |
| Ceiling Collision | `collision.ceilingEnabled` | false | **No** |
| Ceiling Y Position | `collision.ceilingY` | 0.0 | **No** |
| Wall Collision | `collision.wallsEnabled` | false | **No** |
| Particle-Particle | `collision.particleCollision` | false | **No** |
| Collision Radius | `collision.particleCollisionRadius` | 1.0 | **No** |
| Collision Response | `collision.particleCollisionResponse` | 'bounce' | **No** |
| Collision Damping | `collision.particleCollisionDamping` | 0.8 | **No** |
| Bounciness | `collision.bounciness` | 0.7 | **No** |
| Friction | `collision.friction` | 0.1 | **No** |
| Spatial Hash Cell Size | `collision.spatialHashCellSize` | 50 | **No** |

**Collision Response Types:**
- `'bounce'` - Elastic collision with damping
- `'absorb'` - Smaller particle dies, larger grows
- `'explode'` - Both particles die, triggers sub-emitters

**Critical UI Gap:** ENTIRE collision panel is missing from ParticleProperties.vue

### Sub-Emitters

**Backend Implementation:** `particleSystem.ts:1703-1769`

| Feature | Backend Property | UI Wired | Notes |
|---------|------------------|----------|-------|
| Parent Emitter | `subEmitter.parentEmitterId` | **Yes** | Dropdown with '*' for all |
| Trigger Type | `subEmitter.trigger` | **Partial** | Only 'death' exposed |
| Spawn Count | `subEmitter.spawnCount` | **Yes** | 1-10 slider |
| Inherit Velocity | `subEmitter.inheritVelocity` | **Yes** | 0-100% slider |
| Size | `subEmitter.size` | **Yes** | Pixel slider |
| Size Variance | `subEmitter.sizeVariance` | **Yes** | Variance slider |
| Lifetime | `subEmitter.lifetime` | **Yes** | Frame slider |
| Speed | `subEmitter.speed` | **Yes** | Speed slider |
| Spread | `subEmitter.spread` | **Yes** | Degree slider |
| Color | `subEmitter.color` | **Yes** | Color picker |
| Enable | `subEmitter.enabled` | **Yes** | Checkbox |

**Missing Trigger Types (Backend Ready):**
- `'collision'` - On particle collision
- `'birth'` - On particle spawn
- `'bounce'` - On boundary bounce
- `'lifetime'` - At specific age

### Modulations (Property Over Lifetime)

**Backend Implementation:** `particleSystem.ts:1622-1662`

| Property | Backend Key | UI Wired | Curve Support |
|----------|-------------|----------|---------------|
| Size | `'size'` | **Yes** | Linear only (no curve editor) |
| Speed | `'speed'` | **Yes** | Linear only |
| Opacity | `'opacity'` | **Yes** | Linear only |
| Color R | `'colorR'` | **Yes** | Linear only |
| Color G | `'colorG'` | **Yes** | Linear only |
| Color B | `'colorB'` | **Yes** | Linear only |

**UI Controls** (ParticleProperties.vue:715-793):
- Target emitter dropdown ('*' for all)
- Property dropdown
- Start value input
- End value input
- Easing dropdown (linear, easeIn, easeOut, easeInOut, bounce, elastic)

**Missing:**
- Visual curve editor
- Bezier curve support
- Multiple keypoint curves
- GPU-side modulation textures

### Rendering

**Backend Implementation:** `particleSystem.ts:1993-2366`, `RenderOptions` interface

| Feature | Backend Property | Values | UI Wired | UI Location |
|---------|------------------|--------|----------|-------------|
| Blend Mode | `renderOptions.blendMode` | normal, additive, multiply, screen | **Yes** | ParticleProperties.vue:805-814 |
| Particle Shape | `renderOptions.particleShape` | circle, square, triangle, star, sprite | **Partial** | No 'sprite' option in dropdown |
| Render Trails | `renderOptions.renderTrails` | boolean | **Yes** | ParticleProperties.vue:827-835 |
| Trail Length | `renderOptions.trailLength` | 1-20 | **Yes** | ParticleProperties.vue:837-848 |
| Trail Opacity Falloff | `renderOptions.trailOpacityFalloff` | 0-1 | **No** | Backend only |
| Glow Enabled | `renderOptions.glowEnabled` | boolean | **Yes** | ParticleProperties.vue:849-858 |
| Glow Radius | `renderOptions.glowRadius` | 1-50 px | **Yes** | ParticleProperties.vue:859-870 |
| Glow Intensity | `renderOptions.glowIntensity` | 0-1 | **Yes** | ParticleProperties.vue:871-882 |
| Motion Blur | `renderOptions.motionBlur` | boolean | **No** | Backend only |
| Motion Blur Strength | `renderOptions.motionBlurStrength` | 0-1 | **No** | Backend only |
| Motion Blur Samples | `renderOptions.motionBlurSamples` | 1-16 | **No** | Backend only |
| Connections Enabled | `renderOptions.connections.enabled` | boolean | **Yes** | ParticleProperties.vue:886-895 |
| Connection Max Distance | `renderOptions.connections.maxDistance` | 10-300 px | **Yes** | ParticleProperties.vue:896-907 |
| Connection Max Count | `renderOptions.connections.maxConnections` | 1-5 | **Yes** | ParticleProperties.vue:908-919 |
| Connection Line Width | `renderOptions.connections.lineWidth` | 0.5-3 | **Yes** | ParticleProperties.vue:920-931 |
| Connection Line Opacity | `renderOptions.connections.lineOpacity` | 0-1 | **Yes** | ParticleProperties.vue:932-943 |
| Connection Fade By Distance | `renderOptions.connections.fadeByDistance` | boolean | **Yes** | ParticleProperties.vue:944-953 |
| Emissive Enabled | `renderOptions.emissiveEnabled` | boolean | **No** | Backend only |
| Emissive Intensity | `renderOptions.emissiveIntensity` | 0-10 | **No** | Backend only |
| Emissive Color | `renderOptions.emissiveColor` | RGB or null | **No** | Backend only |
| Sprite Smoothing | `renderOptions.spriteSmoothing` | boolean | **No** | Backend only |
| Sprite Opacity By Age | `renderOptions.spriteOpacityByAge` | boolean | **No** | Backend only |

### Sprite/Texture System

**Backend Implementation:** `particleSystem.ts:231-249`, `SpriteConfig` interface

| Feature | Backend Property | UI Status | Notes |
|---------|------------------|-----------|-------|
| Sprite Enabled | `emitter.sprite.enabled` | **No** | No checkbox in emitter config |
| Image URL | `emitter.sprite.imageUrl` | **Import only** | AssetsPanel imports, no assignment |
| Image Data | `emitter.sprite.imageData` | N/A | Runtime loaded |
| Is Sprite Sheet | `emitter.sprite.isSheet` | **Import only** | Set during import |
| Columns | `emitter.sprite.columns` | **Import only** | Set during import |
| Rows | `emitter.sprite.rows` | **Import only** | Set during import |
| Total Frames | `emitter.sprite.totalFrames` | **Import only** | Calculated |
| Frame Rate | `emitter.sprite.frameRate` | **Import only** | Set during import |
| Play Mode | `emitter.sprite.playMode` | **No** | loop, once, pingpong, random |
| Billboard | `emitter.sprite.billboard` | **No** | Always face camera |
| Rotation Enabled | `emitter.sprite.rotationEnabled` | **No** | Enable spin |
| Rotation Speed | `emitter.sprite.rotationSpeed` | **No** | Degrees per frame |
| Rotation Variance | `emitter.sprite.rotationSpeedVariance` | **No** | Random variation |
| Align To Velocity | `emitter.sprite.alignToVelocity` | **No** | Point in movement direction |

**Sprite Import Flow (Working):**
1. AssetsPanel.vue:191-241 - Sprites tab with import dialog
2. User drops sprite sheet image
3. Configure columns, rows, framerate
4. assetStore.importSpriteSheet() stores in asset registry

**Missing Link:** No UI to assign imported sprite to an emitter

### Audio Reactivity

**Backend Implementation:** `particleSystem.ts:836-845`, `audioFeatures.ts`

| Feature | Backend Method | UI Wired | Notes |
|---------|----------------|----------|-------|
| Burst on Beat | `emitter.burstOnBeat` | **Yes** | Checkbox per emitter |
| Trigger All Bursts | `triggerAllBursts()` | N/A | Called by audio system |
| Set Feature Value | `setFeatureValue(param, value, emitterId?)` | **No** | No mapping UI |
| Emission Rate Override | `featureOverrides['emissionRate']` | **No** | |
| Gravity Override | `featureOverrides['gravity']` | **No** | |
| Wind Override | `featureOverrides['windStrength']` | **No** | |
| Speed Override | `featureOverrides['speed']` | **No** | |
| Size Override | `featureOverrides['size']` | **No** | |

**GPU Audio Features** (`GPUParticleSystem.ts`):

| Feature | Backend Property | UI Wired |
|---------|------------------|----------|
| Amplitude | `audioFeatures.amplitude` | **No** |
| Bass | `audioFeatures.bass` | **No** |
| Mid | `audioFeatures.mid` | **No** |
| High | `audioFeatures.high` | **No** |
| Onset | `audioFeatures.onset` | **No** |
| Beat | `audioFeatures.beat` | **No** |
| Pitch | `audioFeatures.pitch` | **No** |
| Spectral Centroid | `audioFeatures.spectralCentroid` | **No** |
| RMS | `audioFeatures.rms` | **No** |

**Audio Binding System** (GPU, `types.ts:495-517`):

```typescript
interface AudioBinding {
  id: string;
  feature: AudioFeature;
  target: 'emitter' | 'forceField' | 'system';
  targetId: string;
  property: string;
  scale: number;
  offset: number;
  smoothing: number;
  invert: boolean;
  clampMin: number;
  clampMax: number;
}
```

**Critical UI Gap:** No audio binding/mapping panel exists

### Determinism & Caching

**Backend Implementation:** `particleSystem.ts:48-136`, `GPUParticleSystem.ts:57-70`

| Feature | Status | Notes |
|---------|--------|-------|
| Seeded RNG | **Implemented** | Mulberry32 algorithm in `SeededRandom` class |
| RNG State Save/Restore | **Implemented** | `getState()`, `setState()` methods |
| Frame Caching | **Implemented** | `ParticleFrameCache` interface |
| Cache Interval | **Configurable** | Default every 30 frames |
| Scrub-Safe Simulation | **Implemented** | Restore from nearest cache + replay |
| Particle Pool | **Implemented** | Reduces GC pressure, 10k max pool |
| Cache Stats | **Implemented** | `getCacheStats()` returns metrics |
| Deterministic IDs | **Implemented** | Counter-based, not Date.now() |

**Cache Performance:**
- Memory: ~64 bytes per particle per cached frame
- 100 frames, 10k particles = ~64MB cache
- Cache hit restores in <1ms
- Cache miss replays at ~60k particles/sec

---

## 1.2 Feature Comparison: Industry Leaders

### vs Trapcode Particular (After Effects)

**Gap Assessment: 95% - We are far behind**

#### Physics Model

| Particular Feature | Our Status | Gap Level |
|--------------------|------------|-----------|
| Gravity with direction vector | Partial (Y-only global) | MEDIUM |
| Air resistance (proper drag) | Friction only, not velocity-squared | HIGH |
| Bounce with energy loss | Backend only, no UI | MEDIUM |
| Motion inheritance from emitter | Not implemented | HIGH |
| Repel/attract from layer | Not implemented | CRITICAL |

#### Emitter Types

| Particular Emitter | Our Status | Gap Level |
|--------------------|------------|-----------|
| Point | Done | - |
| Box | Backend only | HIGH |
| Sphere | Backend only | HIGH |
| Grid | Not implemented | MEDIUM |
| Layer (emit from pixels) | Not implemented | CRITICAL |
| Layer as emitter RGB/Luminance | Not implemented | CRITICAL |
| Light emitter | Not implemented | LOW |
| Text/mask emitter | Not implemented | HIGH |
| Directional with spread | Done | - |
| OBJ mesh emitter | Done (via AssetsPanel) | - |

#### Aux System (Secondary Particles)

| Particular Feature | Our Status | Gap Level |
|--------------------|------------|-----------|
| Emit from primary particles | Sub-emitters exist | Partial |
| On death | Done | - |
| On collision | Backend only | MEDIUM |
| On bounce | Not implemented | MEDIUM |
| Continuous emission from primaries | Not implemented | HIGH |
| Aux inherits primary properties | Partial (velocity only) | MEDIUM |

#### Physics/Behaviors

| Particular Feature | Our Status | Gap Level |
|--------------------|------------|-----------|
| Spherical Field | Gravity wells | Done |
| Spin | Backend only | MEDIUM |
| Opacity over life | Done | - |
| Size over life | Done | - |
| Color over life | Done | - |
| Turbulence | Done | - |
| Motion Path (spline influence) | Spline emitter exists | Partial |

#### Rendering

| Particular Feature | Our Status | Gap Level |
|--------------------|------------|-----------|
| Sprite texture | Backend only | HIGH |
| Textured polygon | Not implemented | MEDIUM |
| Cloudlet/multi-stroke | Not implemented | LOW |
| Streaklet | Trails | Done |
| Glow | Done | - |
| Motion blur | Backend only | MEDIUM |
| Depth of field integration | Not implemented | HIGH |
| Z-buffer modes | Basic depth sort only | MEDIUM |
| Shadowlets | Not implemented | MEDIUM |
| Reflection/refraction | Not implemented | LOW |

#### Designer Presets

| Particular Feature | Our Status | Gap Level |
|--------------------|------------|-----------|
| ~300 built-in presets | 0 presets | CRITICAL |
| Preset browser with previews | Not implemented | CRITICAL |
| Save/load custom presets | Not implemented | CRITICAL |
| Preset categories | Not implemented | CRITICAL |

### vs X-Particles (Cinema 4D)

**Gap Assessment: 85% - Missing advanced modifiers**

#### Modifiers

| X-Particles Modifier | Our Status | Gap Level |
|----------------------|------------|-----------|
| Total modifier count | 6 vs 50+ | CRITICAL |
| Flow field | Not implemented | HIGH |
| Cover (distribute on surface) | Not implemented | MEDIUM |
| Gravity | Done (wells) | - |
| Turbulence | Done | - |
| Vortex/Rotation | Done | - |
| Kill (conditional death) | Basic boundary only | LOW |
| Sprite (per-particle textures) | Backend only | MEDIUM |
| Attractor | Gravity wells | Done |
| Wind | Done | - |
| Drag | GPU only | MEDIUM |
| Explode | Sub-emitter on death | Partial |
| Flocking | GPU only, no UI | HIGH |
| Inheritance | Not implemented | MEDIUM |
| Limit | Not implemented | LOW |
| Network (connections) | Done | - |
| Physical (collision) | Backend only | HIGH |
| Python/expressions | Not implemented | HIGH |
| Sound | Partial (beat only) | HIGH |
| Spawn | Sub-emitters | Done |
| Speed | Modulation exists | Done |
| Sprite animator | Backend only | MEDIUM |
| Transform | Not implemented | MEDIUM |
| Trigger | Sub-emitter triggers | Partial |
| Weight | Not implemented | LOW |

#### Emitter Features

| X-Particles Feature | Our Status | Gap Level |
|---------------------|------------|-----------|
| Object/mesh emitter | Done | - |
| Spline emitter | Backend only | HIGH |
| Volume emitter | Box/sphere backend | MEDIUM |
| Particle groups | Not implemented | HIGH |
| Shot/burst emission | Done | - |
| Pulse emission | Not implemented | MEDIUM |
| Rate by surface area | Not implemented | LOW |
| Texture emission (from image) | Not implemented | CRITICAL |

#### Dynamics

| X-Particles Feature | Our Status | Gap Level |
|---------------------|------------|-----------|
| Cloth constraints | Not implemented | LOW |
| Fluid simulation (SPH) | Not implemented | LOW |
| Collision with scene objects | Not implemented | HIGH |
| Soft body | Not implemented | LOW |
| Constraints (springs) | Not implemented | MEDIUM |

#### Cache System

| X-Particles Feature | Our Status | Gap Level |
|---------------------|------------|-----------|
| Full simulation cache | Frame caching | Done |
| Disk cache | Memory only | MEDIUM |
| Alembic export | Not implemented | HIGH |
| OpenVDB export | Not implemented | LOW |
| Cache scrubbing | Done | - |

### vs RyanOnTheInside (ComfyUI)

**Gap Assessment: 60% - This is our closest competitor**

#### Audio Integration

| RyanOnTheInside Feature | Our Status | Gap Level |
|-------------------------|------------|-----------|
| Multi-band frequency analysis | Not implemented | HIGH |
| Per-band parameter mapping | Not implemented | HIGH |
| MIDI note mapping | Not implemented | MEDIUM |
| Onset detection | Global only | MEDIUM |
| Per-emitter audio reactivity | Backend ready, no UI | HIGH |
| Audio-driven force fields | Not implemented | HIGH |
| BPM sync | Not implemented | MEDIUM |
| Waveform visualization | Basic in AudioPanel | Partial |

#### Emitter Types

| RyanOnTheInside Feature | Our Status | Gap Level |
|-------------------------|------------|-----------|
| Shape from node input | Spline emitter backend | Partial |
| Depth map emission | Not implemented | CRITICAL |
| Mask-based emission | Not implemented | CRITICAL |
| Flow-based emission | Not implemented | HIGH |
| Audio-reactive position | Not implemented | HIGH |

#### Forces

| RyanOnTheInside Feature | Our Status | Gap Level |
|-------------------------|------------|-----------|
| Audio-reactive gravity | Backend ready | MEDIUM |
| Audio-reactive wind | Backend ready | MEDIUM |
| Audio-reactive turbulence | Not implemented | HIGH |
| Per-emitter force overrides | Global only | MEDIUM |

#### ComfyUI Integration

| RyanOnTheInside Feature | Our Status | Gap Level |
|-------------------------|------------|-----------|
| Particle node in workflow | Backend nodes exist | Partial |
| Depth map interaction | Not implemented | CRITICAL |
| Matte output | Basic matte | Partial |
| Particle to mask | Not implemented | HIGH |
| Integration with inpainting | Not implemented | CRITICAL |

---

# PART 2: POINT CLOUD SYSTEM

## 2.1 Current Implementation

**Backend:** `ui/src/engine/layers/PointCloudLayer.ts` (~800 lines)

### Format Support

| Format | Status | Implementation | Notes |
|--------|--------|----------------|-------|
| PLY (ASCII) | **Working** | `parsePLY()` | Vertex, color, normal |
| PLY (Binary) | **Working** | `parsePLYBinary()` | Little/big endian |
| PCD | **Working** | `parsePCD()` | ASCII and binary |
| XYZ | **Working** | `parseXYZ()` | Simple x y z format |
| PTS | **Working** | `parsePTS()` | With intensity |
| LAS | **PLACEHOLDER** | Throws "Not yet implemented" | CRITICAL GAP |
| LAZ | **PLACEHOLDER** | Throws "Not yet implemented" | CRITICAL GAP |
| E57 | Not implemented | - | Industry standard |

### Color Modes

| Mode | Backend | UI Wired | Description |
|------|---------|----------|-------------|
| RGB | `'rgb'` | **Yes** | Original point colors |
| Height | `'height'` | **Yes** | Color by Y position |
| Depth | `'depth'` | **Yes** | Color by Z (camera distance) |
| Normal | `'normal'` | **Yes** | RGB from normal direction |
| Intensity | `'intensity'` | **Yes** | Grayscale from intensity value |
| Classification | `'classification'` | **Yes** | LAS classification colors |

### Render Modes

| Mode | Backend | UI Wired | Description |
|------|---------|----------|-------------|
| Points | `'points'` | **Yes** | GL_POINTS |
| Circles | `'circles'` | **Yes** | Screenspace circles |
| Squares | `'squares'` | **Yes** | Screenspace squares |
| Splats | `'splats'` | **Yes** | Gaussian splats |

### Point Cloud Parameters

| Parameter | Backend | UI Wired | Range |
|-----------|---------|----------|-------|
| Point Size | `pointSize` | **Yes** | 1-50 |
| Opacity | `opacity` | **Yes** | 0-1 |
| Color Mode | `colorMode` | **Yes** | Dropdown |
| Render Mode | `renderMode` | **Yes** | Dropdown |
| Height Range | `heightRange` | **Yes** | Min/max |
| Depth Range | `depthRange` | **Yes** | Min/max |
| Intensity Scale | `intensityScale` | **Yes** | 0-2 |

### Missing Features

| Feature | Status | Priority |
|---------|--------|----------|
| LAS/LAZ parsing | Placeholder only | CRITICAL |
| Level of Detail (LOD) | Not implemented | HIGH |
| Octree structure | Not implemented | HIGH |
| Point cloud streaming | Not implemented | MEDIUM |
| Point selection/editing | Not implemented | MEDIUM |
| Point cloud generation from depth | Not implemented | HIGH |
| Point to mesh conversion | Not implemented | LOW |
| Potree format | Not implemented | MEDIUM |

---

# PART 3: CAMERA TRAJECTORY SYSTEM

## 3.1 Current Implementation

**Backend:** `ui/src/services/cameraTrajectory.ts` (~600 lines)

### Preset Types (22 Total)

| Preset | Status | Parameters |
|--------|--------|------------|
| orbit | **Working** | radius, speed, center |
| orbit-reverse | **Working** | Opposite direction orbit |
| swing | **Working** | Arc swing, angle range |
| dolly-in | **Working** | Linear approach |
| dolly-out | **Working** | Linear retreat |
| dolly-forward | **Working** | Z-axis movement |
| dolly-backward | **Working** | Z-axis retreat |
| pan-left | **Working** | Horizontal pan |
| pan-right | **Working** | Horizontal pan |
| tilt-up | **Working** | Vertical tilt |
| tilt-down | **Working** | Vertical tilt |
| zoom-in | **Working** | FOV change |
| zoom-out | **Working** | FOV change |
| circle | **Working** | Full 360 orbit |
| figure8 | **Working** | Figure-8 path |
| spiral-in | **Working** | Inward spiral |
| spiral-out | **Working** | Outward spiral |
| crane-up | **Working** | Vertical + dolly |
| crane-down | **Working** | Vertical + dolly |
| truck-left | **Working** | Lateral movement |
| truck-right | **Working** | Lateral movement |
| arc | **Working** | Curved path segment |

### Trajectory Parameters

| Parameter | Backend | UI Wired | Description |
|-----------|---------|----------|-------------|
| Preset Type | `type` | **Yes** | Dropdown |
| Duration | `duration` | **Yes** | Frames |
| Easing | `easing` | **Yes** | Easing preset |
| Radius | `radius` | **Yes** | For orbital moves |
| Speed | `speed` | **Yes** | Movement speed |
| Start/End Angles | `startAngle`, `endAngle` | **Yes** | Arc range |
| Center Point | `center` | **Partial** | XYZ inputs |
| Audio Reactive | `audioReactive` | **Yes** | Checkbox |
| Beat Trigger | `beatTrigger` | **Yes** | On beat effects |

### Missing Features

| Feature | Status | Priority |
|---------|--------|----------|
| Custom path drawing | Not implemented | MEDIUM |
| Camera shake presets | Not implemented | HIGH |
| Rack focus animation | Not implemented | MEDIUM |
| Camera rig presets | Not implemented | LOW |
| Multi-camera switching | Not implemented | MEDIUM |
| Path import (SVG/JSON) | Not implemented | LOW |

---

# PART 4: CAMERA CONTROLLER

## 4.1 Current Implementation

**Backend:** `ui/src/engine/core/CameraController.ts` (~500 lines)

### Camera Features

| Feature | Status | UI Wired |
|---------|--------|----------|
| Perspective Camera | **Working** | **Yes** |
| Orthographic Camera | **Working** | **Yes** |
| OrbitControls | **Working** | **Yes** |
| Pan/Zoom/Rotate | **Working** | **Yes** |
| View Presets | **Working** | **Yes** |
| Camera Bookmarks | **Working** | **Yes** |
| DOF Preview | **Working** | **Partial** |
| Animation Support | **Working** | **Yes** |

### View Presets (6)

| Preset | Direction | UI Button |
|--------|-----------|-----------|
| Front | +Z | **Yes** |
| Back | -Z | **Yes** |
| Left | -X | **Yes** |
| Right | +X | **Yes** |
| Top | -Y | **Yes** |
| Bottom | +Y | **Yes** |
| Perspective | Isometric | **Yes** |

### Camera Parameters

| Parameter | Backend | UI Wired | Animatable |
|-----------|---------|----------|------------|
| Position XYZ | **Yes** | **Yes** | **Yes** |
| Target XYZ | **Yes** | **Yes** | **Yes** |
| FOV | **Yes** | **Yes** | **Yes** |
| Near Clip | **Yes** | **Yes** | No |
| Far Clip | **Yes** | **Yes** | No |
| DOF Focus Distance | **Yes** | **Partial** | **Yes** |
| DOF Aperture | **Yes** | **Partial** | **Yes** |
| DOF Blur | **Yes** | **Partial** | **Yes** |

### Missing Features

| Feature | Status | Priority |
|---------|--------|----------|
| Frustum visualization | Not implemented | LOW |
| Camera preview (PiP) | Not implemented | MEDIUM |
| Multi-camera switching | Not implemented | MEDIUM |
| Camera constraints | Not implemented | LOW |
| Look-at target layer | Not implemented | MEDIUM |

---

# PART 5: DEPTHFLOW SYSTEM

## 5.1 Current Implementation

**Backend:** `ui/src/services/depthflow.ts` (~1200 lines)

### Motion Components (Stackable)

| Component | Status | Parameters |
|-----------|--------|------------|
| Linear | **Working** | direction, speed |
| Exponential | **Working** | base, exponent |
| Sine | **Working** | frequency, amplitude, phase |
| Cosine | **Working** | frequency, amplitude, phase |
| Arc | **Working** | radius, startAngle, endAngle |
| Bounce | **Working** | height, bounces, damping |
| Elastic | **Working** | amplitude, frequency, decay |
| Custom | **Working** | Expression-based |

### Depthflow Parameters

| Parameter | Backend | UI Wired |
|-----------|---------|----------|
| Depth Map Source | **Yes** | **Yes** |
| Parallax Amount | **Yes** | **Yes** |
| Motion Components | **Yes** | **Yes** |
| DOF Enabled | **Yes** | **Yes** |
| Focus Distance | **Yes** | **Yes** |
| Aperture | **Yes** | **Yes** |
| Blur Amount | **Yes** | **Yes** |
| Depth Range | **Yes** | **Yes** |
| Invert Depth | **Yes** | **Yes** |

### Rendering Modes

| Mode | Status | Notes |
|------|--------|-------|
| WebGL Shader | **Working** | Primary renderer |
| Canvas2D Fallback | **Working** | CPU fallback |
| K-means Slicing | **Working** | Automatic layer separation |

### Advanced Features

| Feature | Status | UI Wired |
|---------|--------|----------|
| Camera to Depthflow Sync | **Working** | **Yes** |
| Multiple Motion Stacking | **Working** | **Yes** |
| Audio-reactive Motion | **Working** | **Partial** |
| Depth Slicing (K-means) | **Working** | **Yes** |

### Missing Features

| Feature | Status | Priority |
|---------|--------|----------|
| Optical flow | Not implemented | HIGH |
| Inpainting for disocclusion | Not implemented | HIGH |
| True 3D mesh from depth | Not implemented | MEDIUM |
| Normal map integration | Partial | MEDIUM |
| Depth-aware compositing | Not implemented | HIGH |

---

# PART 6: UI WIRING GAPS SUMMARY

## Critical Missing UI Components

### 1. Emitter Shape Selector (CRITICAL)

**Impact:** Unlocks 6 additional emitter shapes already in backend

**Location:** ParticleProperties.vue, after emitter position controls

```vue
<div class="property-row">
  <label>Emitter Shape</label>
  <select @change="updateEmitter(emitter.id, 'shape', $event.target.value)">
    <option value="point">Point</option>
    <option value="line">Line</option>
    <option value="circle">Circle</option>
    <option value="box">Box</option>
    <option value="sphere">Sphere</option>
    <option value="ring">Ring (Donut)</option>
    <option value="spline">Spline Path</option>
  </select>
</div>

<!-- Conditional shape parameters -->
<template v-if="emitter.shape === 'circle' || emitter.shape === 'sphere' || emitter.shape === 'ring'">
  <div class="property-row">
    <label>Radius</label>
    <input type="range" :value="emitter.shapeRadius" min="0.01" max="1" step="0.01"
      @input="updateEmitter(emitter.id, 'shapeRadius', Number($event.target.value))" />
    <span class="value-display">{{ emitter.shapeRadius?.toFixed(2) }}</span>
  </div>
</template>

<template v-if="emitter.shape === 'ring'">
  <div class="property-row">
    <label>Inner Radius</label>
    <input type="range" :value="emitter.shapeInnerRadius" min="0" max="0.5" step="0.01"
      @input="updateEmitter(emitter.id, 'shapeInnerRadius', Number($event.target.value))" />
    <span class="value-display">{{ emitter.shapeInnerRadius?.toFixed(2) }}</span>
  </div>
</template>

<template v-if="emitter.shape === 'box' || emitter.shape === 'line'">
  <div class="property-row">
    <label>Width</label>
    <input type="range" :value="emitter.shapeWidth" min="0.01" max="1" step="0.01"
      @input="updateEmitter(emitter.id, 'shapeWidth', Number($event.target.value))" />
    <span class="value-display">{{ emitter.shapeWidth?.toFixed(2) }}</span>
  </div>
</template>

<template v-if="emitter.shape === 'box'">
  <div class="property-row">
    <label>Height</label>
    <input type="range" :value="emitter.shapeHeight" min="0.01" max="1" step="0.01"
      @input="updateEmitter(emitter.id, 'shapeHeight', Number($event.target.value))" />
    <span class="value-display">{{ emitter.shapeHeight?.toFixed(2) }}</span>
  </div>
</template>

<template v-if="['circle', 'box', 'sphere'].includes(emitter.shape)">
  <div class="property-row checkbox-row">
    <label>
      <input type="checkbox" :checked="emitter.emitFromEdge"
        @change="updateEmitter(emitter.id, 'emitFromEdge', $event.target.checked)" />
      Emit from Edge Only
    </label>
  </div>
</template>

<template v-if="emitter.shape === 'spline'">
  <div class="property-row">
    <label>Spline Layer</label>
    <select @change="updateEmitterSplinePath(emitter.id, 'layerId', $event.target.value)">
      <option value="">Select layer...</option>
      <option v-for="layer in splineLayers" :key="layer.id" :value="layer.id">
        {{ layer.name }}
      </option>
    </select>
  </div>
  <div class="property-row">
    <label>Emit Mode</label>
    <select @change="updateEmitterSplinePath(emitter.id, 'emitMode', $event.target.value)">
      <option value="random">Random</option>
      <option value="uniform">Uniform</option>
      <option value="sequential">Sequential</option>
      <option value="start">Near Start</option>
      <option value="end">Near End</option>
    </select>
  </div>
  <div class="property-row checkbox-row">
    <label>
      <input type="checkbox" :checked="emitter.splinePath?.alignToPath"
        @change="updateEmitterSplinePath(emitter.id, 'alignToPath', $event.target.checked)" />
      Align to Path Direction
    </label>
  </div>
</template>
```

### 2. Collision Panel (CRITICAL)

**Impact:** Enables entire collision system already implemented

**Location:** New section in ParticleProperties.vue

```vue
<!-- Collision Section -->
<div class="property-section">
  <div class="section-header" @click="toggleSection('collision')">
    <i class="pi" :class="expandedSections.has('collision') ? 'pi-chevron-down' : 'pi-chevron-right'" />
    <span>Collision</span>
  </div>
  <div v-if="expandedSections.has('collision')" class="section-content">
    <div class="property-row checkbox-row">
      <label>
        <input type="checkbox" :checked="collisionConfig.enabled"
          @change="updateCollision('enabled', $event.target.checked)" />
        Enable Collision
      </label>
    </div>

    <template v-if="collisionConfig.enabled">
      <div class="subsection-divider">Environment Boundaries</div>

      <div class="property-row checkbox-row">
        <label>
          <input type="checkbox" :checked="collisionConfig.floorEnabled"
            @change="updateCollision('floorEnabled', $event.target.checked)" />
          Floor
        </label>
      </div>
      <div v-if="collisionConfig.floorEnabled" class="property-row">
        <label>Floor Y</label>
        <input type="range" :value="collisionConfig.floorY" min="0" max="1" step="0.01"
          @input="updateCollision('floorY', Number($event.target.value))" />
        <span class="value-display">{{ collisionConfig.floorY?.toFixed(2) }}</span>
      </div>

      <div class="property-row checkbox-row">
        <label>
          <input type="checkbox" :checked="collisionConfig.ceilingEnabled"
            @change="updateCollision('ceilingEnabled', $event.target.checked)" />
          Ceiling
        </label>
      </div>
      <div v-if="collisionConfig.ceilingEnabled" class="property-row">
        <label>Ceiling Y</label>
        <input type="range" :value="collisionConfig.ceilingY" min="0" max="1" step="0.01"
          @input="updateCollision('ceilingY', Number($event.target.value))" />
        <span class="value-display">{{ collisionConfig.ceilingY?.toFixed(2) }}</span>
      </div>

      <div class="property-row checkbox-row">
        <label>
          <input type="checkbox" :checked="collisionConfig.wallsEnabled"
            @change="updateCollision('wallsEnabled', $event.target.checked)" />
          Walls (Left/Right)
        </label>
      </div>

      <div class="subsection-divider">Particle-to-Particle</div>

      <div class="property-row checkbox-row">
        <label>
          <input type="checkbox" :checked="collisionConfig.particleCollision"
            @change="updateCollision('particleCollision', $event.target.checked)" />
          Enable Particle Collision
        </label>
      </div>

      <template v-if="collisionConfig.particleCollision">
        <div class="property-row">
          <label>Collision Radius</label>
          <input type="range" :value="collisionConfig.particleCollisionRadius" min="0.5" max="3" step="0.1"
            @input="updateCollision('particleCollisionRadius', Number($event.target.value))" />
          <span class="value-display">{{ collisionConfig.particleCollisionRadius?.toFixed(1) }}x</span>
        </div>

        <div class="property-row">
          <label>Response</label>
          <select :value="collisionConfig.particleCollisionResponse"
            @change="updateCollision('particleCollisionResponse', $event.target.value)">
            <option value="bounce">Bounce</option>
            <option value="absorb">Absorb (merge)</option>
            <option value="explode">Explode (trigger sub-emitters)</option>
          </select>
        </div>

        <div class="property-row">
          <label>Damping</label>
          <input type="range" :value="collisionConfig.particleCollisionDamping" min="0" max="1" step="0.05"
            @input="updateCollision('particleCollisionDamping', Number($event.target.value))" />
          <span class="value-display">{{ (collisionConfig.particleCollisionDamping * 100)?.toFixed(0) }}%</span>
        </div>
      </template>

      <div class="subsection-divider">Physics</div>

      <div class="property-row">
        <label>Bounciness</label>
        <input type="range" :value="collisionConfig.bounciness" min="0" max="1" step="0.05"
          @input="updateCollision('bounciness', Number($event.target.value))" />
        <span class="value-display">{{ collisionConfig.bounciness?.toFixed(2) }}</span>
      </div>

      <div class="property-row">
        <label>Surface Friction</label>
        <input type="range" :value="collisionConfig.friction" min="0" max="1" step="0.05"
          @input="updateCollision('friction', Number($event.target.value))" />
        <span class="value-display">{{ collisionConfig.friction?.toFixed(2) }}</span>
      </div>
    </template>
  </div>
</div>
```

### 3. Sprite Assignment (HIGH)

**Impact:** Makes sprite import actually useful

**Location:** Inside emitter content, ParticleProperties.vue

```vue
<div class="subsection-divider">Sprite Texture</div>

<div class="property-row checkbox-row">
  <label>
    <input type="checkbox" :checked="emitter.sprite?.enabled"
      @change="updateEmitterSprite(emitter.id, 'enabled', $event.target.checked)" />
    Use Sprite Texture
  </label>
</div>

<template v-if="emitter.sprite?.enabled">
  <div class="property-row">
    <label>Sprite</label>
    <select :value="emitter.sprite?.imageUrl || ''"
      @change="updateEmitterSprite(emitter.id, 'imageUrl', $event.target.value)">
      <option value="">None (use shape)</option>
      <option v-for="sprite in assetStore.spriteSheetList" :key="sprite.id" :value="sprite.textureUrl">
        {{ sprite.name }}
      </option>
    </select>
  </div>

  <template v-if="emitter.sprite?.imageUrl">
    <div class="property-row checkbox-row">
      <label>
        <input type="checkbox" :checked="emitter.sprite?.isSheet"
          @change="updateEmitterSprite(emitter.id, 'isSheet', $event.target.checked)" />
        Is Sprite Sheet (animated)
      </label>
    </div>

    <template v-if="emitter.sprite?.isSheet">
      <div class="property-row">
        <label>Columns</label>
        <input type="number" :value="emitter.sprite?.columns || 1" min="1" max="16"
          @input="updateEmitterSprite(emitter.id, 'columns', Number($event.target.value))" />
      </div>
      <div class="property-row">
        <label>Rows</label>
        <input type="number" :value="emitter.sprite?.rows || 1" min="1" max="16"
          @input="updateEmitterSprite(emitter.id, 'rows', Number($event.target.value))" />
      </div>
      <div class="property-row">
        <label>Frame Rate</label>
        <input type="number" :value="emitter.sprite?.frameRate || 30" min="1" max="120"
          @input="updateEmitterSprite(emitter.id, 'frameRate', Number($event.target.value))" />
      </div>
      <div class="property-row">
        <label>Play Mode</label>
        <select :value="emitter.sprite?.playMode || 'loop'"
          @change="updateEmitterSprite(emitter.id, 'playMode', $event.target.value)">
          <option value="loop">Loop</option>
          <option value="once">Play Once</option>
          <option value="pingpong">Ping Pong</option>
          <option value="random">Random Frame</option>
        </select>
      </div>
    </template>

    <div class="property-row checkbox-row">
      <label>
        <input type="checkbox" :checked="emitter.sprite?.alignToVelocity"
          @change="updateEmitterSprite(emitter.id, 'alignToVelocity', $event.target.checked)" />
        Align to Movement Direction
      </label>
    </div>

    <div class="property-row checkbox-row">
      <label>
        <input type="checkbox" :checked="emitter.sprite?.rotationEnabled"
          @change="updateEmitterSprite(emitter.id, 'rotationEnabled', $event.target.checked)" />
        Enable Rotation
      </label>
    </div>

    <template v-if="emitter.sprite?.rotationEnabled">
      <div class="property-row">
        <label>Rotation Speed</label>
        <input type="range" :value="emitter.sprite?.rotationSpeed || 0" min="-360" max="360" step="5"
          @input="updateEmitterSprite(emitter.id, 'rotationSpeed', Number($event.target.value))" />
        <span class="value-display">{{ emitter.sprite?.rotationSpeed || 0 }}°/f</span>
      </div>
      <div class="property-row">
        <label>Speed Variance</label>
        <input type="range" :value="emitter.sprite?.rotationSpeedVariance || 0" min="0" max="180" step="5"
          @input="updateEmitterSprite(emitter.id, 'rotationSpeedVariance', Number($event.target.value))" />
        <span class="value-display">±{{ emitter.sprite?.rotationSpeedVariance || 0 }}°</span>
      </div>
    </template>
  </template>
</template>
```

### 4. Motion Blur Controls (MEDIUM)

**Location:** Render Options section, ParticleProperties.vue

```vue
<div class="subsection-divider">Motion Blur</div>

<div class="property-row checkbox-row">
  <label>
    <input type="checkbox" :checked="renderOptions.motionBlur"
      @change="updateRenderOption('motionBlur', $event.target.checked)" />
    Enable Motion Blur
  </label>
</div>

<template v-if="renderOptions.motionBlur">
  <div class="property-row">
    <label>Strength</label>
    <input type="range" :value="renderOptions.motionBlurStrength" min="0" max="1" step="0.05"
      @input="updateRenderOption('motionBlurStrength', Number($event.target.value))" />
    <span class="value-display">{{ renderOptions.motionBlurStrength?.toFixed(2) }}</span>
  </div>

  <div class="property-row">
    <label>Samples</label>
    <input type="range" :value="renderOptions.motionBlurSamples" min="2" max="16" step="1"
      @input="updateRenderOption('motionBlurSamples', Number($event.target.value))" />
    <span class="value-display">{{ renderOptions.motionBlurSamples }}</span>
  </div>
</template>
```

### 5. Emissive/Bloom Controls (LOW)

**Location:** Render Options section, ParticleProperties.vue

```vue
<div class="subsection-divider">Emissive / Bloom</div>

<div class="property-row checkbox-row">
  <label>
    <input type="checkbox" :checked="renderOptions.emissiveEnabled"
      @change="updateRenderOption('emissiveEnabled', $event.target.checked)" />
    Enable Emissive (for Bloom)
  </label>
</div>

<template v-if="renderOptions.emissiveEnabled">
  <div class="property-row">
    <label>Intensity</label>
    <input type="range" :value="renderOptions.emissiveIntensity" min="0" max="10" step="0.1"
      @input="updateRenderOption('emissiveIntensity', Number($event.target.value))" />
    <span class="value-display">{{ renderOptions.emissiveIntensity?.toFixed(1) }}</span>
  </div>

  <div class="property-row">
    <label>Color Override</label>
    <input type="color" :value="emissiveColorHex"
      @input="updateEmissiveColor($event.target.value)" />
    <button class="small-btn" @click="clearEmissiveColor" title="Use particle color">
      <i class="pi pi-times" />
    </button>
  </div>
</template>
```

### 6. Audio Parameter Mapping (HIGH)

**Location:** New section in ParticleProperties.vue or separate AudioMappingPanel.vue

```vue
<!-- Audio Reactivity Section -->
<div class="property-section">
  <div class="section-header" @click="toggleSection('audio')">
    <i class="pi" :class="expandedSections.has('audio') ? 'pi-chevron-down' : 'pi-chevron-right'" />
    <span>Audio Reactivity</span>
    <button class="add-btn" @click.stop="addAudioMapping" title="Add Mapping">
      <i class="pi pi-plus" />
    </button>
  </div>
  <div v-if="expandedSections.has('audio')" class="section-content">
    <div v-for="mapping in audioMappings" :key="mapping.id" class="audio-mapping-item">
      <div class="mapping-header">
        <span class="mapping-label">{{ mapping.feature }} → {{ mapping.property }}</span>
        <button class="remove-btn" @click="removeAudioMapping(mapping.id)">
          <i class="pi pi-trash" />
        </button>
      </div>

      <div class="property-row">
        <label>Audio Feature</label>
        <select :value="mapping.feature" @change="updateAudioMapping(mapping.id, 'feature', $event.target.value)">
          <option value="amplitude">Amplitude (overall)</option>
          <option value="bass">Bass (low freq)</option>
          <option value="mid">Mid (mid freq)</option>
          <option value="high">High (high freq)</option>
          <option value="onset">Onset (transients)</option>
          <option value="beat">Beat</option>
          <option value="rms">RMS Energy</option>
        </select>
      </div>

      <div class="property-row">
        <label>Target</label>
        <select :value="mapping.target" @change="updateAudioMapping(mapping.id, 'target', $event.target.value)">
          <option value="system">Global System</option>
          <option value="emitter">Emitter</option>
          <option value="forceField">Force Field</option>
        </select>
      </div>

      <div v-if="mapping.target === 'emitter'" class="property-row">
        <label>Emitter</label>
        <select :value="mapping.targetId" @change="updateAudioMapping(mapping.id, 'targetId', $event.target.value)">
          <option value="*">All Emitters</option>
          <option v-for="e in emitters" :key="e.id" :value="e.id">{{ e.name }}</option>
        </select>
      </div>

      <div class="property-row">
        <label>Property</label>
        <select :value="mapping.property" @change="updateAudioMapping(mapping.id, 'property', $event.target.value)">
          <option value="emissionRate">Emission Rate</option>
          <option value="speed">Speed</option>
          <option value="size">Size</option>
          <option value="gravity">Gravity</option>
          <option value="windStrength">Wind Strength</option>
          <option value="turbulenceStrength">Turbulence</option>
        </select>
      </div>

      <div class="property-row">
        <label>Scale</label>
        <input type="range" :value="mapping.scale" min="0" max="5" step="0.1"
          @input="updateAudioMapping(mapping.id, 'scale', Number($event.target.value))" />
        <span class="value-display">{{ mapping.scale?.toFixed(1) }}x</span>
      </div>

      <div class="property-row">
        <label>Smoothing</label>
        <input type="range" :value="mapping.smoothing" min="0" max="1" step="0.05"
          @input="updateAudioMapping(mapping.id, 'smoothing', Number($event.target.value))" />
        <span class="value-display">{{ mapping.smoothing?.toFixed(2) }}</span>
      </div>

      <div class="property-row checkbox-row">
        <label>
          <input type="checkbox" :checked="mapping.invert"
            @change="updateAudioMapping(mapping.id, 'invert', $event.target.checked)" />
          Invert
        </label>
      </div>
    </div>

    <div v-if="audioMappings.length === 0" class="empty-message">
      No audio mappings. Click + to add reactive parameters.
    </div>
  </div>
</div>
```

---

# PART 7: IMPLEMENTATION ROADMAP

## Phase 1: UI Wiring (Estimated: 15-20 hours)

**Goal:** Expose all existing backend features in UI

| Task | File | Effort | Impact |
|------|------|--------|--------|
| Add emitter shape dropdown | ParticleProperties.vue | 3h | HIGH |
| Add shape parameter sliders | ParticleProperties.vue | 2h | HIGH |
| Add spline emitter layer selector | ParticleProperties.vue | 2h | HIGH |
| Add collision section | ParticleProperties.vue | 4h | HIGH |
| Add sprite assignment dropdown | ParticleProperties.vue | 3h | HIGH |
| Add motion blur controls | ParticleProperties.vue | 1h | MEDIUM |
| Add emissive/bloom controls | ParticleProperties.vue | 1h | LOW |
| Add audio mapping panel | ParticleProperties.vue | 4h | HIGH |

**Deliverable:** All 7 emitter shapes accessible, collision working, sprites assignable

## Phase 2: Critical Features (Estimated: 40-50 hours)

**Goal:** Match RyanOnTheInside for ComfyUI workflow parity

| Task | Files | Effort | Impact |
|------|-------|--------|--------|
| Depth map emission | particleSystem.ts, ParticleProperties.vue | 12h | CRITICAL |
| Mask-based emission | particleSystem.ts, ParticleProperties.vue | 10h | CRITICAL |
| Multi-band audio analysis | audioFeatures.ts | 8h | HIGH |
| Audio parameter mapping backend | particleSystem.ts | 6h | HIGH |
| Preset save/load system | New files | 8h | HIGH |
| Preset browser UI | New component | 6h | HIGH |

**Deliverable:** Particles emit from depth/masks, audio-reactive parameters, saveable presets

## Phase 3: Professional Features (Estimated: 80-100 hours)

**Goal:** Approach Trapcode Particular lite quality

| Task | Effort | Impact |
|------|--------|--------|
| Layer emitter (emit from layer pixels) | 16h | HIGH |
| Flow field modifier | 20h | HIGH |
| Additional sub-emitter triggers (collision, birth, bounce) | 8h | MEDIUM |
| Curve editor for modulations | 16h | MEDIUM |
| Collider objects (arbitrary shapes) | 16h | MEDIUM |
| 50+ preset library creation | 20h | HIGH |
| LAS/LAZ point cloud parsing | 8h | HIGH |

**Deliverable:** Layer-based emission, flow fields, rich preset library

## Phase 4: Advanced Features (Estimated: 150+ hours)

**Goal:** Industry-leading particle system

| Task | Effort | Impact |
|------|--------|--------|
| WebGPU compute shaders | 50h | HIGH |
| 1M+ particle support | Included above | HIGH |
| Fluid simulation (SPH) | 60h | MEDIUM |
| Alembic cache export | 20h | MEDIUM |
| Particle meshing (marching cubes) | 40h | LOW |
| Point cloud LOD (octree) | 16h | HIGH |

**Deliverable:** WebGPU acceleration, fluid effects, industry-standard export

---

# PART 8: TESTING CHECKLIST

## Particle System

### Emitter Shapes
- [ ] Point emitter spawns at exact (x, y) position
- [ ] Line emitter spawns along perpendicular line of correct width
- [ ] Circle emitter: edge-only spawns on circumference
- [ ] Circle emitter: filled spawns uniformly (not clustered at center)
- [ ] Box emitter: edge-only spawns on perimeter
- [ ] Box emitter: filled spawns uniformly in area
- [ ] Sphere emitter: proper 3D distribution when viewed from camera
- [ ] Ring emitter spawns between inner and outer radius
- [ ] Spline emitter follows path with correct tangent alignment
- [ ] Spline emitter sequential mode progresses along path
- [ ] Mesh emitter spawns from imported vertices

### Collision
- [ ] Floor collision bounces particles with correct bounciness
- [ ] Ceiling collision reflects particles downward
- [ ] Wall collision contains particles horizontally
- [ ] Particle-particle collision detects overlaps correctly
- [ ] Bounce response preserves momentum * bounciness
- [ ] Absorb response: smaller particle dies, larger grows
- [ ] Explode response triggers sub-emitters on both particles
- [ ] Spatial hash performance: 10k particles colliding < 16ms

### Sprites
- [ ] Sprite texture renders instead of shape
- [ ] Sprite sheet animates through frames at correct rate
- [ ] Loop mode: cycles continuously
- [ ] Once mode: stops at last frame
- [ ] Pingpong mode: reverses at ends
- [ ] Random mode: different particles show different frames
- [ ] Align to velocity rotates sprite correctly
- [ ] Manual rotation adds to alignment

### Determinism
- [ ] Same seed produces identical particle positions
- [ ] Scrubbing backward restores exact state from cache
- [ ] Scrubbing forward continues deterministically
- [ ] Export produces identical frames on re-render
- [ ] Sub-emitter spawns are deterministic

### Audio Reactivity
- [ ] Burst on beat triggers correct particle count
- [ ] Emission rate scales with amplitude
- [ ] Size modulation responds to bass
- [ ] Mapping smoothing prevents jitter
- [ ] Multiple mappings can target same emitter

## Point Cloud

- [ ] PLY ASCII loads with correct colors
- [ ] PLY binary loads without corruption
- [ ] PCD format loads correctly
- [ ] XYZ format positions correctly
- [ ] PTS format includes intensity
- [ ] Color modes switch correctly
- [ ] Point size slider works
- [ ] 100k points renders at 60fps
- [ ] 1M points renders (may be <60fps)

## Camera

- [ ] All 22 trajectory presets execute correctly
- [ ] Easing applies to camera movement
- [ ] Camera bookmarks save and restore
- [ ] View presets snap to correct angles
- [ ] DOF preview shows blur
- [ ] Audio-reactive camera responds to beats

## Depthflow

- [ ] Parallax amount controls depth displacement
- [ ] Motion components stack correctly
- [ ] DOF blur matches depth
- [ ] K-means slicing creates correct layers
- [ ] WebGL and Canvas2D produce similar results
- [ ] Camera sync matches camera movement

---

# PART 9: PERFORMANCE TARGETS

| Metric | Target | Current | Notes |
|--------|--------|---------|-------|
| Particles @ 60fps (CPU) | 50,000 | ~30,000 | V8 JIT optimized |
| Particles @ 60fps (GPU TF) | 500,000 | ~100,000 | Transform Feedback |
| Particles @ 60fps (WebGPU) | 2,000,000 | N/A | Not implemented |
| Memory per particle | 64 bytes | 64 bytes | Cache-line aligned |
| Cache memory (100 frames, 10k) | <100MB | ~80MB | Acceptable |
| Sprite texture memory | <50MB | <50MB | Acceptable |
| Point cloud (1M points) | 30fps | ~20fps | Needs LOD |
| Collision detection (10k) | <16ms | ~12ms | Spatial hash working |

---

# PART 10: TYPE DEFINITIONS

## Core Particle Types

```typescript
// Emitter Configuration
interface EmitterConfig {
  id: string;
  name: string;
  enabled: boolean;

  // Position & Direction
  x: number;              // 0-1 normalized
  y: number;              // 0-1 normalized
  direction: number;      // degrees
  spread: number;         // degrees

  // Emission
  emissionRate: number;   // particles/second
  initialBurst: number;   // 0-1 (percentage)
  burstOnBeat: boolean;
  burstCount: number;

  // Particle Properties
  speed: number;
  speedVariance: number;
  size: number;
  sizeVariance: number;
  color: [number, number, number];
  particleLifetime: number;
  lifetimeVariance: number;

  // Shape
  shape: 'point' | 'line' | 'circle' | 'box' | 'sphere' | 'ring' | 'spline' | 'mesh';
  shapeRadius: number;
  shapeWidth: number;
  shapeHeight: number;
  shapeDepth: number;
  shapeInnerRadius: number;
  emitFromEdge: boolean;
  emitFromVolume: boolean;

  // Spline Path
  splinePath: SplinePathEmission | null;

  // Sprite
  sprite: SpriteConfig;
}

// Collision Configuration
interface CollisionConfig {
  enabled: boolean;

  // Particle-to-particle
  particleCollision: boolean;
  particleCollisionRadius: number;
  particleCollisionResponse: 'bounce' | 'absorb' | 'explode';
  particleCollisionDamping: number;

  // Layer collision
  layerCollision: boolean;
  layerCollisionLayerId: string | null;
  layerCollisionThreshold: number;

  // Environment
  floorEnabled: boolean;
  floorY: number;
  ceilingEnabled: boolean;
  ceilingY: number;
  wallsEnabled: boolean;

  // Physics
  bounciness: number;
  friction: number;
  spatialHashCellSize: number;
}

// Sprite Configuration
interface SpriteConfig {
  enabled: boolean;
  imageUrl: string | null;
  imageData: ImageBitmap | HTMLImageElement | null;
  isSheet: boolean;
  columns: number;
  rows: number;
  totalFrames: number;
  frameRate: number;
  playMode: 'loop' | 'once' | 'pingpong' | 'random';
  billboard: boolean;
  rotationEnabled: boolean;
  rotationSpeed: number;
  rotationSpeedVariance: number;
  alignToVelocity: boolean;
}

// Audio Binding
interface AudioBinding {
  id: string;
  feature: AudioFeature;
  target: 'emitter' | 'forceField' | 'system';
  targetId: string;
  property: string;
  scale: number;
  offset: number;
  smoothing: number;
  invert: boolean;
  clampMin: number;
  clampMax: number;
}

type AudioFeature =
  | 'amplitude'
  | 'bass'
  | 'mid'
  | 'high'
  | 'onset'
  | 'beat'
  | 'pitch'
  | 'spectralCentroid'
  | 'rms';
```

---

# PART 11: REFERENCES

## Industry Documentation
- Trapcode Particular: https://www.maxon.net/en/red-giant/trapcode-suite/particular
- X-Particles Manual: https://insydium.ltd/products/x-particles/
- RyanOnTheInside: https://github.com/RyanOnTheInside

## Technical References
- WebGL2 Transform Feedback: https://developer.mozilla.org/en-US/docs/Web/API/WebGL2RenderingContext/transformFeedbackVaryings
- WebGPU Compute: https://gpuweb.github.io/gpuweb/
- Simplex Noise: https://github.com/jwagner/simplex-noise.js
- LAS Specification: https://www.asprs.org/divisions-committees/lidar-division/laser-las-file-format-exchange-activities

## Internal References
- `ui/src/services/particleSystem.ts` - CPU simulation
- `ui/src/engine/particles/GPUParticleSystem.ts` - GPU simulation
- `ui/src/engine/particles/types.ts` - Type definitions
- `ui/src/components/properties/ParticleProperties.vue` - UI controls
