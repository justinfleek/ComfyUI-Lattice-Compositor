# CLAUDE.md - Weyl Compositor Development Guide

**Version:** 8.4 | **Last Updated:** December 23, 2025

---

## Quick Reference

| Resource | Location |
|----------|----------|
| Product Specification | [docs/PRODUCT_SPEC.md](docs/PRODUCT_SPEC.md) |
| Architecture | [docs/ARCHITECTURE.md](docs/ARCHITECTURE.md) |
| API Reference | [docs/SERVICE_API_REFERENCE.md](docs/SERVICE_API_REFERENCE.md) |
| Changelog | [CHANGELOG.md](CHANGELOG.md) |
| Debug Guide | [docs/DEBUG_TROUBLESHOOTING.md](docs/DEBUG_TROUBLESHOOTING.md) |
| **File Splitting Plan** | [FILE_SPLITTING_PLAN.md](FILE_SPLITTING_PLAN.md) |
| Integration Audit | [COMPREHENSIVE_INTEGRATION_AUDIT.md](COMPREHENSIVE_INTEGRATION_AUDIT.md) |
| Production Readiness | [PRODUCTION_READINESS_AUDIT.md](PRODUCTION_READINESS_AUDIT.md) |

---

## What is Weyl Compositor?

A **professional motion graphics compositor** for the **ComfyUI ecosystem**:
- Timeline, keyframes, curve editor, nested compositions
- Deterministic particle systems (scrub-safe)
- Audio reactivity with beat detection
- Matte export for AI video generation (Wan 2.1, AnimateDiff)

**Target Output:** 81 frames at 16fps = 5 seconds, dimensions divisible by 8

---

## Build Commands

```bash
cd ui

# Development
npm install        # First time only
npm run dev        # http://localhost:5173

# Production build
npm run build      # Outputs to ../web/js/

# Testing
npm test                           # Run all tests
npm test -- --reporter=verbose     # Verbose output
npm test -- audioFeatures.test.ts  # Specific test

# Type checking
npx tsc --noEmit
```

### Build Output

```
web/js/
├── weyl-compositor.js     # Main bundle (2.2MB)
├── weyl-compositor.css    # Styles (146KB)
├── weyl-three-vendor.js   # Three.js (2.4MB)
├── weyl-vue-vendor.js     # Vue (210KB)
└── extension.js           # ComfyUI registration
```

---

## Trade Dress Terminology

Use Weyl terms (not industry-trademarked terms) in new code:

| Avoid | Use Instead |
|-------|-------------|
| Pickwhip | **PropertyLink** |
| Graph Editor | **CurveEditor** |
| Adjustment Layer | **EffectLayer** |
| loopOut/loopIn | **repeatAfter/repeatBefore** |
| Solo | **Isolate** |
| Null Object | **Control** |
| Precomp | **NestedComp** |
| Anchor Point | **origin** |
| inPoint/outPoint | **startFrame/endFrame** |
| Time Remap | **SpeedMap** |
| Work Area | **RenderRange** |

Backwards compatibility pattern:
```typescript
const start = layer.startFrame ?? layer.inPoint ?? 0;
```

---

## The Determinism Rule (CRITICAL)

Every frame must be **reproducible**. Scrub to frame 50, then frame 10, then back to 50 = **identical output**.

### Forbidden Patterns
```typescript
// ❌ NEVER use in evaluation logic
Date.now()
performance.now()
Math.random()
this.state += delta     // Accumulation
previousFrame           // Frame-order dependent
```

### Required Patterns
```typescript
// ✅ Always use
const state = evaluate(frame, project)        // Pure function
const random = seededRNG(seed, frame, id)     // Seeded RNG
Object.freeze(result)                         // Immutable output
```

### Particle Checkpointing
Particles save state every 30 frames. To evaluate frame 75:
1. Load checkpoint at frame 60
2. Simulate frames 61-75
3. Result identical regardless of scrub order

---

## Architecture Overview

```
┌────────────────────────────────────────┐
│         PRESENTATION LAYER             │
│  Vue 3.5 + PrimeVue 4 (106 components) │
└────────────────┬───────────────────────┘
                 │
                 ▼
┌────────────────────────────────────────┐
│           STATE LAYER (Pinia)          │
│  compositorStore + 6 sub-stores        │
└────────────────┬───────────────────────┘
                 │
                 ▼
┌────────────────────────────────────────┐
│         ENGINE LAYER (Three.js)        │
│  WeylEngine, MotionEngine, Layers      │
└────────────────┬───────────────────────┘
                 │
                 ▼
┌────────────────────────────────────────┐
│          SERVICE LAYER (122)           │
│  Animation, Audio, Particles, Effects  │
└────────────────────────────────────────┘
```

### Key Files

| File | Purpose |
|------|---------|
| `engine/WeylEngine.ts` | Main engine facade |
| `engine/MotionEngine.ts` | Pure frame evaluation |
| `stores/compositorStore.ts` | Main state store |
| `services/interpolation.ts` | Keyframe math |
| `services/particleSystem.ts` | Deterministic particles |
| `services/expressions.ts` | Expression language |

### Store Actions

Located in `stores/actions/`:
- `layerActions.ts` - Layer CRUD
- `keyframeActions.ts` - Keyframe operations
- `projectActions.ts` - Project save/load
- `audioActions.ts` - Audio reactivity
- `effectActions.ts` - Effect stack
- `cameraActions.ts` - Camera presets

---

## Data Flow

```
User Scrubs Timeline
        │
        ▼
compositorStore.setFrame(50)
        │
        ▼
MotionEngine.evaluate(50, project)  ← Pure function
        │
        ├── interpolation.ts: Calculate property values
        ├── particleSystem.ts: Load checkpoint, simulate
        └── expressions.ts: Evaluate expressions
        │
        ▼
FrameState (frozen, immutable)
        │
        ▼
WeylEngine.applyFrameState()
        │
        ▼
WebGL Canvas Render
```

---

## Layer System

26 layer types (24 active + 2 deprecated aliases). See [PRODUCT_SPEC.md](docs/PRODUCT_SPEC.md#layer-types-25) for full list.

### Standard Properties (All Layers)

```typescript
interface Layer {
  id: string;
  name: string;
  type: LayerType;
  enabled: boolean;
  locked: boolean;

  // Timing
  startFrame: number;
  endFrame: number;

  // Transform (all animatable)
  transform: {
    position: AnimatableProperty<Vec3>;
    rotation: AnimatableProperty<Vec3>;
    scale: AnimatableProperty<Vec3>;
    origin: AnimatableProperty<Vec3>;
    opacity: AnimatableProperty<number>;
  };

  blendMode: BlendMode;
  effects: EffectInstance[];
  masks: Mask[];
}
```

### Transform Order
```
1. Translate by -origin
2. Scale
3. Rotate Z → Y → X
4. Translate by position
```

---

## Animation System

### Keyframe Structure

```typescript
interface Keyframe<T> {
  frame: number;
  value: T;
  interpolation: 'linear' | 'bezier' | 'hold';
  inHandle?: Vec2;
  outHandle?: Vec2;
  controlMode: 'linked' | 'free' | 'auto';
}
```

### Expression Context

```typescript
interface ExpressionContext {
  time: number;      // Seconds
  frame: number;     // Frame number
  value: T;          // Current value

  // Functions
  jitter(freq, amp): T;
  repeatAfter(type): T;
  repeatBefore(type): T;
  bounce(elasticity): T;
  inertia(friction): T;

  // Math
  sin, cos, abs, clamp, linear, random
}
```

### thisLayer / thisComp / thisProperty

Full AE-compatible expression references:

```typescript
// thisLayer - current layer properties
thisLayer.name                    // Layer name
thisLayer.index                   // Layer index (1-based)
thisLayer.transform.position      // [x, y, z]
thisLayer.transform.rotation      // [x, y, z]
thisLayer.transform.scale         // [x, y, z]
thisLayer.transform.opacity       // 0-100
thisLayer.effect("name")("param") // Effect parameter value
thisLayer.toComp([x, y, z])       // Convert to comp space

// thisComp - composition properties
thisComp.width                    // Composition width
thisComp.height                   // Composition height
thisComp.duration                 // Duration in seconds
thisComp.numLayers                // Number of layers
thisComp.layer("Name")            // Get layer by name
thisComp.layer(1)                 // Get layer by index (1-based)

// thisProperty - current property
thisProperty.value                // Current interpolated value
thisProperty.velocity             // Current velocity
thisProperty.numKeys              // Number of keyframes
thisProperty.key(n)               // Get keyframe by index
thisProperty.valueAtTime(t)       // Value at time t
```

### Effect Access in Expressions

```typescript
// Access effect on current layer
thisLayer.effect("Blur Amount")("Slider")

// Access effect on another layer
thisComp.layer("Control").effect("Slider Control")("Slider")

// Alternative syntax
thisLayer.effect("Blur").param("radius")
```

### Expression Validation

```typescript
import { validateExpression } from '@/services/expressions';

const result = validateExpression('wiggle(2, 10)');
// { valid: true }

const badResult = validateExpression('wiggle(2,');
// { valid: false, error: "Unexpected end of input" }
```

35 easing functions available. See [PRODUCT_SPEC.md](docs/PRODUCT_SPEC.md#easing-functions-35).

---

## Particle System

Fully deterministic using seeded RNG (Mulberry32) + checkpoints.

### Key Classes

```typescript
// Seeded random - DETERMINISTIC
class SeededRandom {
  constructor(seed: number);
  next(): number;        // 0-1
  nextRange(min, max): number;
}

// Particle evaluation
class ParticleSystem {
  evaluate(frame: number): Particle[];  // Load checkpoint, simulate
}
```

24 presets, 7 emitter shapes. See [PRODUCT_SPEC.md](docs/PRODUCT_SPEC.md#particle-system).

---

## Audio Reactivity

### Analysis Pipeline

```
Audio File → Web Audio API → audioWorker.js → Per-Frame Data
```

Features: amplitude, bass, mid, high, beat detection, BPM

### Audio Mapping

```typescript
interface AudioMapping {
  sourceFeature: 'amplitude' | 'bass' | 'mid' | 'beat';
  targetPropertyPath: string;  // e.g., 'transform.scale.x'
  sensitivity: number;
  smoothing: number;
  min: number;
  max: number;
}
```

---

## Effects Pipeline

22 effects in 4 categories. Effects processed top-to-bottom.

```typescript
interface EffectInstance {
  id: string;
  effectKey: string;
  enabled: boolean;
  parameters: Record<string, AnimatableProperty>;
}
```

See [PRODUCT_SPEC.md](docs/PRODUCT_SPEC.md#effects-22) for full list.

---

## Layer Styles

9 style types, rendered in fixed order BEFORE effects.

### Render Order

```
Layer Content
    ↓
1. Drop Shadow (behind)
2. Inner Shadow
3. Outer Glow (behind)
4. Inner Glow
5. Bevel and Emboss
6. Satin
7. Color Overlay
8. Gradient Overlay
9. Stroke
    ↓
Effects Stack
    ↓
Final Output
```

### Layer Styles Interface

```typescript
interface LayerStyles {
  enabled: boolean;
  blendingOptions?: StyleBlendingOptions;
  dropShadow?: DropShadowStyle;
  innerShadow?: InnerShadowStyle;
  outerGlow?: OuterGlowStyle;
  innerGlow?: InnerGlowStyle;
  bevelEmboss?: BevelEmbossStyle;
  satin?: SatinStyle;
  colorOverlay?: ColorOverlayStyle;
  gradientOverlay?: GradientOverlayStyle;
  stroke?: StrokeStyle;
}
```

### Style Properties (All Animatable)

| Style | Key Properties |
|-------|---------------|
| **Drop Shadow** | color, angle, distance, spread, size, noise |
| **Inner Shadow** | color, angle, distance, choke, size, noise |
| **Outer Glow** | color/gradient, technique, spread, size, range |
| **Inner Glow** | color/gradient, source (center/edge), choke, size |
| **Bevel & Emboss** | style, technique, depth, direction, soften, altitude |
| **Satin** | color, angle, distance, size, invert |
| **Color Overlay** | color, blend mode, opacity |
| **Gradient Overlay** | gradient, style, angle, scale, offset |
| **Stroke** | color/gradient, size, position (inside/outside/center) |

### Global Light

Styles using `useGlobalLight: true` share a composition-wide light angle:

```typescript
import { setGlobalLightAngle, getGlobalLightAngle } from '@/services/globalLight';

setGlobalLightAngle(compositionId, 120);  // 120 degrees
const angle = getGlobalLightAngle(compositionId, frame);
```

### Store Actions

```typescript
// Enable/disable
compositorStore.setLayerStylesEnabled(layerId, true);
compositorStore.setStyleEnabled(layerId, 'dropShadow', true);

// Update properties
compositorStore.updateStyleProperty(layerId, 'dropShadow', 'distance', 10);

// Quick add
compositorStore.addDropShadow(layerId);
compositorStore.addStroke(layerId, { size: 3, color: [255, 0, 0, 255] });

// Copy/paste
const styles = compositorStore.copyLayerStyles(layerId);
compositorStore.pasteLayerStyles(targetLayerId);

// Presets
compositorStore.applyStylePreset(layerId, 'neonGlow');
const presets = compositorStore.getStylePresetNames();
```

### Key Files

| File | Purpose |
|------|---------|
| `types/layerStyles.ts` | Type definitions |
| `services/effects/layerStyleRenderer.ts` | Main renderer |
| `services/effects/styles/*.ts` | Individual renderers (9) |
| `stores/actions/layerStyleActions.ts` | Store actions |
| `components/properties/styles/*.vue` | UI editors (11) |

---

## 3D Camera System

### Properties

```typescript
interface CameraLayerData {
  fov: AnimatableProperty<number>;
  near: number;
  far: number;
  dof: {
    enabled: boolean;
    focusDistance: AnimatableProperty<number>;
    aperture: AnimatableProperty<number>;
  };
  trajectory?: {
    preset: string;
    progress: AnimatableProperty<number>;
  };
}
```

22 trajectory presets. See [PRODUCT_SPEC.md](docs/PRODUCT_SPEC.md#trajectory-presets-22).

---

## AI Features

### AI Compositor Agent

Natural language interface using GPT-4o or Claude Sonnet.

Location: `services/ai/`

```typescript
const agent = getAIAgent();
await agent.processInstruction('Fade in the title over 1 second');
```

### Layer Decomposition (Qwen AI)

Decomposes images into 3-16 semantically-separated layers.

```
POST /weyl/decomposition/decompose
{
  "image": "data:image/png;base64,...",
  "num_layers": 5,
  "resolution": 640
}
```

---

## Common Tasks

### Adding a New Layer Type

1. Create class in `engine/layers/MyLayer.ts`
2. Register in `LayerManager.ts`
3. Add to `compositorStore.addLayer()`
4. Create properties component

### Adding a New Effect

1. Create renderer in `services/effects/myEffect.ts`
2. Register in `effectProcessor.ts`
3. Add to `EFFECT_DEFINITIONS`
4. Create parameter controls

### Adding a Keyboard Shortcut

In `composables/useKeyboardShortcuts.ts`:
```typescript
case 'MyKey':
  e.preventDefault();
  myAction();
  break;
```

---

## Testing

### Required Test Patterns

```typescript
// ✅ Test actual behavior
const result = evaluator.evaluate(property, 40);
expect(result).toBe(50);

// ✅ Test determinism
const state1 = particleSystem.evaluate(50);
particleSystem.reset();
const state2 = particleSystem.evaluate(50);
expect(state1).toEqual(state2);
```

### Forbidden Test Patterns

```typescript
// ❌ Surface-level tests
expect(fn).toBeDefined();
expect(layer).toHaveProperty('transform');
```

### Current Status

| Metric | Value |
|--------|-------|
| Tests Passing | 1,777 |
| Tests Skipped | 9 |
| Test Files | 48 |

---

## Troubleshooting

### Animation Not Playing
1. Check `playbackStore.isPlaying`
2. Verify `currentFrame < frameCount`
3. Check browser tab is focused

### Layer Not Visible
1. Check `layer.enabled === true`
2. Verify frame is between startFrame/endFrame
3. Check opacity > 0

### Particle Positions Change on Scrub
1. Verify using `SeededRandom`, not `Math.random()`
2. Check checkpoint system working
3. Ensure seed is consistent

### WebGL Context Lost
1. Close other tabs with WebGL
2. Reduce texture sizes
3. Context loss handlers exist in `WeylEngine.ts`

---

## UI Design System

### Design Tokens

```css
--weyl-void: #050505;           /* Background */
--weyl-surface-1: #121212;      /* Panels */
--weyl-accent: #8B5CF6;         /* Primary purple */
--weyl-text-primary: #E5E5E5;   /* Main text */
```

### Themes

6 gradient themes: Violet (default), Ocean, Sunset, Forest, Ember, Mono

### Semantic Keyframe Shapes

16 shapes encode easing type visually. Defined in `styles/keyframe-shapes.ts`.

---

## Critical Integration Fixes (December 22, 2025)

The following critical integration gaps were identified and fixed:

### 1. PoseLayer Integration
- **Problem:** `PoseLayer.ts` existed but was not imported or used in `LayerManager.ts`
- **Fix:** Added import and `case 'pose':` in `LayerManager.ts:408-409`
- **Result:** Pose layers now create correctly instead of falling back to ControlLayer

### 2. EffectLayer/Adjustment Layer Properties
- **Problem:** `effectLayer` and `adjustment` layer types had no case in `PropertiesPanel.vue`
- **Fix:** Added cases at `PropertiesPanel.vue:480-482` returning `EffectControlsPanel`
- **Result:** Effect layers now show their properties panel correctly

### 3. Physics System Integration
- **Problem:** Complete physics system existed but was NOT wired to UI
- **Fix:**
  - Added Physics section to `PropertiesPanel.vue:255-264`
  - Created `stores/actions/physicsActions.ts` (440+ lines)
  - Exported from `stores/actions/index.ts`
- **Result:** Physics can now be enabled/configured on any layer

### New Store Module: physicsActions.ts

Key functions:
- `enableLayerPhysics(store, layerId, config)` - Enable physics for layer
- `disableLayerPhysics(store, layerId)` - Disable physics
- `stepPhysics(store, deltaTime)` - Step simulation
- `evaluatePhysicsAtFrame(store, frame)` - Deterministic evaluation
- `bakePhysicsToKeyframes(store, layerId, options)` - Bake to keyframes
- `resetPhysicsSimulation(store)` - Reset simulation

---

## File Splitting Plan

**26 files exceed 1500 lines (~20k tokens)** and need splitting for future Claude sessions.

See **[FILE_SPLITTING_PLAN.md](FILE_SPLITTING_PLAN.md)** for complete details.

### Priority Files (Must Split First)

| File | Lines | Status |
|------|-------|--------|
| `GPUParticleSystem.ts` | 3,556 | PENDING |
| `expressions.ts` | 3,136 | PENDING |
| `types/project.ts` | 3,069 | PENDING |
| `compositorStore.ts` | 3,037 | PARTIAL |
| `ParticleProperties.vue` | 3,022 | PENDING |
| `particleSystem.ts` | 2,720 | PENDING |

---

## Large Files (>2000 lines)

Use `offset` and `limit` parameters when reading:

| File | Lines | Purpose |
|------|-------|---------|
| `compositorStore.ts` | 2,763 | Main store |
| `particleSystem.ts` | 2,650 | Particle simulation |
| `GPUParticleSystem.ts` | 3,459 | GPU particles |
| `ParticleProperties.vue` | 2,404 | Particle UI |
| `SplineEditor.vue` | 2,095 | Spline editing |

---

## Tech Stack

| Technology | Version | Purpose |
|------------|---------|---------|
| Vue | 3.5 | UI framework |
| Pinia | 2.2 | State management |
| PrimeVue | 4.2 | Components |
| Three.js | r170 | 3D rendering |
| Vite | 5 | Build tool |
| Vitest | 1 | Testing |
| TypeScript | 5 | Type safety |

---

## Project Metrics

| Metric | Value |
|--------|-------|
| Lines of Code | 236,000 |
| TypeScript Files | 286 |
| Vue Components | 112 |
| Services | 165 |
| Layer Types | 26 |
| Effects | 69 |
| Easing Functions | 45 |
| Blend Modes | 24 |
| Camera Presets | 22 |
| Particle Presets | 24 |
| AI Agent Tools | 39 |
| Keyboard Shortcuts | 86+ |
| Total Exports | 2,788 |

---

## Recent Changes (December 22, 2025 - Tutorial 20)

### Tutorial 20: Advanced Trajectories & Export Pipeline

**Expression Functions (expressions.ts):**
- `smooth(width, samples)` - Temporal smoothing by averaging values over time window
- `posterizeTime(fps)` - Quantize time for step-motion effects (like 12fps animation)
- Both functions now available in expression context

**Keyframe Actions (keyframeActions.ts):**
- `scaleKeyframeTiming()` - Scale keyframe timing with anchor frame
- `timeReverseKeyframes()` - Reverse keyframe values (keep frames, swap values)
- `insertKeyframeOnPath()` - Insert interpolated keyframe on position motion path

**UI Enhancements (PropertyTrack.vue):**
- Ctrl+Alt+Drag keyframes to scale timing proportionally
- Right-click track context menu: "Add Keyframe", "Insert on Path", "Go to Frame"

**New Services:**
- `exportTemplates.ts` - Save/load/manage export configuration templates
- `projectCollection.ts` - Download project + assets as ZIP with manifest
- `rovingKeyframes.ts` - Roving keyframes for constant velocity motion

**Expression Functions Added:**
- `speedAtTime(t)` - Velocity magnitude (scalar speed) at time

**New UI Components:**
- `MotionPathOverlay.vue` - Visualize position keyframe paths in viewport
- `RenderSettingsPanel.vue` - Render quality, resolution, motion blur settings
- `OutputModulePanel.vue` - Format, color profile, destination settings

**Viewport Enhancements (ThreeCanvas.vue):**
- Motion path visualization for selected layers with position keyframes
- Diamond-shaped keyframe markers on motion paths
- Frame ticks every 5 frames along path
- Current position indicator

**Render Queue (WorkspaceLayout.vue):**
- RenderQueuePanel now wired to CollapsiblePanel in right sidebar

**Export Dialog (ExportDialog.vue):**
- "Collect Files" button downloads project + assets as ZIP

**Store Integration:**
- `store.scaleKeyframeTiming()` wrapper
- `store.timeReverseKeyframes()` wrapper
- `store.insertKeyframeOnPath()` wrapper
- `applyRovingToPosition()` action for roving keyframes

---

## Planned Features (Not Yet Integrated)

The following services are **complete implementations** but not yet wired into the UI:

| Service | Purpose | Status |
|---------|---------|--------|
| `colorDepthReactivity.ts` | Pixel-based color/depth sampling for audio-style reactivity | Complete, needs UI |
| `motionReactivity.ts` | Layer motion-based reactivity (velocity, acceleration) | Complete, needs UI |

These were inspired by RyanOnTheInside's ComfyUI nodes and provide frame-based reactive values. Integration would require adding UI in the Properties panel similar to audio reactivity mappings.

---

**For detailed feature documentation, see [docs/PRODUCT_SPEC.md](docs/PRODUCT_SPEC.md)**

---

*🤖 Documentation generated with [Claude Code](https://claude.com/claude-code)*
