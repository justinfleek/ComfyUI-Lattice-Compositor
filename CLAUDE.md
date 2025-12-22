# CLAUDE.md - Weyl Compositor Development Guide

**Version:** 8.0 | **Last Updated:** December 22, 2025

---

## Quick Reference

| Resource | Location |
|----------|----------|
| Product Specification | [docs/PRODUCT_SPEC.md](docs/PRODUCT_SPEC.md) |
| Architecture | [docs/ARCHITECTURE.md](docs/ARCHITECTURE.md) |
| API Reference | [docs/SERVICE_API_REFERENCE.md](docs/SERVICE_API_REFERENCE.md) |
| Changelog | [CHANGELOG.md](CHANGELOG.md) |
| Debug Guide | [docs/DEBUG_TROUBLESHOOTING.md](docs/DEBUG_TROUBLESHOOTING.md) |

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

Use Weyl terms (not Adobe After Effects terms) in new code:

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

25 layer types. See [PRODUCT_SPEC.md](docs/PRODUCT_SPEC.md#layer-types-25) for full list.

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
| Tests Passing | 1,615 |
| Tests Skipped | 9 |
| Test Files | 43 |

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

**For detailed feature documentation, see [docs/PRODUCT_SPEC.md](docs/PRODUCT_SPEC.md)**
