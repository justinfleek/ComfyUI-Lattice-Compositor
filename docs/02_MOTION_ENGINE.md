# WEYL COMPOSITOR — MOTION ENGINE

**Document ID**: 02_MOTION_ENGINE  
**Version**: 1.0.0  
**Status**: CANONICAL  
**Depends On**: [00_MASTER_GROUND_TRUTH.md](./00_MASTER_GROUND_TRUTH.md), [01_TYPE_DEFINITIONS.md](./01_TYPE_DEFINITIONS.md)

> MotionEngine is the **sole authority** for frame evaluation.
> If evaluation exists elsewhere, the architecture is broken.

---

## 1. CORE IDENTITY

MotionEngine is the single system that answers:

> "What is the evaluated state of the project at frame N?"

```typescript
interface MotionEngine {
  evaluate(
    frame: number,
    project: WeylProject,
    audioAnalysis?: AudioAnalysis
  ): FrameState
}
```

**No other system may evaluate animation.**

---

## 2. PURITY GUARANTEE

MotionEngine evaluation must be **pure**:

| Input | Output |
|-------|--------|
| Same frame + same project + same audio | **Identical FrameState** |

```typescript
// This MUST always be true
const a = motionEngine.evaluate(100, project, audio)
const b = motionEngine.evaluate(100, project, audio)
assert(deepEqual(a, b))  // MUST pass
assert(a.frame === b.frame)
```

---

## 3. RESPONSIBILITIES

### 3.1 What MotionEngine DOES

| Responsibility | Description |
|----------------|-------------|
| Interpolate properties | Compute values between keyframes |
| Resolve dependencies | Evaluate pickwhip links in correct order |
| Sample audio | Read pre-computed audio features at frame N |
| Evaluate visibility | Determine which layers are visible |
| Evaluate camera | Compute camera matrices |
| Request particles | Get particle snapshot from controller |
| Compose transforms | Build transform hierarchy |

### 3.2 What MotionEngine DOES NOT DO

| Forbidden | Why |
|-----------|-----|
| Store evaluated values | FrameState is returned, not stored |
| Advance simulations | No step(), tick(), or update() |
| Play audio | Audio is pre-computed lookup |
| Manage UI state | UI is separate concern |
| Render pixels | RenderEngine applies FrameState |
| Maintain internal state | Each call is independent |

---

## 4. EVALUATION PIPELINE

```
┌─────────────────────────────────────────────────────────────────────┐
│                     MotionEngine.evaluate(frame, project)           │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  1. Build dependency graph                                          │
│     └── Collect all property drivers                               │
│     └── Detect cycles (fail if found)                              │
│     └── Topological sort                                           │
│                                                                     │
│  2. Evaluate properties in dependency order                         │
│     └── For each property:                                          │
│         ├── If has driver: resolve source first                    │
│         └── Interpolate from keyframes at frame N                   │
│                                                                     │
│  3. Evaluate layers                                                 │
│     └── For each visible layer at frame N:                          │
│         ├── Evaluate transform properties                           │
│         ├── Build transform matrix                                  │
│         └── Create EvaluatedLayer                                   │
│                                                                     │
│  4. Evaluate camera                                                 │
│     └── Evaluate camera properties                                  │
│     └── Compute view/projection matrices                            │
│                                                                     │
│  5. Request particle snapshot                                       │
│     └── Call ParticleController.evaluateAtFrame(frame)              │
│                                                                     │
│  6. Sample audio features                                           │
│     └── Direct lookup in pre-computed arrays                        │
│                                                                     │
│  7. Compose FrameState                                              │
│     └── Combine all evaluated data                                  │
│     └── Object.freeze() the result                                  │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

---

## 5. INTERPOLATION

### 5.1 Interpolation Function

```typescript
function interpolateProperty<T>(
  property: AnimatableProperty<T>,
  frame: number
): T {
  const { keyframes, defaultValue } = property
  
  // No keyframes: return default
  if (keyframes.length === 0) {
    return defaultValue
  }
  
  // Before first keyframe
  if (frame <= keyframes[0].frame) {
    return keyframes[0].value
  }
  
  // After last keyframe
  if (frame >= keyframes[keyframes.length - 1].frame) {
    return keyframes[keyframes.length - 1].value
  }
  
  // Find surrounding keyframes
  let prevIdx = 0
  for (let i = 0; i < keyframes.length - 1; i++) {
    if (frame >= keyframes[i].frame && frame < keyframes[i + 1].frame) {
      prevIdx = i
      break
    }
  }
  
  const prev = keyframes[prevIdx]
  const next = keyframes[prevIdx + 1]
  
  // Interpolate based on type
  switch (prev.interpolation) {
    case 'hold':
      return prev.value
    case 'linear':
      return linearInterpolate(prev, next, frame)
    case 'bezier':
      return bezierInterpolate(prev, next, frame)
  }
}
```

### 5.2 Linear Interpolation

```typescript
function linearInterpolate<T>(
  prev: Keyframe<T>,
  next: Keyframe<T>,
  frame: number
): T {
  const t = (frame - prev.frame) / (next.frame - prev.frame)
  return lerp(prev.value, next.value, t)
}
```

### 5.3 Bezier Interpolation

```typescript
function bezierInterpolate<T>(
  prev: Keyframe<T>,
  next: Keyframe<T>,
  frame: number
): T {
  const t = (frame - prev.frame) / (next.frame - prev.frame)
  
  // Apply bezier easing if present
  const easedT = prev.easing 
    ? cubicBezier(t, prev.easing.outHandle, next.easing?.inHandle)
    : t
  
  return lerp(prev.value, next.value, easedT)
}
```

---

## 6. TRANSFORM EVALUATION

```typescript
function evaluateTransform(
  transform: TransformProperties,
  frame: number,
  propertyValues: Map<string, unknown>
): EvaluatedTransform {
  const position = getOrInterpolate(transform.position, propertyValues, frame)
  const rotation = getOrInterpolate(transform.rotation, propertyValues, frame)
  const scale = getOrInterpolate(transform.scale, propertyValues, frame)
  const anchor = getOrInterpolate(transform.anchor, propertyValues, frame)
  const opacity = getOrInterpolate(transform.opacity, propertyValues, frame)
  
  // Build transform matrix
  const matrix = composeMatrix(position, rotation, scale, anchor)
  
  return Object.freeze({
    position,
    rotation,
    scale,
    anchor,
    opacity,
    matrix
  })
}
```

---

## 7. OUTPUT REQUIREMENTS

### 7.1 FrameState Must Be Frozen

```typescript
function createFrameState(
  frame: number,
  layers: EvaluatedLayer[],
  camera: EvaluatedCamera,
  particles: ParticleSnapshot,
  audio: EvaluatedAudio
): FrameState {
  return Object.freeze({
    frame,
    timestamp: frame / project.composition.frameRate,
    layers: Object.freeze(layers.map(l => Object.freeze(l))),
    camera: Object.freeze(camera),
    particles: Object.freeze(particles),
    audio: Object.freeze(audio)
  })
}
```

### 7.2 Completeness

Every FrameState must include:
- All visible layers, fully evaluated
- Camera state with matrices
- Particle snapshot (empty if no particles)
- Audio features at frame (zeros if no audio)

---

## 8. FORBIDDEN PATTERNS

```typescript
// ❌ FORBIDDEN: Internal state
class MotionEngine {
  private lastFrame: number  // NO!
  private cache: Map<number, FrameState>  // NO!
}

// ❌ FORBIDDEN: Mutation
function evaluate(frame) {
  this.currentFrame = frame  // NO!
  this.layers.forEach(l => l.update(frame))  // NO!
}

// ❌ FORBIDDEN: Time-based
function evaluate(frame) {
  const elapsed = Date.now() - this.startTime  // NO!
  return interpolate(elapsed)  // NO!
}

// ❌ FORBIDDEN: Random
function evaluate(frame) {
  const noise = Math.random()  // NO!
}

// ✅ REQUIRED: Pure evaluation
function evaluate(frame: number, project: WeylProject): FrameState {
  const properties = evaluateAllProperties(project.composition, frame)
  const layers = evaluateAllLayers(project.composition, frame, properties)
  const camera = evaluateCamera(project.composition, frame, properties)
  return Object.freeze({ frame, layers, camera, ... })
}
```

---

## 9. ERROR HANDLING

| Error Condition | Action |
|-----------------|--------|
| Circular dependency | Throw with cycle path |
| Missing layer reference | Log warning, skip |
| Invalid keyframe data | Throw with details |
| Missing asset | Log warning, use placeholder |

---

## 10. TESTING REQUIREMENTS

```typescript
describe('MotionEngine', () => {
  it('is deterministic', () => {
    const a = motionEngine.evaluate(100, project)
    const b = motionEngine.evaluate(100, project)
    expect(a).toEqual(b)
  })

  it('is order-independent', () => {
    const forward = motionEngine.evaluate(100, project)
    motionEngine.evaluate(200, project)
    motionEngine.evaluate(50, project)
    const backward = motionEngine.evaluate(100, project)
    expect(forward).toEqual(backward)
  })

  it('produces frozen output', () => {
    const result = motionEngine.evaluate(0, project)
    expect(Object.isFrozen(result)).toBe(true)
  })

  it('does not modify project', () => {
    const before = JSON.stringify(project)
    motionEngine.evaluate(100, project)
    const after = JSON.stringify(project)
    expect(before).toBe(after)
  })
})
```

---

## 11. AUDIT CHECKLIST

Claude Code must verify:

- [ ] MotionEngine exists as single evaluation point
- [ ] No other code evaluates animation
- [ ] evaluate() is a pure function
- [ ] No internal state between calls
- [ ] All outputs are frozen
- [ ] No forbidden patterns present
- [ ] Interpolation is frame-based, not time-based
- [ ] Dependency order is respected
- [ ] Tests verify determinism

**Any evaluation outside MotionEngine is a critical violation.**

---

**Previous**: [01_TYPE_DEFINITIONS.md](./01_TYPE_DEFINITIONS.md)  
**Next**: [03_LAYER_SYSTEM.md](./03_LAYER_SYSTEM.md)
