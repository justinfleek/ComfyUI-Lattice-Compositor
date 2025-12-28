# Systemic Issues

These are patterns that appear across multiple files. Instead of logging separate bugs for each instance, we track the pattern here and reference it in FILES_ANALYZED.md.

---

## SYSTEMIC-001: NaN Frame Equality Fails

**Pattern:** `frame === frame` or `k.frame === frame` comparisons fail because `NaN === NaN` is always `false` in JavaScript.

**Impact:**
- NaN keyframes can never be found/matched
- NaN keyframes accumulate (always pushed, never replaced)
- Sort operations produce undefined order (`a.frame - b.frame` returns NaN)

**Individual bugs logged:** BUG-036, BUG-040, BUG-044, BUG-050

**Files affected (add as discovered):**
- cameraActions.ts - Line 207
- compositionActions.ts - Line 312
- keyframeActions.ts - Lines 128, 322, 444, 657, 666, 677, 687, 950, 1220 (17+ points)
- markerActions.ts - Lines 62, 105, 188, 280
- effectActions.ts - Line 150

**Fix approach:**
```typescript
// Option 1: Use Number.isNaN for equality
const existingIndex = keyframes.findIndex(k =>
  Number.isNaN(frame) ? Number.isNaN(k.frame) : k.frame === frame
);

// Option 2: Validate at input boundary (preferred)
if (!Number.isFinite(frame)) {
  console.warn('Invalid frame number:', frame);
  return null;
}
```

---

## SYSTEMIC-002: NaN Bypasses Comparison Guards

**Pattern:** `if (x < 0 || x >= length)` guards don't catch NaN because `NaN < 0` and `NaN >= length` are both `false`.

**Impact:**
- NaN indices bypass bounds checks
- `splice(NaN, 1)` treats NaN as 0, operating on wrong element
- `array[NaN]` returns undefined

**Individual bugs logged:** BUG-040, BUG-042, BUG-047

**Files affected:**
- compositionActions.ts - Line 312 (navigateToBreadcrumb)
- effectActions.ts - Lines 150-151 (reorderEffects)
- layerActions.ts - Line 595 (moveLayer)

**Fix approach:**
```typescript
// Use Number.isInteger for index validation
if (!Number.isInteger(index) || index < 0 || index >= array.length) {
  return;
}
```

---

## SYSTEMIC-003: Division by Zero / fps=0

**Pattern:** Division operations without zero-check, especially with fps values that use `?? defaultValue` (doesn't catch 0).

**Impact:**
- Produces Infinity or NaN
- Corrupts duration calculations, keyframe positions, velocity values

**Individual bugs logged:** BUG-034, BUG-039, BUG-045, BUG-046, BUG-048, BUG-049

**Files affected:**
- audioActions.ts - fps division
- compositionActions.ts - fps division
- keyframeActions.ts - Lines 958, 1312-1314
- layerActions.ts - Lines 1339, 1597

**Fix approach:**
```typescript
// Option 1: Use || instead of ?? (catches 0 and NaN)
const fps = store.fps || 16;

// Option 2: Explicit validation
if (!Number.isFinite(fps) || fps <= 0) {
  console.warn('Invalid fps:', fps);
  return;
}
const result = value / fps;
```

---

## SYSTEMIC-004: NaN Config/Parameter Values Stored

**Pattern:** Functions accept values without validation and store them directly. NaN/Infinity values don't crash immediately but corrupt rendering later.

**Impact:**
- Canvas operations with NaN produce no output (`ctx.scale(NaN, NaN)`)
- Effect parameters with NaN cause renderer failures
- Delayed corruption - bug appears far from source

**Individual bugs logged:** BUG-041, BUG-043

**Files affected:**
- depthflowActions.ts - Line 91 (updateDepthflowConfig)
- effectActions.ts - Line 78 (updateEffectParameter)
- layerActions.ts - Lines 465, 495 (updateLayer, updateLayerData)

**Fix approach:**
```typescript
// Validate before storing
for (const [key, value] of Object.entries(updates)) {
  if (typeof value === 'number' && !Number.isFinite(value)) {
    console.warn(`Invalid ${key} value: ${value}, ignoring`);
    continue;
  }
  target[key] = value;
}
```

---

## SYSTEMIC-005: Math.max/min Don't Catch NaN

**Pattern:** Using `Math.max(0, Math.min(value, limit))` for clamping, which propagates NaN.

**Impact:**
- `Math.min(NaN, x)` returns NaN
- `Math.max(0, NaN)` returns NaN
- Clamped value is NaN, corrupting state

**Individual bugs logged:** BUG-051

**Files affected:**
- playbackActions.ts - Lines 66, 133

**Fix approach:**
```typescript
// Validate before clamping
if (!Number.isFinite(value)) {
  console.warn('Invalid value:', value);
  return currentValue; // or return early
}
const clamped = Math.max(0, Math.min(value, limit));
```

---

## SYSTEMIC-006: Unbounded maxParticles Causes Infinite Loops

**Pattern:** `for (let i = 0; i < this.maxParticles; i++)` with no validation in constructor.

**Impact:**
- If maxParticles = Infinity, loop never terminates
- Browser tab freezes, requires force-close
- User loses unsaved work

**Individual bugs logged:** BUG-059, BUG-061, BUG-062, BUG-064, BUG-066

**Files affected:**
- SpatialHashGrid.ts - Line 59 (rebuild)
- ParticleConnectionSystem.ts - Line 87 (update)
- ParticleTrailSystem.ts - Line 116 (update)
- ParticleCollisionSystem.ts - Lines 101, 255 (applyBoundaryCollisions, applyParticleCollisions)
- ParticleGPUPhysics.ts - Line 456 (async readback callback)

**Fix approach:**
```typescript
// Validate in constructor:
const MAX_SAFE_PARTICLES = 1000000;

constructor(maxParticles: number, ...) {
  if (!Number.isFinite(maxParticles) || maxParticles < 0) {
    console.warn('Invalid maxParticles, using 10000');
    this.maxParticles = 10000;
  } else {
    this.maxParticles = Math.min(maxParticles, MAX_SAFE_PARTICLES);
  }
}
```

---

## Summary

| ID | Pattern | Bugs | Files |
|----|---------|------|-------|
| SYSTEMIC-001 | NaN Frame Equality | 4 | 5+ |
| SYSTEMIC-002 | NaN Bypasses Guards | 3 | 3+ |
| SYSTEMIC-003 | Division by Zero | 6 | 4+ |
| SYSTEMIC-004 | NaN Values Stored | 2 | 3+ |
| SYSTEMIC-005 | Math.max/min NaN | 1 | 1+ |
| SYSTEMIC-006 | Unbounded maxParticles | 5 | 5+ |

**Root Cause:** TypeScript's `number` type doesn't distinguish valid numbers from NaN/Infinity. Validation must happen at runtime boundaries.

**Recommended Fix Strategy:**
1. Create a `ValidNumber` branded type or validation utility
2. Validate at input boundaries (function parameters, JSON parsing)
3. Use `Number.isFinite()` for numeric validation
4. Use `||` instead of `??` for numeric defaults that should catch 0
