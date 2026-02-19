# effectProcessor.ts - COMPREHENSIVE AUDIT DOCUMENT

**File:** `ui/src/services/effectProcessor.ts`
**Lines:** 900
**Importers:** 18 (CRITICAL)
**Date:** 2026-01-06
**Auditor:** AI Assistant

---

## 1. FILE OVERVIEW

This file is the central effect processing engine. It:
1. Evaluates animated effect parameters at specific frames
2. Manages canvas buffer pools for performance
3. Caches effect results to avoid recomputation
4. Routes effects to GPU or CPU renderers
5. Handles audio-reactive effect modifications

**Critical Importance:** 18 other files import this. Any bug here affects:
- All effect rendering
- All layer compositing with effects
- All video export with effects
- Real-time preview
- GPU acceleration path

---

## 2. EXPORTED FUNCTIONS CATALOG

| # | Function | Line | Browser API | Testable in Node? |
|---|----------|------|-------------|-------------------|
| 1 | `clearEffectCaches` | 347 | No | ✅ Yes |
| 2 | `getEffectProcessorStats` | 355 | No | ✅ Yes |
| 3 | `cleanupEffectResources` | 369 | No | ✅ Yes |
| 4 | `registerEffectRenderer` | 410 | No | ✅ Yes |
| 5 | `evaluateEffectParameters` | 425 | No | ✅ Yes |
| 6 | `processEffectStack` | 484 | Canvas | ❌ Browser only |
| 7 | `processEffectStackAsync` | 609 | Canvas+GPU | ❌ Browser only |
| 8 | `isGPUEffectProcessingAvailable` | 808 | GPU | ❌ Browser only |
| 9 | `getGPUEffectCapabilities` | 816 | GPU | ❌ Browser only |
| 10 | `imageDataToCanvas` | 834 | Canvas | ❌ Browser only |
| 11 | `canvasToImageData` | 846 | Canvas | ❌ Browser only |
| 12 | `createMatchingCanvas` | 855 | Canvas | ❌ Browser only |
| 13 | `releaseCanvas` | 865 | Canvas | ❌ Browser only |
| 14 | `hasEnabledEffects` | 872 | No | ✅ Yes |
| 15 | `getRegisteredEffects` | 879 | No | ✅ Yes |

**Node-testable:** 6 functions
**Browser-only:** 9 functions

---

## 3. DETAILED FUNCTION ANALYSIS

### 3.1 `evaluateEffectParameters(effect, frame)` - Line 425

**Purpose:** Resolve AnimatableProperty values to concrete values at a specific frame.

**Inputs:**
- `effect: EffectInstance` - Contains parameters as AnimatableProperty objects
- `frame: number` - The frame number to evaluate at

**Outputs:**
- `EvaluatedEffectParams` - Object with same keys as effect.parameters, but concrete values

**Upstream Dependencies:**
- `interpolateProperty()` from `./interpolation.ts` - Already audited ✅

**Downstream Impact:**
- All effect renderers receive these evaluated params
- Audio modifiers applied after evaluation
- Context injection (_frame, _fps, _layerId) added after evaluation

**INVARIANTS TO TEST:**

| ID | Invariant | How to Test |
|----|-----------|-------------|
| EP-1 | Same effect + frame always returns same output | Property: determinism |
| EP-2 | Output keys match input parameter keys | Property: key preservation |
| EP-3 | Output contains no AnimatableProperty objects | Property: full resolution |
| EP-4 | Empty parameters → empty output | Edge case |
| EP-5 | Works for frame = 0 | Edge case |
| EP-6 | Works for very large frames (1000000) | Edge case |
| EP-7 | Works for negative frames | Edge case - interpolateProperty handles this |
| EP-8 | Non-animated property returns static value | Property test |
| EP-9 | At keyframe returns keyframe value | Property test |
| EP-10 | Between keyframes returns interpolated value | Property test |

**REAL-WORLD SCENARIOS:**

1. **Timeline scrubbing:** User drags playhead, params evaluated at many frames rapidly
   - Need: Determinism, no memory leaks, correct interpolation
   
2. **Render export:** Every frame evaluated sequentially
   - Need: Correct values at integer frames, no drift

3. **Effect with 100+ parameters:** Complex effects have many params
   - Need: All params evaluated, no missing keys

**POTENTIAL BUGS IDENTIFIED:**

| # | Line | Issue | Severity | Status |
|---|------|-------|----------|--------|
| 1 | 433 | `param as AnimatableProperty<any>` - no validation if param is not AnimatableProperty | P2 | INVESTIGATE |

**Bug Investigation #1:**
```typescript
// Line 431-434
for (const [key, param] of Object.entries(effect.parameters)) {
  const animatableProp = param as AnimatableProperty<any>;
  evaluated[key] = interpolateProperty(animatableProp, frame);
}
```

What if `param` is not actually an AnimatableProperty? Let me check what interpolateProperty does with invalid input.

---

### 3.2 `hasEnabledEffects(effects)` - Line 872

**Purpose:** Check if any effects in array are enabled.

**Inputs:**
- `effects: EffectInstance[]` - Array of effect instances

**Outputs:**
- `boolean` - true if at least one effect has `enabled: true`

**INVARIANTS TO TEST:**

| ID | Invariant | How to Test |
|----|-----------|-------------|
| HE-1 | Empty array → false | Edge case |
| HE-2 | All disabled → false | Property |
| HE-3 | Any enabled → true | Property |
| HE-4 | Single enabled in middle → true | Edge case |
| HE-5 | Matches `effects.some(e => e.enabled)` | Property: equivalence |

**REAL-WORLD SCENARIOS:**

1. **Performance optimization:** Skip effect processing if nothing to do
2. **UI indication:** Show "effects active" badge

**No bugs identified** - this is a simple `.some()` call.

---

### 3.3 `registerEffectRenderer(effectKey, renderer)` - Line 410

**Purpose:** Add an effect renderer to the global registry.

**Inputs:**
- `effectKey: string` - Unique identifier for the effect
- `renderer: EffectRenderer` - Function that processes the effect

**Outputs:** void

**Side Effects:** Modifies global `effectRenderers` Map

**INVARIANTS TO TEST:**

| ID | Invariant | How to Test |
|----|-----------|-------------|
| RE-1 | After registration, key appears in getRegisteredEffects() | Property |
| RE-2 | Registering same key replaces old renderer | Property |
| RE-3 | Empty string key is allowed (or should it throw?) | Edge case |
| RE-4 | Key with special characters works | Edge case |

**POTENTIAL BUGS IDENTIFIED:**

| # | Line | Issue | Severity | Status |
|---|------|-------|----------|--------|
| 2 | 414 | No validation of effectKey - empty string allowed | P3 | INVESTIGATE |
| 3 | 414 | No validation of renderer - could be null | P2 | INVESTIGATE |

---

### 3.4 `getRegisteredEffects()` - Line 879

**Purpose:** Get list of all registered effect keys.

**Inputs:** None

**Outputs:** `string[]` - Array of effect keys

**INVARIANTS TO TEST:**

| ID | Invariant | How to Test |
|----|-----------|-------------|
| GE-1 | Returns array | Type check |
| GE-2 | All elements are strings | Property |
| GE-3 | Contains all registered keys | Property after registration |

**No bugs identified.**

---

### 3.5 `clearEffectCaches()` - Line 347

**Purpose:** Clear effect cache and canvas pool.

**INVARIANTS TO TEST:**

| ID | Invariant | How to Test |
|----|-----------|-------------|
| CE-1 | After call, effectCache.size === 0 | Property |
| CE-2 | After call, canvasPool.total === 0 | Property |
| CE-3 | Idempotent - calling twice is same as once | Property |

**REAL-WORLD SCENARIOS:**

1. **Project load:** Clear old project's cached effects
2. **Memory pressure:** Manual cleanup when low on memory

---

### 3.6 `getEffectProcessorStats()` - Line 355

**Purpose:** Get cache and pool statistics.

**INVARIANTS TO TEST:**

| ID | Invariant | How to Test |
|----|-----------|-------------|
| ES-1 | effectCache.size >= 0 | Property |
| ES-2 | effectCache.size <= effectCache.maxSize | Property |
| ES-3 | canvasPool.available = total - inUse | Property |
| ES-4 | All values non-negative | Property |

---

## 4. INTERNAL FUNCTIONS ANALYSIS

### 4.1 `applyAudioModifiersToEffect()` - Line 31-92 (INTERNAL)

**Purpose:** Apply audio-reactive values to effect parameters.

**CRITICAL ANALYSIS:**

```typescript
// Line 43-44
const baseIntensity = params.intensity ?? 1;
params.intensity = baseIntensity * (1 + audioModifiers.glowIntensity);
```

**Issue:** If `audioModifiers.glowIntensity = -2`:
- Result: `baseIntensity * (1 + (-2)) = baseIntensity * -1 = NEGATIVE`
- Is negative intensity valid? Depends on effect implementation.

**POTENTIAL BUGS:**

| # | Line | Issue | Severity | Status |
|---|------|-------|----------|--------|
| 4 | 44 | Negative intensity possible if glowIntensity < -1 | P2 | INVESTIGATE |
| 5 | 52 | Negative radius possible if glowRadius < -0.4 (since base default is 20, 20 + (-0.5)*50 = -5) | P2 | INVESTIGATE |
| 6 | 76 | Very large glitchAmount could overflow | P3 | LOW RISK |
| 7 | 88 | Very large rgbSplitAmount could overflow | P3 | LOW RISK |

**Question:** Are audio modifiers bounded to [0, 1] or can they be any value?

---

### 4.2 CanvasPool class - Line 112-199 (INTERNAL)

**CRITICAL ANALYSIS:**

```typescript
// Line 138
const ctx = canvas.getContext("2d")!;
```

**Issue:** Non-null assertion. If browser has exhausted canvas contexts (typically 16 per page), `getContext("2d")` returns `null`. The `!` assertion doesn't actually check - it just tells TypeScript to ignore the null possibility. At runtime, `ctx` would be `null`, and subsequent operations would fail.

**POTENTIAL BUGS:**

| # | Line | Issue | Severity | Status |
|---|------|-------|----------|--------|
| 8 | 138 | getContext can return null if contexts exhausted | P1 | BROWSER TEST NEEDED |
| 9 | 125 | Exact dimension match only - inefficient for many different sizes | P3 | OPTIMIZATION |

---

### 4.3 EffectCache class - Line 220-338 (INTERNAL)

**CRITICAL ANALYSIS:**

```typescript
// Line 228-237 - hashParams
private hashParams(params: EvaluatedEffectParams): string {
  const str = JSON.stringify(params);
  let hash = 0;
  for (let i = 0; i < str.length; i++) {
    const char = str.charCodeAt(i);
    hash = (hash << 5) - hash + char;
    hash = hash & hash;
  }
  return hash.toString(36);
}
```

**Issues with JSON.stringify:**
1. Object key order affects output (but JS objects maintain insertion order since ES2015)
2. Circular references throw
3. Functions are stripped
4. `-0` becomes `"0"`
5. `undefined` values are dropped

**POTENTIAL BUGS:**

| # | Line | Issue | Severity | Status |
|---|------|-------|----------|--------|
| 10 | 230 | JSON.stringify throws on circular refs | P2 | UNLIKELY - params shouldn't have circulars |
| 11 | 230 | -0 and 0 hash the same | P3 | UNLIKELY to matter |
| 12 | 246 | Returns "" on null ctx - could cause collisions | P2 | BROWSER TEST NEEDED |

---

## 5. REAL-WORLD TEST SCENARIOS

### Scenario 1: Effect Chain with Animation

```
User Story: Artist has a layer with:
- Gaussian blur (radius animated 0→10 over 100 frames)
- Brightness adjustment (static 1.2)
- Glow effect (intensity animated 0→2)

Expected: At frame 50, blur=5, brightness=1.2, glow=1
```

**What could go wrong:**
- Interpolation produces wrong values
- Parameter evaluation order matters (it shouldn't)
- Animated vs static detection fails

### Scenario 2: Timeline Scrubbing

```
User Story: Artist drags playhead back and forth rapidly between frames 0-100
Expected: Parameters update smoothly, no memory leaks, no crashes
```

**What could go wrong:**
- Cache grows unbounded
- Memory leak from canvas pool
- Non-deterministic results

### Scenario 3: Audio-Reactive Effects

```
User Story: Artist enables audio reactivity for glow effect
Audio has beat at certain times with intensity 0.8
Expected: Glow pulses with the beat
```

**What could go wrong:**
- Negative values if audio modifier is negative
- Overflow if audio modifier is very large
- NaN propagation

### Scenario 4: Unregistered Effect

```
User Story: Project file references effect "custom-blur" but renderer not loaded
Expected: Clear error message, not silent skip
```

**What could go wrong:**
- Silent skip (BUG-078 - already fixed)
- Crash without useful message

---

## 6. PROPERTY TESTS NEEDED

### Category A: Pure Functions (Node.js testable)

| Test | Function | Property |
|------|----------|----------|
| A1 | evaluateEffectParameters | Determinism |
| A2 | evaluateEffectParameters | Key preservation |
| A3 | evaluateEffectParameters | Static values unchanged |
| A4 | evaluateEffectParameters | Animated values interpolate correctly |
| A5 | evaluateEffectParameters | Frame boundaries (before/after keyframes) |
| A6 | evaluateEffectParameters | NaN/Infinity frame handling |
| A7 | hasEnabledEffects | Equivalence to .some() |
| A8 | hasEnabledEffects | Empty array handling |
| A9 | registerEffectRenderer | Registration appears in getRegisteredEffects |
| A10 | registerEffectRenderer | Replacement behavior |
| A11 | getRegisteredEffects | All registered keys present |
| A12 | clearEffectCaches | Stats reset to zero |
| A13 | getEffectProcessorStats | Available = total - inUse |

### Category B: Browser-only (Canvas API)

| Test | Function | Property |
|------|----------|----------|
| B1 | processEffectStack | Empty effects returns input unchanged |
| B2 | processEffectStack | Disabled effects skipped |
| B3 | processEffectStack | Dimension preservation |
| B4 | processEffectStack | Determinism |
| B5 | processEffectStack | Unregistered effect throws |
| B6 | processEffectStack | Renderer error propagates |
| B7 | imageDataToCanvas | Round-trip with canvasToImageData |
| B8 | createMatchingCanvas/releaseCanvas | Pool recycles correctly |
| B9 | processEffectStackAsync | Falls back to CPU on GPU fail |
| B10 | processEffectStackAsync | Equivalent to sync path |

---

## 7. BUGS IDENTIFIED (SUMMARY)

### ⚠️ P0 CRITICAL: PARAMETER NAME MISMATCH (BUG-082)

**Location:** `effectProcessor.ts` lines 31-92 (`applyAudioModifiersToEffect`)

**Problem:** Audio-reactive modifiers set WRONG parameter names. The effects never receive the modifiers because they read different parameter names.

| Audio Modifier Sets | Effect Reads | Effect File |
|---------------------|--------------|-------------|
| `params.intensity` | `params.glow_intensity` | cinematicBloom.ts:789 |
| `params.radius` | `params.glow_radius` | cinematicBloom.ts:788 |
| `params.amount` | `params.glitch_amount` | stylizeRenderer.ts:185 |

**Impact:** 
- Audio-reactive glow intensity has NO EFFECT
- Audio-reactive glow radius has NO EFFECT  
- Audio-reactive glitch amount has NO EFFECT
- Users expect audio to drive effects but it doesn't work

**Root Cause:** 
The audio modifier code was written assuming generic parameter names (`intensity`, `radius`, `amount`) but the actual effect renderers use prefixed names (`glow_intensity`, `glow_radius`, `glitch_amount`).

**Fix Required:**
Change `effectProcessor.ts` to use correct parameter names:
```typescript
// Line 43-44: WRONG
params.intensity = baseIntensity * (1 + audioModifiers.glowIntensity);
// Should be:
params.glow_intensity = baseIntensity * (1 + audioModifiers.glowIntensity);

// Line 52: WRONG  
params.radius = baseRadius + audioModifiers.glowRadius * 50;
// Should be:
params.glow_radius = baseRadius + audioModifiers.glowRadius * 50;

// Line 76: WRONG
params.amount = baseAmount + audioModifiers.glitchAmount * 2;
// Should be:
params.glitch_amount = baseAmount + audioModifiers.glitchAmount * 2;
```

**Evidence:**
- `cinematicBloom.ts:787-789`: `const intensity = (params.glow_intensity ?? 100) / 100;`
- `stylizeRenderer.ts:185`: `const rawGlitchAmount = params.glitch_amount ?? 5;`

---

### Other Bugs Found

| Bug # | Line | Description | Severity | Type |
|-------|------|-------------|----------|------|
| 1 | 433 | Type assertion without validation | P2 | Code smell |
| 2 | 414 | Empty effectKey allowed | P3 | Edge case |
| 3 | 414 | Null renderer not validated | P2 | Edge case |
| 4 | 138 | getContext can return null | P1 | Browser limit |
| 5 | 125 | Exact dimension match only | P3 | Optimization |
| 6 | 230 | JSON.stringify circular ref | P2 | Defensive |
| 7 | 230 | -0 and 0 hash same | P3 | Edge case |
| 8 | 246 | Empty hash on null ctx | P2 | Browser limit |

**Already Fixed:** BUG-078 (unregistered effects throw)

---

## 8. NEXT STEPS

1. **Verify Bug #4, #5:** Check if audio modifiers can actually be negative
2. **Write property tests for Category A** (Node.js testable)
3. **Write browser tests for Category B**
4. **Add input validation for Bug #2, #3**
5. **Add null check for Bug #8**

---

*Document created: 2026-01-06*
*Status: ANALYSIS COMPLETE - TESTS PENDING*
