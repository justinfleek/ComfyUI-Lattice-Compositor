# Files Analyzed

## Summary
- Total files: 504
- Analyzed: 102
- Bugs found: 75 (across 52 files)
- Verified clean: 50
- Pending: 402

## services/expressions/ - COMPLETE (16/16 files)

---

## /ui/src/services/expressions/

### expressionEvaluator.ts - BUGS FOUND (4 bugs)
- Started: 2025-12-27
- Completed: 2025-12-27
- Lines: 784
- Bugs: BUG-001, BUG-002, BUG-003, BUG-006
- Status: COMPLETE
- Notes: **CRITICAL: BUG-006** - Sandbox escape via constructor chain allows arbitrary code execution. Also has 3 division-by-zero bugs in math/time helpers. Error handling exists but doesn't prevent security bypass.

### expressionValidation.ts - VERIFIED CLEAN
- Lines: 160
- Analyzed: 2025-12-27
- 6-Category Evidence:
  - Error Handling: 1 try/catch (lines 22-129), returns structured result
  - Loops: 0 loops
  - Input Validation: Empty code check (line 18-20)
  - Null/Undefined: Type assertion safe in catch, line 126 guards negative
  - Async: 0 async operations
  - State: No global state, pure function
- Notes: Syntax validation only via `new Function()`, doesn't execute code.

### expressionHelpers.ts - BUGS FOUND (2 bugs)
- Lines: 112
- Analyzed: 2025-12-27
- Bugs: BUG-004, BUG-005
- Notes: Division by zero in interpolateAtTime() line 107, empty array access risk line 104.

### expressionNamespaces.ts - VERIFIED CLEAN
- Lines: 121
- Analyzed: 2025-12-27
- 6-Category Evidence:
  - Error Handling: 0 try/catch (not needed - pure re-exports)
  - Loops: 0 loops
  - Input Validation: N/A - no logic
  - Null/Undefined: N/A - no logic
  - Async: 0 async operations
  - State: Exports only, no mutable state
- Notes: Pure re-exports from other modules, no runtime logic.

### expressionPresets.ts - VERIFIED CLEAN
- Lines: 114
- Analyzed: 2025-12-27
- 6-Category Evidence:
  - Error Handling: 0 try/catch (not needed - static data)
  - Loops: 0 loops
  - Input Validation: Line 98 returns null for unknown preset (safe fallback)
  - Null/Undefined: `|| null` fallback on line 98
  - Async: 0 async operations
  - State: EXPRESSION_PRESETS is const object, immutable
- Notes: Static preset data and simple lookup functions.

### easing.ts - VERIFIED CLEAN
- Lines: 346
- Analyzed: 2025-12-27
- 6-Category Evidence:
  - Error Handling: 0 try/catch (pure math, returns NaN/Infinity on edge cases)
  - Loops: 1 loop (line 137, bounded to 8 iterations in cubicBezier)
  - Input Validation: Lines 132-133 boundary clamp, line 143 derivative guard, line 146 result clamp, line 211 fallback to linear
  - Null/Undefined: Line 211 uses `|| linear` safe fallback
  - Async: 0 async operations
  - State: c1-c5 are immutable constants, EASING_FUNCTIONS/EASING_PRESETS are const objects
- Notes: Pure mathematical easing functions. Single bounded Newton-Raphson loop for cubic bezier. All edge cases handled with clamping.

### audioExpressions.ts - BUGS FOUND (1 bug)
- Lines: 294
- Analyzed: 2025-12-27
- Bugs: BUG-007
- 6-Category Evidence:
  - Error Handling: 0 try/catch, returns sensible defaults (value, 0)
  - Loops: 4 loops (lines 40, 56-62, 259, 267-272), all bounded by array length
  - Input Validation: Lines 32-34, 249 empty keyframes ✓; Lines 43-50, 261-264 boundary checks ✓; Line 65, 269 div protected by loop ✓; **Line 107 NO validation for framesPerSecond=0**; Lines 155,186,207,222 div-zero produces NaN (same pattern as BUG-001/002)
  - Null/Undefined: Lines 32, 249 handle undefined keyframes ✓
  - Async: 0 async operations
  - State: `audio` const object, all functions pure
- Notes: BUG-007 at line 107 - posterizeTime divides by framesPerSecond without checking for zero. Interp functions have NaN risk on equal tMin/tMax but clamped.

### coordinateConversion.ts - BUGS FOUND (2 bugs)
- Lines: 235
- Analyzed: 2025-12-27
- Bugs: BUG-010, BUG-011
- 6-Category Evidence:
  - Error Handling: 0 try/catch - **NO crash protection on recursion**
  - Loops: Recursion at lines 135-136, 153-154 - **NO cycle detection, NO max depth** → BUG-010
  - Input Validation: `|| 100` at lines 185-187 catches 0/NaN but **silently corrupts user data** (scale=0 becomes scale=100) → BUG-011; `|| 1` guards at 188-190 are **REDUNDANT** (never trigger)
  - Null/Undefined: Lines 135, 153 check parent exists but not if it's circular
  - Async: 0 async operations
  - State: `coords` const object, functions pure
- Test Cases Verified:
  - scale=[0,0,0]: Silently becomes [100,100,100] - DATA CORRUPTION
  - scale=[NaN,NaN,NaN]: Silently becomes [100,100,100] - silent failure
  - scale=[-1,-1,-1]: Works but inverts/scales unexpectedly
  - Circular parent: STACK OVERFLOW CRASH

### jitterExpressions.ts - BUGS FOUND (3 bugs)
- Lines: 133
- Analyzed: 2025-12-27
- Bugs: BUG-008, BUG-012, BUG-013
- 6-Category Evidence:
  - Error Handling: 0 try/catch
  - Loops: Lines 47, 113, 125 use `octaves` as bound - **NO VALIDATION** → BUG-012 (Infinity = infinite loop)
  - Input Validation: Line 54 division `1 + (octaves-1) * amplitudeMultiplier` - **NO VALIDATION** → BUG-013 (specific combos = div zero); frequency=0 at line 79 produces Infinity → constant output (silent failure)
  - Null/Undefined: ctx.value undefined → crash at line 62 `.map()` (type contract violation)
  - Async: 0 async operations
  - State: Pure functions
- Test Cases Verified:
  - octaves=Infinity: INFINITE LOOP HANG
  - octaves=-1 or 0: No jitter applied (silent failure)
  - octaves=2, amplitudeMultiplier=-1: DIVISION BY ZERO
  - frequency=0: Constant output (no jitter, silent failure)
  - ctx.value=undefined: CRASH on .map()

### loopExpressions.ts - BUGS FOUND (2 bugs)
- Lines: 146
- Analyzed: 2025-12-27
- Bugs: BUG-014, BUG-015
- 6-Category Evidence:
  - Error Handling: 0 try/catch
  - Loops: No explicit loops (uses modulo for cycling)
  - Input Validation: Line 54, 113 check `duration <= 0` - **DOES NOT catch NaN** (NaN <= 0 is false); **NO validation of fps** (fps=0 → silent failure, fps=NaN → NaN propagation)
  - Null/Undefined: Lines 58-89, 117-144 switch - **NO DEFAULT** → returns undefined for invalid type → BUG-014
  - Type Safety: Lines 84-87, 139-142 - **TYPE MISMATCH** not checked → array + number = string → BUG-015
  - Async: 0 async operations
  - State: Pure functions
- Test Cases Verified:
  - fps=0: Silent failure (returns ctx.value due to Infinity comparison)
  - fps=NaN: NaN propagates through calculations
  - type='invalid': Returns UNDEFINED - BUG-014
  - value=[100,200], velocity=5: Returns STRING "100,20050" - BUG-015
  - duration=NaN: NOT caught by `duration <= 0` check

### motionExpressions.ts - BUGS FOUND (2 bugs)
- Lines: 179
- Analyzed: 2025-12-27
- Bugs: BUG-009, BUG-016
- 6-Category Evidence:
  - Error Handling: 0 try/catch
  - Loops: Lines 47-52, 95-100, 155-160 reverse iteration - bounded ✓; Line 116-124 while loop - bounded by maxBounces=10 ✓
  - Input Validation: Line 43 `ctx.fps || 16` - **silently replaces fps=0 with 16** (same pattern as BUG-011); Line 171 division by period - **NO VALIDATION** → BUG-009; Line 117 Math.sqrt of negative - **NO VALIDATION** → BUG-016
  - Null/Undefined: Line 72 `|| 0` for missing velocity component ✓
  - Async: 0 async operations
  - State: Pure functions
- Test Cases Verified:
  - period=0 in elastic(): NaN - BUG-009
  - gravity<0 in bounce(): NaN propagation - BUG-016
  - gravity=0: Silent failure (returns value unchanged)
  - fps=0: Silently becomes 16 (data corruption)
  - fps=NaN: Silently becomes 16
  - fps=-30: Causes keyframe matching to fail

### textAnimator.ts - BUGS FOUND (1 bug)
- Lines: 115
- Analyzed: 2025-12-27
- Bugs: BUG-017
- 6-Category Evidence:
  - Error Handling: 0 try/catch
  - Loops: Line 42-57 bounded by `i < text.length` ✓
  - Input Validation: Line 32 `|| ''` handles out-of-bounds ✓; **Line 93 incomplete string escaping** → BUG-017
  - Null/Undefined: text=null → crash at `text[charIndex]` and `text.length` (type contract)
  - Async: 0 async operations
  - State: Pure functions
- Test Cases Verified:
  - ctx.char='\\' (backslash): **SYNTAX ERROR** - BUG-017
  - ctx.char='\n' (newline): **SYNTAX ERROR** - BUG-017
  - charIndex=-1: Negative indices produce empty char and negative positions (silent)
  - charIndex > text.length: Inconsistent context (textIndex=100, textTotal=5)
  - text=null: **CRASH** (TypeError)

### vectorMath.ts - BUGS FOUND (1 bug)
- Lines: 199
- Analyzed: 2025-12-27
- Bugs: BUG-018
- 6-Category Evidence:
  - Error Handling: 0 try/catch
  - Loops: All loops use `Math.max/min(a.length, b.length)` - bounded ✓
  - Input Validation: Lines 66, 69, 75 division guards `|| 1` work for 0 and NaN ✓; Line 88 len===0 check ✓; **Lines 146-147 `|| 0` for missing array elements** - min||0 OK but **max||0 is WRONG** → BUG-018
  - Null/Undefined: null inputs crash at `.length` (type contract)
  - Async: 0 async operations
  - State: Pure functions
- Test Cases Verified:
  - vectorDiv by 0: Caught by `|| 1` ✓
  - vectorDiv by NaN: Caught by `|| 1` (NaN is falsy) ✓
  - vectorNormalize([0,0,0]): Returns [0,0,0] ✓
  - vectorClamp([5,6,7], 0, [10]): Returns [5,0,0] - **BUG-018**
  - vectorMul(5, 3) both numbers: Returns [0] (silent failure)
  - null inputs: CRASH (type contract)

### layerContentExpressions.ts - VERIFIED CLEAN
- Lines: 233
- Analyzed: 2025-12-27
- 6-Category Evidence:
  - Error Handling: 0 try/catch (returns sensible defaults)
  - Loops: 2 forEach loops (lines 91, 93), bounded by array length ✓
  - Input Validation: `|| 100`/`|| 1920` for missing dimensions (valid defaults for visual layers); isFinite check at line 103 catches NaN/Infinity ✓
  - Null/Undefined: Line 42 null check; lines 85, 92 `|| []`; lines 94-95 `??` nullish coalescing; line 208 optional chaining ✓
  - Async: 0 async operations
  - State: Pure functions, const object exports
- Adversarial Tests:
  - `paths = []`: Returns default ✓
  - `paths = [{points: []}]`: isFinite catches Infinity ✓
  - `paths = [{points: [{x: NaN}]}]`: isFinite catches NaN ✓
  - `data.stroke.width = 0`: Falsy, block skipped ✓
  - Switch has default case (no undefined return) ✓
- Notes: `|| 100` pattern differs from BUG-011 - width=0 is invalid for visual layers (unlike scale=0 which is meaningful). Defaults are sensible error handling.

### types.ts - BUGS FOUND (1 bug)
- Lines: 161
- Analyzed: 2025-12-27
- Bugs: BUG-019
- 6-Category Evidence:
  - Error Handling: N/A - no runtime code
  - Loops: 0 loops
  - Input Validation: **FAILS** - `any` types at lines 39, 42, 45, 69, 90, 129, 130 disable TypeScript validation
  - Null/Undefined: Optional fields properly marked with `?`
  - Async: 0 async operations
  - State: No state - pure type definitions
- Adversarial Tests:
  - Can fps=0 reach runtime? YES - `fps: number` allows any number
  - Can NaN reach runtime? YES - `number` type doesn't exclude NaN
  - Can invalid colors pass? YES - `fillColor: any` accepts anything
  - **ROOT CAUSE**: `any` types are WHY all the div-by-zero bugs exist
- Notes: BUG-019 is systemic - proper branded types (PositiveNumber, NonZeroNumber) would prevent most runtime bugs at compile time.

### index.ts - VERIFIED CLEAN
- Lines: 68
- Analyzed: 2025-12-27
- 6-Category Evidence:
  - Error Handling: N/A - no runtime code
  - Loops: 0 loops
  - Input Validation: N/A - re-exports only
  - Null/Undefined: N/A - no runtime code
  - Async: 0 async operations
  - State: No side effects on import (verified - no top-level function calls)
- Adversarial Tests:
  - Export name collisions? TypeScript compiler would warn - no evidence of suppressed warnings
  - Circular imports? No obvious cycles in import structure
  - Side effects on import? Checked all modules - functions defined but not called, const objects only
- Notes: Standard barrel export pattern. No runtime logic to audit.

---

## /ui/src/services/effects/

### audioVisualizer.ts - BUGS FOUND (2 bugs)
- Lines: 516
- Analyzed: 2025-12-27
- Bugs: BUG-020, BUG-021
- 6-Category Evidence:
  - Error Handling: 0 try/catch - no error handling for canvas operations
  - Loops: 8 loops using user params as bounds (lines 141, 162, 199, 248, 272, 360, 380, 394, 429, 440)
  - Input Validation: **FAILS** - no validation of frequencyBands, displayedSamples, start/end points
  - Null/Undefined: Optional chaining at lines 242, 427 ✓; `|| 0` fallbacks for missing frame data ✓
  - Async: 0 async operations
  - State: Creates canvas, draws to it - expected side effects
- Adversarial Tests:
  - `startPoint === endPoint`: length=0 → perpX/perpY = NaN → **BUG-020**
  - `frequencyBands = Infinity`: infinite loop at line 141 → **BUG-021**
  - `displayedSamples = Infinity`: infinite loop at line 360 → **BUG-021**
  - `frequencyBands = NaN`: `i < NaN` false → loop skipped (silent failure)
  - `frequencyBands = 0`: bandWidth = length/0 = Infinity, loop skipped

### blurRenderer.ts - BUGS FOUND (2 bugs)
- Lines: 1281
- Analyzed: 2025-12-27
- Bugs: BUG-022, BUG-023
- 6-Category Evidence:
  - Error Handling: 3 try/catch blocks for WebGL/WebGPU ✓; non-null assertions (`!`) at lines 156, 206, 312 on nullable WebGL returns
  - Loops: All loops bounded by clamped params or canvas dimensions ✓
  - Input Validation: **FAILS** - SHG_TABLE[255] out of bounds; NaN not caught by `??`
  - Null/Undefined: Non-null assertions on WebGL calls that can fail on context loss
  - Async: ensureWebGPUInitialized() properly handles async; line 796 side-effect on load (intentional)
  - State: Module-level singleton for WebGL context caching (intentional)
- Adversarial Tests:
  - `radius = 255`: SHG_TABLE[255] = undefined → wrong shift amount → **BUG-022**
  - `blurriness = NaN`: MUL_TABLE[NaN] = undefined → corrupted output → **BUG-023**
  - `blurriness = Infinity`: Clamped to 255 ✓
  - `blurriness = -10`: Clamped to 0, returns input unchanged ✓

### cinematicBloom.ts - BUGS FOUND (1 bug)
- Lines: 809
- Analyzed: 2025-12-27
- Bugs: BUG-024
- 6-Category Evidence:
  - Error Handling: 0 try/catch
  - Loops: All bounded by clamped params (radius max 200, kernel max 801)
  - Input Validation: **FAILS** - Division by dist=0 at center pixel in chromatic aberration; NaN params cause silent failure (0-length kernel)
  - Null/Undefined: Optional chaining at line 687 ✓; cache properly invalidated ✓
  - Async: 0 async operations
  - State: Module-level lens dirt cache with proper invalidation
- Adversarial Tests:
  - `chromaticAberration > 0` + center pixel: dist=0 → NaN coordinates → **BUG-024**
  - `params.radius_r = NaN`: Creates 0-length kernel, blur has no effect (silent)
  - `radius = 0`: Returns input unchanged ✓
  - Threshold division: Protected by `threshold - knee < luminance` condition ✓

### colorGrading.ts - VERIFIED CLEAN
- Lines: 631
- Analyzed: 2025-12-27
- 6-Category Evidence:
  - Error Handling: 0 try/catch
  - Loops: All bounded by 256, data.length, or inputRange (max 360) ✓
  - Input Validation: Gamma protected by `Math.max(0.1, gamma)` ✓; softRange/hueMatch divisions protected by ternary/conditions ✓
  - Null/Undefined: Reference histograms checked at line 495 ✓; LUTs created before use ✓
  - Async: 0 async operations
  - State: No module-level mutable state, pure functions
- Adversarial Tests:
  - `gamma = 0`: Protected by Math.max(0.1, ...) ✓
  - `gamma = NaN`: Math.max(0.1, NaN) = NaN → black output (same pattern as BUG-023, systemic issue)
  - `falloff = 0`: Protected by ternary returns ✓
  - `p0.x === p1.x`: Protected by explicit check ✓
  - `lum = 0`: Protected by `lum > 0 ? ... : 1` ✓
- Notes: Well-protected file. NaN susceptibility exists but is systemic issue (BUG-019/023), not unique bug.

### colorRenderer.ts - BUGS FOUND (2 bugs)
- Lines: 1591
- Analyzed: 2025-12-27
- Bugs: BUG-025, BUG-026
- 6-Category Evidence:
  - Error Handling: 1 try/catch for LUT parsing (line 1475-1483) ✓
  - Loops: All bounded by data.length, 256, canvas dimensions ✓
  - Input Validation: Multiple `|| 1` guards ✓; `+ 0.001` in vignette ✓; **FAILS** at levels inputRange=0
  - Null/Undefined: All params use `??` defaults ✓; LUT sampling uses `?? 0` ✓
  - Async: 0 async operations
  - State: **FAILS** - lutCache (line 1344) has no size limit → unbounded memory growth
- Adversarial Tests:
  - `inputWhite === inputBlack`: inputRange=0 → NaN at exact value → **BUG-025**
  - Load 100 unique LUTs: ~330MB memory leak → **BUG-026**
  - `params.contrast = 101.57`: denominator=0 → Infinity (edge case beyond range)
  - `gamma = 0`: 1/gamma = Infinity (same NaN pattern as colorGrading)
  - `threshold = 255` in glow: Protected by `lum > threshold` condition ✓
  - Curves tangents: Protected by `|| 1` guards ✓
- Notes: BUG-025 is edge case div-by-zero. BUG-026 is memory leak from unbounded LUT cache.

### distortRenderer.ts - BUGS FOUND (1 bug)
- Lines: 1139
- Analyzed: 2025-12-27
- Bugs: BUG-027
- 6-Category Evidence:
  - Error Handling: 0 try/catch; Line 377 `getContext('2d')!` non-null assertion (minor risk on context loss)
  - Loops: All bounded - canvas dimensions for pixel loops, complexity clamped [1,10] at line 755 for octave loops ✓
  - Input Validation: `Math.max(1, ...)` guards at lines 754, 755, 1032, 428 for size/wavelength/complexity ✓; fisheye guards r>0 at line 277 ✓; turbulent bulge guards dist>0 at line 880 ✓; ripple guards dist>0 at line 1063 ✓; **FAILS at warp bulge** lines 264-266 (no guard for factor=0)
  - Null/Undefined: All params use `??` defaults ✓; Line 563-568 proper null check with fallback ✓
  - Async: 0 async operations
  - State: SimplexNoise created per-call (line 786), no module-level mutable state ✓
- Adversarial Tests:
  - `bend = -100` at center pixel (r=0): factor=0 → **BUG-027**
  - `complexity = Infinity`: Clamped to 10 ✓
  - `complexity = NaN`: Loop skipped (silent failure, no crash)
  - `size = 0`: Math.max(1, 0) = 1 ✓
  - `size = NaN`: Produces garbage noise (systemic NaN issue, same as BUG-023)
  - `wavelength = NaN`: Silent failure (systemic)
  - `amount = Infinity`: Clamped by Math.max/min at lines 970-972 ✓
- Notes: Most division operations protected by explicit checks (lines 277, 880, 1063). One unguarded edge case: BUG-027 warp bulge division by zero at center with bend=-1.

### expressionControlRenderer.ts - VERIFIED CLEAN (with caveats)
- Lines: 153
- Analyzed: 2025-12-27
- 6-Category Evidence:
  - Error Handling: 0 try/catch - renderers perform no operations
  - Loops: 0 loops
  - Input Validation: **NO VALIDATION** - lines 26, 37, 48, 59, 70, 81, 92, 103 all `return input` with no guards
  - Null/Undefined: `getControlParameterName` line 150 has default case; `isExpressionControl` line 133 uses `.includes()` which handles non-strings safely
  - Async: 0 async operations
  - State: No module-level mutable state
- Adversarial Tests:
  - `sliderControlRenderer(null, {})`: Returns `null` - **type violation** but crash happens downstream, not here
  - `sliderControlRenderer({canvas: null}, {})`: Returns object with null canvas - crash downstream
  - `getControlParameterName(Symbol())`: Falls to default line 150, returns `'value'`
  - `getControlParameterName(null)`: Falls to default, returns `'value'`
  - `isExpressionControl(undefined)`: Returns `false` (includes handles gracefully)
  - `isExpressionControl({toString: () => 'slider-control'})`: Returns `false` (strict equality)
- Notes: Renderers are pure passthrough (`return input`). No operations = no crashes HERE, but malformed input propagates unchanged to downstream consumers. Type contract trusted, not enforced.

### generateRenderer.ts - BUGS FOUND (1 bug)
- Lines: 797
- Analyzed: 2025-12-27
- Bugs: BUG-028
- 6-Category Evidence:
  - Error Handling: 0 try/catch; Line 505 `getContext('2d')!` non-null assertion
  - Loops: Octave loops bounded by `complexity` clamped [1, 20] at line 395; pixel loops bounded by canvas dimensions
  - Input Validation: Line 590 `Math.max(1, frequency)` ✓; Line 592 `Math.max(1, wave_width)` ✓; Line 635, 637 `Math.max(0.001, ...)` ✓; **Line 394 `scale` NOT protected** → BUG-028
  - Null/Undefined: All params use `??` defaults; Line 79 `if (firstKey)` check before cache delete
  - Async: 0 async operations
  - State: Line 111 `noiseTileCache` singleton - **properly bounded** by maxSize=32 (line 39) and maxAgeMs=30000 (line 40), unlike BUG-026
- Adversarial Tests:
  - `scale = 0`: Line 351 `x / 0 = Infinity` → NaN through noise → black output → **BUG-028**
  - `scale = NaN`: Same NaN propagation, black output
  - `complexity = Infinity`: Clamped to 20 at line 395 ✓
  - `complexity = NaN`: `Math.min(20, NaN) = NaN`, `Math.max(1, NaN) = NaN` → loop skipped, black output (systemic)
  - `frequency = 0`: Protected by `Math.max(1, ...)` at line 590 ✓
  - `ellipseWidth = 0`: Line 710 `dx²/0² = Infinity` → normalizedDist = Infinity → solid background (edge case, not crash)
  - `startPoint === endPoint` in radial gradient: radius=0, valid canvas API (point gradient)
- Notes: Cache is bounded (contrast with BUG-026). Single bug: scale=0 not guarded despite documented range 10-10000.

### hdrRenderer.ts - BUGS FOUND (1 bug)
- Lines: 534
- Analyzed: 2025-12-27
- Bugs: BUG-029
- 6-Category Evidence:
  - Error Handling: 0 try/catch
  - Loops: Line 260, 319, 396 all bounded by `data.length` ✓
  - Input Validation: **Line 215 `1 / params.gamma` NOT protected** → BUG-029; Line 416 `hueDiff / params.hueRange` protected by `Math.max(0, ...)` ✓
  - Null/Undefined: No param validation - if params.gamma undefined → `1/undefined = NaN`
  - Async: 0 async operations
  - State: No module-level mutable state
- Adversarial Tests:
  - `gamma = 0`: Line 215 `Math.pow(x, Infinity) = 0` for x<1 → BLACK OUTPUT → **BUG-029**
  - `gamma = NaN`: `Math.pow(x, NaN) = NaN` → Line 238 `Math.max(0, Math.min(100, NaN)) = NaN` - **DOES NOT CATCH NaN** → garbage output
  - `gamma = undefined`: `1/undefined = NaN` → same as NaN
  - `hueRange = 0`: Line 416 `Math.max(0, 1 - Infinity) = 0` → no effect applied (safe, not crash)
  - `contrast = NaN`: Line 224 `Math.pow(x, NaN) = NaN` → propagates
  - `saturationBoost = NaN`: Line 232-234 `a * NaN = NaN` → propagates
- Notes: Documentation at line 18 says gamma range 0.1-3.0 but line 215 doesn't enforce. Math.max/min clamps DON'T catch NaN.

### index.ts - VERIFIED CLEAN (coordination file)
- Lines: 194
- Analyzed: 2025-12-27
- 6-Category Evidence:
  - Error Handling: `initializeEffects()` lines 22-33 calls 10 registration functions with no try/catch - if one throws, subsequent skip (fail-fast design, not a bug)
  - Loops: 0 loops
  - Input Validation: N/A - pure re-exports and function calls
  - Null/Undefined: N/A - no object access
  - Async: 0 async operations
  - State: `initializeEffects()` mutates global effect registry - no idempotency guard but Map.set overwrites safely
- Adversarial Tests:
  - `initializeEffects()` called twice: Map.set overwrites, no duplication, no crash
  - Registration function throws: Uncaught, but this is fail-fast startup behavior
  - Import cycle: No evidence of cycles in import graph
- Notes: Barrel export file. Bugs (if any) exist in imported modules, not here. No unique runtime bugs.

### layerStyleRenderer.ts - BUGS FOUND (1 bug)
- Lines: 1075
- Analyzed: 2025-12-27
- Bugs: BUG-030
- 6-Category Evidence:
  - Error Handling: 0 try/catch; Lines 87, 114, 123, 522, 887 `getContext('2d')!` non-null assertions
  - Loops: Lines 146-156, 183-193 use `Math.ceil(amount)` as bound - **Infinity causes infinite loop** → BUG-030; Lines 535-577 bounded by width-1, height-1 ✓
  - Input Validation: Line 136 `if (amount <= 0)` doesn't catch Infinity; Line 66 handles undefined prop
  - Null/Undefined: Lines 415, 618, 755, 881 use `??` for optional style properties ✓
  - Async: 0 async operations
  - State: Line 52 `let currentFrame = 0` module-level mutable state (single-threaded, acceptable)
- Adversarial Tests:
  - `amount = Infinity` in dilateAlpha: `Math.ceil(Infinity) = Infinity` → loop `-Infinity to Infinity` → **INFINITE LOOP** → **BUG-030**
  - `amount = NaN`: `Math.ceil(NaN) = NaN` → `dy <= NaN` always false → loop skipped (silent failure)
  - `style.size = Infinity` with `spread > 0`: Triggers dilateAlpha with Infinity → **BUG-030**
  - `normalLen` in bevelEmboss: Always >= 1 due to normalZ=1 ✓ (can't be zero)
  - Gradient with 0 stops: forEach loops 0 times ✓
- Notes: Multiple paths trigger BUG-030 (dropShadow, outerGlow, innerGlow, stroke). All use dilateAlpha/erodeAlpha with unbounded style.size.

### maskRenderer.ts - VERIFIED CLEAN (with systemic NaN caveats)
- Lines: 681
- Analyzed: 2025-12-27
- 6-Category Evidence:
  - Error Handling: 0 try/catch; Multiple `getContext('2d')!` at lines 276, 280, 303, 309, 328, 392, 471, etc.
  - Loops: All bounded - line 34 by vertices.length; line 317 steps bounded [3,15] via Math.max/min ✓
  - Input Validation: Line 23, 152 check `vertices.length < 2`; Line 268 `|| 1` prevents div-by-zero; Line 94, 101, 119 guard length > 0; Line 132 `Math.max(0.5, ...)` ✓
  - Null/Undefined: Line 215 handles null previousPath ✓
  - Async: 0 async operations
  - State: Line 338 `previousPathCache` Map - bounded by unique maskIds (overwrites per ID); Line 370 `clearMaskPathCacheOnSeek()` clears on seek ✓
- Adversarial Tests:
  - `inLen = 0`: Guarded by `if (inLen > 0)` at line 95 ✓
  - `nLen = 0`: Guarded at line 120, with fallback at line 125 ✓
  - Empty `motionVectors`: Line 433 `0/0 = NaN`, but `NaN > 1` is false → if block skipped (silent, same systemic issue)
  - `steps = NaN`: Loop at line 320 executes 0 times (silent failure)
  - `width/height = 0`: Creates empty canvas, loops iterate 0 times ✓
- Notes: Division guards are thorough. NaN handling follows systemic pattern (BUG-023). Cache is properly bounded by design.

### matteEdge.ts - BUGS FOUND (1 bug)
- Lines: 643
- Analyzed: 2025-12-27
- Bugs: BUG-031
- 6-Category Evidence:
  - Error Handling: 0 try/catch
  - Loops: Multiple unbounded: Line 64 `iterations`, lines 92/131 erode/dilate `Math.ceil(amount)`, line 170 blur `Math.ceil(sigma*3)`, line 475 distance `Math.ceil(maxDist)` → **BUG-031**
  - Input Validation: Lines 240, 294, 590, 593 use `|| 1` to prevent div-by-zero ✓; Line 378 `if (radius <= 0)` early return ✓; **No Infinity checks**
  - Null/Undefined: Line 349 `if (replaceColor)` handles optional ✓
  - Async: 0 async operations
  - State: No module-level mutable state (only logger)
- Adversarial Tests:
  - `iterations = Infinity`: Line 64 infinite loop → **BUG-031**
  - `amount = Infinity`: Lines 92, 131 `Math.ceil(Infinity) = Infinity` → infinite loop → **BUG-031**
  - `softness = Infinity`: Line 170 `Math.ceil(Infinity * 3) = Infinity` → infinite loop → **BUG-031**
  - `radius = Infinity` (EdgeFeather): Line 475 → infinite loop → **BUG-031**
  - `spillColor = {r:0,g:0,b:0}`: Line 240 `|| 1` prevents div-by-zero ✓
- Notes: Same infinite loop pattern as BUG-030 but in separate erode/dilate/blur implementations. Division protected by `|| 1` at lines 240, 294, 590, 593.

### meshDeformRenderer.ts - VERIFIED CLEAN (with caveats)
- Lines: 831
- Analyzed: 2025-12-27
- 6-Category Evidence:
  - Error Handling: 0 try/catch; Line 82-83 `if (!ctx) return ''` handles null; Lines 131, 540 `getContext('2d')!` non-null assertions
  - Loops: All bounded by mesh.vertexCount, mesh.triangleCount, pins.length, canvas dimensions
  - Input Validation: Line 202 `if (dist < 0.001)` prevents near-zero; Line 222 `if (totalWeight > 0.001)` prevents div-by-zero; Line 395 `if (Math.abs(denom) < 0.0001) return` skips degenerate triangles; Line 518 ternary prevents div-by-zero
  - Null/Undefined: Line 706 `effectInstance?.pins ?? []` handles missing instance
  - Async: 0 async operations
  - State: Line 75 `meshCaches` Map - keyed by effectId (bounded by effects in project), cleared via `clearMeshDeformCaches()` line 767
- Adversarial Tests:
  - `pin.radius = 0`: Line 205 `1 - dist/0 = -Infinity`, `Math.pow(-Infinity, 2) = +Infinity`, then normalized by totalWeight=Infinity → weights become 0 (cancels out)
  - `falloffPower = 0`: `Math.pow(x, 0) = 1` for all → weights = 1, normalized to 1/pinCount (valid)
  - `falloffPower = NaN`: `Math.pow(x, NaN) = NaN` → propagates through deformation (systemic NaN issue)
  - `triangleCount = Infinity` in params: Passed to `generateMeshFromAlpha()` - potential issue in that file, not here
  - Degenerate triangle (denom=0): Line 395 early return prevents div-by-zero
- Notes: Division protected at lines 202, 222, 395, 518. Cache bounded by project scope. NaN propagation follows systemic pattern.

### perspectiveRenderer.ts - BUGS FOUND (1 bug)
- Lines: 330
- Analyzed: 2025-12-27
- Bugs: BUG-032
- 6-Category Evidence:
  - Error Handling: 0 try/catch
  - Loops: Line 99, 173, 249-296 bounded by data.length and image dimensions
  - Input Validation: Line 53 `calculateFogFactor` checks `if (range === 0)` ✓; **Line 170 `applyDepthMatte` does NOT check range=0** → BUG-032
  - Null/Undefined: Lines 92, 168 `depthMap?.data`; Line 242 `rightImage?.data || leftImage.data`
  - Async: 0 async operations
  - State: No module-level mutable state
- Adversarial Tests:
  - `nearDepth = farDepth = 100` (range=0): Line 200/207 `(depth - 100) / 0 = NaN` → alpha becomes 0 → **BUG-032**
  - `range = 0` in calculateFogFactor: Line 53 handles it ✓
  - `softnessFactor = 0` with `range = 0`: Still divides by range at line 207 → **BUG-032**
  - `fogOpacity = NaN`: Line 97 `NaN / 100 = NaN` → pixels become black (systemic)
- Notes: Inconsistency: calculateFogFactor handles range=0, applyDepthMatte does not.

### stylizeRenderer.ts - BUGS FOUND (1 bug)
- Lines: 1099
- Analyzed: 2025-12-27
- Bugs: BUG-033
- 6-Category Evidence:
  - Error Handling: 0 try/catch
  - Loops: Most bounded by image dimensions; **Line 193 `numBlocks = Math.floor(glitchAmount * 3)` unbounded** → BUG-033; **Line 320 `numLines = Math.floor(tracking * 20)` unbounded** → BUG-033
  - Input Validation: Line 66, 76 `if (max === min) return 0`; Line 598, 1069 `if (count === 0) continue`; Line 639-641 `k < 1 ? ... : 0`; Line 561, 909, 1036-1037 `Math.max(N, ...)`
  - Null/Undefined: All params use `??` defaults
  - Async: 0 async operations
  - State: No module-level mutable state
- Adversarial Tests:
  - `glitchAmount = Infinity`: Line 193 `Math.floor(Infinity * 3) = Infinity` → infinite loop → **BUG-033**
  - `tracking = Infinity`: Line 320 `Math.floor(Infinity * 20) = Infinity` → infinite loop → **BUG-033**
  - `blockSize = Infinity`: Line 198 `Math.min(y + Infinity, height) = height` → bounded (safe)
  - `wavelength = 0` in ripple: `Math.sin(dist / 0 * ...) = NaN` → pixels become black (systemic NaN)
  - `max === min` in hue/saturation: Line 66, 76 prevent div-by-zero ✓
  - `count = 0` in halftone/mosaic: Line 598, 1069 skip block ✓
- Notes: Division protected at lines 66, 76, 598, 639-641, 1069. Loop bounds at lines 193, 320 not protected.

### timeRenderer.ts - VERIFIED CLEAN (with caveats)
- Lines: 956
- Analyzed: 2025-12-27
- 6-Category Evidence:
  - Error Handling: Line 53-54 `if (!ctx) return;`; Line 269 `getContext('2d')!` non-null assertion
  - Loops: Line 69-71 bounded by maxFrames=64; Line 114, 256 bounded by numEchoes≤50; Line 801-841 bounded by searchRadius=8 (hardcoded)
  - Input Validation: Line 220 `Math.max(1, Math.min(50, ...))` numEchoes; Line 221-222 `Math.max(0, Math.min(1, ...))` intensity/decay; Line 348 `Math.max(1, Math.min(60, ...))` targetFps; Line 546 `Math.max(0, ...)` freezeAtFrame
  - Null/Undefined: Lines 116-119, 262, 370-375, 505-516, 558-565, 576-585, 747 all use guards/fallbacks
  - Async: 0 async operations
  - State: Lines 159, 530 Maps bounded by layer count, cleared via `clearAllFrameBuffers()` and `clearAllFrozenFrames()`
- Adversarial Tests:
  - `numEchoes = Infinity`: Line 220 clamps to 50 ✓
  - `targetFps = 0`: Line 348 clamps to 1 ✓
  - `_fps = 0` (internal): Line 354 `0/1=0`, line 355 `frame/0=NaN` → wrong frame returned (NaN propagation but _fps is internal, not user-controllable)
  - `width = height = 0`: Line 412 `dist/0=Infinity` → falls back to input (silent)
  - `validPixels = 0` in SAD: Line 831 `if (validPixels > 0)` prevents div-by-zero ✓
- Notes: User params bounded. Internal _fps param could cause NaN but is set by renderer. Caches bounded by layer count, cleared on project change.

## services/effects/ - COMPLETE (17/17 files, 10 bugs found)

---

## /ui/src/services/ (additional files discovered during audit)

### frameCache.ts - BUGS FOUND (3 bugs)
- Lines: 649
- Analyzed: 2025-12-27
- Bugs: BUG-035, BUG-037, BUG-038
- 6-Category Evidence:
  - Error Handling: Line 504-512 try/catch around renderFrame ✓; Lines 592-603 `compressFrame()` NO try/catch - canvas can throw; Lines 605-620 `decompressFrame()` NO try/catch - createImageBitmap can throw; Lines 595, 615 `getContext('2d')!` non-null assertions - crash risk
  - Loops: **Line 475 `for (i <= window)` where window=preCacheWindow - Infinity causes infinite loop** → BUG-037; Line 498 `for...of` bounded by queue ✓; Line 565-589 while loop has `lru.size > 0` guard ✓ but `requiredSize=Infinity` evicts ALL entries
  - Input Validation: **Line 246-248 `getCacheKey()` NO validation** → BUG-035; **Line 334 `size = width * height * 4` with NaN → currentMemory = NaN permanently** → BUG-038; Line 579 `split(':')[0]` breaks if compositionId contains `:`
  - Null/Undefined: Lines 151-152, 167-168, 570-571 null checks ✓; Lines 595, 615 non-null assertions crash risk
  - Async: Line 504-508 abort signal checked ✓; Lines 592-603, 605-620 no error handling
  - State: Line 364 `currentMemory += size` - NaN corrupts permanently; Line 627 `globalFrameCache` singleton no cleanup
- Adversarial Tests:
  - `frame = NaN`: Key = `"comp:NaN"` → all NaN frames collide → **BUG-035**
  - `preCacheWindow = Infinity`: Line 475 `i <= Infinity` always true → **infinite loop** → **BUG-037**
  - `imageData.width = NaN`: Line 334 `size = NaN` → line 364 `currentMemory = NaN` → all memory checks fail → cache grows unbounded → **BUG-038**
  - `requiredSize = Infinity`: Line 567 `NaN > maxBytes` always false → no eviction triggers
  - `compositionId = "a:b:c"`: Line 579 `split(':')[0]` returns "a" not "a:b:c" (key parsing breaks)
- Notes: Central cache service with 3 distinct bugs. BUG-035 shared with cacheActions.ts.

---

## /ui/src/stores/actions/

### audioActions.ts - BUGS FOUND (1 bug)
- Lines: 1012
- Analyzed: 2025-12-27
- Bugs: BUG-034
- 6-Category Evidence:
  - Error Handling: Lines 57-101 try/catch around loadAndAnalyzeAudio ✓
  - Loops: Lines 541-564 bounded by frameCount; line 550-554 bounded by buffer.length; line 275-277, 356-358, 365-367 bounded by map/array size
  - Input Validation: **Line 529 `sampleRate / fps` with fps=0 → Infinity** → BUG-034; Line 556-557 `count > 0` check ✓; Line 561-563 `Math.min(1, ...)` clamps ✓
  - Null/Undefined: Lines 134, 155, 219, 254, 270 null checks before method calls; Line 382 `|| []` handles undefined
  - Async: Lines 58-72 proper async/await with error handling
  - State: Line 123 `.clear()` on Map (proper cleanup)
- Adversarial Tests:
  - `fps = 0`: `sampleRate / 0 = Infinity` → `samplesPerFrame = Infinity` → frames 1+ get amplitude 0 → **BUG-034**
  - `fps = NaN`: Same behavior, NaN propagation
  - `frameCount = 0`: Loop executes 0 times (no keyframes, but not crash)
  - `smoothing = NaN`: Line 586 `NaN * previous + (1-NaN) * value = NaN` → all smoothed values NaN
- Notes: Lines 17-18, 35-37 use `| any` type unions (systemic, logged in BUG-019).

### cacheActions.ts - BUGS FOUND (1 bug)
- Lines: 159
- Analyzed: 2025-12-27
- Bugs: BUG-035 (shared with frameCache.ts)
- 6-Category Evidence:
  - Error Handling: 0 try/catch (errors propagate to caller)
  - Loops: Line 152-156 bounded by string length (JSON.stringify result always finite)
  - Input Validation: **Line 63, 77, 87, 101 pass `frame` to frameCache without validation** → BUG-035
  - Null/Undefined (Rule 9 compliance):
    | Line | What's checked | What happens if null/undefined |
    |------|----------------|-------------------------------|
    | 36 | `store.frameCacheEnabled` | undefined → falsy → skips init |
    | 46 | `store.frameCacheEnabled = enabled` | store undefined → TypeError |
    | 60, 74, 84, 98 | `!store.frameCacheEnabled` | undefined → truthy → early return |
    | 62, 76, 86, 100, 112, 120, 129 | `getFrameCache()` | Always returns FrameCache (lazy singleton at frameCache.ts:633-635) |
    | 138 | `store.project.compositions[...]` | project undefined → TypeError; compositions undefined → TypeError |
    | 139 | `if (!comp) return ''` | **SAFE** - handles missing composition |
    | 143 | `comp.layers.length` | layers undefined → TypeError (trusts type contract) |
    | 144 | `comp.layers.map(l => l.id)` | null layer → TypeError (trusts type contract) |
    | 145 | `store.project.meta.modified` | meta undefined → TypeError (trusts type contract) |
  - Async: Lines 35-40, 69-78, 93-102 async/await, no error handling
  - State: Lines 46, 109 direct mutations; line 121 mutates global cache singleton
- Adversarial Tests:
  - `frame = NaN`: Passed to `cache.get(NaN, ...)` → key = `"comp:NaN"` → **all NaN frames collide** → **BUG-035**
  - `frame = Infinity`: Same collision issue → **BUG-035**
  - `store.project = undefined`: Line 138 throws TypeError (type contract trusted)
  - `activeCompositionId` not in compositions: Line 139 returns '' (safe)
  - Hash overflow: Line 155 `& hash` converts to 32-bit (safe)
- Notes: Neither this file nor frameCache.ts validates frame inputs. Verified by reading frameCache.ts lines 246-248. Trusts CacheStore type contract for store structure.

### cameraActions.ts - BUGS FOUND (1 bug)
- Lines: 300
- Analyzed: 2025-12-27
- Bugs: BUG-036
- 6-Category Evidence:
  - Error Handling: 0 try/catch; returns null on not-found (lines 105, 246, 277)
  - Loops: Line 133-138 bounded by layers array ✓
  - Input Validation: Line 207 `k.frame === keyframe.frame` - **NaN === NaN is false** → BUG-036; Line 254 delegates to interpolateCameraAtFrame (not verified)
  - Null/Undefined: Lines 48-49, 63 optional chaining with fallbacks ✓
  - Async: 0 async operations
  - State: Line 158 external store call `useSelectionStore()`; direct array mutations at lines 91, 157
- Adversarial Tests:
  - `keyframe.frame = NaN`: Line 207 findIndex returns -1 (NaN === NaN is false) → keyframe always pushed → **accumulation** → **BUG-036**
  - `sort with NaN`: Line 213 `a.frame - b.frame` with NaN → undefined ordering
  - `frame = NaN` in removeCameraKeyframe: Line 230 findIndex returns -1 → can't remove NaN keyframes
- Notes: Same NaN equality bug pattern could exist elsewhere. Line 254 delegates to interpolateCameraAtFrame without frame validation.

### compositionActions.ts - BUGS FOUND (2 bugs)
- Lines: 441
- Analyzed: 2025-12-27
- Bugs: BUG-039, BUG-040
- 6-Category Evidence:
  - Error Handling: 0 try/catch; early returns on null at lines 107, 150, 203, 354 ✓
  - Loops: Line 167-171 `for...of comp.layers` bounded ✓; Line 373-390 `for...of selectedLayers` bounded ✓
  - Input Validation: **Line 64 fps not validated in createComposition** (but validated in updateCompositionSettings at line 155-157) → BUG-039; **Line 312 bounds check doesn't catch NaN** → BUG-040; Line 370, 393 `Math.min/max(...[])` risk if selectedLayers empty but guarded at line 348
  - Null/Undefined: Lines 61-64 `??` fallbacks ✓; Lines 106-107, 149-150, 202-203, 224-227, 272-276, 353-354 null checks ✓
  - Async: 0 async operations ✓
  - State: Lines 81, 110, 115, 255, 279, 297, 322, 385 direct mutations; Lines 235-237, 433 external `useSelectionStore()` calls
- Adversarial Tests:
  - `settings.fps = 0` in createComposition: Line 70 `duration = 81/0 = Infinity` → **BUG-039**
  - `index = NaN` in navigateToBreadcrumb: Line 312 `NaN < 0` false, `NaN >= 3` false → bypasses guard → Line 322 `slice(0, NaN)` = [] → breadcrumbs corrupted → **BUG-040**
  - `selectedLayerIds` with non-existent IDs: Line 365-367 returns empty array → Line 370 `Math.min()` = Infinity → layer timing corruption
- Notes: Inconsistency between createComposition (no fps validation) and updateCompositionSettings (validates fps). NaN comparison pattern same as BUG-036.

### depthflowActions.ts - BUGS FOUND (1 bug)
- Lines: 94
- Analyzed: 2025-12-27
- Bugs: BUG-041
- 6-Category Evidence:
  - Error Handling: 0 try/catch (file is minimal, delegates to store)
  - Loops: 0 loops
  - Input Validation: **FAILS** - Line 91 `Object.assign(data.config, updates)` stores NaN/Infinity without validation → BUG-041
  - Null/Undefined: Line 87-88 null check ✓
  - Async: 0 async operations
  - State: Lines 91, 92 direct mutations (expected for action file)
- Adversarial Tests:
  - `layerId` not found: Line 87 `find()` returns undefined → line 88 `!layer` early return ✓
  - `layer.type !== 'depthflow'`: Line 88 early return ✓
  - **`updates = {zoom: NaN}`: Stored in config → later `ctx.scale(NaN, NaN)` → corrupted output** → BUG-041
  - `updates = {depthScale: Infinity}`: Stored → `z * Infinity = Infinity` → depth calculations break
- Notes: NaN/Infinity values don't crash HERE but corrupt rendering downstream. Same pattern as BUG-035 (data stored unchecked, corruption happens later).

### effectActions.ts - BUGS FOUND (2 bugs)
- Lines: 212
- Analyzed: 2025-12-27
- Bugs: BUG-042, BUG-043
- 6-Category Evidence:
  - Error Handling: 0 try/catch; early returns on null at lines 30, 33, 52, 73, 94, 128, 131, 148, 168, 171, 197, 200
  - Loops: No explicit loops (array methods: find, findIndex, splice)
  - Input Validation: **FAILS** - Line 70 `value: any` no validation → BUG-043; Lines 150-151 NaN bypasses bounds check → BUG-042
  - Null/Undefined (Rule 9 compliance):
    | Line | What's checked | What happens if null/undefined |
    |------|----------------|-------------------------------|
    | 29-30 | `layer = find()`, `if (!layer)` | **SAFE** - early return |
    | 32-33 | `createEffectInstance()`, `if (!effect)` | **SAFE** - early return |
    | 35-37 | `if (!layer.effects)` | **SAFE** - creates empty array |
    | 51-52 | `if (!layer \|\| !layer.effects)` | **SAFE** - early return |
    | 54-55 | `findIndex()`, `if (index >= 0)` | **SAFE** - skips if -1 |
    | 72-76 | Standard pattern + parameters check | **RISK**: Line 76 if `effect.parameters` undefined → TypeError |
    | 93-97 | Same as 72-76 | **SAME RISK** at line 97 |
    | 103 | `!param.keyframes \|\| ...length === 0` | **SAFE** - handles undefined keyframes |
    | 127-131 | Standard pattern | **SAFE** |
    | 147-151 | Standard pattern + bounds check | NaN bypasses bounds (BUG-042) |
    | 167-171 | Standard pattern | **SAFE** |
    | 179-180 | `findIndex()` unchecked | If -1 → `splice(0,0,...)` inserts at start (minor) |
    | 196-200 | Same as 72-76 | **SAME RISK** |
    | 203 | `getActiveComp()?.currentFrame ?? 0` | **SAFE** - optional chain + ?? |
    | 206 | `param.keyframes.length` | **RISK**: if keyframes undefined → TypeError |
  - Async: 0 async operations
  - State: Direct mutations at lines 38, 56, 78, 100, 104-112, 133, 153-154, 175-176, 180
- Adversarial Tests:
  - `fromIndex = NaN`: Line 150 `NaN < 0` false, `NaN >= length` false → bypasses → `splice(0,1)` → **wrong effect moved** → **BUG-042**
  - `value = NaN` in updateEffectParameter: Stored at line 78 → renderer uses → **corrupted output** → **BUG-043**
  - `store.currentFrame = NaN`: Line 106 creates keyframe with frame=NaN (BUG-036 pattern)
  - `effect.parameters = undefined`: Line 76 throws TypeError before check completes (type contract trusted)
- Notes: Lines 76, 97, 200 trust that `effect.parameters` exists (EffectInstance type contract). Malformed JSON would crash. BUG-043 is entry point that triggers downstream renderer bugs (BUG-023, BUG-033).

### keyframeActions.ts - BUGS FOUND (3 bugs)
- Lines: 1786
- Analyzed: 2025-12-27
- Bugs: BUG-044, BUG-045, BUG-046
- 6-Category Evidence:
  - Error Handling: 0 try/catch; Line 1013 dynamic import with no .catch()
  - Loops: All bounded by array sizes (lines 348-382, 654-742, 763-793, 814-862, 1504-1552)
  - Input Validation: **FAILS** - Line 128 NaN frame equality → BUG-044; Line 958 division by zero → BUG-045; Line 1312-1314 fps=0 → BUG-046
  - Null/Undefined (Rule 10 - Complete Analysis for 1786 lines):
    **SAFE Patterns (Grouped):**
    - Pattern A: `find() + if (!x) return` (23 instances) - Lines: 101-104, 157-158, 186-187, 220-223, 312-313, 349-350, 365-366, 401-402, 432-433, 478-479, 504-505, 539-540, 567-568, 599-600, 647-648, 701-702, 843-844, 891-892, 941-942, 994-997, 1055-1056, 1113-1114, 1134-1135, 1185-1186, 1290-1291, 1348-1349, 1415-1416, 1494-1495, 1584-1585, 1693-1694, 1713-1714, 1731-1732, 1751-1752
    - Pattern B: `findPropertyByPath() + if (!property) return` (18 instances) - Lines: 107-110, 160-161, 189-190, 258-260, 315-316, 352-353, 372-373, 404-405, 435-436, 481-482, 507-508, 542-543, 570-571, 602-603, 855-857, 903-904, 1000-1004, 1058-1061, 1116-1117, 1137-1138, 1197-1202, 1293-1294, 1351-1352, 1418-1419, 1497-1498, 1587-1588
    - Pattern C: `findIndex() + if (index >= 0)` (12 instances) - Lines: 128-130, 163-165, 318-319, 355-356, 407-408, 438-439, 484-485, 510-511, 545-546, 578-579, 1220-1221, 1296-1297, 1354-1355, 1423-1424, 1590-1591
    - Pattern D: `?.` optional chain (27 instances) - Lines: 97, 203, 577, 614, 655-656, 665, 675-676, 709-710, 718, 727-728, 807, 857, 905, 945, 1001, 1059, 1117, 1138, 1294, 1352, 1366, 1370, 1376, 1380, 1770, 1772, 1782, 1784
    - Pattern E: `?? fallback` (8 instances) - Lines: 97, 203, 577, 614, 959, 965, 1312, 1375
    - Pattern F: Ternary bounds check (6 instances) - Lines: 1300-1301, 1304-1305, 1358-1359, 1362-1363, 1427-1428, 1506-1507
    **RISKS (Individual):**
    | Line | Risk |
    |------|------|
    | 76 | `effect.parameters[paramKey]` - TypeError if parameters undefined |
    | 128 | `k.frame === frame` - NaN === NaN is false → BUG-044 |
    | 134, 284, 333, 374, 452, 744, 769, 795, 864, 1233, 1501 | `a.frame - b.frame` - NaN → undefined sort |
    | 270-274 | `propertyData.keyframes.map()` - assumes array after undefined check |
    | 322-323, 444, 657, 666, 677, 687, 950, 1220 | `kf.frame === X` - NaN === NaN is false |
    | 358, 861, 1148, 1209 | `frame + delta` - NaN propagation |
    | 416, 456, 573, 580, 619 | `x.value = value` - NaN/Infinity stored |
    | 712, 720, 730, 739, 860 | `kf.frame` access - could be NaN |
    | 770, 796, 815, 817 | `f > currentFrame` / `f < currentFrame` - NaN comparison fails |
    | 912 | `property.keyframes[i].value` - concurrent modification risk |
    | 958 | `/ (after.frame - before.frame)` - division by zero → BUG-045 |
    | 1013-1039 | Dynamic import `.then()` - no `.catch()`, async mutation |
    | 1019-1020 | `keyframes![index]` - non-null assertion after async gap |
    | 1105 | `get(key)!.push()` - non-null assertion |
    | 1119, 1121 | `property.keyframes.filter()`, `kf.frame < Infinity` - NaN fails |
    | 1312 | `store.fps ?? 16` - fps=0 passes → BUG-046 |
    | 1313-1314 | `/ fps` - division by zero |
    | 1367, 1371, 1377, 1381 | `/ duration` or `/ frame` - `> 0` check but not NaN |
    | 1441-1445, 1518-1537 | Frame/value deltas - NaN propagation |
    | 1617-1658 | `Math.sqrt()`, division - `> 0` check but not NaN |
    **Summary:** 94 SAFE instances, 58 RISK points identified
  - Async: Line 1013-1039 dynamic import with async mutation, no error handling
  - State: Multiple direct mutations, line 1013-1039 async mutation = race condition risk
- Adversarial Tests:
  - `frame = NaN` in addKeyframe: `NaN === NaN` false → keyframe always pushed → **accumulates** → **BUG-044**
  - `before.frame === after.frame`: Line 958 `(x - y) / 0 = NaN/Infinity` → **BUG-045**
  - `store.fps = 0`: Line 1312 `0 ?? 16 = 0` → Line 1313 `velocity / 0 = Infinity` → **BUG-046**
  - Sort with NaN frames: Undefined ordering at 11 sort() calls
  - NaN frame equality: Fails at 8 comparison points
- Notes: Large file (1786 lines). Rule 10 applied. Three distinct bugs logged. Systemic NaN frame handling issue (17+ failure points).

### layerActions.ts - BUGS FOUND (3 bugs)
- Lines: 1634
- Analyzed: 2025-12-27
- Bugs: BUG-047, BUG-048, BUG-049
- 6-Category Evidence:
  - Error Handling: Lines 1106-1108 try/catch in convertTextLayerToSplines; all other functions rely on early returns
  - Loops: All bounded by array sizes (lines 304-326, 437-439, 684-688, 769-787, 813-818, 832-921, 1009-1064, 1214-1385, 1403-1410, 1520-1531, 1600-1627)
  - Input Validation: **FAILS** - Line 595 newIndex not validated → BUG-047; Line 1339 count-1 division → BUG-048; Line 1597 startScale division → BUG-049
  - Null/Undefined (Rule 10 - Complete Analysis for 1634 lines):
    **SAFE Patterns (Grouped):**
    - Pattern A: `find() + if (!x) return` (16 instances) - Lines: 298-299, 353-354, 452-453, 485-486, 510-511, 589-592, 608-609, 673-674, 949-953, 1147-1150, 1154-1157, 1161-1164, 1503-1509, 1583-1586
    - Pattern B: `?.` optional chain (15 instances) - Lines: 114, 118-119, 135, 138, 158, 624-630, 771, 980-981, 1033, 1076, 1220, 1231
    - Pattern C: `||` or `??` fallback (12 instances) - Lines: 118-119, 135, 138, 514, 520-577, 795, 1168
    - Pattern D: `filter()` returns array (5 instances) - Lines: 386, 683, 802, 813, 1505
    - Pattern E: `findIndex() + if (index === -1)` (3 instances) - Lines: 298-299, 589-592
    **RISKS (Individual):**
    | Line | Risk |
    |------|------|
    | 82-85 | `store.project.composition.width/height` - undefined propagation |
    | 146 | `layerData as Layer['data']` - type assertion mismatch |
    | 163 | `layers.unshift(layer)` - no array validity check |
    | 317-325 | `(layer.data as any).pathLayerId` - unsafe cast |
    | 367 | `findIndex()` not checked - race condition |
    | 465, 495 | `Object.assign` / spread - NaN/Infinity propagation |
    | 551 | `path.split('.').pop()` - undefined if empty |
    | 595 | **`splice(newIndex, ...)` - newIndex not validated** → BUG-047 |
    | 768, 772, 782 | Type assertions, assumes keyframes array exists |
    | 874 | `map(parseFloat)` - NaN if non-numeric |
    | 905-906 | Array access could be undefined |
    | 995 | `findIndex()` result not checked |
    | 1041-1043, 1049, 1083-1086 | Deep property access, could throw |
    | 1186, 1215, 1339, 1364 | Division risks (0, NaN) |
    | 1521, 1596-1597, 1605 | Arithmetic with potential NaN/Infinity |
    | 1607, 1611 | Property access could be undefined |
    **Summary:** 51 SAFE instances across 5 patterns, 24 RISK points identified
  - Async: Lines 935-1109 `convertTextLayerToSplines` - async with try/catch (proper)
  - State: Multiple direct mutations; pushHistory() called before changes at 991, 1256, 1516, 1590 (good pattern)
- Adversarial Tests:
  - `newIndex = NaN` in moveLayer: `splice(NaN, 0, ...)` = `splice(0, 0, ...)` → **wrong position** → **BUG-047**
  - `count = 1` in samplePathPoints: `totalLength / 0 = Infinity` → **path sampling fails** → **BUG-048**
  - `startScale = 0` in applyExponentialScale: `endScale / 0 = Infinity` → **NaN keyframes** → **BUG-049**
  - `Object.assign(layer, {opacity: NaN})`: Stored without validation
  - `parseFloat` on non-numeric SVG path data: NaN in control points
- Notes: Large file (1634 lines). Rule 10 applied. Three distinct division/validation bugs. Good pattern of pushHistory() before mutations for undo.

### markerActions.ts - BUGS FOUND (1 bug)
- Lines: 318
- Analyzed: 2025-12-27
- Bugs: BUG-050
- 6-Category Evidence:
  - Error Handling: 0 try/catch; early returns on null at lines 41-43, 85, 103, 106, 125, 128, 154, 200, 210, 220, 261, 305
  - Loops: Line 269-288 `for (const markerData of markers)` - bounded by input
  - Input Validation: **FAILS** - Lines 62, 105, 188, 280 `m.frame === frame` fails for NaN → BUG-050; Lines 70, 139, 291 sort with NaN → undefined order
  - Null/Undefined (Rule 9 compliance):
    | Line | What's checked | Result |
    |------|----------------|--------|
    | 40-43 | `getActiveComp()`, `if (!comp)` | **SAFE** |
    | 47-49 | `if (!comp.markers)` | **SAFE** - initializes |
    | 84-88 | `if (!comp?.markers)`, `if (index < 0)` | **SAFE** |
    | 102-106, 124-128, 153-154 | Standard guards | **SAFE** |
    | 171-172 | `comp?.markers \|\| []` | **SAFE** |
    | 179-180, 187-188 | `?.find() \|\| null` | **SAFE** |
    | 199-200, 209-210, 219-224 | Guards + ternary | **SAFE** |
    | 236-246 | `?.frame ?? null` | **SAFE** |
    | 260-265, 304-305 | Standard guards | **SAFE** |
  - Async: None
  - State: Direct mutations of comp.markers; pushHistory() after mutations (correct)
- Adversarial Tests:
  - `marker.frame = NaN`: Line 62 `NaN === NaN` false → always pushes → **accumulates** → **BUG-050**
  - `removeMarkerAtFrame(NaN)`: Line 105 `NaN === NaN` false → returns false (can't remove)
  - `getMarkerAtFrame(NaN)`: Line 188 `NaN === NaN` false → returns null (can't find)
  - Sort with NaN: Lines 70, 139, 291 produce undefined ordering
- Notes: Same NaN frame equality pattern as BUG-044. All null/undefined handling is correct.

### playbackActions.ts - BUGS FOUND (1 bug)
- Lines: 139
- Analyzed: 2025-12-27
- Bugs: BUG-051
- 6-Category Evidence:
  - Error Handling: 0 try/catch; early returns on null at lines 26, 65, 83, 94, 105, 118, 132
  - Loops: None
  - Input Validation: **FAILS** - Lines 66, 133 `Math.max(0, Math.min(frame, ...))` doesn't catch NaN → BUG-051
  - Null/Undefined (Rule 9 compliance):
    | Line | What's checked | Result |
    |------|----------------|--------|
    | 22-26 | `usePlaybackStore()`, `getActiveComp()`, `if (!comp)` | **SAFE** |
    | 42-44, 51-56 | Playback store access | **SAFE** |
    | 64-66, 82-86, 93-97, 104-110, 117-124, 131-138 | `if (!comp) return` pattern | **SAFE** |
  - Async: None
  - State: Direct mutation of `comp.currentFrame`; no history push (correct for UI state)
- Adversarial Tests:
  - `setFrame(store, NaN)`: Line 66 `Math.max(0, NaN) = NaN` → `comp.currentFrame = NaN` → **timeline broken** → **BUG-051**
  - `jumpFrames(store, NaN)`: Same issue at line 133
  - `comp.settings.frameCount = undefined`: `undefined - 1 = NaN` → same corruption path
- Notes: Math.max/min don't validate NaN. All null/undefined handling is correct.

### projectActions.ts - VERIFIED CLEAN
- Lines: 674
- Analyzed: 2025-12-27
- Bugs: None
- 6-Category Evidence:
  - Error Handling: Excellent - 8 try/catch blocks covering all async operations (lines 127-150, 167-179, 194-210, 222-256, 263-273, 279-286, 351-365, 600-604)
  - Loops: All bounded by Object.keys/values/entries iteration (lines 455-491, 507-513, 538-541, 581-611)
  - Input Validation: SYSTEMIC-002 risk in history management (lines 41, 61, 74), but internal state - low risk
  - Null/Undefined (Rule 10):
    **SAFE Patterns (Grouped):**
    - Pattern A: `result.status === 'success' && result.X` (5 instances) - Lines: 197, 225, 266, 282, 355
    - Pattern B: try/catch error handling (8 instances)
    - Pattern C: `?? value` / `|| value` fallbacks (6 instances) - Lines: 132, 230, 352, 569, 585, 660
    - Pattern D: Explicit null check `if (!folder) throw` - Line 571
    - Pattern E: Object iteration (4 instances) - Lines: 455, 507, 538, 581
    **RISKS (Minor):**
    | Line | Risk |
    |------|------|
    | 65, 78 | `historyStack[index]` - internal state, controlled access |
    | 307 | `autosaveIntervalMs` - config issue if 0/undefined |
    | 132, 230, 459, 615, 618 | Type assertions `as any` |
    | 593-595 | `split(',')[1]` - guarded by `if (base64Data)` |
    **Summary:** 24 SAFE instances, 10 minor risks (type assertions, internal state)
  - Async: All properly try/catch wrapped
  - State: History mutations internal, controlled; `delete assets[id]` safe
- Adversarial Tests:
  - `store.historyIndex = NaN` then `undo()`: NaN <= 0 false, continues, historyStack[NaN] = undefined → structuredClone throws. But historyIndex is internal, never externally set to NaN.
  - `store.autosaveIntervalMs = 0`: Rapid autosave (config issue, not crash)
  - Invalid JSON in `importProject`: Caught by try/catch, returns false
  - Network failure in `saveProjectToServer`: Caught, returns null
- Notes: Well-architected file with proper error handling. No new bugs. SYSTEMIC-002 pattern exists but on internal state only.

### index.ts - VERIFIED CLEAN
- Lines: 47
- Analyzed: 2025-12-27
- Bugs: None
- 6-Category Evidence:
  - Error Handling: N/A - barrel export only
  - Loops: 0 loops
  - Input Validation: N/A - re-exports only
  - Null/Undefined: N/A - no runtime code
  - Async: N/A
  - State: No side effects on import
- Notes: Standard barrel export file. No runtime logic to audit.

### layerDecompositionActions.ts - VERIFIED CLEAN
- Lines: 395
- Analyzed: 2025-12-27
- Bugs: None
- 6-Category Evidence:
  - Error Handling: 6 try/catch blocks (lines 92-204, 216-268, 296-313, 329-361, 376-393) - excellent coverage
  - Loops: Line 159 `for (let i = 0; i < sortedLayers.length; i++)` - bounded
  - Input Validation:
    - Line 335-336: `percent = bytes_downloaded / total_bytes * 100` - if total_bytes=0 → Infinity (UI issue, not crash)
    - Line 106-108: Checks empty decomposition result
  - Null/Undefined:
    - Line 156-157: `?.estimatedDepth || 0`, `?.suggestedZPosition || 0` - proper fallbacks
    - Line 167-168: `?.contentDescription || layer.label` - proper fallback
  - Async: All wrapped in try/catch
  - State: Direct mutations with pushHistory() call
- Adversarial Tests:
  - Empty decomposition result: Line 106-108 throws descriptive error
  - LLM depth fails: Line 134-137 falls back to heuristics
  - total_bytes=0: Shows Infinity% progress (UI oddity, not crash)
- Notes: Well-protected async file. No unique bugs. Error handling is thorough.

### layerStyleActions.ts - VERIFIED CLEAN (with systemic caveats)
- Lines: 710
- Analyzed: 2025-12-27
- Bugs: None unique (SYSTEMIC-004 applies)
- 6-Category Evidence:
  - Error Handling: 0 try/catch; relies on early returns for not-found
  - Loops: Line 349 `for (const layerId of layerIds)` - bounded
  - Input Validation:
    - Line 197 `value: any` - no validation, stores NaN/Infinity (SYSTEMIC-004)
    - All other values come from typed config objects
  - Null/Undefined:
    - Lines 95-99, 120-124, 199-203, 236-240, 260-264, 289-293, 316-320, 368-372 - layer not found guards ✓
    - Line 130 `if (enabled && !styles[styleType])` - creates default ✓
    - Line 167 `if (style && typeof style === 'object' && 'enabled' in style)` - safe type check ✓
  - Async: 0 async operations
  - State: Line 280 `styleClipboard` module-level mutable state (acceptable for clipboard pattern)
- Adversarial Tests:
  - Layer not found: Early return in all functions
  - `updateStyleProperty(..., value: NaN)`: Stored unchanged → SYSTEMIC-004
  - JSON.parse of circular styles: Would throw, but styles are always serializable objects
- Notes: Style management is straightforward. SYSTEMIC-004 NaN storage applies but bugs manifest in renderer (BUG-030 area).

### particleLayerActions.ts - VERIFIED CLEAN (with systemic caveats)
- Lines: 222
- Analyzed: 2025-12-27
- Bugs: None unique (SYSTEMIC-004 applies)
- 6-Category Evidence:
  - Error Handling: 0 try/catch
  - Loops: 0 explicit loops
  - Input Validation:
    - Line 167 `Object.assign(data, updates)` - stores without validation (SYSTEMIC-004)
  - Null/Undefined:
    - Lines 164, 180, 197, 215 - layer not found or wrong type guards ✓
    - Line 200 `data.emitters.find()` - may return undefined, line 201 `if (emitter)` guards ✓
  - Async: 0 async operations
  - State: Direct layer.data mutations
- Adversarial Tests:
  - `updates = {maxParticles: NaN}`: Stored → SYSTEMIC-004
  - Layer not particles type: Early return
  - Emitter not found: Line 201 guard prevents crash
- Notes: Simple CRUD operations. SYSTEMIC-004 applies for particle config values.

### physicsActions.ts - BUGS FOUND (1 bug)
- Lines: 686
- Analyzed: 2025-12-27
- Bugs: BUG-052
- 6-Category Evidence:
  - Error Handling: Lines 81-83 throws on no composition; Lines 443-448 throws on layer/comp not found
  - Loops:
    - Lines 348-351, 358-370, 382-403, 523-529, 609-633 - bounded by array sizes ✓
    - **Line 464 `for (frame = startFrame; frame <= endFrame; frame += sampleInterval)` - sampleInterval=0 causes infinite loop** → BUG-052
  - Input Validation:
    - Line 138-140: Uses `?? 0` fallbacks ✓
    - Line 451-453: Uses `?? 0` and `?? 1` fallbacks ✓
    - Line 401: `bodyState.angle * (180 / Math.PI)` - NaN angle → NaN rotation (systemic)
  - Null/Undefined:
    - Line 128-132, 203-204, 552-553, 596-600, 659-660 - layer null guards ✓
    - Line 206-207: `(layer.data as any)?.physics` - safe optional chain ✓
    - Line 387-388: bodyState undefined handled by continue ✓
  - Async: Lines 436-509 async/await with throws on error
  - State: Lines 68, 71, 234 module-level state (physics engine, states map, force fields)
- Adversarial Tests:
  - `sampleInterval = 0`: `frame += 0` → frame never increments → **INFINITE LOOP** → BUG-052
  - `sampleInterval = NaN`: `frame += NaN` → frame becomes NaN → `NaN <= endFrame` false → loop exits (silent failure)
  - Layer not found: Throws or returns null
  - No active composition: Line 81-83 throws
- Notes: One infinite loop bug when sampleInterval=0 in bakePhysicsToKeyframes.

### propertyDriverActions.ts - VERIFIED CLEAN (with systemic caveats)
- Lines: 237
- Analyzed: 2025-12-27
- Bugs: None unique (SYSTEMIC-003 applies)
- 6-Category Evidence:
  - Error Handling: 0 try/catch; Line 116-119 returns false on circular dependency
  - Loops: Line 45 `for...of` bounded by array
  - Input Validation:
    - Line 68 `store.fps ?? 16` - fps=0 passes through (SYSTEMIC-003)
  - Null/Undefined:
    - Lines 59-64, 114-120, 179, 199, 228 - proper guards ✓
  - Async: 0 async operations
  - State: Lines 122-124 direct array mutation with pushHistory()
- Adversarial Tests:
  - store.fps = 0: Passes through, causes division issues downstream (SYSTEMIC-003)
  - Circular dependency: Line 116-119 returns false, prevents addition
  - Driver not found: Lines 179, 199, 228 handle gracefully
- Notes: Circular dependency detection is good. SYSTEMIC-003 fps=0 issue applies.

### segmentationActions.ts - VERIFIED CLEAN
- Lines: 268
- Analyzed: 2025-12-27
- Bugs: None
- 6-Category Evidence:
  - Error Handling: 5 try/catch blocks (lines 53-120, 137-151, 168-181, 199-217, 233-266)
  - Loops: Line 248 `for (let i = 0; i < result.masks.length; i++)` - bounded
  - Input Validation:
    - Lines 132-135, 162-165, 193-197, 227-230 - check for null sourceImage ✓
    - Lines 140-143, 171-174, 207-210, 240-243 - check result.status ✓
  - Null/Undefined:
    - All functions return null/empty array on failure ✓
    - Line 104 `layer.transform.origin || layer.transform.anchorPoint` - fallback ✓
  - Async: All properly try/catch wrapped
  - State: Direct project mutations with pushHistory()
- Adversarial Tests:
  - No source image: All functions return null/empty with logged error
  - Segmentation fails: Returns null/empty with logged error
  - Empty masks: Return null/empty (line 140, 171, 207, 240 guards)
- Notes: Excellent error handling throughout. All async operations protected.

### textAnimatorActions.ts - VERIFIED CLEAN (with systemic caveats)
- Lines: 1009
- Analyzed: 2025-12-27
- Bugs: None unique (SYSTEMIC-002, SYSTEMIC-004 apply)
- 6-Category Evidence (Rule 10 applied):
  - Error Handling: 0 try/catch
  - Loops: Lines 519, 536, 588, 625 - all bounded by totalChars or array sizes ✓
  - Input Validation:
    - Line 515 `fps || 16` - catches fps=0 ✓ (good pattern)
    - Line 687 `value: any` - stores without validation (SYSTEMIC-004)
    - Line 659 `charIndex < 0 || charIndex >= totalChars` - doesn't catch NaN (SYSTEMIC-002)
  - Null/Undefined:
    **SAFE Patterns (Grouped):**
    - Pattern A: `getTextLayer() + if (!layer) return` (25 instances)
    - Pattern B: `getTextData() + if (!textData) return` (25 instances)
    - Pattern C: `find() + if (!animator) return` (12 instances)
    - Pattern D: `|| fallback` (8 instances) - Lines 509, 515, 614, 657, 908, 919, 935
    - Pattern E: `?? fallback` (5 instances) - Lines 817-824, 903
    **RISKS (Minor):**
    | Line | Risk |
    |------|------|
    | 659 | `charIndex >= totalChars` - NaN bypasses (SYSTEMIC-002) |
    | 687 | `value: any` - NaN stored (SYSTEMIC-004) |
    | 815-825 | `(textData as any).pathConfig` - type assertion |
    **Summary:** 75+ SAFE instances, 3 minor risks (systemic patterns)
  - Async: 0 async operations
  - State: Line 772 `pathServices` Map - bounded by layer count
- Adversarial Tests:
  - `charIndex = NaN`: Line 659 `NaN >= totalChars` false → bypasses check → wrong result
  - fps=0: Line 515 `0 || 16 = 16` → properly catches ✓
  - Empty text: Line 511 returns empty array ✓
  - Layer not text type: getTextLayer returns null ✓
- Notes: Large file with thorough null handling. SYSTEMIC-002/004 apply. fps=0 is caught (good pattern).

### videoActions.ts - VERIFIED CLEAN (with systemic caveats)
- Lines: 623
- Analyzed: 2025-12-27
- Bugs: None unique (SYSTEMIC-003 applies at multiple points)
- 6-Category Evidence:
  - Error Handling: Lines 115-127 try/catch for URL/metadata, returns error status
  - Loops: Lines 315-339, 600-606 - bounded by layer arrays ✓
  - Input Validation:
    - Line 168: `Math.abs(metadata.fps - store.project.composition.fps) > 0.5` - if fps=NaN, comparison fails gracefully (NaN > 0.5 = false)
    - Lines 214, 222, 348, 355, 494, 501, 591, 595: `frameCount / fps` - if fps=0 → Infinity (SYSTEMIC-003)
    - Line 393: `videoFps / compositionFps` - if compositionFps=0 → Infinity (SYSTEMIC-003)
  - Null/Undefined:
    - Line 125: Revokes URL on error ✓
    - Line 148-164: Handles null fps case explicitly ✓
    - Lines 195, 310, 487, 577: comp null check ✓
  - Async: Lines 108-243, 303-370, 436-512 - async with proper error handling
  - State: Direct project mutations with pushHistory()
- Adversarial Tests:
  - File URL creation fails: Line 118 returns error status
  - Metadata extraction fails: Line 124-127 returns error status
  - fps unknown (null): Lines 148-164 returns fps_unknown status for user resolution ✓
  - compositionFps=0: Infinity timeStretch (SYSTEMIC-003)
  - fps mismatch with NaN: Comparison fails, no mismatch detected (benign)
- Notes: Good fps unknown handling. Multiple fps division points are SYSTEMIC-003.

## stores/actions/ - COMPLETE (20/20 files, 19 bugs found)

---


## engine/ - PENDING RE-AUDIT (0/60 files)

**STATUS: Full re-audit with Rule 14 A-Z protocol (26 categories)**

Previous analysis found 21 bugs (BUG-065 through BUG-089) but was not thorough enough.
Re-audit required with complete adversarial testing per CLAUDE.md Rule 14.

### Files to re-audit:

#### /ui/src/engine/ (barrel exports)
- [ ] index.ts
- [ ] types.ts
- [ ] WebGLContextManager.ts
- [ ] EngineLogger.ts
- [ ] TransformMatrixHandler.ts

#### /ui/src/engine/utils/
- [ ] audioSync.ts
- [ ] colorConversion.ts
- [ ] easingUtils.ts
- [ ] interpolation.ts
- [ ] layerHierarchy.ts
- [ ] motionBlur.ts
- [ ] transformUtils.ts

#### /ui/src/engine/animation/
- [ ] AnimationCurve.ts
- [ ] AnimationEvaluator.ts
- [ ] BlendShapeController.ts
- [ ] index.ts

#### /ui/src/engine/layers/

### BaseLayer.ts - BUGS FOUND (6)
- Started: 2025-12-27
- Completed: 2025-12-27
- Lines: 1956
- Status: Rule 14 A-Z Analysis COMPLETE
- Bugs: BUG-090, BUG-091, BUG-092, BUG-093, BUG-094, BUG-095

#### Rule 14 A-Z Adversarial Analysis Results:
| Category | Test | Result |
|----------|------|--------|
| 14A Numbers | setCompositionFps(0/NaN/Inf) | **BUG-090** |
| 14A Numbers | computeMotionPath endFrame=Inf | **BUG-091** |
| 14A Numbers | applyOpacity(NaN) | **BUG-092** |
| 14F Resources | computeMotionPath 1M frames | **BUG-093** |
| 14J Lifecycle | dispose() memory leaks | **BUG-094** |
| 14U Nesting | setParent circular ref | **BUG-095** |
| 14B Strings | blendMode validation | Delegates to utility |
| 14C Arrays | setEffects/setMasks null | TypeScript prevents |
| 14E Async | No async operations | N/A |
| 14G Boundaries | frame 0/-1/last | SAFE (fails invisible) |
| 14I Ordering | dispose twice | SAFE (null checks) |
| 14K Error Recovery | processEffects try/catch | SAFE |
| 14L Security | No eval/innerHTML | SAFE |
| 14O Animation | backwards playback | SAFE |
| 14P WebGL | Context via Three.js | Delegated |
| 14T Math | atan2(0,0) | SAFE (returns 0) |

- [ ] AdjustmentLayer.ts
- [ ] AudioLayer.ts
- [ ] CameraLayer.ts
- [ ] CanvasCacheManager.ts
- [ ] CompositingLayer.ts
- [ ] DepthFlowLayer.ts
- [ ] GradientLayer.ts
### ImageLayer.ts - BUGS FOUND (1)
- Started: 2025-12-27
- Completed: 2025-12-27
- Lines: 404
- Status: Rule 14 A-Z COMPLETE
- Bugs: BUG-121

#### Rule 14 Adversarial Tests:
| Method | Parameter | Type | Test Cases | Result |
|--------|-----------|------|------------|--------|
| setDimensions | width/height | number | height=0: DIV/0 in updateMeshSize | **BUG-121** |
| loadImage | url | string | Catches errors (line 120) | SAFE |
| setTexture | texture | object | Uses `|| 100` fallbacks for dims | SAFE |
| updateMeshSize | - | - | targetHeight guard at line 196 | PARTIAL |
| onDispose | - | - | Disposes geometry, material | SAFE |

#### Safe Patterns:
- setTexture() has `|| 100` fallbacks for width/height (lines 137-138)
- loadImage() catches errors with try/catch
- updateMeshSize() only divides if targetWidth && targetHeight truthy
- onDispose() properly disposes geometry and material
- [ ] index.ts
- [ ] LayerFactory.ts
- [ ] LightLayer.ts
- [ ] MaskManager.ts
- [ ] ModelLayer.ts
### NestedCompLayer.ts - BUGS FOUND (1)
- Started: 2025-12-27
- Completed: 2025-12-27
- Lines: 549
- Status: Rule 14 A-Z COMPLETE
- Bugs: BUG-120

#### Rule 14 Adversarial Tests:
| Method | Parameter | Type | Test Cases | Result |
|--------|-----------|------|------------|--------|
| setFPS | fps | number | 0:DIV/0 at line 229 | **BUG-120** |
| setFrameRateOverride | fps | number | fps=0: just produces 0 frame | SAFE |
| calculateNestedFrame | - | - | timeStretch guard OK (line 218) | PARTIAL |
| combineTransforms | - | - | /100 divisions safe (constant) | SAFE |
| onDispose | - | - | Disposes material, mesh, nulls refs | SAFE |
| resizeMesh | width/height | number | Called internally only | N/A |

#### Safe Patterns:
- calculateNestedFrame has timeStretch !== 0 guard (line 218)
- Frame clamping at lines 256-259: Math.max(0, Math.min(...))
- onDispose properly disposes material/mesh
- Clears cachedComposition and renderTexture on dispose
- [ ] NullLayer.ts
### ParticleLayer.ts - BUGS FOUND (4)
- Completed: 2025-12-27
- Lines: 1840
- Status: Rule 14 A-Z RE-AUDIT COMPLETE
- Bugs: BUG-085, BUG-086, BUG-087, BUG-096

#### Rule 14 A-Z Adversarial Analysis:
| Category | Test | Result |
|----------|------|--------|
| 14A Numbers | setFPS(0/NaN) | **BUG-085** (prev) |
| 14A Numbers | preCacheFrames endFrame=Inf | **BUG-086** (prev) |
| 14A Numbers | createParticleGrid gridSize=0 | **BUG-087** (prev) |
| 14A Numbers | setCacheInterval(0/NaN) | **BUG-096** (new) |
| 14I Ordering | initializeWithRenderer twice | SAFE (guards) |
| 14J Lifecycle | onDispose cleanup | SAFE (disposes all) |
| 14K Error | loadTexture catch | SAFE (logged) |
| 14M Concurrency | preCacheFrames concurrent | LOW (no mutex) |
| 14P WebGL | Context handling | Delegated |
| 14V State | initialized flag | SAFE |
- [ ] ProceduralMatteLayer.ts
- [ ] ShapeLayer.ts
- [ ] SolidLayer.ts
### TextLayer.ts - BUGS FOUND (4)
- Started: 2025-12-27
- Completed: 2025-12-27
- Lines: 1432
- Status: Rule 14 A-Z COMPLETE
- Bugs: BUG-112, BUG-113, BUG-114, BUG-115

#### Rule 14 Adversarial Tests:
| Method | Parameter | Type | Test Cases | Result |
|--------|-----------|------|------------|--------|
| setFontSize | size | number | 0:DIV/0, NaN, Infinity | **BUG-112** |
| setStroke | width/fontSize | number | fontSize=0: DIV/0 | **BUG-113** |
| setPathOffset | offset | number | NaN/<0/>100 | **BUG-114** |
| applyOpacity | opacity | number | NaN: Math.min/max bypass | **BUG-115** |
| setTracking | tracking | number | /1000 is safe (constant) | SAFE |
| setText | text | string | "": empty string OK | SAFE |
| onDispose | - | - | Disposes meshes and path | SAFE |
| loadFontMetrics | - | async | Catches errors (line 209) | SAFE |

#### Safe Patterns:
- loadFontMetrics() catches errors and falls back to heuristics
- disposeCharacterMeshes() properly disposes all Troika meshes
- onDispose() disposes textMesh, character meshes, and path service
- createCharacterMeshes() handles empty text (no-op)
- [ ] types.ts
### VideoLayer.ts - BUGS FOUND (4)
- Started: 2025-12-27
- Completed: 2025-12-27
- Lines: 1132
- Status: Rule 14 A-Z COMPLETE
- Bugs: BUG-116, BUG-117, BUG-118, BUG-119

#### Rule 14 Adversarial Tests:
| Method | Parameter | Type | Test Cases | Result |
|--------|-----------|------|------------|--------|
| setFPS | fps | number | 0:DIV/0, NaN, negative | **BUG-116** |
| setSpeed | speed | number | 0/NaN/Infinity/negative | **BUG-117** |
| setAudioLevel | level | number | NaN: Math.min/max bypass | **BUG-118** |
| setStartTime | time | number | negative/NaN/Infinity/>duration | **BUG-119** |
| setEndTime | time | number | undefined OK (expected) | SAFE |
| calculateVideoTime | - | - | Guards: timeStretch !== 0 | PARTIAL |
| seekToFrame | compositionFrame | number | Clamps time (line 396) | SAFE |
| clearVideo | - | - | Properly disposes all resources | SAFE |
| onDispose | - | - | Calls clearVideo() + cleans canvases | SAFE |

#### Safe Patterns:
- seekToFrame clamps time to [0, duration] (line 396)
- getBlendedFrame uses `fps || 30` default (line 705)
- initializeFrameAccurateDecoder catches errors, falls back (line 242-246)
- waitForMetadata properly cleans up event listeners
- calculateVideoTime has guard for timeStretch !== 0

### SplineLayer.ts - BUGS FOUND (4)
- Started: 2025-12-27
- Completed: 2025-12-27
- Lines: 1613
- Status: Rule 14 A-Z COMPLETE
- Bugs: BUG-108, BUG-109, BUG-110, BUG-111

#### Rule 14 Adversarial Tests:
| Method | Parameter | Type | Test Cases | Result |
|--------|-----------|------|------------|--------|
| getPointAt/getTangentAt | t | number | NaN: Math.min/max bypass | **BUG-108** |
| setStrokeWidth | width | number | 0/NaN/Infinity/negative | **BUG-109** |
| setResolution | width/height | number | 0/NaN/negative | **BUG-110** |
| setTrimStart/End/Offset | value | number | NaN/<0/>100/Infinity | **BUG-111** |
| setControlPoints | points | array | []: early return (line 457) | SAFE |
| addWarpPin | x, y | number | No validation but lower risk | NOTE |
| buildSpline | - | - | points.length < 2: early return | SAFE |
| onDispose | - | - | Clears meshes + warp cleanup | SAFE |

#### Safe Patterns:
- buildSpline() guards against points.length < 2 (line 457)
- clearMeshes() properly disposes geometry and materials (lines 585-600)
- onDispose() calls clearMeshes() and clears warp mesh
- Curve null checks before operations
- LOD context has safe defaults

#### /ui/src/engine/particles/

### GPUParticleSystem.ts - BUGS FOUND (4)
- Completed: 2025-12-27
- Lines: 1701
- Status: Rule 14 A-Z Analysis COMPLETE
- Bugs: BUG-097, BUG-098, BUG-099, BUG-100

#### Rule 14 A-Z Adversarial Analysis:
| Category | Test | Result |
|----------|------|--------|
| 14A Numbers | simulateToFrame fps=0/NaN | **BUG-097** |
| 14A Numbers | maxParticles NaN/Infinity | **BUG-098** |
| 14A Numbers | mass division | SAFE (Math.max(0.1)) |
| 14I Ordering | initialize() twice | **BUG-099** |
| 14J Lifecycle | dispose() incomplete | **BUG-100** |
| 14K Error | WebGL2 missing | SAFE (throws) |
| 14P WebGL | Context loss | No handling (delegated) |
| 14T Math | RNG overflow | SAFE (bitwise AND) |
| 14W Caching | Frame cache | SAFE (versioned) |
- [ ] index.ts
- [ ] ParticleEmitter.ts
- [ ] ParticleForceField.ts
- [ ] ParticleGPUPhysics.ts
- [ ] ParticleRenderer.ts
- [ ] ParticleSystem.ts
- [ ] types.ts

### LatticeEngine.ts - BUGS FOUND
- Started: 2025-12-27
- Completed: 2025-12-27
- Lines: 1704
- Status: Rule 14 A-Z COMPLETE
- Bugs: BUG-101, BUG-102, BUG-103, BUG-104, BUG-105, BUG-106, BUG-107

#### Rule 14 Adversarial Tests:
| Method | Parameter | Type | Test Cases | Result |
|--------|-----------|------|------------|--------|
| validateConfig | width/height | number | NaN bypasses `<=0` check | **BUG-101** |
| setCompositionFPS | fps | number | 0:DIV/0, NaN:propagates | **BUG-102** |
| resize | width/height | number | NaN bypasses `<=0` check | **BUG-103** |
| setViewportTransform | transform | number[] | []:OOB, scale=0:DIV/0 | **BUG-104** |
| setResolution | width/height | number | NaN bypasses `<=0` check | **BUG-105** |
| fitCompositionToViewport | padding | number | negative/NaN/large | **BUG-106** |
| captureFrameAsBlob | quality | number | >1, <0, NaN | **BUG-107** |
| dispose | - | - | Double call: SAFE (guard at line 1651) | SAFE |
| constructor | config | object | Missing props: SAFE (TypeScript) | SAFE |

#### Safe Patterns:
- dispose() has idempotent guard (line 1651): `if (this.state.isDisposed) return;`
- assertNotDisposed() check before most operations
- Event system uses Set (handles duplicate listeners)
- Context loss handlers properly cleaned up in dispose()
- WebGL context loss has proper event handler removal

#### /ui/src/engine/core/
- [ ] Compositor.ts
- [ ] FrameScheduler.ts
- [ ] NestedCompRenderer.ts
- [ ] RenderCache.ts
- [ ] SceneBuilder.ts

---

### blendModeUtils.ts - BUGS FOUND (3)
- Started: 2025-12-27
- Completed: 2025-12-27
- Lines: 162
- Status: Rule 14 A-Z Analysis COMPLETE
- Bugs: BUG-136, BUG-137, BUG-138

#### Crash Path Traces:

**Function: setMaterialBlendMode(material, mode)**
```
Line 18: export function setMaterialBlendMode(material: THREE.Material, mode: string): void {
  - No validation on material parameter

Line 20: material.blending = THREE.NormalBlending;
  - material=null → TypeError: Cannot set properties of null (setting 'blending')
  - material=undefined → TypeError: Cannot set properties of undefined (setting 'blending')

Result: CRASH - TypeError → BUG-136
```

**Function: applyBlendModeToGroup(group, mode)**
```
Line 125: export function applyBlendModeToGroup(group: THREE.Group, mode: string): void {
  - No validation on group parameter

Line 126: group.traverse((child) => {
  - group=null → TypeError: Cannot read properties of null (reading 'traverse')
  - group=undefined → TypeError: Cannot read properties of undefined (reading 'traverse')

Result: CRASH - TypeError → BUG-137
```

**Line 127 Silent Skip:**
```
Line 127: if (child instanceof THREE.Mesh && child.material) {
  - child=Mesh with material=null → condition FALSE, body skipped
  - child=Mesh with material=undefined → condition FALSE, body skipped

Lines 128-131: (NEVER EXECUTED)
  - setMaterialBlendMode() NOT called
  - material.needsUpdate NOT set
  - NO warning, NO error, NO logging

Result: SILENT NO-OP → BUG-138
```

**Function: isValidBlendMode(mode)**
```
Line 159-160: return SUPPORTED_BLEND_MODES.includes(mode as BlendModeName);
  - mode=null → includes("null") = false → returns false (SAFE)
  - mode=undefined → includes("undefined") = false → returns false (SAFE)
  - mode=NaN → includes("NaN") = false → returns false (SAFE)

Result: SAFE - all invalid inputs return false
```

#### Safe Patterns Found:
- Line 114-116: Default case returns normal blending for unknown modes ✓
- Line 159-160: isValidBlendMode() handles any input gracefully ✓
- SUPPORTED_BLEND_MODES as const for type safety ✓

---

### ModelLayer.ts - BUGS FOUND (7)
- Started: 2025-12-27
- Completed: 2025-12-27
- Lines: 898
- Status: Rule 14 A-Z Analysis COMPLETE
- Bugs: BUG-139, BUG-140, BUG-141, BUG-142, BUG-143, BUG-144, BUG-145
- Note: BUG-074 (line 783 fps=0 division) was previously filed

#### Crash Path Traces:

**Function: applyMaterialOverrideToMesh(mesh, override)**
```
Line 568-570:
  let material = Array.isArray(mesh.material)
    ? mesh.material[0].clone()  // CRASH if []
    : mesh.material.clone();

  - mesh.material=[] → mesh.material[0]=undefined → undefined.clone()
  - TypeError: Cannot read properties of undefined (reading 'clone')
Result: CRASH → BUG-139
```

**Function: setScale(scale)**
```
Line 684-687:
  if (typeof scale === 'number') {
    this.model.scale.setScalar(scale);
  } else {
    this.model.scale.set(scale.x, scale.y, scale.z);
  }

  - scale=NaN → model.scale = (NaN, NaN, NaN) → transform corrupted
  - scale=0 → model invisible
  - scale=Infinity → rendering glitch
Result: SILENT CORRUPTION → BUG-140
```

**Function: setAnimationTime(time)**
```
Line 518-519:
  this.currentAction.time = time;
  this.mixer.update(0);

  - time=NaN → animation at undefined position
  - time=-100 → negative time (undefined behavior)
  - time=Infinity → animation at broken state
Result: SILENT CORRUPTION → BUG-141
```

**Function: updateAnimation(deltaTime)**
```
Line 528-529:
  const speed = this.modelData.animation?.speed ?? 1;
  this.mixer.update(deltaTime * speed);

  - speed=NaN → deltaTime * NaN = NaN → mixer corrupted
  - speed=Infinity → animation jumps
Result: SILENT CORRUPTION → BUG-142
```

**Function: applyMaterialOverrideToMesh - opacity**
```
Line 586-589:
  if (override.opacityOverride !== undefined) {
    material.transparent = override.opacityOverride < 1;  // NaN < 1 = false
    material.opacity = override.opacityOverride;  // NaN stored
  }

  - opacityOverride=NaN → transparent=false, opacity=NaN
Result: SILENT CORRUPTION (SYSTEMIC-005) → BUG-143
```

**Function: applyMaterialOverrideToMesh - PBR**
```
Line 597-601:
  if (override.metalness !== undefined) {
    material.metalness = override.metalness;  // No validation
  }
  if (override.roughness !== undefined) {
    material.roughness = override.roughness;  // No validation
  }

  - metalness/roughness=NaN/Infinity/-5/100 → stored without clamping
  - PBR expects [0,1] range
Result: SILENT CORRUPTION → BUG-144
```

**Function: onUpdate(properties)**
```
Line 849:
  Object.assign(this.modelData.animation ?? {}, data.animation);

  When this.modelData.animation is null:
  - `this.modelData.animation ?? {}` creates temp object {}
  - Object.assign({}, data.animation) → assigns to temp
  - Temp object DISCARDED
  - this.modelData.animation still null
Result: SILENT NO-OP → BUG-145
```

#### Safe Patterns Found:
- Line 159-163: loadModel() catches errors with try/catch ✓
- Line 199-205: Proper error handling with finally block ✓
- Line 477-480: playAnimation() null checks on mixer and clip ✓
- Line 632-636: boundingBoxHelper disposal before recreation ✓
- Line 864-896: disposeModel() properly cleans up resources ✓
- Line 194-196: Default case throws for unsupported formats ✓

---

### CameraLayer.ts - BUGS FOUND (5)
- Started: 2025-12-27
- Completed: 2025-12-27
- Lines: 702
- Status: Rule 14 A-Z Analysis COMPLETE
- Bugs: BUG-146, BUG-147, BUG-148, BUG-149, BUG-150
- Note: BUG-072 (autoAdvanceSpeed NaN/Infinity) was previously filed

#### Crash Path Traces:

**Function: setCompositionAspect(aspect)**
```
Line 133: this.compositionAspect = aspect;
  - aspect=NaN → stored → createFrustum() nearWidth=NaN
  - aspect=0 → nearWidth=0, farWidth=0 → degenerate frustum
  - aspect=-1 → negative frustum dimensions
Result: SILENT CORRUPTION → BUG-146
```

**Function: createFrustum()**
```
Line 246-254:
  const near = camera.nearClip;  // No validation
  const far = Math.min(camera.farClip, 2000);  // Math.min(NaN,2000)=NaN
  const fov = camera.angleOfView * (Math.PI / 180);  // NaN propagates
  const nearHeight = 2 * Math.tan(fov / 2) * near;  // Math.tan(NaN)=NaN

  - camera.nearClip=NaN → all vertices NaN
  - camera.angleOfView=180 → Math.tan(π/2)=huge → frustum explodes
Result: SILENT CORRUPTION → BUG-147
```

**Function: applyPathFollowing() - t clamp**
```
Line 522: t = Math.max(0, Math.min(1, t));
  - t=NaN → Math.min(1, NaN)=NaN → Math.max(0, NaN)=NaN
  - NaN passed to splineProvider at line 525
  - NaN passed to lookAhead calculation at line 536
Result: SILENT CORRUPTION (SYSTEMIC-005) → BUG-148
```

**Function: applyPathFollowing() - banking**
```
Line 593-594:
  const bankAngle = cross * pathFollowing.bankingStrength * Math.PI / 4;
  this.group.rotateZ(bankAngle);

  - bankingStrength=Infinity → bankAngle=±Infinity
  - rotateZ(Infinity) → rotation.z=Infinity
Result: SILENT CORRUPTION → BUG-149
```

**Function: onApplyEvaluatedState(state)**
```
Line 485:
  this.cameraData.pathFollowing.parameter.value = props['pathParameter'] as number;

  - props['pathParameter']=NaN → stored directly
  - Used in applyPathFollowing() line 511
Result: SILENT CORRUPTION → BUG-150
```

#### Safe Patterns Found:
- Line 237-238: createFrustum() early return if no camera ✓
- Line 330-331: getCamera() null checks on getter and cameraId ✓
- Line 412: onEvaluateFrame() early return if no camera ✓
- Line 500: applyPathFollowing() early return if no splineProvider ✓
- Line 527-530: Fallback to camera position if spline not found ✓
- Line 584: Banking only applied if before/after tangents exist ✓
- Line 670-701: Proper disposal of wireframe and frustum ✓

---

**Previous bugs found (kept for reference, may find more):**
- BUG-065 through BUG-089 documented in BUGS.md

---

### DepthflowLayer.ts - BUGS FOUND (6)
- Started: 2025-12-27
- Completed: 2025-12-27
- Lines: 543
- Status: Rule 14 A-Z COMPLETE
- Bugs: BUG-151, BUG-152, BUG-153, BUG-154, BUG-155, BUG-156

#### Rule 14 Adversarial Tests:
| Method | Parameter | Type | Test Cases | Result |
|--------|-----------|------|------------|--------|
| setDimensions | width/height | number | 0/NaN/negative/Infinity: degenerate geometry | **BUG-151** |
| updateConfig | config.* | Partial | NaN/Infinity: stored to uniforms | **BUG-152** |
| shader | zoom uniform | number | zoom=0: GPU division by zero | **BUG-153** |
| calculatePresetValues | fps | number | fps=0: time=Infinity (SYSTEMIC-003) | **BUG-154** |
| onEvaluateFrame | fps | number | fps=0: division by zero | **BUG-154** |
| onApplyEvaluatedState | props.* | number | NaN: stored directly to uniforms | **BUG-155** |
| onApplyEvaluatedState | audioMod.* | number | NaN: added to uniforms (NaN !== 0 passes) | **BUG-156** |
| setSourceLayer | layerId | string | Empty string: handled (returns null) | SAFE |
| setDepthLayer | layerId | string | Empty string: handled (returns null) | SAFE |
| onDispose | - | - | Properly disposes textures + geometry | SAFE |

#### Crash Path Traces:

**Function: setDimensions(width, height)**
```
Line 247: if (width === this.width && height === this.height) return;
  - width=NaN: NaN === this.width → false (continues)
Line 254: this.geometry = new THREE.PlaneGeometry(width, height);
  - width=NaN → PlaneGeometry(NaN, height) → vertices are NaN
  - width=0 → PlaneGeometry(0, height) → zero-area invisible plane
  - width=-100 → PlaneGeometry(-100, height) → inverted/negative geometry
Result: SILENT CORRUPTION → BUG-151
```

**Function: updateConfig(config)**
```
Line 288: Object.assign(this.depthflowData.config, config);
Line 297-298:
  if (config.zoom !== undefined) {
    this.material.uniforms.zoom.value = config.zoom;
  }
  - config.zoom=NaN → uniform zoom=NaN → shader uses NaN
  - config.zoom=0 → shader division by zero (line 63)
Result: SILENT CORRUPTION → BUG-152, BUG-153
```

**Shader line 63:**
```
vec2 zoomedUV = (vUv - 0.5) / zoom + 0.5;
  - zoom=0 → GPU division by zero → undefined behavior
Result: GPU-DEPENDENT CORRUPTION → BUG-153
```

**Function: onEvaluateFrame(frame) / calculatePresetValues(frame, fps)**
```
Line 320: const time = frame / fps;
Line 442: this.material.uniforms.time.value = frame / fps;
  - fps=0, frame=30 → time=Infinity
  - fps=0, frame=0 → time=NaN (0/0)
Result: SILENT CORRUPTION (SYSTEMIC-003) → BUG-154
```

**Function: onApplyEvaluatedState(state)**
```
Line 452-453: this.material.uniforms.zoom.value = props['zoom'] as number;
Line 462-463: this.material.uniforms.rotation.value = THREE.MathUtils.degToRad(props['rotation'] as number);
  - props['zoom']=NaN → uniform=NaN
  - degToRad(NaN) = NaN
Result: SILENT CORRUPTION (SYSTEMIC-005) → BUG-155
```

**Audio modifier section (lines 470-492):**
```
Line 473-474:
  if (audioMod.depthflowZoom !== undefined && audioMod.depthflowZoom !== 0) {
    this.material.uniforms.zoom.value += audioMod.depthflowZoom;
  }
  - audioMod.depthflowZoom=NaN: NaN !== 0 is true → check passes
  - 1.0 + NaN = NaN stored to uniform
Result: SILENT CORRUPTION (SYSTEMIC-005) → BUG-156
```

#### Safe Patterns Found:
- Line 207-217: loadTextures() null checks texture before use
- Line 233-240: loadTextureFromLayer() returns null if not found
- Line 264-268: setSourceLayer() disposes old texture with optional chaining
- Line 274-280: setDepthLayer() same safe pattern
- Line 534-541: onDispose() properly disposes textures, geometry, material

---

### LightLayer.ts - BUGS FOUND (5)
- Started: 2025-12-27
- Completed: 2025-12-27
- Lines: 1083
- Status: Rule 14 A-Z COMPLETE
- Bugs: BUG-157, BUG-158, BUG-159, BUG-160, BUG-161

#### Rule 14 Adversarial Tests:
| Method | Parameter | Type | Test Cases | Result |
|--------|-----------|------|------------|--------|
| setColorTemperature | kelvin | number | 0:Math.log(0)=-Inf, negative:NaN | **BUG-157** |
| setIntensity | intensity | number | NaN/Infinity: stored directly | **BUG-158** |
| setAreaSize | width/height | number | 0/NaN/negative: corrupt RectAreaLight | **BUG-159** |
| onApplyEvaluatedState | props.* | number | NaN: stored directly (SYSTEMIC-005) | **BUG-160** |
| updatePathFollowing | audioMod | number | NaN: bypasses Math.max/min (SYSTEMIC-005) | **BUG-161** |
| setLightType | type | LightType | Invalid type: handled (default case) | SAFE |
| setColor | color | string | Invalid: Three.js handles gracefully | SAFE |
| setFalloffDistance | distance | number | NaN: stored but lower impact | NOTE |
| onDispose | - | - | Properly disposes light and helper | SAFE |

#### Crash Path Traces:

**Function: setColorTemperature(kelvin)**
```
Line 646: const rgb = kelvinToRGB(kelvin);
  → kelvin=0: temp=0 → Math.log(0)=-Infinity → g=-Infinity
  → kelvin=-100: temp=-1 → Math.log(-1)=NaN
Line 200: g = Math.max(0, Math.min(255, g)); // NaN bypasses (SYSTEMIC-005)
Line 647: this.light.color.setRGB(rgb.r, rgb.g, rgb.b); // NaN color
Result: SILENT CORRUPTION → BUG-157
```

**Function: setIntensity(intensity)**
```
Line 653: this.light.intensity = intensity / 100;
  → intensity=NaN: light.intensity = NaN
  → intensity=Infinity: light.intensity = Infinity
Result: SILENT CORRUPTION → BUG-158
```

**Function: setAreaSize(width, height)**
```
Line 684-685: this.light.width = width; this.light.height = height;
  → width=NaN: RectAreaLight.width = NaN
  → width=0: zero-area light (no illumination)
  → width=-100: negative dimensions (undefined behavior)
Result: SILENT CORRUPTION → BUG-159
```

**Function: onApplyEvaluatedState(state)**
```
Line 955: this.light.intensity = (props['intensity'] as number) / 100;
Line 960: this.light.angle = THREE.MathUtils.degToRad((props['coneAngle'] as number) / 2);
Line 973: const rgb = kelvinToRGB(props['colorTemperature'] as number);
  → All evaluated values stored without validation
Result: SILENT CORRUPTION (SYSTEMIC-005) → BUG-160
```

**Function: updatePathFollowing(frame)**
```
Line 597: progress = Math.max(0, Math.min(1, progress + audioMod.pathPosition));
  → audioMod.pathPosition=NaN: NaN !== 0 true, Math.max/min bypass
  → progress = NaN passed to pathProvider
Result: SILENT CORRUPTION (SYSTEMIC-005) → BUG-161
```

#### Safe Patterns Found:
- Line 393-396: createLight() has default case for unknown light type
- Line 472-476: createHelper() disposes old helper before creating new
- Line 530: updatePointOfInterest() early return if not enabled
- Line 533-535: Light type check before lookAt operations
- Line 538-545: layerPositionGetter null check before use
- Line 589: updatePathFollowing() early return if disabled/no provider
- Line 602: result null check before using path data
- Line 789-795: setDriverPropertyValue uses Math.max/min for color (but NaN bypasses)
- Line 1075-1081: onDispose() properly disposes light and helper

---

### NormalLayer.ts - BUGS FOUND (1)
- Started: 2025-12-27
- Completed: 2025-12-27
- Lines: 197
- Status: Rule 14 A-Z COMPLETE
- Bugs: BUG-162

#### Rule 14 Adversarial Tests:
| Method | Parameter | Type | Test Cases | Result |
|--------|-----------|------|------------|--------|
| onUpdate | data.lightDirection | object | {x:NaN, y:NaN, z:NaN}: normalize()=NaN | **BUG-162** |
| onUpdate | data.lightIntensity | number | NaN: stored to uniform | **BUG-162** |
| setTexture | texture | Texture | null: clears uniform (intentional) | SAFE |
| createMesh | - | - | Uses || defaults (0 treated as falsy) | NOTE |
| onEvaluateFrame | - | - | Material null check at line 160 | SAFE |
| onDispose | - | - | Properly disposes texture, material, geometry | SAFE |
| getVisualizationModeIndex | - | - | Default case returns 0 | SAFE |

#### Crash Path Traces:

**Function: onUpdate(properties) → onEvaluateFrame(frame)**
```
Line 182: Object.assign(this.normalData, data);
  - data = { lightDirection: { x: NaN, y: NaN, z: NaN } }
  - NaN merged into this.normalData.lightDirection

Line 170-174:
  this.material.uniforms.lightDirection.value.set(
    this.normalData.lightDirection.x,  // NaN
    this.normalData.lightDirection.y,  // NaN
    this.normalData.lightDirection.z   // NaN
  ).normalize();
  - normalize() on NaN vector = NaN for all components

Also:
  - lightDirection = {x:0, y:0, z:0} → normalize() = NaN (zero-length vector)

Result: SILENT CORRUPTION → BUG-162
```

#### Safe Patterns Found:
- Line 160: `if (!this.material) return;` - early return on null material
- Line 139-146: getVisualizationModeIndex() has default case returning 0
- Lines 186-196: onDispose() properly disposes all Three.js resources
- Line 150-152: setTexture() checks material before accessing uniforms

#### Notes:
- arrowDensity and arrowScale are dead code - arrows visualization mode (index 2) not implemented in shader
- Shader only handles modes 0 (rgb), 1 (hemisphere), 3 (lit) - mode 2 falls through to default

---

### PointCloudLayer.ts - BUGS FOUND (2)
- Started: 2025-12-27
- Completed: 2025-12-27
- Lines: 1147
- Status: Rule 14 A-Z COMPLETE
- Bugs: BUG-163, BUG-164

#### Rule 14 Adversarial Tests:
| Method | Parameter | Type | Test Cases | Result |
|--------|-----------|------|------------|--------|
| setPointSize | size | number | NaN/Infinity/negative: stored to uniform | **BUG-163** |
| setOpacity | opacity | number | NaN/Infinity/negative: stored to uniform | **BUG-163** |
| onApplyEvaluatedState | props.* | number | NaN: passed through setters | **BUG-163** |
| getGradientTexture | stops | array | Same position stops: DIV/0 | **BUG-164** |
| loadPointCloud | - | - | try/catch handles errors properly | SAFE |
| loadXYZ | url | string | parseFloat NaN: stored but low risk | NOTE |
| loadLAS | url | string | File signature validated | SAFE |
| applyHeightColoring | - | - | range || 1 handles zero range | SAFE |
| applyIntensityColoring | - | - | range || 1 handles zero range | SAFE |
| disposePointCloud | - | - | All resources properly disposed | SAFE |

#### Crash Path Traces:

**Function: setPointSize(size) / setOpacity(opacity)**
```
Line 964: this.material.uniforms.pointSize.value = size;
Line 973: this.material.uniforms.opacity.value = opacity;
  → size=NaN: uniform pointSize=NaN → gl_PointSize=NaN → points invisible
  → opacity=NaN: uniform opacity=NaN → shader alpha=NaN → corrupt rendering
  → size=-5: negative point size → undefined GPU behavior
Result: SILENT CORRUPTION (SYSTEMIC-005) → BUG-163
```

**Function: onApplyEvaluatedState(state)**
```
Line 1064: this.setPointSize(props['pointSize'] as number);
Line 1068: this.setOpacity(props['opacity'] as number);
  → Evaluated NaN values passed directly to setters
Result: SILENT CORRUPTION (SYSTEMIC-005) → BUG-163
```

**Function: getGradientTexture()**
```
Line 655: const localT = (t - stop1.position) / (stop2.position - stop1.position);
  → stops = [{position: 0.5}, {position: 0.5}]
  → stop2.position - stop1.position = 0
  → localT = Infinity or NaN
Line 658: const color = color1.lerp(color2, localT);
  → lerp with NaN produces NaN color
Result: SILENT CORRUPTION → BUG-164
```

#### Safe Patterns Found:
- Line 155-158: Early return if no assetId
- Line 282-284: LAS file signature validation
- Line 500: storeOriginalAttributes() early return if no geometry
- Lines 706, 757, 788, 817, 846, 888: Early returns if no geometry/material/attributes
- Line 765, 796, 866: `|| 1` guards against zero range in coloring methods
- Lines 1121-1146: Comprehensive disposal with null checks
- Line 188-191: try/catch around file loading with error message

---

### PoseLayer.ts - BUGS FOUND (2)
- Started: 2025-12-27
- Completed: 2025-12-27
- Lines: 727
- Status: Rule 14 A-Z COMPLETE
- Bugs: BUG-165, BUG-166

#### Rule 14 Adversarial Tests:
| Method | Parameter | Type | Test Cases | Result |
|--------|-----------|------|------------|--------|
| setCompositionSize | width/height | number | NaN/0/negative: corrupt canvas | **BUG-165** |
| interpolatePoses | t | number | NaN/Infinity: NaN keypoints | **BUG-166** |
| scalePose | scale | number | NaN: propagates to keypoints | NOTE |
| rotatePose | angleDegrees | number | NaN: Math.cos/sin(NaN)=NaN | NOTE |
| scalePose | - | - | count=0: early return (line 642) | SAFE |
| rotatePose | - | - | count=0: early return (line 671) | SAFE |
| renderSinglePose | keypoints | array | Empty: forEach no-op | SAFE |
| dispose | - | - | Properly disposes texture, material, geometry | SAFE |

#### Crash Path Traces:

**Function: setCompositionSize(width, height) → renderPoses()**
```
Line 447-448: this.compWidth = width; this.compHeight = height;
  → width=NaN: stored without validation

Line 313-314: canvas.width = width; canvas.height = height;
  → canvas.width = NaN → becomes 0 or undefined behavior

Line 346-347: x: kp.x * width, y: kp.y * height
  → 0.5 * NaN = NaN → keypoint positions become NaN

Result: SILENT CORRUPTION → BUG-165
```

**Function: interpolatePoses(pose1, pose2, t)**
```
Line 709: x: kp1.x + (kp2.x - kp1.x) * t
Line 710: y: kp1.y + (kp2.y - kp1.y) * t
  → t=NaN: (0.8 - 0.2) * NaN = NaN
  → kp1.x + NaN = NaN
  → All keypoint positions become NaN

Result: SILENT CORRUPTION → BUG-166
```

#### Safe Patterns Found:
- Line 275: getContext('2d')! - uses non-null assertion (minor risk)
- Line 368: Index bounds check `if (startIdx >= keypoints.length || endIdx >= keypoints.length) return;`
- Line 433: Index bounds check `if (index >= names.length) return;`
- Line 554: Pose lookup with early return `if (!pose) return;`
- Line 642: scalePose count=0 early return
- Line 671: rotatePose count=0 early return
- Line 698-699: interpolatePoses validates keypoint array lengths
- Lines 616-621: dispose() properly cleans up Three.js resources

---

### ProceduralMatteLayer.ts - BUGS FOUND (4)
- Started: 2025-12-27
- Completed: 2025-12-27
- Lines: 768
- Status: Rule 14 A-Z COMPLETE
- Bugs: BUG-167, BUG-168, BUG-169, BUG-170

#### Rule 14 Adversarial Tests:
| Method | Parameter | Type | Test Cases | Result |
|--------|-----------|------|------------|--------|
| setDimensions | width/height | number | NaN/0/negative: corrupt canvas | **BUG-167** |
| renderPattern | compositionFps | number | fps=0: DIV/0 → time=Infinity (SYSTEMIC-003) | **BUG-168** |
| applyLevels | inputBlack/White | number | Equal values: inputRange=0 → DIV/0 | **BUG-169** |
| renderDissolve | blockSize | number | 0: blocksX=Infinity → **INFINITE LOOP** | **BUG-170** |
| renderCheckerboard | tilesX/Y | number | 0: tileW=Infinity → fillRect fails | **BUG-170** |
| renderVenetianBlinds | slats | number | 0: slatHeight=Infinity (loop safe) | **BUG-170** |
| extractMatteData | data | object | null: returns safe defaults | SAFE |
| onDispose | - | - | Properly disposes texture, material, geometry | SAFE |

#### Crash Path Traces:

**Function: setDimensions(width, height)**
```
Line 133-137:
  this.width = width;
  this.height = height;
  this.renderCanvas.width = width;   // NaN → 0
  this.renderCanvas.height = height; // NaN → 0

Line 142: this.mesh.geometry = new THREE.PlaneGeometry(width, height);
  → width=NaN: degenerate geometry

Result: SILENT CORRUPTION → BUG-167
```

**Function: renderPattern(frame)**
```
Line 186: const time = ... (frame * speed / this.compositionFps + phase)
  → compositionFps=0: frame * speed / 0 = Infinity or NaN
  → time = Infinity passed to all pattern renderers
  → Line 250: angle + time * 360 = Infinity → Math.cos(Infinity) = NaN

Result: SILENT CORRUPTION (SYSTEMIC-003) → BUG-168
```

**Function: applyLevels(frame)**
```
Line 644: const inputRange = inputWhite - inputBlack;
  → inputBlack=inputWhite=128: inputRange=0

Line 651: (value - inputBlack) / inputRange * 255
  → (128 - 128) / 0 = NaN
  → Math.max(0, NaN) = NaN (SYSTEMIC-005)

Result: SILENT CORRUPTION → BUG-169
```

**Function: renderDissolve()**
```
Line 550-551:
  const blocksX = Math.ceil(w / blockSize);  // blockSize=0 → Infinity
  const blocksY = Math.ceil(h / blockSize);  // blockSize=0 → Infinity

Line 553-554:
  for (let by = 0; by < blocksY; by++) {   // 0 < Infinity is ALWAYS TRUE
    for (let bx = 0; bx < blocksX; bx++) { // INFINITE LOOP

Result: **INFINITE LOOP - BROWSER FREEZE** → BUG-170
```

#### Safe Patterns Found:
- Lines 81-106: extractMatteData() returns full default object if data is null
- Line 229-232: Default case in pattern switch returns solid white (graceful fallback)
- Line 637-640: applyLevels() early return if all values are defaults
- Lines 751-766: onDispose() properly disposes all Three.js resources
- Line 268: Math.max(0.001, blend / 2) prevents zero blend in gradients

---

### AudioLayer.ts - BUGS FOUND (2)
- Started: 2025-12-27
- Completed: 2025-12-27
- Lines: 421
- Status: Rule 14 A-Z COMPLETE
- Bugs: BUG-171, BUG-172

#### Rule 14 Adversarial Tests:
| Method | Parameter | Type | Test Cases | Result |
|--------|-----------|------|------------|--------|
| getAudioTimeForFrame | fps | number | fps=0: DIV/0 → Infinity/NaN (SYSTEMIC-003) | **BUG-171** |
| updateGain | levelDb | number | NaN: bypasses Math.max/min clamp → Web Audio NaN | **BUG-172** |
| updatePan | pan | number | NaN: bypasses Math.max/min clamp → Web Audio NaN | **BUG-172** |
| startPlayback | - | - | Calls getAudioTimeForFrame, delegates fps | SAFE (caller) |
| stopPlayback | - | - | Null check at line 282-283 | SAFE |
| scrubAtFrame | - | - | Calls getAudioTimeForFrame, delegates fps | SAFE (caller) |
| isPlayingAtFrame | - | - | Calls getAudioTimeForFrame, early returns | SAFE (caller) |

#### Crash Path Traces:

**Function: getAudioTimeForFrame(frame, fps)**
```
Line 183: const layerTime = frame / fps;
  → fps=0, frame=30: 30/0 = Infinity
  → fps=0, frame=0: 0/0 = NaN

Line 184: const audioTime = (layerTime - startTime) * speed;
  → layerTime=Infinity → audioTime=Infinity or NaN

Line 185: return Math.max(0, audioTime);
  → Math.max(0, NaN) = NaN (SYSTEMIC-005)

Result: SILENT CORRUPTION (SYSTEMIC-003) - audio sync broken → BUG-171
```

**Function: updateGain(levelDb)**
```
Line 328: const clampedDb = Math.max(-60, Math.min(12, levelDb));
  → levelDb=NaN: Math.min(12, NaN)=NaN, Math.max(-60, NaN)=NaN

Line 329: const linearGain = clampedDb <= -60 ? 0 : Math.pow(10, clampedDb / 20);
  → NaN <= -60 is FALSE
  → Math.pow(10, NaN/20) = Math.pow(10, NaN) = NaN

Line 332-335: gainNode.gain.setValueAtTime(linearGain, ...)
  → linearGain=NaN passed to Web Audio API

Result: SILENT CORRUPTION (SYSTEMIC-005) - audio undefined → BUG-172
```

**Function: updatePan(pan)**
```
Line 345: const clampedPan = Math.max(-1, Math.min(1, pan));
  → pan=NaN: Math.max(-1, NaN) = NaN (SYSTEMIC-005)

Line 347-350: panNode.pan.setValueAtTime(clampedPan, ...)
  → clampedPan=NaN passed to Web Audio API

Result: SILENT CORRUPTION (SYSTEMIC-005) - stereo undefined → BUG-172
```

#### Safe Patterns Found:
- Line 78: loadAudio() has try/catch with reject handler
- Line 282-283: stopPlayback() null checks before accessing playbackNodes
- Line 397-415: onDispose() properly cleans up audio nodes and buffers
- Line 260-277: startPlayback() null check on audioContext and playbackNodes
- Line 189-207: isPlayingAtFrame() returns safe defaults (false) on missing data

---

### blendModeUtils.ts - VERIFIED CLEAN
- Started: 2025-12-27
- Completed: 2025-12-27
- Lines: 162
- Status: Rule 14 A-Z COMPLETE
- Bugs: None

#### Rule 14 Adversarial Tests:
| Method | Parameter | Type | Test Cases | Result |
|--------|-----------|------|------------|--------|
| setMaterialBlendMode | material | object | null: TypeError (caller type contract) | SAFE |
| setMaterialBlendMode | mode | string | null/undefined/unknown: default case line 114-116 | SAFE |
| applyBlendModeToGroup | group | object | null: TypeError (caller type contract) | SAFE |
| isValidBlendMode | mode | string | null: includes(null)=false | SAFE |

#### Analysis:
- Line 28: switch(mode) - unknown/null values fall through to default (NormalBlending)
- Line 126: group.traverse() - bounded by Three.js scene graph
- Line 127: instanceof + && guard before material access
- No loops, no division, no numeric edge cases

---

### ControlLayer.ts - BUGS FOUND (1)
- Started: 2025-12-27
- Completed: 2025-12-27
- Lines: 181
- Status: Rule 14 A-Z COMPLETE
- Bugs: BUG-173

#### Rule 14 Adversarial Tests:
| Method | Parameter | Type | Test Cases | Result |
|--------|-----------|------|------------|--------|
| constructor | showIndicator | boolean | undefined: default true; NaN: falsy | SAFE |
| setIndicatorVisible | visible | boolean | null/undefined: falsy, no render | SAFE |
| setIndicatorSize | size | number | NaN/0/Infinity: stored, corrupts geometry | **BUG-173** |
| disposeIndicator | - | - | null check line 132 | SAFE |
| onUpdate | properties | object | empty object: both clauses false | SAFE |
| onDispose | - | - | delegates to disposeIndicator | SAFE |

#### Crash Path Trace:

**Function: setIndicatorSize(size)**
```
Line 116: if (size === this.indicatorSize) return;
  → size=NaN: NaN === 50 is FALSE (proceeds)

Line 118: this.indicatorSize = size;
  → this.indicatorSize = NaN (stored)

Line 124: this.createIndicator();
  → Inside createIndicator(), line 44: const size = this.indicatorSize; (NaN)
  → Line 57: new THREE.Vector3(-size / 2, 0, 0) = Vector3(NaN, 0, 0)

Result: SILENT CORRUPTION - indicator geometry has NaN coordinates → BUG-173
```

#### Safe Patterns Found:
- Line 107: if (this.indicator) - null check before access
- Line 132: if (!this.indicator) return - early return on null
- Line 134-143: traverse with instanceof guards before dispose
- Line 146: this.indicator = null - proper cleanup

---

### DepthLayer.ts - BUGS FOUND (1)
- Started: 2025-12-27
- Completed: 2025-12-27
- Lines: 331
- Status: Rule 14 A-Z COMPLETE
- Bugs: BUG-174

#### Rule 14 Adversarial Tests:
| Method | Parameter | Type | Test Cases | Result |
|--------|-----------|------|------------|--------|
| extractDepthData | layerData | object | null data: ?? fallbacks | SAFE |
| createMesh | - | - | Fixed geometry, || fallbacks | SAFE |
| getVisualizationModeIndex | - | - | Unknown mode: default 0 | SAFE |
| updateColormapTexture | - | - | Unknown colorMap: grayscale fallback | SAFE |
| onUpdate | data | object | minDepth===maxDepth: shader DIV/0; NaN: stored | **BUG-174** |
| onDispose | - | - | All null checks | SAFE |

#### Crash Path Trace:

**Shader Code (Line 107):**
```
float normalizedDepth = (depth - minDepth) / (maxDepth - minDepth);
  → minDepth=0.5, maxDepth=0.5: (depth - 0.5) / 0 = undefined
  → minDepth=NaN: X / NaN = NaN

Line 108: clamp(normalizedDepth, 0.0, 1.0)
  → clamp(NaN, 0.0, 1.0) = NaN in GLSL

Result: SILENT CORRUPTION - depth visualization renders undefined colors → BUG-174
```

#### Safe Patterns Found:
- Lines 49-61: extractDepthData uses ?? fallbacks for all properties
- Line 159: updateColormapTexture falls back to grayscale colormap
- Line 154: getVisualizationModeIndex default returns 0
- Lines 237-250: onDispose has null checks for all resources
- Shader line 108: clamp attempts to bound values (but NaN bypasses)

---

## /ui/src/stores/actions/

### audioActions.ts - PENDING
- Started: 2025-12-28
- Lines: TBD
- Status: READING
- Completed: 2025-12-28
- Lines: 1012
- Status: Rule 14 COMPLETE - ALL BUGS FIXED
- Bugs Found: BUG-029, BUG-030, BUG-031, BUG-032, BUG-033, BUG-034, BUG-047, BUG-048, BUG-049 (9 total)
- Bugs Fixed: All 9

#### Rule 14 Adversarial Tests:
| Method | Parameter | Test Cases | Result |
|--------|-----------|------------|--------|
| extractChannelAmplitudes | fps | 0:DIV/0, NaN:PROPAGATES | FIXED |
| getAudioAmplitudeAtFrame | frame | same-frame:DIV/0 | FIXED |
| removeLegacyAudioMapping | index | NaN:COERCES_TO_0 | FIXED |
| createAmplitudeProperty | amplitudes | contains NaN | FIXED |
| getAudioFeatureAtFrame | currentFrame | NaN passthrough | FIXED |
| getAllMappedValuesAtFrame | currentFrame | NaN passthrough | FIXED |
| isBeatAtCurrentFrame | currentFrame | NaN passthrough | FIXED |
| updatePathAnimators | currentFrame | NaN passthrough | FIXED |
| convertAudioToKeyframes | options | NaN bypass defaults | FIXED |
| clearAudio | - | mapper not disposed | FIXED |
| createPathAnimator | - | overwrites without dispose | FIXED |
| removePathAnimator | - | deletes without dispose | FIXED |

#### Fixes Applied:
1. Added `safeFrame()` helper function for NaN-safe frame access
2. Validated fps/frameCount in extractChannelAmplitudes
3. Added frameDiff guard in getAudioAmplitudeAtFrame
4. Validated index bounds in removeLegacyAudioMapping
5. Sanitized NaN amplitudes in createAmplitudeProperty
6. Validated destructured numeric options in convertAudioToKeyframes
7. Added dispose() calls for mapper and animators in clearAudio
8. Added dispose() for existing animator in createPathAnimator
9. Added dispose() before delete in removePathAnimator

---
