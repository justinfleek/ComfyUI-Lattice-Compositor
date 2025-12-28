# Bug Registry

## Summary
- Total bugs: 184
- Critical: 1
- High: 1
- Medium: 48
- Low: 134

---

## BUG-006: CRITICAL - Sandbox Escape via Constructor Chain
- **File:** /ui/src/services/expressions/expressionEvaluator.ts
- **Lines:** 600-601
- **Type:** Security / Arbitrary Code Execution
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-006.md
- **Summary:** `new Function()` sandbox can be escaped via `[].constructor.constructor()` allowing full arbitrary code execution. Malicious project files can execute arbitrary JavaScript.

---

## BUG-001: MEDIUM - Division by Zero in mathExpressions.map()
- **File:** /ui/src/services/expressions/expressionEvaluator.ts
- **Lines:** 80-81
- **Type:** Input Validation / Division by Zero
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-001.md

---

## BUG-002: MEDIUM - Division by Zero in mathExpressions.normalize()
- **File:** /ui/src/services/expressions/expressionEvaluator.ts
- **Lines:** 84-86
- **Type:** Input Validation / Division by Zero
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-002.md

---

## BUG-003: MEDIUM - Division by Zero in timeExpressions.timeRamp()
- **File:** /ui/src/services/expressions/expressionEvaluator.ts
- **Lines:** 31-36
- **Type:** Input Validation / Division by Zero
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-003.md

---

## BUG-004: MEDIUM - Division by Zero in interpolateAtTime()
- **File:** /ui/src/services/expressions/expressionHelpers.ts
- **Lines:** 107
- **Type:** Input Validation / Division by Zero
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-004.md

---

## BUG-005: MEDIUM - Array Access on Empty Keyframes
- **File:** /ui/src/services/expressions/expressionHelpers.ts
- **Lines:** 104
- **Type:** Null/Undefined / Array Bounds
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-005.md

---

## BUG-007: LOW - Division by Zero in posterizeTime()
- **File:** /ui/src/services/expressions/audioExpressions.ts
- **Lines:** 107
- **Type:** Input Validation / Division by Zero
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-007.md
- **Summary:** `1 / framesPerSecond` without checking for zero. Returns Infinity → NaN propagates.

---

## BUG-008: LOW - Division by Zero in temporalJitter()
- **File:** /ui/src/services/expressions/jitterExpressions.ts
- **Lines:** 79
- **Type:** Input Validation / Division by Zero
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-008.md
- **Summary:** `period = 1 / frequency` without checking for zero.

---

## BUG-009: LOW - Division by Zero in elastic()
- **File:** /ui/src/services/expressions/motionExpressions.ts
- **Lines:** 171
- **Type:** Input Validation / Division by Zero
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-009.md
- **Summary:** `(t - s) * (2 * Math.PI) / period` without checking period=0.

---

## BUG-010: MEDIUM - Stack Overflow on Circular Parent Chain
- **File:** /ui/src/services/expressions/coordinateConversion.ts
- **Lines:** 135-136, 153-154
- **Type:** Infinite Recursion / Crash
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-010.md
- **Summary:** `toComp()` and `fromComp()` recursively traverse parent chain with no cycle detection. Circular parent references cause stack overflow crash.

---

## BUG-011: LOW - Silent Data Corruption on Zero Scale
- **File:** /ui/src/services/expressions/coordinateConversion.ts
- **Lines:** 185-187
- **Type:** Data Integrity / Silent Failure
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-011.md
- **Summary:** `scale[0] || 100` treats user's explicit scale=0 as falsy, silently replacing with 100. The `|| 1` guards at lines 188-190 are redundant and never trigger.

---

## BUG-012: MEDIUM - Infinite Loop with octaves=Infinity
- **File:** /ui/src/services/expressions/jitterExpressions.ts
- **Lines:** 47, 113, 125
- **Type:** Unbounded Loop / Hang
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-012.md
- **Summary:** Loops use `octaves` as bound without validation. `octaves=Infinity` causes infinite loop, hanging browser.

---

## BUG-013: LOW - Division by Zero in jitter() with Specific Parameters
- **File:** /ui/src/services/expressions/jitterExpressions.ts
- **Lines:** 54
- **Type:** Division by Zero
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-013.md
- **Summary:** `result / (1 + (octaves - 1) * amplitudeMultiplier)` - denominator is zero when `amplitudeMultiplier = -1/(octaves-1)`. E.g., octaves=2, amp=-1 → div by zero.

---

## BUG-014: MEDIUM - Missing Switch Default Returns Undefined
- **File:** /ui/src/services/expressions/loopExpressions.ts
- **Lines:** 58-89, 117-144
- **Type:** Missing Default / Type Violation
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-014.md
- **Summary:** Switch statement has no default case. Invalid `type` parameter causes function to return `undefined` instead of declared `number | number[]`.

---

## BUG-015: LOW - Type Mismatch in Continue Mode Returns String
- **File:** /ui/src/services/expressions/loopExpressions.ts
- **Lines:** 84-87, 139-142
- **Type:** Type Coercion / Data Corruption
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-015.md
- **Summary:** In 'continue' mode, if `value` is array and `velocity` is number, JavaScript coerces to string: `[100,200] + 50 = "100,20050"`.

---

## BUG-016: LOW - NaN Propagation with Negative Gravity in bounce()
- **File:** /ui/src/services/expressions/motionExpressions.ts
- **Lines:** 117, 127
- **Type:** Input Validation / NaN Propagation
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-016.md
- **Summary:** `Math.sqrt(2 * bounceHeight / gravity)` with negative gravity produces NaN via sqrt of negative number.

---

## BUG-017: MEDIUM - Special Characters Break Code Generation in textAnimator
- **File:** /ui/src/services/expressions/textAnimator.ts
- **Lines:** 93
- **Type:** String Escaping / Syntax Error
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-017.md
- **Summary:** Only double quotes escaped in string interpolation. Backslash (`\`) or newline (`\n`) in `ctx.char` causes SyntaxError when code is evaluated.

---

## BUG-018: MEDIUM - vectorClamp Silently Clamps to 0 for Missing Max Values
- **File:** /ui/src/services/expressions/vectorMath.ts
- **Lines:** 145-150
- **Type:** Silent Data Corruption / Wrong Default
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-018.md
- **Summary:** `max[i] || 0` uses 0 as default max when array is shorter than vec. `vectorClamp([5,6,7], 0, [10])` returns `[5,0,0]` instead of `[5,6,7]`.

---

## BUG-019: MEDIUM - Excessive Use of `any` Types Disables Type Safety
- **File:** /ui/src/services/expressions/types.ts
- **Lines:** 39, 42, 45, 69, 90, 129, 130
- **Type:** Type Safety / Systemic
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-019.md
- **Summary:** 7 uses of `any` type completely bypass TypeScript checking. This is the ROOT CAUSE enabling all division-by-zero, NaN propagation, and invalid input bugs. Proper branded types (PositiveNumber, NonZeroNumber, etc.) would catch these at compile time.

---

## BUG-020: MEDIUM - Division by Zero in Audio Visualizer (Zero-Length Line)
- **File:** /ui/src/services/effects/audioVisualizer.ts
- **Lines:** 127-128, 332-333
- **Type:** Input Validation / Division by Zero
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-020.md
- **Summary:** When startPoint equals endPoint, line length is 0, causing `perpX = -dy/0` and `perpY = dx/0` → NaN propagates through all drawing coordinates.

---

## BUG-021: MEDIUM - Infinite Loop with Unbounded frequencyBands/displayedSamples
- **File:** /ui/src/services/effects/audioVisualizer.ts
- **Lines:** 141, 248, 272, 360, 380, 394, 429, 440
- **Type:** Unbounded Loop / Hang
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-021.md
- **Summary:** Loop bounds use user params without validation. `frequencyBands=Infinity` or `displayedSamples=Infinity` causes infinite loop, hanging browser.

---

## BUG-022: LOW - SHG_TABLE Array Out of Bounds at radius=255
- **File:** /ui/src/services/effects/blurRenderer.ts
- **Lines:** 392-409 (table), 479, 626 (access)
- **Type:** Array Bounds / Edge Case
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-022.md
- **Summary:** SHG_TABLE only has 255 entries but radius clamps to 0-255. `SHG_TABLE[255]` returns undefined, causing incorrect shift in blur calculation (blown-out output).

---

## BUG-023: LOW - NaN Parameters Cause Undefined Lookup Table Access
- **File:** /ui/src/services/effects/blurRenderer.ts
- **Lines:** 802, 866, 918, 995, 1126, 1217
- **Type:** Input Validation / NaN Propagation
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-023.md
- **Summary:** Nullish coalescing (`??`) doesn't catch NaN. `blurriness=NaN` → `MUL_TABLE[NaN]=undefined` → black/corrupted output.

---

## BUG-024: LOW - Division by Zero at Center Pixel in Chromatic Aberration
- **File:** /ui/src/services/effects/cinematicBloom.ts
- **Lines:** 386-390
- **Type:** Division by Zero / Edge Case
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-024.md
- **Summary:** Chromatic aberration divides by distance from center. At center pixel (dist=0), `offset/dist = 0/0 = NaN` → center pixel's red channel becomes 0.

---

## BUG-025: LOW - Levels Effect NaN When inputWhite Equals inputBlack
- **File:** /ui/src/services/effects/colorRenderer.ts
- **Lines:** 273-288
- **Type:** Division by Zero / Edge Case
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-025.md
- **Summary:** Division by inputRange when inputWhite === inputBlack causes NaN for exact input value, producing black pixel artifact instead of expected threshold behavior.

---

## BUG-026: MEDIUM - Unbounded LUT Cache Memory Leak
- **File:** /ui/src/services/effects/colorRenderer.ts
- **Lines:** 1344, 1479
- **Type:** Memory Leak / Resource Management
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-026.md
- **Summary:** `lutCache` Map stores parsed LUTs with no size limit or eviction. Each 65³ LUT is ~3.3MB. Loading many LUTs causes unbounded memory growth.

---

## BUG-027: LOW - Division by Zero in Warp Bulge at Center
- **File:** /ui/src/services/effects/distortRenderer.ts
- **Lines:** 264-266
- **Type:** Division by Zero / Edge Case
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-027.md
- **Summary:** Warp bulge divides by `factor = 1 + bend * (1 - r²)`. At center pixel (r=0) with bend=-1, factor=0 causes division by zero producing NaN/Infinity.

---

## BUG-028: LOW - Division by Zero in Fractal Noise with scale=0
- **File:** /ui/src/services/effects/generateRenderer.ts
- **Lines:** 351, 394
- **Type:** Division by Zero / Missing Validation
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-028.md
- **Summary:** `scale` param used directly without `Math.max()` guard. `scale=0` causes `x/0=Infinity`, NaN propagation through noise functions, producing black output.

---

## BUG-029: LOW - Division by Zero in HDR Gamma Correction
- **File:** /ui/src/services/effects/hdrRenderer.ts
- **Lines:** 215
- **Type:** Division by Zero / Missing Validation
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-029.md
- **Summary:** `1 / params.gamma` without validation. `gamma=0` causes `Math.pow(x, Infinity)=0` for most pixels, producing black output. Documented range 0.1-3.0 not enforced.

---

## BUG-030: MEDIUM - Infinite Loop in dilateAlpha/erodeAlpha
- **File:** /ui/src/services/effects/layerStyleRenderer.ts
- **Lines:** 140, 146-156, 177, 183-193
- **Type:** Infinite Loop / Unbounded Input
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-030.md
- **Summary:** `Math.ceil(amount)` used as loop bound. `amount=Infinity` causes `for (dy = -Infinity; dy <= Infinity)` infinite loop. Triggered via style.size=Infinity with spread>0.

---

## BUG-031: MEDIUM - Multiple Infinite Loop Triggers in Matte Edge
- **File:** /ui/src/services/effects/matteEdge.ts
- **Lines:** 64, 92, 131, 170, 475
- **Type:** Infinite Loop / Unbounded Input
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-031.md
- **Summary:** Multiple params trigger infinite loops: `iterations=Infinity` (line 64), `amount=Infinity` (erode/dilate), `softness=Infinity` (blur), `radius=Infinity` (distance field). Same pattern as BUG-030.

---

## BUG-032: LOW - Division by Zero in Depth Matte with Equal Near/Far
- **File:** /ui/src/services/effects/perspectiveRenderer.ts
- **Lines:** 170, 195, 197, 200, 207
- **Type:** Division by Zero / Missing Validation
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-032.md
- **Summary:** `applyDepthMatte` divides by `range = farDepth - nearDepth` without zero check. When equal, `0/0 = NaN` → alpha becomes 0 (transparent). Contrast: `calculateFogFactor` at line 53 handles this.

---

## BUG-033: MEDIUM - Infinite Loop in Glitch/VHS with Infinite Params
- **File:** /ui/src/services/effects/stylizeRenderer.ts
- **Lines:** 193, 320
- **Type:** Infinite Loop / Unbounded Input
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-033.md
- **Summary:** `numBlocks = Math.floor(glitchAmount * 3)` and `numLines = Math.floor(tracking * 20)` used as loop bounds. `Infinity` input causes infinite loop.

---

## BUG-034: MEDIUM - Division by Zero in Audio Keyframe Conversion
- **File:** /ui/src/stores/actions/audioActions.ts
- **Lines:** 529
- **Type:** Division by Zero / Data Corruption
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-034.md
- **Summary:** `Math.floor(sampleRate / fps)` with fps=0 produces Infinity. Frames 1+ get amplitude 0 (all audio data concentrated in frame 0).

---

## BUG-035: MEDIUM - Cache Key Collision with NaN/Infinity Frame Numbers
- **File:** /ui/src/services/frameCache.ts (also /ui/src/stores/actions/cacheActions.ts)
- **Lines:** 246-248, 254, 318, 401, 478, 485
- **Type:** Input Validation / Data Corruption
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-035.md
- **Summary:** `getCacheKey(frame, compositionId)` has no validation. `frame = NaN` → key = `"comp:NaN"` → all NaN frames collide to same key, each overwrite silently corrupts previous data. Same for Infinity.

---

## BUG-036: LOW - NaN Keyframe Accumulation Due to Equality Check Failure
- **File:** /ui/src/stores/actions/cameraActions.ts
- **Lines:** 207, 213, 230
- **Type:** Input Validation / Data Corruption
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-036.md
- **Summary:** `k.frame === keyframe.frame` fails for NaN (since `NaN === NaN` is false). NaN keyframes never match, always accumulate, can't be removed. Sort with NaN produces undefined ordering.

---

## BUG-037: MEDIUM - Infinite Loop in Pre-Cache with preCacheWindow = Infinity
- **File:** /ui/src/services/frameCache.ts
- **Lines:** 473-490
- **Type:** Unbounded Loop / Hang
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-037.md
- **Summary:** `for (let i = 1; i <= window; i++)` where `window = config.preCacheWindow`. `preCacheWindow = Infinity` causes infinite loop, hanging browser.

---

## BUG-038: MEDIUM - NaN ImageData Dimensions Permanently Corrupt Memory Counter
- **File:** /ui/src/services/frameCache.ts
- **Lines:** 334, 364
- **Type:** Input Validation / State Corruption
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-038.md
- **Summary:** `size = width * height * 4` with NaN dimensions → `currentMemory += NaN` → currentMemory = NaN permanently. All memory checks fail, cache grows unbounded.

---

## BUG-039: LOW - createComposition() Does Not Validate fps
- **File:** /ui/src/stores/actions/compositionActions.ts
- **Lines:** 64, 70
- **Type:** Input Validation / Inconsistency
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-039.md
- **Summary:** `createComposition()` uses fps directly without validation, while `updateCompositionSettings()` validates. `fps=0` causes `duration = Infinity`.

---

## BUG-040: LOW - NaN Index Bypasses Bounds Check in navigateToBreadcrumb
- **File:** /ui/src/stores/actions/compositionActions.ts
- **Lines:** 311-322
- **Type:** Input Validation / NaN Handling
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-040.md
- **Summary:** `if (index < 0 || index >= length)` doesn't catch NaN. `slice(0, NaN)` returns empty array, corrupting breadcrumbs.

---

## BUG-041: LOW - NaN/Infinity Config Values Corrupt Depthflow Rendering
- **File:** /ui/src/stores/actions/depthflowActions.ts
- **Lines:** 91
- **Type:** Input Validation / Data Corruption
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-041.md
- **Summary:** `Object.assign(data.config, updates)` stores NaN/Infinity config values without validation. Later, renderer uses these for canvas transforms (`ctx.scale(NaN, NaN)`) producing corrupted/blank output.

---

## BUG-042: LOW - NaN Index Bypasses Bounds Check in reorderEffects
- **File:** /ui/src/stores/actions/effectActions.ts
- **Lines:** 150-154
- **Type:** Input Validation / NaN Handling
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-042.md
- **Summary:** `if (fromIndex < 0 || fromIndex >= length)` doesn't catch NaN. `splice(NaN, 1)` treats NaN as 0, moving wrong effect.

---

## BUG-043: LOW - NaN/Infinity Parameter Values Stored Without Validation
- **File:** /ui/src/stores/actions/effectActions.ts
- **Lines:** 70, 78
- **Type:** Input Validation / Data Corruption
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-043.md
- **Summary:** `updateEffectParameter()` accepts `value: any` without validation. NaN/Infinity stored in effect parameters, later corrupts renderers (triggers BUG-023, BUG-033).

---

## BUG-044: LOW - NaN Frame Bypasses Keyframe Equality Check
- **File:** /ui/src/stores/actions/keyframeActions.ts
- **Lines:** 128, 134
- **Type:** Input Validation / NaN Handling
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-044.md
- **Summary:** `k.frame === frame` fails for NaN (NaN === NaN is false). NaN keyframes accumulate indefinitely. Sort with NaN produces undefined order.

---

## BUG-045: LOW - Division by Zero in insertKeyframeOnPath
- **File:** /ui/src/stores/actions/keyframeActions.ts
- **Lines:** 958
- **Type:** Input Validation / Division by Zero
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-045.md
- **Summary:** `t = (frame - before.frame) / (after.frame - before.frame)` divides by zero when keyframes have same frame number.

---

## BUG-046: LOW - fps=0 Produces Infinity in Velocity Calculations
- **File:** /ui/src/stores/actions/keyframeActions.ts
- **Lines:** 1312-1314
- **Type:** Input Validation / Division by Zero
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-046.md
- **Summary:** `store.fps ?? 16` doesn't catch fps=0. Division by zero corrupts bezier handle values.

---

## BUG-047: LOW - Unchecked newIndex in moveLayer
- **File:** /ui/src/stores/actions/layerActions.ts
- **Lines:** 595
- **Type:** Input Validation / NaN Handling
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-047.md
- **Summary:** `splice(newIndex, 0, layer)` without validation. NaN treated as 0, inserts at wrong position.

---

## BUG-048: LOW - Division by Zero in samplePathPoints
- **File:** /ui/src/stores/actions/layerActions.ts
- **Lines:** 1339
- **Type:** Input Validation / Division by Zero
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-048.md
- **Summary:** `step = totalLength / (count - 1)` - count=1 causes division by zero, step=Infinity.

---

## BUG-049: LOW - Division by Zero in applyExponentialScale
- **File:** /ui/src/stores/actions/layerActions.ts
- **Lines:** 1597
- **Type:** Input Validation / Division by Zero
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-049.md
- **Summary:** `ratio = endScale / startScale` - startScale=0 causes division by zero, ratio=Infinity, keyframes contain NaN.

---

## BUG-050: LOW - NaN Frame Bypasses Marker Equality Check
- **File:** /ui/src/stores/actions/markerActions.ts
- **Lines:** 62, 105, 188, 280
- **Type:** Input Validation / NaN Handling
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-050.md
- **Summary:** `m.frame === frame` fails for NaN (NaN === NaN is false). NaN markers accumulate and cannot be found/removed. Same pattern as BUG-044.

---

## BUG-051: LOW - NaN Frame Not Caught by Math.max/min Clamping
- **File:** /ui/src/stores/actions/playbackActions.ts
- **Lines:** 66, 133
- **Type:** Input Validation / NaN Handling
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-051.md
- **Summary:** `Math.max(0, Math.min(frame, ...))` doesn't catch NaN. NaN propagates through and corrupts `comp.currentFrame`, breaking timeline.

---

## BUG-052: MEDIUM - Infinite Loop in bakePhysicsToKeyframes with sampleInterval=0
- **File:** /ui/src/stores/actions/physicsActions.ts
- **Lines:** 464
- **Type:** Unbounded Loop / Hang
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-052.md
- **Summary:** `for (frame += sampleInterval)` with sampleInterval=0 causes infinite loop. Frame never increments, loop runs forever, browser hangs.

---

## BUG-053: LOW - NaN Geometry Cache Key Collision
- **File:** /ui/src/engine/core/ResourceManager.ts
- **Lines:** 276, 295, 314-318
- **Type:** Input Validation / Cache Corruption
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-053.md
- **Summary:** NaN dimensions create cache key `plane:NaN:NaN`. All NaN geometry requests return same degenerate cached geometry, causing invisible meshes.

---

## BUG-054: LOW - Animation Continues After Camera Disposal (Memory Leak)
- **File:** /ui/src/engine/core/CameraController.ts
- **Lines:** 821-834, 978-999
- **Type:** Resource Leak / Missing Cleanup
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-054.md
- **Summary:** `setViewPreset()` and `loadBookmark()` animations use requestAnimationFrame with no cancellation mechanism. No dispose() method exists. Animations continue on destroyed camera, leaking memory.

---

## BUG-055: LOW - Grid Division by Zero Causes Infinite Step
- **File:** /ui/src/engine/core/SceneManager.ts
- **Lines:** 757, 783-784, 796-797
- **Type:** Input Validation / Division by Zero
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-055.md
- **Summary:** `updateCompositionGrid(0)` causes `step = w/0 = Infinity`. Loop creates lines at NaN positions. Grid becomes invisible/incorrect.

---

## BUG-056: LOW - Circular Easing Functions Return NaN for Out-of-Range Input
- **File:** /ui/src/engine/animation/EasingFunctions.ts
- **Lines:** 99, 101, 103-105
- **Type:** Input Validation / NaN Production
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-056.md
- **Summary:** `easeInCirc`, `easeOutCirc`, `easeInOutCirc` use `Math.sqrt(1 - t²)`. When t > 1 or t < 0, sqrt argument becomes negative → NaN. No input clamping.

---

## BUG-057: LOW - Division by Zero in Flocking Perception Angle Check
- **File:** /ui/src/engine/particles/ParticleFlockingSystem.ts
- **Lines:** 121-123, 126
- **Type:** Input Validation / Division by Zero
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-057.md
- **Summary:** When two particles occupy exact same position (dist=0), perception angle calculation divides by zero. Direction vectors become NaN, dot product becomes NaN, check at line 129 fails (NaN < X is false), particle proceeds to flocking calculations where normalize(0,0,0) produces NaN steering vector.

---

## BUG-058: MEDIUM - Drag Force Has Wrong Sign (Accelerates Instead of Decelerates)
- **File:** /ui/src/engine/particles/ParticleForceCalculator.ts
- **Lines:** 101-108
- **Type:** Logic Error / Physics Bug
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-058.md
- **Summary:** Line 106 `force.set(-vx,-vy,-vz).normalize().multiplyScalar(-dragMag * strength)` has double negation. The `-dragMag` negates the already-opposite direction, causing drag to accelerate particles instead of slowing them.

---

## BUG-059: LOW - Infinite Loop When maxParticles is Infinity
- **File:** /ui/src/engine/particles/SpatialHashGrid.ts
- **Lines:** 59
- **Type:** Infinite Loop / Denial of Service
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-059.md
- **Summary:** Line 59 `for (i < maxParticles)` loops forever if maxParticles=Infinity. Secondary: setCellSize(NaN) at line 187 allows cellSize to become NaN since Math.max(1,NaN)=NaN.

---

## BUG-060: LOW - TypeError When SubEmitter overrides is Undefined
- **File:** /ui/src/engine/particles/ParticleSubEmitter.ts
- **Lines:** 158-159
- **Type:** Null/Undefined Access
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-060.md
- **Summary:** Line 158-159 accesses `subEmitter.overrides.initialSpeed` without checking if overrides is defined. If SubEmitterConfig has undefined overrides, throws TypeError.

---

## BUG-061: LOW - Infinite Loop When maxParticles is Infinity (ConnectionSystem)
- **File:** /ui/src/engine/particles/ParticleConnectionSystem.ts
- **Lines:** 87
- **Type:** Infinite Loop / Denial of Service
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-061.md
- **Summary:** Same pattern as BUG-059. Line 87 `for (i < maxParticles)` loops forever if maxParticles=Infinity.

---

## BUG-062: LOW - Infinite Loop / RangeError from Invalid maxParticles (ParticleTrailSystem)
- **File:** /ui/src/engine/particles/ParticleTrailSystem.ts
- **Lines:** 47-55, 68-72, 116
- **Type:** Infinite Loop / RangeError
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-062.md
- **Summary:** Same pattern as BUG-059, BUG-061. Constructor accepts maxParticles without validation. If Infinity, line 116 loops forever. If negative, Float32Array constructor throws RangeError at lines 68, 72, 76, 77.

---

## BUG-063: LOW - Division by Zero in getModulation() When binding.max === binding.min
- **File:** /ui/src/engine/particles/ParticleAudioReactive.ts
- **Lines:** 156-157
- **Type:** Input Validation / Division by Zero
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-063.md
- **Summary:** getModulation() divides by (binding.max - binding.min) without clamping. When max===min, returns ±Infinity. Note: applyModulation() at line 106 handles this correctly with Math.max/min clamps.

---

## BUG-064: LOW - Infinite Loop When maxParticles is Infinity (ParticleCollisionSystem)
- **File:** /ui/src/engine/particles/ParticleCollisionSystem.ts
- **Lines:** 101, 255
- **Type:** Infinite Loop / Denial of Service
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-064.md
- **Summary:** Same pattern as BUG-059, BUG-061, BUG-062. Two loops bounded by maxParticles in applyBoundaryCollisions and applyParticleCollisions. If maxParticles=Infinity, both loop forever.

---

## BUG-065: LOW - Division by Zero When Both Particle Masses Are Zero
- **File:** /ui/src/engine/particles/ParticleCollisionSystem.ts
- **Lines:** 306-307
- **Type:** Input Validation / Division by Zero
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-065.md
- **Summary:** Impulse calculation `-(1 + bounciness) * dvn / totalMass` divides by totalMass. If both particles have mass=0, totalMass=0, impulse=±Infinity, velocities become NaN.

---

## BUG-066: LOW - Infinite Loop in Async Readback (ParticleGPUPhysics) - SYSTEMIC-006
- **File:** /ui/src/engine/particles/ParticleGPUPhysics.ts
- **Line:** 456
- **Type:** Infinite Loop / Denial of Service
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-066.md
- **Summary:** Same pattern as SYSTEMIC-006. Async WebGPU readback callback iterates `for (i < maxParticles)`. If maxParticles=Infinity, loop never terminates.

---

## BUG-067: LOW - Division by Zero in simulateToFrame fps Parameter - SYSTEMIC-003
- **File:** /ui/src/engine/particles/GPUParticleSystem.ts
- **Line:** 1502
- **Type:** Input Validation / Division by Zero
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-067.md
- **Summary:** simulateToFrame() calculates `deltaTime = 1 / fps` without validating fps. If fps=0 passed explicitly, deltaTime=Infinity corrupts simulation.

---

## BUG-068: LOW - Infinite Loop When burstCount is Infinity
- **File:** /ui/src/engine/particles/GPUParticleSystem.ts
- **Lines:** 1281, 1288
- **Type:** Infinite Loop / Denial of Service
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-068.md
- **Summary:** triggerBurst() iterates `for (i < burstCount)`. If burstCount=Infinity, loop never terminates.

---

## BUG-069: LOW - Infinite Loop When warmupFrames is Infinity
- **File:** /ui/src/engine/particles/GPUParticleSystem.ts
- **Line:** 1536
- **Type:** Infinite Loop / Denial of Service
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-069.md
- **Summary:** simulateToFrame() warmup loop iterates `for (w < warmupFrames)`. If warmupFrames=Infinity, loop never terminates.

---

## BUG-070: LOW - Division by Zero When compositionFPS is 0 - SYSTEMIC-003
- **File:** /ui/src/engine/layers/VideoLayer.ts
- **Lines:** 556-558 (setFPS), 492 (division)
- **Type:** Input Validation / Division by Zero
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-070.md
- **Summary:** setFPS() accepts 0 without validation. calculateVideoTime() divides by compositionFPS at line 492.

---

## BUG-071: LOW - Division by Zero in FPS Detection When Few Frames - SYSTEMIC-003
- **File:** /ui/src/engine/layers/VideoLayer.ts
- **Line:** 983
- **Type:** Division by Zero
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-071.md
- **Summary:** detectVideoFps() divides by trimmed.length which can be 0 if only 2 frames captured before 0.5s timeout.

---

## BUG-072: LOW - NaN Propagation When autoAdvanceSpeed is Infinity - SYSTEMIC-005
- **File:** /ui/src/engine/layers/CameraLayer.ts
- **Lines:** 508, 522
- **Type:** NaN Propagation
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-072.md
- **Summary:** `(frame * Infinity) % 1 = NaN`, then Math.max/min doesn't catch NaN, corrupting path following.

---

## BUG-073: LOW - Division by Zero When fontSize is 0 - SYSTEMIC-003
- **File:** /ui/src/engine/layers/TextLayer.ts
- **Line:** 359
- **Type:** Division by Zero
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-073.md
- **Summary:** `strokeWidth / fontSize` divides by zero when fontSize=0 (nullish coalescing doesn't catch 0).

---

## BUG-074: LOW - Division by Zero in ModelLayer Animation - SYSTEMIC-003
- **File:** /ui/src/engine/layers/ModelLayer.ts
- **Line:** 783
- **Type:** Division by Zero
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-074.md
- **Summary:** `1 / this.compositionFps` divides by zero when fps=0, producing Infinity animation delta.

---

## BUG-075: LOW - Division by Zero in ProceduralMatteLayer Animation - SYSTEMIC-003
- **File:** /ui/src/engine/layers/ProceduralMatteLayer.ts
- **Line:** 186
- **Type:** Division by Zero
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-075.md
- **Summary:** `frame * speed / this.compositionFps` divides by zero when fps=0, corrupting animation time.

---

## BUG-076: LOW - Infinite Loops with Infinity Tile/Slat Parameters - SYSTEMIC-006
- **File:** /ui/src/engine/layers/ProceduralMatteLayer.ts
- **Lines:** 399-405, 532
- **Type:** Infinite Loop
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-076.md
- **Summary:** tilesX/tilesY/slats=Infinity causes infinite for loops in checkerboard/venetian patterns.

---

## BUG-077: LOW - Division by Zero in Levels (inputRange=0) - SYSTEMIC-003
- **File:** /ui/src/engine/layers/ProceduralMatteLayer.ts
- **Lines:** 644, 651
- **Type:** Division by Zero
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-077.md
- **Summary:** When inputWhite===inputBlack, inputRange=0 causes division by zero in applyLevels().

---

## BUG-078: LOW - NaN Copies Bypasses Comparison Guard - SYSTEMIC-005
- **File:** /ui/src/engine/layers/ShapeLayer.ts
- **Lines:** 495, 598
- **Type:** NaN Bypass
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-078.md
- **Summary:** `if (copies <= 1)` guard is bypassed when copies is NaN (NaN <= 1 is false).

---

## BUG-079: MEDIUM - setCompositionFps Lacks Validation (SYSTEMIC-003 ROOT CAUSE)
- **File:** /ui/src/engine/layers/BaseLayer.ts
- **Lines:** 1558-1559
- **Type:** Input Validation
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-079.md
- **Summary:** ROOT CAUSE of all SYSTEMIC-003 bugs. Accepts fps=0, NaN, Infinity without validation.

---

## BUG-080: LOW - Infinite Loop in computeMotionPath - SYSTEMIC-006
- **File:** /ui/src/engine/layers/BaseLayer.ts
- **Line:** 1589
- **Type:** Infinite Loop
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-080.md
- **Summary:** `for (frame <= end)` becomes infinite when outPoint is Infinity.

---

## BUG-081: LOW - Math.log NaN in kelvinToRGB with Invalid Temperature
- **File:** /ui/src/engine/layers/LightLayer.ts
- **Lines:** 195, 209
- **Type:** NaN Propagation
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-081.md
- **Summary:** Math.log(negative) produces NaN when colorTemperature is <= 0.

---

## BUG-082: LOW - NaN Opacity Bypasses Math.max/min Clamp - SYSTEMIC-005
- **File:** /ui/src/engine/layers/BaseLayer.ts
- **Lines:** 481-482
- **Type:** NaN Bypass
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-082.md
- **Summary:** Math.max/min don't catch NaN in applyOpacity(), corrupts material.opacity.

---

## BUG-083: LOW - NaN Velocity Bypasses Motion Blur Threshold - SYSTEMIC-005
- **File:** /ui/src/engine/layers/BaseLayer.ts
- **Lines:** 1231-1232
- **Type:** NaN Bypass
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-083.md
- **Summary:** NaN < 0.5 is false, so NaN velocity bypasses threshold check.

---

## BUG-084: MEDIUM - NaN Transform Values Propagate to Three.js - Defense Gap
- **File:** /ui/src/engine/layers/BaseLayer.ts
- **Lines:** 382-397
- **Type:** NaN Propagation
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-084.md
- **Summary:** NaN from evaluator/expressions propagates to Three.js position/rotation/scale, corrupting rendering.

---

## BUG-085: LOW - ParticleLayer.setFPS() Lacks Validation - SYSTEMIC-003
- **File:** /ui/src/engine/layers/ParticleLayer.ts
- **Lines:** 747-748
- **Type:** Input Validation
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-085.md
- **Summary:** setFPS() accepts 0/NaN/Infinity without validation. fps=0 propagates to GPUParticleSystem.simulateToFrame() causing division by zero.

---

## BUG-086: LOW - ParticleLayer.preCacheFrames() Infinite Loop - SYSTEMIC-006
- **File:** /ui/src/engine/layers/ParticleLayer.ts
- **Line:** 917
- **Type:** Infinite Loop
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-086.md
- **Summary:** `for (let frame = startFrame; frame <= endFrame; frame++)` infinite loop when endFrame=Infinity.

---

## BUG-087: LOW - ParticleLayer.createParticleGrid() Division/Infinite Loop - SYSTEMIC-006
- **File:** /ui/src/engine/layers/ParticleLayer.ts
- **Lines:** 1673-1674
- **Type:** Division by Zero / Infinite Loop
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-087.md
- **Summary:** `Math.ceil(compWidth / gridSize)` returns Infinity when gridSize=0, causing infinite loop in grid creation.

---

## BUG-088: LOW - NestedCompLayer.setFPS() Lacks Validation - SYSTEMIC-003
- **File:** /ui/src/engine/layers/NestedCompLayer.ts
- **Lines:** 149-151
- **Type:** Input Validation
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-088.md
- **Summary:** setFPS() accepts 0/NaN without validation. fps=0 causes division by zero in calculateNestedFrame() when overrideFrameRate is enabled.

---

## BUG-089: LOW - NestedCompLayer NaN Frame Propagation - SYSTEMIC-005
- **File:** /ui/src/engine/layers/NestedCompLayer.ts
- **Lines:** 256-258
- **Type:** NaN Bypass
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-089.md
- **Summary:** Math.max/min don't catch NaN. If nestedFrame is NaN (from NaN fps), clampedFrame becomes NaN.

---

<!-- APPEND NEW BUGS BELOW THIS LINE -->

## BUG-090: MEDIUM - BaseLayer.setCompositionFps() No Validation - SYSTEMIC-003
- **File:** /ui/src/engine/layers/BaseLayer.ts
- **Lines:** 1558-1560
- **Type:** Input Validation / Division by Zero
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-090.md
- **Summary:** setCompositionFps() accepts 0/NaN/Infinity without validation. fps value used in effect processing and mask rendering.

---

## BUG-091: MEDIUM - BaseLayer.computeMotionPath() Infinite Loop - SYSTEMIC-006
- **File:** /ui/src/engine/layers/BaseLayer.ts
- **Lines:** 1582-1597
- **Type:** Infinite Loop
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-091.md
- **Summary:** `for (frame = start; frame <= end; frame++)` infinite loop when endFrame=Infinity.

---

## BUG-092: LOW - BaseLayer.applyOpacity() NaN Propagation - SYSTEMIC-005
- **File:** /ui/src/engine/layers/BaseLayer.ts
- **Lines:** 481-494
- **Type:** NaN Bypass
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-092.md
- **Summary:** Math.max/min don't catch NaN. opacity=NaN propagates to material.opacity as NaN.

---

## BUG-093: MEDIUM - BaseLayer.computeMotionPath() Memory Exhaustion
- **File:** /ui/src/engine/layers/BaseLayer.ts
- **Lines:** 1586-1593
- **Type:** Resource Exhaustion
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-093.md
- **Summary:** Creates one Vector3 per frame. Large frame ranges (1M+ frames) cause memory exhaustion.

---

## BUG-094: LOW - BaseLayer.dispose() Memory Leaks
- **File:** /ui/src/engine/layers/BaseLayer.ts
- **Lines:** 1896-1948
- **Type:** Memory Leak
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-094.md
- **Summary:** effectSourceCanvas and motionBlurProcessor not disposed, causing memory leaks.

---

## BUG-095: MEDIUM - BaseLayer.setParent() Circular Parenting Not Prevented
- **File:** /ui/src/engine/layers/BaseLayer.ts
- **Lines:** 1519-1531
- **Type:** Circular Reference
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-095.md
- **Summary:** No check for circular parenting. A->B->A creates infinite recursion potential.

---

<!-- APPEND NEW BUGS BELOW THIS LINE -->

## BUG-096: LOW - ParticleLayer.setCacheInterval() No Validation - SYSTEMIC-003
- **File:** /ui/src/engine/layers/ParticleLayer.ts
- **Lines:** 934-936
- **Type:** Input Validation
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-096.md
- **Summary:** setCacheInterval() accepts 0/NaN/negative without validation. Delegates to GPUParticleSystem but wrappers must validate.

---

<!-- APPEND NEW BUGS BELOW THIS LINE -->

## BUG-097: MEDIUM - GPUParticleSystem.simulateToFrame() Division by Zero - SYSTEMIC-003
- **File:** /ui/src/engine/particles/GPUParticleSystem.ts
- **Lines:** 1500-1502
- **Type:** Division by Zero
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-097.md
- **Summary:** `deltaTime = 1 / fps` without validation. fps=0 causes Infinity, fps=NaN propagates.

---

## BUG-098: MEDIUM - GPUParticleSystem Constructor maxParticles Not Validated
- **File:** /ui/src/engine/particles/GPUParticleSystem.ts
- **Lines:** 367-378
- **Type:** Input Validation
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-098.md
- **Summary:** maxParticles=NaN/Infinity causes Float32Array constructor to throw RangeError.

---

## BUG-099: LOW - GPUParticleSystem.initialize() Double Call Not Prevented
- **File:** /ui/src/engine/particles/GPUParticleSystem.ts
- **Lines:** 417-444
- **Type:** Memory Leak
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-099.md
- **Summary:** No guard against double initialization. Creates duplicate resources, leaks memory.

---

## BUG-100: LOW - GPUParticleSystem.dispose() Incomplete Cleanup
- **File:** /ui/src/engine/particles/GPUParticleSystem.ts
- **Lines:** 1659-1698
- **Type:** Memory Leak
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-100.md
- **Summary:** spatialHash, flockingSystem, collisionSystem, subEmitterSystem, modulationSystem not disposed.

---

## BUG-101: MEDIUM - LatticeEngine.validateConfig() NaN Bypass
- **File:** /ui/src/engine/LatticeEngine.ts
- **Lines:** 183-195
- **Type:** Input Validation / NaN Bypass
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-101.md
- **Summary:** NaN width/height bypasses validation because `NaN <= 0` is false. Propagates to renderer, camera, scene.

---

## BUG-102: MEDIUM - LatticeEngine.setCompositionFPS() No Validation
- **File:** /ui/src/engine/LatticeEngine.ts
- **Lines:** 399-401
- **Type:** Input Validation / Division by Zero
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-102.md
- **Summary:** fps passed to layers without validation. fps=0 causes division by zero downstream.

---

## BUG-103: MEDIUM - LatticeEngine.resize() NaN Bypass
- **File:** /ui/src/engine/LatticeEngine.ts
- **Lines:** 707-738
- **Type:** Input Validation / NaN Bypass
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-103.md
- **Summary:** NaN dimensions bypass `<= 0` check, propagate to renderer, camera, spline layers.

---

## BUG-104: MEDIUM - LatticeEngine.setViewportTransform() No Validation
- **File:** /ui/src/engine/LatticeEngine.ts
- **Lines:** 1023-1034
- **Type:** Input Validation / Array Bounds
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-104.md
- **Summary:** No array length check. Accesses transform[0,4,5] directly. scale=0 causes division by zero in camera.

---

## BUG-105: MEDIUM - LatticeEngine.setResolution() NaN Bypass
- **File:** /ui/src/engine/LatticeEngine.ts
- **Lines:** 769-786
- **Type:** Input Validation / NaN Bypass
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-105.md
- **Summary:** Identical to BUG-103 - NaN bypasses validation check.

---

## BUG-106: LOW - LatticeEngine.fitCompositionToViewport() No Padding Validation
- **File:** /ui/src/engine/LatticeEngine.ts
- **Lines:** 827-830
- **Type:** Input Validation
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-106.md
- **Summary:** Negative/NaN/large padding passed directly to camera fit calculations.

---

## BUG-107: LOW - LatticeEngine.captureFrameAsBlob() Quality No Validation
- **File:** /ui/src/engine/LatticeEngine.ts
- **Lines:** 1439-1455
- **Type:** Input Validation
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-107.md
- **Summary:** Quality parameter (0-1) not validated. Out-of-range values have browser-dependent behavior.

---

## BUG-108: LOW - SplineLayer.getPointAt/getTangentAt NaN Bypass
- **File:** /ui/src/engine/layers/SplineLayer.ts
- **Lines:** 610-621
- **Type:** Input Validation / NaN Bypass
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-108.md
- **Summary:** Math.min/max don't clamp NaN. NaN propagates to curve calculations causing undefined behavior.

---

## BUG-109: LOW - SplineLayer.setStrokeWidth() No Validation
- **File:** /ui/src/engine/layers/SplineLayer.ts
- **Lines:** 670-676
- **Type:** Input Validation
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-109.md
- **Summary:** Negative, NaN, Infinity width passed directly to LineMaterial.

---

## BUG-110: LOW - SplineLayer.setResolution() No Validation
- **File:** /ui/src/engine/layers/SplineLayer.ts
- **Lines:** 695-700
- **Type:** Input Validation
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-110.md
- **Summary:** NaN, 0, negative dimensions corrupt LineMaterial resolution calculations.

---

## BUG-111: LOW - SplineLayer Trim Properties No Range Validation
- **File:** /ui/src/engine/layers/SplineLayer.ts
- **Lines:** 795-816
- **Type:** Input Validation
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-111.md
- **Summary:** Trim start/end (0-100%) and offset accept NaN, negative, >100 values.

---

## BUG-112: MEDIUM - TextLayer.setFontSize() No Validation
- **File:** /ui/src/engine/layers/TextLayer.ts
- **Lines:** 752-770
- **Type:** Input Validation / Division by Zero
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-112.md
- **Summary:** 0/NaN/Infinity fontSize breaks rendering and causes division by zero in setStroke().

---

## BUG-113: MEDIUM - TextLayer.setStroke() Division by fontSize
- **File:** /ui/src/engine/layers/TextLayer.ts
- **Lines:** 810-829
- **Type:** Division by Zero
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-113.md
- **Summary:** `width / this.textData.fontSize` without guard. If fontSize=0, produces Infinity.

---

## BUG-114: LOW - TextLayer.setPathOffset() No Validation
- **File:** /ui/src/engine/layers/TextLayer.ts
- **Lines:** 865-872
- **Type:** Input Validation
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-114.md
- **Summary:** Path offset (0-100%) accepts NaN, negative, >100 causing text placement issues.

---

## BUG-115: LOW - TextLayer.applyOpacity() NaN Bypass
- **File:** /ui/src/engine/layers/TextLayer.ts
- **Lines:** 1374-1386
- **Type:** Input Validation / NaN Bypass
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-115.md
- **Summary:** Math.max/min don't clamp NaN. NaN opacity passed to Troika fillOpacity.

---

## BUG-116: MEDIUM - VideoLayer.setFPS() No Validation - Division by Zero
- **File:** /ui/src/engine/layers/VideoLayer.ts
- **Lines:** 556-558, 492
- **Type:** Division by Zero
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-116.md
- **Summary:** fps=0 causes division by zero in calculateVideoTime(). SYSTEMIC-003 pattern.

---

## BUG-117: LOW - VideoLayer.setSpeed() No Validation
- **File:** /ui/src/engine/layers/VideoLayer.ts
- **Lines:** 599-604
- **Type:** Input Validation
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-117.md
- **Summary:** 0/NaN/negative/Infinity passed to HTMLVideoElement.playbackRate.

---

## BUG-118: LOW - VideoLayer.setAudioLevel() NaN Bypass
- **File:** /ui/src/engine/layers/VideoLayer.ts
- **Lines:** 532-537
- **Type:** Input Validation / NaN Bypass
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-118.md
- **Summary:** NaN passes through Math.min/max to videoElement.volume.

---

## BUG-119: LOW - VideoLayer.setStartTime() No Validation
- **File:** /ui/src/engine/layers/VideoLayer.ts
- **Lines:** 606-608
- **Type:** Input Validation
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-119.md
- **Summary:** Negative/NaN/Infinity start time breaks video time calculations.

---

## BUG-120: MEDIUM - NestedCompLayer.setFPS() No Validation - Division by Zero
- **File:** /ui/src/engine/layers/NestedCompLayer.ts
- **Lines:** 149-151, 229
- **Type:** Division by Zero
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-120.md
- **Summary:** parentFPS=0 causes division by zero in calculateNestedFrame(). SYSTEMIC-003 pattern.

---

## BUG-121: LOW - ImageLayer.setDimensions() No Validation - Division by Zero
- **File:** /ui/src/engine/layers/ImageLayer.ts
- **Lines:** 257-261, 198
- **Type:** Division by Zero
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-121.md
- **Summary:** height=0 causes division by zero calculating aspect ratio in updateMeshSize().

---

## BUG-122: LOW - AudioLayer.getAudioTimeForFrame() fps=0 Division by Zero
- **File:** /ui/src/engine/layers/AudioLayer.ts
- **Lines:** 182-186
- **Type:** Division by Zero
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-122.md
- **Summary:** `frame / fps` divides by zero when fps=0, producing Infinity. SYSTEMIC-003 pattern.

---

## BUG-123: LOW - AudioLayer.updateGain() NaN Bypass
- **File:** /ui/src/engine/layers/AudioLayer.ts
- **Lines:** 323-336
- **Type:** NaN Bypass
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-123.md
- **Summary:** Math.min/max don't clamp NaN. NaN passes to WebAudio gainNode. SYSTEMIC-005 pattern.

---

## BUG-124: LOW - AudioLayer.updatePan() NaN Bypass
- **File:** /ui/src/engine/layers/AudioLayer.ts
- **Lines:** 341-351
- **Type:** NaN Bypass
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-124.md
- **Summary:** Math.min/max don't clamp NaN. NaN passes to WebAudio panNode. SYSTEMIC-005 pattern.

---

## BUG-125: LOW - ShapeLayer.setSize() No Validation
- **File:** /ui/src/engine/layers/ShapeLayer.ts
- **Lines:** 193-213
- **Type:** Input Validation
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-125.md
- **Summary:** 0/negative/NaN/Infinity dimensions cause OffscreenCanvas constructor to throw.

---

## BUG-126: LOW - ShapeLayer.removeContent() NaN Index Bypass
- **File:** /ui/src/engine/layers/ShapeLayer.ts
- **Lines:** 233-236
- **Type:** NaN Bypass
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-126.md
- **Summary:** `splice(NaN, 1)` treats NaN as 0, removes first element instead of intended.

---

## BUG-127: LOW - SolidLayer.setDimensions() No Validation
- **File:** /ui/src/engine/layers/SolidLayer.ts
- **Lines:** 177-189
- **Type:** Input Validation
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-127.md
- **Summary:** 0/negative/NaN dimensions create degenerate PlaneGeometry.

---

## BUG-128: LOW - SolidLayer.setShadowOpacity() NaN Bypass
- **File:** /ui/src/engine/layers/SolidLayer.ts
- **Lines:** 211-217
- **Type:** NaN Bypass
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-128.md
- **Summary:** Math.min/max don't clamp NaN. NaN passes to material.opacity. SYSTEMIC-005.

---

## BUG-129: LOW - ControlLayer.setIndicatorSize() No Validation
- **File:** /ui/src/engine/layers/ControlLayer.ts
- **Lines:** 115-126
- **Type:** Input Validation
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-129.md
- **Summary:** 0/NaN/Infinity size creates degenerate indicator geometry.

---

## BUG-130: LOW - PathLayer.getPointAt/getTangentAt NaN Bypass
- **File:** /ui/src/engine/layers/PathLayer.ts
- **Lines:** 233-236, 241-244
- **Type:** NaN Bypass
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-130.md
- **Summary:** Math.min/max don't clamp NaN. NaN passes to curve calculation. SYSTEMIC-005.

---

## BUG-131: LOW - PathLayer.setResolution() No Validation
- **File:** /ui/src/engine/layers/PathLayer.ts
- **Lines:** 425-430
- **Type:** Input Validation
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-131.md
- **Summary:** 0/NaN dimensions corrupt LineMaterial resolution.

---

## BUG-132: LOW - PathLayer.setGuideDashPattern() No Validation
- **File:** /ui/src/engine/layers/PathLayer.ts
- **Lines:** 411-420
- **Type:** Input Validation
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-132.md
- **Summary:** NaN/0/negative dash values corrupt line rendering.

---

## BUG-133: LOW - DepthLayer Shader Division by Zero
- **File:** /ui/src/engine/layers/DepthLayer.ts
- **Lines:** 107 (shader), 208-209
- **Type:** Division by Zero / Shader
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-133.md
- **Summary:** minDepth===maxDepth causes shader division by zero, GPU-dependent behavior.

---

## BUG-134: LOW - DepthLayer.contourLevels No Validation
- **File:** /ui/src/engine/layers/DepthLayer.ts
- **Lines:** 228
- **Type:** Input Validation / Shader
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-134.md
- **Summary:** 0/NaN/Infinity contourLevels corrupt shader calculations.

---

## BUG-135: LOW - EffectLayer.resizeMesh() No Validation
- **File:** /ui/src/engine/layers/EffectLayer.ts
- **Lines:** 106-120
- **Type:** Input Validation
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-135.md
- **Summary:** 0/NaN dimensions create degenerate geometry and invalid canvas.

---

## BUG-136: LOW - setMaterialBlendMode() Crashes on Null Material
- **File:** /ui/src/engine/layers/blendModeUtils.ts
- **Lines:** 18-20
- **Type:** Input Validation / Crash
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-136.md
- **Summary:** No null check on `material` parameter. Line 20 `material.blending = ...` throws TypeError if material is null/undefined.

---

## BUG-137: LOW - applyBlendModeToGroup() Crashes on Null Group
- **File:** /ui/src/engine/layers/blendModeUtils.ts
- **Lines:** 125-126
- **Type:** Input Validation / Crash
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-137.md
- **Summary:** No null check on `group` parameter. Line 126 `group.traverse()` throws TypeError if group is null/undefined.

---

## BUG-138: LOW - applyBlendModeToGroup() Silent No-Op for Meshes Without Material
- **File:** /ui/src/engine/layers/blendModeUtils.ts
- **Lines:** 127-131
- **Type:** Silent Failure
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-138.md
- **Summary:** Line 127 `child.material` check silently skips meshes with null material. No warning/error - blend mode application silently fails.

---

## BUG-139: LOW - applyMaterialOverrideToMesh() Crashes on Empty Material Array
- **File:** /ui/src/engine/layers/ModelLayer.ts
- **Lines:** 568-570
- **Type:** Input Validation / Crash
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-139.md
- **Summary:** `mesh.material[0].clone()` crashes when material is empty array `[]`. No array length check.

---

## BUG-140: LOW - ModelLayer.setScale() No Input Validation
- **File:** /ui/src/engine/layers/ModelLayer.ts
- **Lines:** 681-694
- **Type:** Input Validation / NaN Propagation
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-140.md
- **Summary:** NaN/Infinity/0 scale passed directly to Three.js model.scale. Corrupts transform silently.

---

## BUG-141: LOW - ModelLayer.setAnimationTime() No Input Validation
- **File:** /ui/src/engine/layers/ModelLayer.ts
- **Lines:** 516-520
- **Type:** Input Validation / NaN Propagation
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-141.md
- **Summary:** NaN/negative/Infinity time passed directly to AnimationAction.time. Corrupts animation state.

---

## BUG-142: LOW - ModelLayer.updateAnimation() NaN Speed Propagation
- **File:** /ui/src/engine/layers/ModelLayer.ts
- **Lines:** 525-530
- **Type:** Input Validation / NaN Propagation
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-142.md
- **Summary:** `animation.speed` read without validation. NaN/Infinity corrupts mixer.update().

---

## BUG-143: LOW - ModelLayer opacityOverride NaN Bypass (SYSTEMIC-005)
- **File:** /ui/src/engine/layers/ModelLayer.ts
- **Lines:** 586-589
- **Type:** NaN Bypass
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-143.md
- **Summary:** `opacityOverride < 1` comparison fails for NaN. NaN stored in material.opacity.

---

## BUG-144: LOW - ModelLayer metalness/roughness No Validation
- **File:** /ui/src/engine/layers/ModelLayer.ts
- **Lines:** 597-608
- **Type:** Input Validation
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-144.md
- **Summary:** PBR metalness/roughness accept NaN/Infinity/out-of-range without clamping to [0,1].

---

## BUG-145: MEDIUM - ModelLayer.onUpdate() Object.assign Discards Animation Update
- **File:** /ui/src/engine/layers/ModelLayer.ts
- **Lines:** 848-853
- **Type:** Logic Error / Silent No-Op
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-145.md
- **Summary:** `Object.assign(this.modelData.animation ?? {}, data)` creates temp object when animation is null. Update is discarded.

---

## BUG-146: LOW - CameraLayer.setCompositionAspect() No Validation
- **File:** /ui/src/engine/layers/CameraLayer.ts
- **Lines:** 132-134
- **Type:** Input Validation / NaN Propagation
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-146.md
- **Summary:** NaN/0/negative/Infinity aspect stored directly. Corrupts frustum visualization in createFrustum().

---

## BUG-147: LOW - CameraLayer.createFrustum() NaN/Infinity Propagation
- **File:** /ui/src/engine/layers/CameraLayer.ts
- **Lines:** 246-254
- **Type:** Input Validation / NaN Propagation
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-147.md
- **Summary:** Camera nearClip/farClip/angleOfView not validated. NaN/Infinity/extreme FOV corrupts frustum geometry.

---

## BUG-148: LOW - CameraLayer.applyPathFollowing() t Clamp Bypassed by NaN (SYSTEMIC-005)
- **File:** /ui/src/engine/layers/CameraLayer.ts
- **Lines:** 522, 525, 536
- **Type:** NaN Bypass
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-148.md
- **Summary:** `Math.max(0, Math.min(1, t))` doesn't catch NaN. NaN t propagates to spline queries.

---

## BUG-149: LOW - CameraLayer.applyPathFollowing() bankingStrength Infinity Corrupts Rotation
- **File:** /ui/src/engine/layers/CameraLayer.ts
- **Lines:** 593-594
- **Type:** Input Validation / Infinity
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-149.md
- **Summary:** bankingStrength=Infinity → bankAngle=±Infinity → rotateZ(Infinity) corrupts camera rotation.

---

## BUG-150: LOW - CameraLayer.onApplyEvaluatedState() pathParameter NaN Stored
- **File:** /ui/src/engine/layers/CameraLayer.ts
- **Lines:** 483-486
- **Type:** Input Validation / NaN Propagation
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-150.md
- **Summary:** pathParameter value stored without validation. NaN corrupts path following parameter.

---

## BUG-151: LOW - DepthflowLayer.setDimensions() No Validation
- **File:** /ui/src/engine/layers/DepthflowLayer.ts
- **Lines:** 246-256
- **Type:** Input Validation / Degenerate Geometry
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-151.md
- **Summary:** NaN/0/negative/Infinity dimensions create degenerate PlaneGeometry. Silent corruption.

---

## BUG-152: LOW - DepthflowLayer.updateConfig() Stores NaN/Infinity to Uniforms
- **File:** /ui/src/engine/layers/DepthflowLayer.ts
- **Lines:** 287-306
- **Type:** Input Validation / NaN Propagation
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-152.md
- **Summary:** Object.assign stores config values without validation. NaN/Infinity corrupt shader uniforms.

---

## BUG-153: LOW - DepthflowLayer Shader Division by zoom=0
- **File:** /ui/src/engine/layers/DepthflowLayer.ts
- **Lines:** 63 (shader), 297-298
- **Type:** Division by Zero / Shader
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-153.md
- **Summary:** Shader divides UV by zoom uniform. zoom=0 causes GPU division by zero, undefined behavior.

---

## BUG-154: LOW - DepthflowLayer Division by fps=0 (SYSTEMIC-003)
- **File:** /ui/src/engine/layers/DepthflowLayer.ts
- **Lines:** 320, 442
- **Type:** Division by Zero
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-154.md
- **Summary:** calculatePresetValues() and onEvaluateFrame() divide by fps. fps=0 produces Infinity/NaN time.

---

## BUG-155: LOW - DepthflowLayer.onApplyEvaluatedState() NaN Stored Directly
- **File:** /ui/src/engine/layers/DepthflowLayer.ts
- **Lines:** 448-468
- **Type:** Input Validation / NaN Propagation
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-155.md
- **Summary:** Evaluated property values assigned to uniforms without validation. NaN corrupts rendering.

---

## BUG-156: LOW - DepthflowLayer Audio Modifier NaN Bypass
- **File:** /ui/src/engine/layers/DepthflowLayer.ts
- **Lines:** 470-492
- **Type:** Input Validation / NaN Propagation
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-156.md
- **Summary:** Audio modifiers added to uniforms without NaN check. NaN !== 0 is true, so check passes.

---

## BUG-157: LOW - LightLayer.setColorTemperature() No Validation
- **File:** /ui/src/engine/layers/LightLayer.ts
- **Lines:** 643-648
- **Type:** Input Validation / NaN Propagation
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-157.md
- **Summary:** kelvin=0/negative triggers Math.log issues in kelvinToRGB(). Light color becomes NaN.

---

## BUG-158: LOW - LightLayer.setIntensity() No Validation
- **File:** /ui/src/engine/layers/LightLayer.ts
- **Lines:** 650-654
- **Type:** Input Validation / NaN Propagation
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-158.md
- **Summary:** NaN/Infinity intensity stored without validation. Lighting calculations fail.

---

## BUG-159: LOW - LightLayer.setAreaSize() No Validation
- **File:** /ui/src/engine/layers/LightLayer.ts
- **Lines:** 680-687
- **Type:** Input Validation / Degenerate Geometry
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-159.md
- **Summary:** 0/NaN/negative dimensions corrupt RectAreaLight. Area light stops illuminating.

---

## BUG-160: LOW - LightLayer.onApplyEvaluatedState() NaN Stored Directly
- **File:** /ui/src/engine/layers/LightLayer.ts
- **Lines:** 950-992
- **Type:** Input Validation / NaN Propagation
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-160.md
- **Summary:** Evaluated NaN values stored directly to intensity, angle, color, distance. SYSTEMIC-005.

---

## BUG-161: LOW - LightLayer.updatePathFollowing() NaN Bypass in Clamp
- **File:** /ui/src/engine/layers/LightLayer.ts
- **Lines:** 591-600
- **Type:** Input Validation / NaN Bypass
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-161.md
- **Summary:** audioMod NaN bypasses Math.max/min clamp. NaN progress passed to path provider. SYSTEMIC-005.

---

## BUG-162: LOW - NormalLayer.onUpdate() and onEvaluateFrame() NaN Propagation
- **File:** /ui/src/engine/layers/NormalLayer.ts
- **Lines:** 169-175, 178-184
- **Type:** Input Validation / NaN Propagation
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-162.md
- **Summary:** Object.assign merges NaN into normalData. normalize() on NaN vector = NaN. Shader lighting fails.

---

## BUG-163: LOW - PointCloudLayer setPointSize()/setOpacity() NaN Propagation
- **File:** /ui/src/engine/layers/PointCloudLayer.ts
- **Lines:** 962-966, 971-975, 1060-1070
- **Type:** Input Validation / NaN Propagation
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-163.md
- **Summary:** setPointSize/setOpacity store to uniforms without validation. onApplyEvaluatedState passes NaN. SYSTEMIC-005.

---

## BUG-164: LOW - PointCloudLayer.getGradientTexture() Division by Zero
- **File:** /ui/src/engine/layers/PointCloudLayer.ts
- **Lines:** 654-658
- **Type:** Division by Zero / NaN Propagation
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-164.md
- **Summary:** Gradient stops with same position cause division by zero. localT = NaN corrupts gradient texture.

---

## BUG-165: LOW - PoseLayer.setCompositionSize() No Validation
- **File:** /ui/src/engine/layers/PoseLayer.ts
- **Lines:** 446-449, 307-319
- **Type:** Input Validation / Canvas Corruption
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-165.md
- **Summary:** NaN/0/negative dimensions corrupt canvas rendering. Pose rendering fails silently.

---

## BUG-166: LOW - interpolatePoses() NaN Propagation
- **File:** /ui/src/engine/layers/PoseLayer.ts
- **Lines:** 697-720
- **Type:** Input Validation / NaN Propagation
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-166.md
- **Summary:** t=NaN produces pose with NaN keypoint positions. Silent rendering failure.

---

## BUG-167: LOW - ProceduralMatteLayer.setDimensions() No Validation
- **File:** /ui/src/engine/layers/ProceduralMatteLayer.ts
- **Lines:** 132-144
- **Type:** Input Validation / Canvas Corruption
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-167.md
- **Summary:** NaN/0/negative dimensions corrupt canvas and geometry. Matte rendering fails.

---

## BUG-168: LOW - ProceduralMatteLayer.renderPattern() Division by fps=0 (SYSTEMIC-003)
- **File:** /ui/src/engine/layers/ProceduralMatteLayer.ts
- **Lines:** 186
- **Type:** Division by Zero
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-168.md
- **Summary:** compositionFps=0 produces Infinity/NaN time. All animated patterns corrupt.

---

## BUG-169: LOW - ProceduralMatteLayer.applyLevels() Division by Zero
- **File:** /ui/src/engine/layers/ProceduralMatteLayer.ts
- **Lines:** 644, 651
- **Type:** Division by Zero / NaN Propagation
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-169.md
- **Summary:** inputBlack===inputWhite causes inputRange=0. Division by zero → NaN pixels.

---

## BUG-170: MEDIUM - ProceduralMatteLayer Pattern Renderers Infinite Loop
- **File:** /ui/src/engine/layers/ProceduralMatteLayer.ts
- **Lines:** 390-391, 524, 550-551
- **Type:** Division by Zero / Infinite Loop
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-170.md
- **Summary:** tilesX/tilesY/slats/blockSize=0 causes division by zero. renderDissolve() enters INFINITE LOOP, freezing browser.

---

## BUG-171: LOW - AudioLayer.getAudioTimeForFrame() Division by fps=0 (SYSTEMIC-003)
- **File:** /ui/src/engine/layers/AudioLayer.ts
- **Lines:** 182-186
- **Type:** Division by Zero
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-171.md
- **Summary:** fps=0 produces Infinity/NaN audio time. All audio synchronization calculations become invalid.

---

## BUG-172: LOW - AudioLayer.updateGain()/updatePan() NaN Bypass (SYSTEMIC-005)
- **File:** /ui/src/engine/layers/AudioLayer.ts
- **Lines:** 323-336, 341-351
- **Type:** NaN Propagation / Web Audio Corruption
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-172.md
- **Summary:** NaN values bypass Math.max/min clamps and are passed to Web Audio API nodes, causing undefined audio behavior.

---

## BUG-173: LOW - ControlLayer.setIndicatorSize() No Validation
- **File:** /ui/src/engine/layers/ControlLayer.ts
- **Lines:** 115-126
- **Type:** Input Validation / Geometry Corruption
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-173.md
- **Summary:** NaN/0/Infinity/negative size values corrupt visual indicator geometry via NaN coordinates.

---

## BUG-174: LOW - DepthLayer Shader Division by Zero
- **File:** /ui/src/engine/layers/DepthLayer.ts
- **Lines:** 107 (shader), 217 (onUpdate)
- **Type:** Division by Zero / Shader Corruption
- **Found:** 2025-12-27
- **Evidence:** See EVIDENCE/BUG-174.md
- **Summary:** minDepth === maxDepth causes division by zero in shader. NaN values stored without validation.

---

---

## BUG-029: MEDIUM - extractChannelAmplitudes Division by Zero (fps=0/NaN)
- **File:** /ui/src/stores/actions/audioActions.ts
- **Lines:** 529
- **Type:** Input Validation / Division by Zero
- **Found:** 2025-12-28
- **Evidence:** See EVIDENCE/BUG-029.md
- **Summary:** `Math.floor(sampleRate / fps)` causes Infinity when fps=0 or NaN when fps=NaN. Loop never runs, returns all-zero amplitude arrays silently.

---

## BUG-030: MEDIUM - getAudioAmplitudeAtFrame Division by Zero
- **File:** /ui/src/stores/actions/audioActions.ts
- **Lines:** 673
- **Type:** Input Validation / Division by Zero
- **Found:** 2025-12-28
- **Evidence:** See EVIDENCE/BUG-030.md
- **Summary:** Linear interpolation divides by `(nextKf.frame - prevKf.frame)` without checking for zero. Returns NaN when keyframes have identical frame values.

---

## BUG-031: HIGH - removeLegacyAudioMapping NaN Index Removes Wrong Element
- **File:** /ui/src/stores/actions/audioActions.ts
- **Lines:** 397
- **Type:** Input Validation / Type Coercion
- **Found:** 2025-12-28
- **Evidence:** See EVIDENCE/BUG-031.md
- **Summary:** `splice(NaN, 1)` coerces NaN to 0, silently removing the FIRST element instead of failing. Causes data corruption without warning.

---

## BUG-032: MEDIUM - createAmplitudeProperty NaN Keyframe Values
- **File:** /ui/src/stores/actions/audioActions.ts
- **Lines:** 601-604
- **Type:** Input Validation / NaN Propagation
- **Found:** 2025-12-28
- **Evidence:** See EVIDENCE/BUG-032.md
- **Summary:** NaN values in amplitude array create NaN keyframe values (`amp * scale = NaN`). Propagates through animation calculations silently.

---

## BUG-033: LOW - Multiple Functions Don't Validate NaN currentFrame
- **File:** /ui/src/stores/actions/audioActions.ts
- **Lines:** 135, 231, 263, 352
- **Type:** Input Validation / NaN Propagation
- **Found:** 2025-12-28
- **Evidence:** See EVIDENCE/BUG-033.md
- **Summary:** `frame ?? (store.getActiveComp()?.currentFrame ?? 0)` doesn't catch NaN. Nullish coalescing only guards null/undefined.

---

## BUG-034: MEDIUM - convertAudioToKeyframes NaN Options Bypass Defaults
- **File:** /ui/src/stores/actions/audioActions.ts
- **Lines:** 464-468
- **Type:** Input Validation / Destructuring Defaults
- **Found:** 2025-12-28
- **Evidence:** See EVIDENCE/BUG-034.md
- **Summary:** Destructuring `{ amplitudeScale = 100 }` only applies default for undefined, not NaN. NaN options propagate to keyframe values.

---

## BUG-047: MEDIUM - clearAudio Doesn't Dispose audioReactiveMapper
- **File:** /ui/src/stores/actions/audioActions.ts
- **Lines:** 118-124
- **Type:** Resource Management / Memory Leak
- **Found:** 2025-12-28
- **Evidence:** See EVIDENCE/BUG-047.md
- **Summary:** clearAudio() sets references to null but doesn't call dispose() on audioReactiveMapper. Resources leak if mapper has listeners.

---

## BUG-048: MEDIUM - createPathAnimator Overwrites Without Disposal
- **File:** /ui/src/stores/actions/audioActions.ts
- **Lines:** 297-298
- **Type:** Resource Management / Memory Leak
- **Found:** 2025-12-28
- **Evidence:** See EVIDENCE/BUG-048.md
- **Summary:** `store.pathAnimators.set()` overwrites existing animator without disposing it first. Orphaned animators may leak resources.

---

## BUG-049: MEDIUM - removePathAnimator Deletes Without dispose()
- **File:** /ui/src/stores/actions/audioActions.ts
- **Lines:** 332-334
- **Type:** Resource Management / Memory Leak
- **Found:** 2025-12-28
- **Evidence:** See EVIDENCE/BUG-049.md
- **Summary:** `store.pathAnimators.delete()` removes animator from Map without calling dispose(). RAF callbacks and listeners may leak.

---
