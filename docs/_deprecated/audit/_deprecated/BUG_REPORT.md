# Lattice Compositor Bug Report

**Last Updated:** 2025-12-25

---

## Summary

| Severity | Total | Fixed | Open |
|----------|-------|-------|------|
| CRITICAL | 0 | 0 | 0 |
| HIGH | 2 | 2 | 0 |
| MEDIUM | 15 | 15 | 0 |
| LOW | 3 | 3 | 0 |
| **TOTAL** | **20** | **20** | **0** |

---

## BUG-005: getDefaultLayerData returns null without null check
- **Severity:** LOW
- **Feature:** 1.1 Layer Creation/Deletion
- **File:** ui/src/stores/actions/layer/layerDefaults.ts
- **Line:** 407-409
- **Description:** `getDefaultLayerData()` returns `null` for unknown layer types in the default case. The caller in `createLayer()` (layerActions.ts:143) casts this directly as `Layer['data']` without a null check.
- **Expected:** Should either throw an error for unknown types or return a safe default.
- **Actual:** Returns null which could cause null pointer errors downstream if an unknown type is passed.
- **Status:** FIXED
- **Fix:** Changed default case to throw descriptive error instead of returning null. Updated return type from `AnyLayerData | null` to `AnyLayerData`.
- **Files Changed:** ui/src/stores/actions/layer/layerDefaults.ts

---

## BUG-006: Separate dimensions ignored in MotionEngine.evaluateTransform
- **Severity:** HIGH
- **Feature:** 1.2 Layer Transform
- **File:** ui/src/engine/MotionEngine.ts
- **Line:** 618-622
- **Description:** `evaluateTransform()` always evaluates the combined `position` and `scale` properties, completely ignoring the `separateDimensions` flag and individual `positionX/Y/Z` and `scaleX/Y/Z` properties.
- **Expected:** When `transform.separateDimensions.position` is true, should evaluate `positionX`, `positionY`, `positionZ` instead of `position`.
- **Actual:** Always reads `position` property, ignoring separate dimension properties even when the flag is set.
- **Status:** FIXED
- **Fix:** Added conditional checks for `separateDimensions.position` and `separateDimensions.scale` flags. When true, evaluates individual X/Y/Z properties instead of combined position/scale.

---

## BUG-007: insertKeyframeOnPath treats position as array instead of object
- **Severity:** HIGH
- **Feature:** 1.3 Keyframe CRUD
- **File:** ui/src/stores/actions/keyframeActions.ts, ui/src/services/rovingKeyframes.ts
- **Line:** 795-800, 848
- **Description:** `insertKeyframeOnPath()` incorrectly treats position values as `number[]` arrays, but position is stored as `{x: number, y: number, z?: number}` objects. Also affects `applyRovingToPosition()` and the `rovingKeyframes.ts` service.
- **Expected:** Should handle position as `{x, y, z}` object.
- **Actual:** Casts to `number[]` and calls `.map()` which crashes with "map is not a function".
- **Status:** FIXED
- **Fix:** Updated `insertKeyframeOnPath` to use object property access. Updated `rovingKeyframes.ts` to handle both `number[]` and `{x,y,z}` formats with `PositionValue` type union and `extractXYZ` helper function. Made `applyRovingKeyframes` generic to preserve input type.

---

## BUG-008: SolidLayer uses labelColor to set visual fill color
- **Severity:** MEDIUM
- **Feature:** 2.1 SolidLayer
- **File:** ui/src/engine/layers/SolidLayer.ts
- **Line:** 337-339
- **Description:** `onUpdate()` incorrectly uses `labelColor` (timeline organization color) to set the solid's visual fill color. These are separate concepts - labelColor is for timeline organization, not visual rendering.
- **Expected:** labelColor changes should only affect timeline UI, not the solid's rendered color.
- **Actual:** When labelColor is changed via `updateLayer()`, the solid's visual color changes too.
- **Status:** FIXED
- **Fix:** Removed incorrect labelColor handling code. Added comment clarifying labelColor is for timeline only.
- **Files Changed:** ui/src/engine/layers/SolidLayer.ts

---

## BUG-009: AudioLayer hasAudio getter returns true when no audio
- **Severity:** LOW
- **Feature:** 2.6 AudioLayer
- **File:** ui/src/engine/layers/AudioLayer.ts
- **Line:** 418
- **Description:** The `hasAudio` getter uses `this.playbackNodes?.buffer !== null` which returns `true` when `playbackNodes` is null, because optional chaining returns `undefined` and `undefined !== null` is `true`.
- **Expected:** Should return `false` when there's no audio loaded.
- **Actual:** Returns `true` when `playbackNodes` is null.
- **Status:** FIXED
- **Fix:** Changed to explicit null check: `return this.playbackNodes !== null && this.playbackNodes.buffer !== null;`
- **Files Changed:** ui/src/engine/layers/AudioLayer.ts

---

## BUG-010: ShapeLayer hardcoded 30fps in getAnimatedValue
- **Severity:** MEDIUM
- **Feature:** 2.5 ShapeLayer
- **File:** ui/src/engine/layers/ShapeLayer.ts
- **Line:** 699
- **Description:** `getAnimatedValue()` calls `interpolateProperty(prop, this.currentFrame, 30, ...)` with hardcoded 30fps instead of using composition fps. This causes incorrect animation timing at non-30fps framerates.
- **Expected:** Should use composition fps (e.g., 16fps common in AI workflows, 24fps for film, 60fps for games).
- **Actual:** Always uses 30fps regardless of composition settings, causing animations to run at wrong speeds.
- **Status:** FIXED
- **Fix:** Changed hardcoded `30` to `this.compositionFps` (inherited from BaseLayer). BaseLayer already has this property and setCompositionFps() method.
- **Files Changed:** ui/src/engine/layers/ShapeLayer.ts

---

## BUG-011: CameraLayer missing fps in interpolateProperty call
- **Severity:** MEDIUM
- **Feature:** 2.7 CameraLayer
- **File:** ui/src/engine/layers/CameraLayer.ts
- **Line:** 497
- **Description:** `interpolateProperty(pathFollowing.parameter, frame)` is missing fps parameter. Defaults to 30fps causing wrong path animation timing at non-30fps framerates.
- **Expected:** Should pass composition fps for correct timing.
- **Actual:** Falls back to 30fps regardless of composition settings.
- **Status:** FIXED
- **Fix:** Added `this.compositionFps` and `this.id` parameters to interpolateProperty call.
- **Files Changed:** ui/src/engine/layers/CameraLayer.ts

---

## BUG-012: CameraLayer hardcoded 16/9 aspect ratio in frustum
- **Severity:** LOW
- **Feature:** 2.7 CameraLayer
- **File:** ui/src/engine/layers/CameraLayer.ts
- **Line:** 239
- **Description:** Frustum visualization uses hardcoded `16/9` aspect ratio instead of composition aspect. Causes frustum to display incorrectly for non-16:9 compositions.
- **Expected:** Should use composition width/height to calculate aspect ratio.
- **Actual:** Always displays as 16:9 frustum regardless of actual composition dimensions.
- **Status:** FIXED
- **Fix:** Added `compositionAspect` property with `setCompositionAspect()` method. Changed hardcoded `16/9` to `this.compositionAspect`. Also tracks aspect in frustum state for re-creation when aspect changes.
- **Files Changed:** ui/src/engine/layers/CameraLayer.ts

---

## BUG-013: LightLayer POI smoothing violates determinism
- **Severity:** MEDIUM
- **Feature:** 2.8 LightLayer
- **File:** ui/src/engine/layers/LightLayer.ts
- **Line:** 552-556
- **Description:** POI smoothing uses `this.smoothedPOI.lerp()` which accumulates state frame-over-frame. Scrubbing Frame 50 → Frame 10 → Frame 50 produces different results because smoothedPOI depends on previous frame, not just current frame number.
- **Expected:** Same frame number should always produce identical output regardless of playback history.
- **Actual:** Output depends on which frames were previously evaluated, violating determinism.
- **Status:** FIXED
- **Fix:** Added `lastPOIFrame` tracker. Smoothing only applies on sequential frames (frame === lastPOIFrame + 1). Non-sequential access resets smoothedPOI to target directly, ensuring determinism.
- **Files Changed:** ui/src/engine/layers/LightLayer.ts

---

## BUG-014: NestedCompLayer opacity never applied to material
- **Severity:** MEDIUM
- **Feature:** 2.11 NestedCompLayer
- **File:** ui/src/engine/layers/NestedCompLayer.ts
- **Line:** 280-292
- **Description:** The layer's animated opacity is never applied to `this.material.opacity`. Material is created with default opacity=1.0 and `onApplyEvaluatedState` only handles speedMap.
- **Expected:** Animated opacity should control nested comp visibility.
- **Actual:** Nested comp always renders at 100% opacity. Also affects `combineTransforms()` which uses wrong opacity for flattened layers.
- **Status:** FIXED
- **Fix:** Added opacity handling in `onApplyEvaluatedState`: reads `state.transform.opacity` and applies to `this.material.opacity`.
- **Files Changed:** ui/src/engine/layers/NestedCompLayer.ts

---

## BUG-015: EffectLayer.getSourceCanvas hardcodes frame 0
- **Severity:** MEDIUM
- **Feature:** 2.12 EffectLayer
- **File:** ui/src/engine/layers/EffectLayer.ts
- **Line:** 248
- **Description:** `getSourceCanvas()` calls `renderLayersBelow(this.id, 0)` with hardcoded frame 0 instead of current frame.
- **Expected:** Should use `this.currentFrame` to render the correct frame.
- **Actual:** Always renders frame 0 when additional effects need the source canvas.
- **Status:** FIXED
- **Fix:** Changed hardcoded `0` to `this.currentFrame`.
- **Files Changed:** ui/src/engine/layers/EffectLayer.ts

---

## BUG-016: EffectLayer opacity never applied to material
- **Severity:** MEDIUM
- **Feature:** 2.12 EffectLayer
- **File:** ui/src/engine/layers/EffectLayer.ts
- **Line:** 205-210
- **Description:** `onApplyEvaluatedState` only applies effects, not opacity. Docstring states "Respects the effect layer's opacity" but material.opacity is never set from evaluated transform.
- **Expected:** Animated opacity should control effect layer visibility.
- **Actual:** Effect layer always renders at 100% opacity regardless of animated opacity property.
- **Status:** FIXED
- **Fix:** Added opacity handling in `onApplyEvaluatedState`: reads `state.transform.opacity` and applies to `this.material.opacity`.
- **Files Changed:** ui/src/engine/layers/EffectLayer.ts

---

## BUG-017: ParticleLayer audio reactivity compounds emitter values
- **Severity:** MEDIUM
- **Feature:** 2.13 ParticleLayer
- **File:** ui/src/engine/layers/ParticleLayer.ts
- **Line:** 1004-1045
- **Description:** `applyAudioReactivity()` reads current emitter/force field values from config and multiplies by audio factor. Since config values are modified in place, values compound each frame (e.g., 100→110→121→133...) instead of being applied fresh from base values.
- **Expected:** Audio should modulate from original BASE values, not already-modulated values.
- **Actual:** Audio modulation compounds unboundedly over time, causing particle properties to grow/shrink wildly.
- **Status:** FIXED
- **Fix:** Added `baseEmitterValues` and `baseForceFieldValues` Maps to store original values. Modified `applyAudioReactivity` to always multiply from base values. Added `storeBaseValues()` called during initialization.
- **Files Changed:** ui/src/engine/layers/ParticleLayer.ts

---

## BUG-018: PathLayer.evaluateControlPointAtFrame missing fps parameter
- **Severity:** MEDIUM
- **Feature:** 2.14 PathLayer
- **File:** ui/src/engine/layers/PathLayer.ts
- **Line:** 343-355
- **Description:** All `interpolateProperty` calls in `evaluateControlPointAtFrame` are missing fps and layerId parameters. Defaults to 30fps causing incorrect animation timing for animated path control points at non-30fps framerates.
- **Expected:** Should use `this.compositionFps` for correct timing at all framerates.
- **Actual:** Always uses default 30fps regardless of composition settings.
- **Status:** FIXED
- **Fix:** Added fps and layerId variables, passed them to all interpolateProperty calls.
- **Files Changed:** ui/src/engine/layers/PathLayer.ts

---

## BUG-019: SplineLayer missing fps in all interpolateProperty calls
- **Severity:** MEDIUM
- **Feature:** 2.15 SplineLayer
- **File:** ui/src/engine/layers/SplineLayer.ts
- **Line:** 905-921, 1034, 1134-1184
- **Description:** All `interpolateProperty` calls in SplineLayer are missing fps and layerId parameters. This affects control point animation, trim path animation, and all path effect animations (offset, wiggle, zigzag, roughen, wave).
- **Expected:** Should use `this.compositionFps` for correct timing at all framerates.
- **Actual:** Always uses default 30fps regardless of composition settings.
- **Status:** FIXED
- **Fix:** Added fps and layerId parameters to all interpolateProperty calls in evaluateControlPointAtFrame, evaluateStaticOrAnimated, and applyPathEffects.
- **Files Changed:** ui/src/engine/layers/SplineLayer.ts

---

## BUG-020: ModelLayer.onEvaluateFrame missing fps parameter
- **Severity:** MEDIUM
- **Feature:** 2.16 ModelLayer
- **File:** ui/src/engine/layers/ModelLayer.ts
- **Line:** 769, 775 (after fix: 773, 779)
- **Description:** `interpolateProperty` calls in `onEvaluateFrame` for scale and animation time are missing fps and layerId parameters. Defaults to 30fps.
- **Expected:** Should use `this.compositionFps` for correct timing at all framerates.
- **Actual:** Always uses default 30fps regardless of composition settings.
- **Status:** FIXED
- **Fix:** Added fps and layerId variables using `this.compositionFps` and `this.id`, passed to interpolateProperty calls.
- **Files Changed:** ui/src/engine/layers/ModelLayer.ts

---

## BUG-021: PointCloudLayer.onEvaluateFrame missing fps parameter
- **Severity:** MEDIUM
- **Feature:** 2.17 PointCloudLayer
- **File:** ui/src/engine/layers/PointCloudLayer.ts
- **Line:** 1015, 1019
- **Description:** `interpolateProperty` calls for pointSize and opacity are missing fps and layerId parameters. Defaults to 30fps.
- **Expected:** Should use `this.compositionFps` for correct timing at all framerates.
- **Actual:** Always uses default 30fps regardless of composition settings.
- **Status:** FIXED
- **Fix:** Added fps and layerId variables using `this.compositionFps` and `this.id`, passed to interpolateProperty calls.
- **Files Changed:** ui/src/engine/layers/PointCloudLayer.ts

---

## BUG-022: DepthLayer.onEvaluateFrame missing fps parameter
- **Severity:** MEDIUM
- **Feature:** 2.18 DepthLayer
- **File:** ui/src/engine/layers/DepthLayer.ts
- **Line:** 198
- **Description:** `interpolateProperty` call for meshDisplacement is missing fps and layerId parameters. Defaults to 30fps.
- **Expected:** Should use `this.compositionFps` for correct timing at all framerates.
- **Actual:** Always uses default 30fps regardless of composition settings.
- **Status:** FIXED
- **Fix:** Added fps and layerId variables using `this.compositionFps` and `this.id`, passed to interpolateProperty call.
- **Files Changed:** ui/src/engine/layers/DepthLayer.ts

---

## BUG-023: DepthflowLayer hardcoded 30fps in multiple places
- **Severity:** MEDIUM
- **Feature:** 2.19 DepthflowLayer
- **File:** ui/src/engine/layers/DepthflowLayer.ts
- **Line:** 402, 439
- **Description:** `calculatePresetValues()` has fps parameter with default 30, but called without fps argument. Also, time uniform calculated as `frame / 30` instead of using composition fps.
- **Expected:** Should use `this.compositionFps` for correct timing at all framerates.
- **Actual:** Always uses 30fps for preset animations and time-based effects.
- **Status:** FIXED
- **Fix:** Pass `this.compositionFps` to `calculatePresetValues()` and use `fps` variable for time uniform calculation.
- **Files Changed:** ui/src/engine/layers/DepthflowLayer.ts

---

## BUG-024: ProceduralMatteLayer time calculation hardcodes 60fps
- **Severity:** MEDIUM
- **Feature:** 2.23 ProceduralMatteLayer
- **File:** ui/src/engine/layers/ProceduralMatteLayer.ts
- **Line:** 185
- **Description:** Time calculation uses `(frame * speed / 60)` with hardcoded 60fps instead of using composition fps.
- **Expected:** Should use `this.compositionFps` for correct animation timing at all framerates.
- **Actual:** Animations run 2x too fast at 30fps, wrong speed at all non-60fps compositions.
- **Status:** FIXED
- **Fix:** Changed `60` to `this.compositionFps`.
- **Files Changed:** ui/src/engine/layers/ProceduralMatteLayer.ts

---
