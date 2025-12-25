# Lattice Compositor Bug Report

**Last Updated:** 2025-12-25

---

## Summary

| Severity | Total | Fixed | Open |
|----------|-------|-------|------|
| CRITICAL | 0 | 0 | 0 |
| HIGH | 2 | 2 | 0 |
| MEDIUM | 2 | 2 | 0 |
| LOW | 2 | 1 | 1 |
| **TOTAL** | **6** | **5** | **1** |

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
- **Status:** OPEN

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
