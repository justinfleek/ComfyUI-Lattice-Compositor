# Phase 2: Getter & Method Decisions

**Date:** 2026-01-12
**Purpose:** Make architectural decisions for Phase 2 remaining getters and methods

## Getter Decisions (5 getters)

### 1. `currentFrame` ⏳ **NEEDS DECISION**
**Current:** Reads from `comp?.currentFrame || 0` (line 304-307)
**Options:**
- **Option A:** Keep in compositorStore (reads from composition state)
- **Option B:** Migrate to playbackStore (playback domain)
- **Option C:** Migrate to projectStore (project/composition domain)

**Analysis:**
- `currentFrame` is per-composition state (each composition has its own currentFrame)
- Used by playback operations (play, pause, nextFrame, prevFrame)
- Used by rendering (getFrameState, evaluatePropertyAtFrame)
- Used by UI (timeline, preview)

**Recommendation:** **Option A** - Keep in compositorStore
- It's composition state, not playback state
- PlaybackStore manages playback operations, not frame state
- ProjectStore manages project settings, not frame state
- Each composition has its own currentFrame

### 2. `fps` ✅ **ALREADY DELEGATED**
**Current:** Delegates to `projectStore.getFps(this)` (line 278-280)
**Status:** ✅ Correct - Reads from composition settings

### 3. `frameCount` ✅ **ALREADY DELEGATED**
**Current:** Delegates to `projectStore.getFrameCount(this)` (line 275-277)
**Status:** ✅ Correct - Reads from composition settings

### 4. `currentTime` ✅ **ALREADY DELEGATED**
**Current:** Delegates to `projectStore.getCurrentTime(this)` (line 308-310)
**Status:** ✅ Correct - Calculates from currentFrame / fps

### 5. `duration` ✅ **ALREADY DELEGATED**
**Current:** Delegates to `projectStore.getDuration(this)` (line 281-283)
**Status:** ✅ Correct - Reads from composition settings

## Method Decisions (2 methods)

### 1. `getFrameState` ⏳ **NEEDS DECISION**
**Current:** Line 985 - Calls `motionEngine.evaluate()`
**Purpose:** Get evaluated state for rendering (all layers, properties, effects)
**Cross-Domain:** Needs layerStore, keyframeStore, expressionStore, effectStore

**Options:**
- **Option A:** Keep in compositorStore (orchestrates cross-domain evaluation)
- **Option B:** Create new `frameStateStore` (dedicated store for frame evaluation)
- **Option C:** Move to `motionEngine` as static method (pure function)

**Analysis:**
- This is THE canonical way to get evaluated state
- Used by rendering pipeline
- Needs access to all domain stores
- Pure function (deterministic, no side effects)

**Recommendation:** **Option A** - Keep in compositorStore
- Cross-domain orchestration is compositorStore's role
- Until compositorStore is deleted (Phase 5), this stays here
- After Phase 5, this becomes a service/utility function

### 2. `getInterpolatedValue` ⏳ **NEEDS VERIFICATION**
**Current:** Need to find this method
**Purpose:** Interpolate property value at a specific frame
**Cross-Domain:** Needs keyframeStore (interpolation logic)

**Options:**
- **Option A:** Keep in compositorStore
- **Option B:** Move to keyframeStore (keyframe domain)
- **Option C:** Move to interpolation utility (pure function)

**Analysis:**
- Interpolation is keyframe domain logic
- Should be in keyframeStore or interpolation utility
- Used by property evaluation

**Recommendation:** **Option B** - Move to keyframeStore
- Interpolation is keyframe domain
- keyframeStore already has interpolation logic

## Summary

**Getter Decisions:**
- ✅ `fps` - Already delegated to projectStore ✅
- ✅ `frameCount` - Already delegated to projectStore ✅
- ✅ `currentTime` - Already delegated to projectStore ✅
- ✅ `duration` - Already delegated to projectStore ✅
- ⏳ `currentFrame` - **DECISION:** Keep in compositorStore (composition state)

**Method Decisions:**
- ⏳ `getFrameState` - **DECISION:** Keep in compositorStore (cross-domain orchestration)
- ⏳ `getInterpolatedValue` - **DECISION:** Move to keyframeStore (keyframe domain)

## Next Steps

1. ✅ Document decisions (this file)
2. ⏳ Verify `getInterpolatedValue` exists and location
3. ⏳ Update consumers to use domain stores directly
4. ⏳ Fix lazy code patterns (~150 issues)
