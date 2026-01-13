# CompositorStore Remaining Implementation Code Audit

> **Date:** 2026-01-12  
> **Purpose:** Find ALL methods/getters in compositorStore that still have implementation code instead of delegating  
> **Status:** ⏳ IN PROGRESS

---

## Summary

After Phase 1 completion, there are **~20+ methods/getters** that still have implementation code in `compositorStore.ts` instead of delegating to domain stores or action modules.

---

## Methods with Implementation Code

### Phase 2: Animation & Keyframes (5 methods)

1. **`getFrameState`** (Lines 1075-1097) - ~23 lines
   - **Status:** ⏳ Needs migration to `animationStore`
   - **Current:** Calls `motionEngine.evaluate()` directly
   - **Target:** `animationStore` (frame evaluation domain)

2. **`getInterpolatedValue`** (Lines 1361-1369) - ~9 lines
   - **Status:** ⏳ Needs migration to `keyframeStore`
   - **Current:** Calls `interpolateProperty()` directly
   - **Target:** `keyframeStore` (interpolation domain)

3. **`findSnapPoint`** (Lines 2369-2387) - ~19 lines
   - **Status:** ⏳ Needs migration to `animationStore`
   - **Current:** Calls `findNearestSnap()` with local state access
   - **Target:** `animationStore` (timeline snapping domain)

4. **`setTimelineZoom`** (Lines 2751-2753) - ~3 lines
   - **Status:** ⚠️ **WRONG** - Directly sets `useAnimationStore().timelineZoom` instead of calling method
   - **Current:** `useAnimationStore().timelineZoom = Math.max(0.1, Math.min(10, zoom));`
   - **Target:** Should delegate to `useAnimationStore().setTimelineZoom(zoom)`

5. **`currentTime` getter** (Lines 329-333) - ~5 lines
   - **Status:** ⏳ Needs migration to `animationStore`
   - **Current:** Calculates `comp.currentFrame / comp.settings.fps`
   - **Target:** `animationStore` (time calculation domain)

---

### Phase 3: Audio (3 methods)

6. **`loadAudio`** (Lines 2248-2256) - ~8 lines
   - **Status:** ⏳ Needs migration to `audioStore`
   - **Current:** Calls `audioStore.loadAudio()` then updates `expressionStore.propertyDriverSystem`
   - **Target:** `audioStore` (should handle property driver system update internally)

7. **`clearAudio`** (Lines 2260-2264) - ~5 lines
   - **Status:** ⏳ Needs migration to `audioStore`
   - **Current:** Calls `audioStore.clear()` then clears `this.pathAnimators`
   - **Target:** `audioStore` (should handle path animators cleanup internally)

8. **`getAudioFeatureAtFrame`** (Lines 2274-2277) - ~4 lines
   - **Status:** ⏳ Needs migration to `audioStore`
   - **Current:** Gets frame from `this.getActiveComp()?.currentFrame` then delegates
   - **Target:** `audioStore` (should accept frame parameter directly)

---

### Phase 4: Camera (1 getter)

9. **`cameraLayers` getter** (Lines 421-424) - ~4 lines
   - **Status:** ⏳ Needs migration to `cameraStore` or `layerStore`
   - **Current:** Filters layers by type "camera"
   - **Target:** `cameraStore` or `layerStore` (layer query domain)

---

### Phase 5: Project & UI State (11 methods/getters)

10. **`loadInputs`** (Lines 529-605) - ~76 lines ⚠️ **LARGEST**
    - **Status:** ⏳ Needs migration to `projectStore` or `compositionActions`
    - **Current:** Updates composition settings, assets, layer outPoints
    - **Target:** `projectStore` or `compositionActions` (ComfyUI integration domain)

11. **`selectAsset`** (Lines 2758-2760) - ~3 lines
    - **Status:** ⏳ Needs migration to `projectStore`
    - **Current:** Sets `this.selectedAssetId`
    - **Target:** `projectStore` (asset selection domain)

12. **`toggleHideMinimizedLayers`** (Lines 1336-1338) - ~3 lines
    - **Status:** ⏳ Needs migration to `uiStore` or keep in compositorStore (UI state)
    - **Current:** Toggles `this.hideMinimizedLayers`
    - **Target:** `uiStore` (UI state domain)

13. **`setHideMinimizedLayers`** (Lines 1348-1350) - ~3 lines
    - **Status:** ⏳ Needs migration to `uiStore` or keep in compositorStore (UI state)
    - **Current:** Sets `this.hideMinimizedLayers`
    - **Target:** `uiStore` (UI state domain)

14. **`setCurveEditorVisible`** (Lines 1328-1331) - ~4 lines
    - **Status:** ⏳ Needs migration to `uiStore` or keep in compositorStore (UI state)
    - **Current:** Sets `this.curveEditorVisible`
    - **Target:** `uiStore` (UI state domain)

15. **`selectedLayers` getter** (Lines 369-375) - ~7 lines
    - **Status:** ⏳ Needs migration to `selectionStore` or `layerStore`
    - **Current:** Filters layers by selected IDs
    - **Target:** `selectionStore` or `layerStore` (layer query domain)

16. **`selectedLayer` getter** (Lines 376-385) - ~10 lines
    - **Status:** ⏳ Needs migration to `selectionStore` or `layerStore`
    - **Current:** Finds single selected layer
    - **Target:** `selectionStore` or `layerStore` (layer query domain)

17. **`openCompositions` getter** (Lines 391-395) - ~5 lines
    - **Status:** ⏳ Needs migration to `projectStore`
    - **Current:** Maps `openCompositionIds` to compositions
    - **Target:** `projectStore` (composition management domain)

18. **`breadcrumbPath` getter** (Lines 398-405) - ~8 lines
    - **Status:** ⏳ Needs migration to `projectStore`
    - **Current:** Maps `compositionBreadcrumbs` to composition names
    - **Target:** `projectStore` (composition navigation domain)

19. **`getActiveCompLayers`** (Lines 435-438) - ~4 lines
    - **Status:** ⚠️ **HELPER METHOD** - May need to stay or migrate to `projectStore`
    - **Current:** Returns `comp?.layers || []`
    - **Target:** `projectStore` (composition access domain) OR keep as helper

20. **`getActiveComp`** (Lines 443-445) - ~3 lines
    - **Status:** ⚠️ **HELPER METHOD** - May need to stay or migrate to `projectStore`
    - **Current:** Returns `this.project.compositions[this.activeCompositionId]`
    - **Target:** `projectStore` (composition access domain) OR keep as helper

---

## Getters with Implementation Code (Phase 2/5)

### Composition Settings Getters (6 getters)

These access `state.project.compositions[state.activeCompositionId]` directly:

1. **`width`** (Lines 284-287) - ~4 lines
2. **`height`** (Lines 288-291) - ~4 lines
3. **`frameCount`** (Lines 292-295) - ~4 lines
4. **`fps`** (Lines 296-299) - ~4 lines
5. **`duration`** (Lines 300-303) - ~4 lines
6. **`backgroundColor`** (Lines 304-307) - ~4 lines

**Status:** ⏳ Needs migration to `projectStore` or `animationStore`  
**Target:** `projectStore` (composition settings domain)

---

## Summary by Phase

- **Phase 1:** ✅ **COMPLETE** (0 methods remaining)
- **Phase 2:** ⏳ **5 methods/getters** remaining
- **Phase 3:** ⏳ **3 methods** remaining
- **Phase 4:** ⏳ **1 getter** remaining
- **Phase 5:** ⏳ **11 methods/getters** remaining

**Total:** **~20 methods/getters** with implementation code

---

## Priority Order

### High Priority (Phase 2 - Blocking Progress)
1. `getFrameState` (~23 lines) - Used by rendering pipeline
2. `getInterpolatedValue` (~9 lines) - Used by property evaluation
3. `findSnapPoint` (~19 lines) - Used by timeline UI
4. `setTimelineZoom` (~3 lines) - **BUG** - Direct state mutation
5. `currentTime` getter (~5 lines) - Used by timeline UI

### Medium Priority (Phase 3 - Audio Domain)
6. `loadAudio` (~8 lines)
7. `clearAudio` (~5 lines)
8. `getAudioFeatureAtFrame` (~4 lines)

### Low Priority (Phase 4/5 - Can Wait)
9-20. Remaining methods/getters

---

*Created: 2026-01-12*  
*Purpose: Comprehensive audit of remaining implementation code*
