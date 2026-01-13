# Remaining Methods Count - Updated After Phase 2

> **Date:** 2026-01-12  
> **Status:** After Phase 2 completion

---

## Summary

**Phase 2:** ✅ **COMPLETE** (5/5 methods migrated)

**Remaining:** **~21 methods/getters** with implementation code

---

## Breakdown by Phase

### ✅ Phase 2: Animation & Keyframes - COMPLETE
- ✅ `setTimelineZoom` - Migrated
- ✅ `getFrameState` - Migrated  
- ✅ `getInterpolatedValue` - Migrated
- ✅ `findSnapPoint` - Migrated
- ✅ `currentTime` - Migrated

**Status:** ✅ **0 remaining**

---

### ✅ Phase 3: Audio - COMPLETE

1. ✅ **`loadAudio`** - Migrated
   - Property driver system update moved to `audioStore.loadAudio()`

2. ✅ **`clearAudio`** - Migrated
   - Path animators cleanup remains in `compositorStore` (correct)

3. ✅ **`getAudioFeatureAtFrame`** - Migrated
   - Frame resolution moved to `audioStore.getFeatureAtFrame()`

**Status:** ✅ **0 remaining** (COMPLETE)

---

### ✅ Phase 4: Camera - COMPLETE

4. ✅ **`cameraLayers` getter** - Migrated
   - Camera layer query moved to `layerStore.getCameraLayers()`

**Status:** ✅ **0 remaining** (COMPLETE)

---

### ⏳ Phase 5: Project & UI State (11 methods/getters)

5. **`loadInputs`** (Lines ~529-605) - ~76 lines ⚠️ **LARGEST**
   - Updates composition settings, assets, layer outPoints
   - **Target:** `projectStore` or `compositionActions` (ComfyUI integration domain)

6. **`selectAsset`** (Lines ~2758-2760) - ~3 lines
   - Sets `this.selectedAssetId`
   - **Target:** `projectStore` (asset selection domain)

7. **`toggleHideMinimizedLayers`** (Lines ~1336-1338) - ~3 lines
   - Toggles `this.hideMinimizedLayers`
   - **Target:** `uiStore` or keep in compositorStore (UI state)

8. **`setHideMinimizedLayers`** (Lines ~1348-1350) - ~3 lines
   - Sets `this.hideMinimizedLayers`
   - **Target:** `uiStore` or keep in compositorStore (UI state)

9. **`setCurveEditorVisible`** (Lines ~1328-1331) - ~4 lines
   - Sets `this.curveEditorVisible`
   - **Target:** `uiStore` or keep in compositorStore (UI state)

10. **`selectedLayers` getter** (Lines ~369-375) - ~7 lines
    - Filters layers by selected IDs
    - **Target:** `selectionStore` or `layerStore` (layer query domain)

11. **`selectedLayer` getter** (Lines ~374-383) - ~10 lines
    - Finds single selected layer
    - **Target:** `selectionStore` or `layerStore` (layer query domain)

12. **`openCompositions` getter** (Lines ~391-393) - ~5 lines
    - Maps `openCompositionIds` to compositions
    - **Target:** `projectStore` (composition management domain)

13. **`breadcrumbPath` getter** (Lines ~396-403) - ~8 lines
    - Maps `compositionBreadcrumbs` to composition names
    - **Target:** `projectStore` (composition navigation domain)

14. **`getActiveCompLayers`** (Lines ~435-438) - ~4 lines ⚠️ **HELPER METHOD**
    - Returns `comp?.layers || []`
    - **Target:** `projectStore` OR keep as helper (used everywhere)

15. **`getActiveComp`** (Lines ~443-445) - ~3 lines ⚠️ **HELPER METHOD**
    - Returns `this.project.compositions[this.activeCompositionId]`
    - **Target:** `projectStore` OR keep as helper (used everywhere)

**Status:** ⏳ **11 remaining**

---

### ⏳ Composition Settings Getters (6 getters)

16. **`width`** (Lines ~284-287) - ~4 lines
17. **`height`** (Lines ~288-291) - ~4 lines
18. **`frameCount`** (Lines ~292-295) - ~4 lines
19. **`fps`** (Lines ~296-299) - ~4 lines
20. **`duration`** (Lines ~300-303) - ~4 lines
21. **`backgroundColor`** (Lines ~304-307) - ~4 lines

All access `state.project.compositions[state.activeCompositionId]` directly.

**Target:** `projectStore` (composition settings domain)

**Status:** ⏳ **6 remaining**

---

## Total Count

- **Phase 2:** ✅ 0 remaining (COMPLETE)
- **Phase 3:** ✅ 0 remaining (COMPLETE)
- **Phase 4:** ✅ 0 remaining (COMPLETE)
- **Phase 5:** ⏳ 11 remaining
- **Settings Getters:** ⏳ 6 remaining

**TOTAL:** **~17 methods/getters** remaining

---

## Priority Breakdown

### High Priority (Core Functionality)
- `loadInputs` (76 lines) - ComfyUI integration
- `getActiveComp` / `getActiveCompLayers` (helpers used everywhere)

### Medium Priority (Domain Logic)
- Phase 3 Audio methods (3 methods)
- Phase 4 Camera getter (1 getter)
- Composition settings getters (6 getters)

### Low Priority (UI State)
- UI state methods (`toggleHideMinimizedLayers`, `setCurveEditorVisible`, etc.)
- Selection getters (`selectedLayers`, `selectedLayer`)
- Navigation getters (`openCompositions`, `breadcrumbPath`)

---

*Updated: 2026-01-12*  
*After Phase 2 completion*
