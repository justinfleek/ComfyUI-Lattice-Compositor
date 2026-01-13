# Phase 5 Migration Plan

> **Date:** 2026-01-12  
> **Status:** ⏳ IN PROGRESS

---

## Overview

**Goal:** Migrate remaining project & UI state methods/getters from compositorStore

**Stores Needed:**
- `projectStore` - Does NOT exist yet (needs to be created)
- `uiStore` - Does NOT exist yet (needs to be created)

**Strategy:** Start with methods that can use existing stores, then create new stores as needed.

---

## Methods to Migrate

### 1. Selection Getters (Can use existing `selectionStore`)

**`selectedLayers` getter** (Lines 371-377)
- **Current:** Filters layers by `selectionStore.selectedLayerIds`
- **Target:** `selectionStore` or `layerStore` (layer query domain)
- **Decision:** Move to `layerStore` as query method (similar to `getCameraLayers`)

**`selectedLayer` getter** (Lines 378-387)
- **Current:** Finds single selected layer
- **Target:** `selectionStore` or `layerStore` (layer query domain)
- **Decision:** Move to `layerStore` as query method

---

### 2. UI State Methods (Need `uiStore`)

**`toggleHideMinimizedLayers`** (Lines ~1336-1338)
- **Current:** Toggles `this.hideMinimizedLayers`
- **Target:** `uiStore` (needs to be created)

**`setHideMinimizedLayers`** (Lines ~1348-1350)
- **Current:** Sets `this.hideMinimizedLayers`
- **Target:** `uiStore` (needs to be created)

**`setCurveEditorVisible`** (Lines ~1328-1331)
- **Current:** Sets `this.curveEditorVisible`
- **Target:** `uiStore` (needs to be created)

**State to Migrate:**
- `hideMinimizedLayers: boolean`
- `curveEditorVisible: boolean`

---

### 3. Project Getters (Need `projectStore`)

**`openCompositions` getter** (Lines 393-397)
- **Current:** Maps `openCompositionIds` to compositions
- **Target:** `projectStore` (needs to be created)

**`breadcrumbPath` getter** (Lines 400-405)
- **Current:** Maps `compositionBreadcrumbs` to composition names
- **Target:** `projectStore` (needs to be created)

**State to Migrate:**
- `openCompositionIds: string[]`
- `compositionBreadcrumbs: string[]`

---

### 4. Asset Selection (Need `projectStore`)

**`selectAsset`** (Lines ~2758-2760)
- **Current:** Sets `this.selectedAssetId`
- **Target:** `projectStore` (needs to be created)

**State to Migrate:**
- `selectedAssetId: string | null`

---

### 5. Composition Settings Getters (Need `projectStore`)

**`width`, `height`, `frameCount`, `fps`, `duration`, `backgroundColor`** (Lines 284-307)
- **Current:** Access `state.project.compositions[state.activeCompositionId]`
- **Target:** `projectStore` (needs to be created)

---

### 6. ComfyUI Integration (Need `projectStore` or `compositionActions`)

**`loadInputs`** (Lines 529-605) - ~76 lines ⚠️ **LARGEST**
- **Current:** Updates composition settings, assets, layer outPoints
- **Target:** `projectStore` or `compositionActions` (ComfyUI integration domain)
- **Complexity:** High - touches multiple domains

---

### 7. Helper Methods (Decision Needed)

**`getActiveCompLayers`** (Lines 433-436)
- **Current:** Returns `comp?.layers || []`
- **Used:** Everywhere (60+ usages)
- **Options:**
  1. Keep in compositorStore (helper method)
  2. Move to `projectStore` (composition domain)
  3. Move to `layerStore` (layer query domain)

**`getActiveComp`** (Lines 441-443)
- **Current:** Returns `this.project.compositions[this.activeCompositionId]`
- **Used:** Everywhere (100+ usages)
- **Options:**
  1. Keep in compositorStore (helper method)
  2. Move to `projectStore` (composition domain)

**RECOMMENDATION:** Keep as helpers in compositorStore until Phase 5 completion, then decide based on usage patterns.

---

## Migration Order

1. **Start with existing stores:**
   - Selection getters → `layerStore` (can use existing store)

2. **Create `uiStore`:**
   - UI state methods → `uiStore`

3. **Create `projectStore`:**
   - Project getters → `projectStore`
   - Asset selection → `projectStore`
   - Settings getters → `projectStore`
   - ComfyUI integration → `projectStore`

4. **Decide on helpers:**
   - `getActiveCompLayers` and `getActiveComp` - Keep or migrate?

---

*Created: 2026-01-12*
