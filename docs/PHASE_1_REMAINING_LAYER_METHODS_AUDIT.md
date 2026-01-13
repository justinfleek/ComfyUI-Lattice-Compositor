# Phase 1 Remaining Layer Methods Audit

> **Date:** 2026-01-12  
> **Purpose:** Identify layer-related methods still implemented in compositorStore that need migration  
> **Status:** ⏳ IN PROGRESS

---

## Summary

After Phase 1 migration, **2 nested comp layer methods** still have implementation code in `compositorStore.ts` instead of delegating to `layerStore`.

---

## Methods Still Implemented in CompositorStore

### 1. `createNestedCompLayer` (Lines 1909-1931)

**Location:** `ui/src/stores/compositorStore.ts:1909-1931`  
**Lines:** ~23 lines of implementation code  
**Status:** ⏳ **NEEDS MIGRATION**

**Current Implementation:**
```typescript
createNestedCompLayer(compositionId: string, name?: string): Layer {
  const layer = this.createLayer("nestedComp", name || "Nested Comp");
  
  const nestedCompData: NestedCompData = {
    compositionId,
    speedMapEnabled: false,
    speedMap: undefined,
    timeRemapEnabled: false,
    timeRemap: undefined,
    flattenTransform: false,
    overrideFrameRate: false,
    frameRate: undefined,
  };
  
  layer.data = nestedCompData;
  this.project.meta.modified = new Date().toISOString();
  this.pushHistory();
  return layer;
}
```

**Usage Analysis:**
- ✅ **NOT CALLED ANYWHERE** - Grep found 0 usages
- ⚠️ `compositionActions/nesting.ts` creates nested comp layers directly (lines 90-119) without using this method
- **Decision:** Should migrate to `layerStore/specialized.ts` for consistency with other specialized layer creation methods

**Target:** `layerStore/specialized.ts` (alongside `createTextLayer`, `createSplineLayer`, `createShapeLayer`, `createCameraLayer`, `createVideoLayer`)

---

### 2. `updateNestedCompLayerData` (Lines 1936-1946)

**Location:** `ui/src/stores/compositorStore.ts:1936-1946`  
**Lines:** ~11 lines of implementation code  
**Status:** ⏳ **NEEDS MIGRATION**

**Current Implementation:**
```typescript
updateNestedCompLayerData(
  layerId: string,
  updates: Partial<NestedCompData>,
): void {
  const layer = this.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer || layer.type !== "nestedComp") return;
  
  const data = layer.data as NestedCompData;
  Object.assign(data, updates);
  this.project.meta.modified = new Date().toISOString();
}
```

**Usage Analysis:**
- ✅ **NOT CALLED ANYWHERE** - Grep found 0 usages
- ⚠️ `NestedCompProperties.vue` uses `store.updateLayerData()` instead (line 210)
- **Decision:** Should migrate to `layerStore/specialized.ts` OR consolidate into `updateLayerData` if redundant

**Target:** `layerStore/specialized.ts` OR verify if `updateLayerData` can handle this (check if it's redundant)

---

## Comparison with Migrated Methods

### ✅ Already Migrated (Pattern to Follow):

1. **`createTextLayer`** → `layerStore/specialized.ts` → `createTextLayerImpl()`
2. **`createSplineLayer`** → `layerStore/specialized.ts` → `createSplineLayerImpl()`
3. **`createShapeLayer`** → `layerStore/specialized.ts` → `createShapeLayerImpl()`
4. **`createCameraLayer`** → `layerStore/specialized.ts` → `createCameraLayerImpl()`
5. **`createVideoLayer`** → `layerStore/specialized.ts` → `createVideoLayerImpl()` (delegates to videoActions)

**Pattern:**
- Implementation in `layerStore/specialized.ts`
- Exported from `layerStore/index.ts`
- Delegated from `compositorStore.ts` (1-2 lines)

---

## Migration Plan

### Step 1: Move `createNestedCompLayer` to `layerStore/specialized.ts`

**Implementation:**
```typescript
export function createNestedCompLayer(
  compositorStore: CompositorStoreAccess,
  compositionId: string,
  name?: string,
): Layer {
  const layer = createLayer(compositorStore, "nestedComp", name || "Nested Comp");
  
  const nestedCompData: NestedCompData = {
    compositionId,
    speedMapEnabled: false,
    speedMap: undefined,
    timeRemapEnabled: false,
    timeRemap: undefined,
    flattenTransform: false,
    overrideFrameRate: false,
    frameRate: undefined,
  };
  
  layer.data = nestedCompData;
  compositorStore.project.meta.modified = new Date().toISOString();
  compositorStore.pushHistory();
  
  return layer;
}
```

**Changes:**
- Use `createLayer()` helper instead of `this.createLayer()`
- Use `compositorStore` parameter instead of `this`
- Follow same pattern as other specialized layer creation functions

---

### Step 2: Move `updateNestedCompLayerData` to `layerStore/specialized.ts`

**Implementation:**
```typescript
export function updateNestedCompLayerData(
  compositorStore: CompositorStoreAccess,
  layerId: string,
  updates: Partial<NestedCompData>,
): void {
  const layer = compositorStore.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer || layer.type !== "nestedComp") return;
  
  const data = layer.data as NestedCompData;
  Object.assign(data, updates);
  compositorStore.project.meta.modified = new Date().toISOString();
  compositorStore.pushHistory(); // Add missing pushHistory()
}
```

**Changes:**
- Use `compositorStore` parameter instead of `this`
- Add missing `pushHistory()` call (current implementation doesn't have it!)
- Follow same pattern as other layer update functions

**⚠️ NOTE:** Verify if this is redundant with `updateLayerData()` - if `updateLayerData` can handle `NestedCompData` updates, this method might not be needed.

---

### Step 3: Update `layerStore/index.ts`

**Add exports:**
```typescript
import {
  createNestedCompLayer as createNestedCompLayerImpl,
  updateNestedCompLayerData as updateNestedCompLayerDataImpl,
} from "./specialized";
```

**Add actions:**
```typescript
createNestedCompLayer(
  compositorStore: CompositorStoreAccess,
  compositionId: string,
  name?: string,
): Layer {
  return createNestedCompLayerImpl(compositorStore, compositionId, name);
},

updateNestedCompLayerData(
  compositorStore: CompositorStoreAccess,
  layerId: string,
  updates: Partial<NestedCompData>,
): void {
  updateNestedCompLayerDataImpl(compositorStore, layerId, updates);
},
```

---

### Step 4: Update `compositorStore.ts` to Delegate

**Replace implementation with delegation:**
```typescript
createNestedCompLayer(compositionId: string, name?: string): Layer {
  return useLayerStore().createNestedCompLayer(this, compositionId, name);
},

updateNestedCompLayerData(
  layerId: string,
  updates: Partial<NestedCompData>,
): void {
  useLayerStore().updateNestedCompLayerData(this, layerId, updates);
},
```

---

### Step 5: Verify Consumers

**Check if any consumers need updates:**
- ✅ `compositionActions/nesting.ts` - Creates layer directly, doesn't use method
- ✅ `NestedCompProperties.vue` - Uses `updateLayerData()`, doesn't use method
- ⚠️ Verify if methods are truly unused or if they should be used instead

---

## Verification Checklist

- [ ] Implementation moved to `layerStore/specialized.ts`
- [ ] Exported from `layerStore/index.ts`
- [ ] `compositorStore.ts` delegates correctly
- [ ] TypeScript compiles with 0 errors
- [ ] All consumers verified (even if unused)
- [ ] Missing `pushHistory()` added to `updateNestedCompLayerData`
- [ ] Documentation updated

---

## Questions to Resolve

1. **Is `updateNestedCompLayerData` redundant?** Should we use `updateLayerData()` instead?
2. **Should `compositionActions/nesting.ts` use `createNestedCompLayer`?** Currently creates layer directly
3. **Are these methods truly unused?** Or are they part of a public API that should be maintained?

---

---

## ✅ COMPLETED MIGRATIONS

### Nested Comp Methods (2026-01-12)

**Status:** ✅ **MIGRATED**

1. ✅ `createNestedCompLayer` → `layerStore/specialized.ts`
2. ✅ `updateNestedCompLayerData` → `layerStore/specialized.ts` (fixed missing `pushHistory()`)

**Changes:**
- Implementation moved to `layerStore/specialized.ts`
- Exported from `layerStore/index.ts`
- `compositorStore.ts` now delegates (2 lines each)
- Fixed bug: Added missing `pushHistory()` to `updateNestedCompLayerData`

**Verification:**
- ✅ TypeScript compiles (only test file errors, non-blocking)
- ✅ No linter errors
- ✅ Follows same pattern as other specialized layer creation methods

---

## ⏳ REMAINING METHODS WITH IMPLEMENTATION CODE

### Phase 2 Methods Still Implemented

**Found:** 2 methods still have implementation code in `compositorStore.ts`:

1. **`getFrameState`** (Lines 1075-1097) - ~23 lines
   - **Status:** ⏳ Needs migration to `animationStore`
   - **Current:** Calls `motionEngine.evaluate()` directly
   - **Target:** `animationStore` (frame evaluation domain)
   - **Usage:** Used by particle simulation methods, rendering pipeline

2. **`getInterpolatedValue`** (Lines 1361-1369) - ~9 lines
   - **Status:** ⏳ Needs migration to `keyframeStore`
   - **Current:** Calls `interpolateProperty()` directly
   - **Target:** `keyframeStore` (interpolation domain)
   - **Usage:** Convenience method for property interpolation

### Phase 5 Methods Still Implemented

**Found:** 1 method still has implementation code in `compositorStore.ts`:

1. **`loadInputs`** (Lines 529-605) - ~76 lines
   - **Status:** ⏳ Needs migration to `projectStore` or `compositionActions`
   - **Current:** Updates composition settings, assets, layer outPoints
   - **Target:** `projectStore` or `compositionActions` (ComfyUI integration domain)
   - **Usage:** Loads inputs from ComfyUI node

---

*Created: 2026-01-12*  
*Last Updated: 2026-01-12*  
*Purpose: Track remaining layer methods that need migration*
