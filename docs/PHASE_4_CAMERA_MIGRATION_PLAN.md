# Phase 4 Camera Migration Plan

> **Date:** 2026-01-12  
> **Status:** ⏳ IN PROGRESS

---

## Method to Migrate

### `cameraLayers` Getter - Camera Layer Query

**CURRENT (compositorStore.ts:421-424):**
```typescript
cameraLayers(state): Layer[] {
  const comp = state.project.compositions[state.activeCompositionId];
  return (comp?.layers || []).filter((l: Layer) => l.type === "camera");
}
```

**CHANGE:** Move to `layerStore` as a query method  
**TARGET:** `ui/src/stores/layerStore/hierarchy.ts` (add new query function)

**AFTER (compositorStore.ts):**
```typescript
cameraLayers(): Layer[] {
  return useLayerStore().getCameraLayers(this);
}
```

**AFTER (layerStore/hierarchy.ts):**
```typescript
/**
 * Get all camera layers in the active composition
 * @param compositorStore - The compositor store instance
 * @returns Array of camera layers
 */
export function getCameraLayers(compositorStore: CompositorStoreAccess): Layer[] {
  const layers = compositorStore.getActiveCompLayers?.() ?? [];
  return layers.filter((l: Layer) => l.type === "camera");
}
```

**Also Add To:** `ui/src/stores/layerStore/index.ts` (export and expose)

---

## Summary

- **`cameraLayers`**: Move to `layerStore.getCameraLayers()` as a query method

---

*Created: 2026-01-12*
