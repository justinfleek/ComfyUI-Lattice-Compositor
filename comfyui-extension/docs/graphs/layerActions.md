# Dependency Graph: layerActions.ts

> **Generated:** 2026-01-10
> **Updated:** 2026-01-10 (layerStore modularized into 8 files)
> **Purpose:** Phase 1 migration planning - layer actions → layerStore

## layerStore Modularization (2026-01-10)

The layerStore has been split into 8 modules, all under 500 lines:

```
stores/layerStore/
├── types.ts       (159 lines) - Type definitions + CompositorStoreAccess interface
├── crud.ts        (366 lines) - CRUD operations
├── clipboard.ts   (131 lines) - Copy/paste/cut (imports deleteLayer directly)
├── hierarchy.ts   (233 lines) - Parenting, 3D mode, hierarchy queries
├── specialized.ts (278 lines) - Text/spline/shape layer, source replacement
├── time.ts        (429 lines) - Time manipulation
├── batch.ts       (180 lines) - Batch operations
└── index.ts       (401 lines) - Store definition with type-safe API
```

**Architectural decisions:**
- All methods use `CompositorStoreAccess` interface instead of `any`
- clipboard.ts imports deleteLayer directly (no awkward function injection)
- Specialized layer creation (spline, shape, text) grouped in specialized.ts

---

## File Inventory

| File | Lines | Exports | Pattern |
|------|-------|---------|---------|
| `stores/actions/layerActions.ts` | 1,847 | 29 functions, 2 interfaces | DI: `store: LayerStore` |
| `stores/actions/layers/layerTimeActions.ts` | 404 | 7 functions | DI: `store: LayerTimeStore` |
| `stores/actions/layer/splineActions.ts` | 663 | ~15 functions | DI: `store: LayerStore` |
| `stores/actions/layer/layerDefaults.ts` | 430 | ~10 functions | Pure functions |
| **TOTAL** | **3,344** | **~61 exports** | |

---

## Module Structure

```
stores/actions/
├── layerActions.ts          # Main layer CRUD (1,847 lines)
│   ├── createLayer()
│   ├── deleteLayer()
│   ├── duplicateLayer()
│   ├── updateLayer()
│   ├── moveLayer()
│   ├── setLayerParent()
│   ├── copySelectedLayers()
│   ├── pasteLayers()
│   ├── cutSelectedLayers()
│   └── ... (20 more)
│
├── layers/
│   └── layerTimeActions.ts  # Time operations (404 lines)
│       ├── timeStretchLayer()
│       ├── reverseLayer()
│       ├── freezeFrameAtPlayhead()
│       ├── splitLayerAtPlayhead()
│       ├── enableSpeedMap()
│       ├── disableSpeedMap()
│       └── toggleSpeedMap()
│
└── layer/
    ├── splineActions.ts     # Spline operations (663 lines)
    │   ├── addSplineControlPoint()
    │   ├── deleteSplineControlPoint()
    │   ├── updateSplineControlPoint()
    │   ├── smoothSplineHandles()
    │   ├── simplifySpline()
    │   └── ... (10 more)
    │
    ├── layerDefaults.ts     # Default layer data (430 lines)
    │   ├── getDefaultLayerData()
    │   ├── createDefaultImageLayer()
    │   ├── createDefaultVideoLayer()
    │   └── ... (layer type defaults)
    │
    └── index.ts             # Barrel export
```

---

## Dependencies (What layerActions imports)

### External Dependencies
| Import | From | Purpose |
|--------|------|---------|
| `toRaw` | vue | Reactive unwrapping |
| `Layer`, `Keyframe`, etc. | @/types/project | Type definitions |
| `createAnimatableProperty` | @/types/project | Layer property creation |
| `clearLayerCache`, `markLayerDirty` | @/services/layerEvaluationCache | Cache invalidation |
| `textToVectorFromUrl` | @/services/textToVector | Text vectorization |
| `BezierPath` | @/types/shapes | Shape types |
| `storeLogger` | @/utils/logger | Logging |

### Internal Dependencies
| Import | From | Purpose |
|--------|------|---------|
| `useSelectionStore` | ../selectionStore | Selection state access |
| `getDefaultLayerData` | ./layer/layerDefaults | Layer defaults |
| `*` (re-export) | ./layers/layerTimeActions | Time operations |

---

## Importers (Who uses layerActions)

| File | Import Type | Methods Used |
|------|-------------|--------------|
| `stores/compositorStore.ts` | Direct | All - delegates to action functions |
| `services/ai/actionExecutor.ts` | Direct | createLayer, updateLayer, deleteLayer, etc. |
| `components/timeline/EnhancedLayerTrack.vue` | Direct | updateLayer, moveLayer |
| `stores/actions/layers/layerTimeActions.ts` | Type only | `LayerStore` interface |
| `stores/actions/layer/splineActions.ts` | Type only | `LayerStore` interface |
| `stores/actions/layer/layerDefaults.ts` | Indirect | Used by layerActions |
| `stores/actions/index.ts` | Re-export | Barrel file |

---

## Circular Dependency Analysis

### Current State: NO CIRCULAR DEPS ✅

```
layerActions.ts
  ├─→ selectionStore.ts (OK - separate store)
  ├─→ layerDefaults.ts (OK - pure functions)
  ├─→ layerTimeActions.ts (OK - re-export only)
  └─→ types/project.ts (OK - types only)

compositorStore.ts
  └─→ layerActions.ts (OK - one-way)

actionExecutor.ts
  └─→ layerActions.ts (OK - one-way)
```

### Design Pattern: Dependency Injection

The `LayerStore` interface enables DI:

```typescript
export interface LayerStore {
  project: { composition: { width: number; height: number }; meta: { modified: string } };
  clipboard: { layers: Layer[]; keyframes: ClipboardKeyframe[] };
  getActiveComp(): { settings: {...}; layers: Layer[] } | null;
  getActiveCompLayers(): Layer[];
  pushHistory(): void;
}
```

All action functions accept `store: LayerStore` as first param:
```typescript
export function createLayer(store: LayerStore, type: string, options?: CreateLayerOptions): Layer
export function deleteLayer(store: LayerStore, layerId: string, options?: DeleteLayerOptions): void
```

---

## Migration Strategy

### Phase 1A: Create layerStore.ts (Week 3-4) ✅ COMPLETE

1. ✅ Create `stores/layerStore.ts` implementing the `LayerStore` interface
2. ✅ Move clipboard state to layerStore
3. ✅ Export from stores/index.ts

### Phase 1B: Migrate Core Methods (Week 5-6) ✅ COMPLETE

Move into layerStore as methods:
- ✅ `createLayer()` → `layerStore.createLayer()` (2026-01-10)
- ✅ `deleteLayer()` → `layerStore.deleteLayer()` (2026-01-10)
- ✅ `updateLayer()` → `layerStore.updateLayer()` (2026-01-10)
- ✅ `updateLayerData()` → `layerStore.updateLayerData()` (2026-01-10)
- ✅ `duplicateLayer()` → `layerStore.duplicateLayer()` (2026-01-10)
- ✅ `moveLayer()` → `layerStore.moveLayer()` (2026-01-10)
- ✅ `setLayerParent()` → `layerStore.setLayerParent()` (2026-01-10)
- ✅ `copySelectedLayers()` → `layerStore.copySelectedLayers()` (2026-01-10)
- ✅ `pasteLayers()` → `layerStore.pasteLayers()` (2026-01-10)
- ✅ `cutSelectedLayers()` → `layerStore.cutSelectedLayers()` (2026-01-10)
- ✅ `toggleLayer3D()` → `layerStore.toggleLayer3D()` (2026-01-10)
- ✅ `createTextLayer()` → `layerStore.createTextLayer()` (2026-01-10)
- ✅ `createSplineLayer()` → `layerStore.createSplineLayer()` (2026-01-10)
- ✅ `createShapeLayer()` → `layerStore.createShapeLayer()` (2026-01-10)
- ✅ `replaceLayerSource()` → `layerStore.replaceLayerSource()` (2026-01-10)
- ✅ `selectLayer()` → `layerStore.selectLayer()` (2026-01-10)
- ✅ `deselectLayer()` → `layerStore.deselectLayer()` (2026-01-10)
- ✅ `clearSelection()` → `layerStore.clearSelection()` (2026-01-10)
- ✅ `sequenceLayers()` → `layerStore.sequenceLayers()` (2026-01-10)
- ✅ `applyExponentialScale()` → `layerStore.applyExponentialScale()` (2026-01-10)
- ✅ `timeStretchLayer()` → `layerStore.timeStretchLayer()` (2026-01-10)
- ✅ `reverseLayer()` → `layerStore.reverseLayer()` (2026-01-10)
- ✅ `freezeFrameAtPlayhead()` → `layerStore.freezeFrameAtPlayhead()` (2026-01-10)
- ✅ `splitLayerAtPlayhead()` → `layerStore.splitLayerAtPlayhead()` (2026-01-10)
- ✅ `enableSpeedMap()` → `layerStore.enableSpeedMap()` (2026-01-10)
- ✅ `disableSpeedMap()` → `layerStore.disableSpeedMap()` (2026-01-10)
- ✅ `toggleSpeedMap()` → `layerStore.toggleSpeedMap()` (2026-01-10)
- ✅ `compositorStore` delegates to `layerStore` (23 methods + addLayer alias)
- ⚠️ 7 methods in layerStore not yet delegated: enableSpeedMap, disableSpeedMap, toggleSpeedMap, clearSelection, getLayerById, getLayerChildren, getLayerDescendants

### Phase 1B-MOD: Modularize layerStore ✅ COMPLETE (2026-01-10)

layerStore.ts was at 1,680 lines (over 500 line limit). Split into 8 modules:
- `types.ts` (159 lines) - Type definitions + CompositorStoreAccess interface
- `crud.ts` (366 lines) - CRUD operations
- `clipboard.ts` (131 lines) - Copy/paste/cut (direct deleteLayer import)
- `hierarchy.ts` (233 lines) - Parenting, 3D mode, hierarchy queries
- `specialized.ts` (278 lines) - Text/spline/shape layer, source replacement
- `time.ts` (429 lines) - Time manipulation
- `batch.ts` (180 lines) - Batch operations
- `index.ts` (401 lines) - Store definition with type-safe CompositorStoreAccess API

**Quality fixes applied:**
- Module consistency: All specialized layer creation in specialized.ts
- No function injection: clipboard.ts imports deleteLayer directly
- Type safety: All methods use CompositorStoreAccess (no `any`)

### Phase 1C: Migrate Remaining (Week 7-8)

- Move splineActions into layerStore (~15 methods)
- Update all 7 importers

### Phase 1D: Delete layerActions.ts (Week 9-10)

After all consumers updated:
- Delete `stores/actions/layerActions.ts`
- Delete `stores/actions/layers/layerTimeActions.ts`
- Delete `stores/actions/layer/splineActions.ts`
- Keep `stores/actions/layer/layerDefaults.ts` (pure functions)

---

## Cross-Domain Dependencies

These methods need access to OTHER stores:

| Method | Needs | Strategy |
|--------|-------|----------|
| `splitLayerAtPlayhead()` | `currentFrame` | Import animationStore |
| `freezeFrameAtPlayhead()` | `currentFrame` | Import animationStore |
| `timeStretchLayer()` | `frameCount` | Import animationStore |
| `copySelectedLayers()` | `selectedLayerIds` | Import selectionStore |
| `pasteLayers()` | `selectedLayerIds` | Import selectionStore |
| `cutSelectedLayers()` | `selectedLayerIds` | Import selectionStore |
| `nestSelectedLayers()` | `selectedLayerIds` | Import selectionStore |
| `reverseSelectedLayers()` | `selectedLayerIds` | Import selectionStore |

---

## Exported Functions (29 total + 7 time actions) - 27 migrated

### Layer CRUD (10) - 10 migrated
- ✅ `createLayer(store, type, options)` → layerStore
- ✅ `createTextLayer(store, text, options)` → layerStore
- ✅ `createSplineLayer(store)` → layerStore
- ✅ `createShapeLayer(store, shapeType)` → layerStore
- ✅ `deleteLayer(store, layerId, options)` → layerStore
- ✅ `duplicateLayer(store, layerId, options)` → layerStore
- ✅ `updateLayer(store, layerId, updates)` → layerStore
- ✅ `updateLayerData(store, layerId, dataUpdates)` → layerStore
- ✅ `replaceLayerSource(store, layerId, newSource)` → layerStore
- ✅ `moveLayer(store, layerId, newIndex)` → layerStore

### Clipboard (4) - 3 migrated
- ✅ `copySelectedLayers(store)` → layerStore
- ✅ `pasteLayers(store)` → layerStore
- ✅ `cutSelectedLayers(store)` → layerStore
- (clipboard state in store)

### Hierarchy (3) - 2 migrated
- ✅ `setLayerParent(store, layerId, parentId)` → layerStore
- ✅ `toggleLayer3D(store, layerId)` → layerStore
- `getLayerChildren(store, layerId)`
- `getLayerDescendants(store, layerId)`

### Selection Helpers (3) - 3 migrated
- ✅ `selectLayer(store, layerId)` → layerStore
- ✅ `deselectLayer(store, layerId)` → layerStore
- ✅ `clearSelection(store)` → layerStore

### Query (2)
- `getLayerById(store, layerId)`
- `getLayerChildren(store, layerId)`

### Path Operations (2)
- `copyPathToPosition(store, layerId, pathId, position)`
- (more in splineActions)

### Batch Operations (2) - 2 migrated
- ✅ `sequenceLayers(store, layerIds, options)` → layerStore
- ✅ `applyExponentialScale(store, layerId, options)` → layerStore

### Interfaces (2)
- `LayerStore`
- `LayerSourceReplacement`
- `DeleteLayerOptions`
- `SequenceLayersOptions`
- `ExponentialScaleOptions`

---

## Risk Assessment

| Risk | Level | Mitigation |
|------|-------|------------|
| Breaking compositorStore delegation | HIGH | Keep delegation working during migration |
| Breaking actionExecutor AI actions | HIGH | Update imports incrementally |
| Breaking EnhancedLayerTrack.vue | MEDIUM | Update after core migration |
| Type mismatches | LOW | TypeScript will catch |
| Missing history calls | LOW | Existing pattern preserved |

---

*Document Version: 1.0*
*Generated: 2026-01-10*
