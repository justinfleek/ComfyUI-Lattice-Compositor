# CompositorStore Breakdown - What's Left After Phase 1

> **Date:** 2026-01-12  
> **Purpose:** Document what remains in compositorStore after Phase 1 layer migration  
> **Status:** Phase 1 ✅ COMPLETE - Layers migrated, ~2,500 lines remaining

---

## Current State (After Phase 1)

**File:** `ui/src/stores/compositorStore.ts`  
**Size:** ~3,292 lines (down from ~3,500+ before Phase 1)  
**Status:** Still contains 8+ domains that need migration

---

## What's Left in CompositorStore

### ✅ Phase 1: Layer Domain (COMPLETE)
- **Migrated:** 46 layer methods → `layerStore`
- **Status:** All layer operations now delegate to `layerStore`
- **Remaining:** Delegation methods (will be deleted in Phase 5)

---

### ⏳ Phase 2: Keyframes, Animation & Expressions (Weeks 11-18)

**Keyframe Domain:**
- `keyframes: Map<string, Keyframe[]>` - Keyframe storage
- `interpolationType: InterpolationType` - Default interpolation
- ~35 keyframe methods (add, delete, update, interpolate, etc.)
- **Target:** `keyframeStore.ts`

**Animation Domain:**
- `currentFrame: number` - Current playback frame
- `isPlaying: boolean` - Playback state
- `fps: number` - Frame rate
- `timelineZoom: number` - Timeline zoom level
- `snapConfig: SnapConfig` - Snap settings
- ~20 animation methods (play, pause, setFrame, nextFrame, etc.)
- **Target:** `animationStore.ts`

**Expression Domain:**
- `propertyDriverSystem: PropertyDriverSystem | null` - Expression system
- `propertyDrivers: PropertyDriver[]` - Property driver configs
- ~15 expression methods (evaluate, addDriver, etc.)
- **Target:** `expressionStore.ts`

**New Service:**
- `services/propertyEvaluator.ts` - Cross-domain property evaluation

---

### ⏳ Phase 3: Audio & Effects (Weeks 19-26)

**Audio Domain (DUPLICATE STATE - CRITICAL):**
- `audioBuffer: AudioBuffer | null` - Audio data (DUPLICATE - also in audioStore)
- `audioAnalysis: AudioAnalysis | null` - Analysis data (DUPLICATE)
- `audioFile: File | null` - Audio file reference
- `audioVolume: number` - Volume level (DUPLICATE)
- `audioMuted: boolean` - Mute state (DUPLICATE)
- `audioLoadingState: "idle" | "loading" | "loaded" | "error"` - Loading state (DUPLICATE)
- `audioMappings: AudioMapping[]` - Audio mappings (DUPLICATE)
- `audioReactiveMappings: Map<string, TargetParameter[]>` - Reactive mappings (DUPLICATE)
- `pathAnimators: Map<string, PathAnimatorAccess>` - Path animators
- ~15 audio methods
- **Target:** Expand `audioStore.ts` (already exists)
- **CRITICAL:** Must DELETE duplicate state from compositorStore

**Effect Domain:**
- Effect state (if any - need to verify)
- ~20 effect methods
- **Target:** `effectStore.ts` (new store)

**Text Animator Domain:**
- Text animator methods (already migrated to layerStore in Phase 1)
- **Status:** ✅ Already in layerStore

---

### ⏳ Phase 4: Camera & Physics (Weeks 27-34)

**Camera Domain:**
- `cameras: Map<string, Camera3D>` - All cameras by ID
- `cameraKeyframes: Map<string, CameraKeyframe[]>` - Keyframes per camera
- `activeCameraId: string | null` - Active camera
- `viewportState: ViewportState` - Multi-view layout state
- `viewOptions: ViewOptions` - Display options (wireframes, etc.)
- ~10 camera methods
- **Target:** `cameraStore.ts` (new store)

**Physics Domain:**
- Physics simulation state (need to verify exact properties)
- ~8 physics methods
- **Target:** `physicsStore.ts` (new store)

---

### ⏳ Phase 5: Project & Cleanup (Weeks 35-40)

**Project Domain:**
- `project: LatticeProject` - Main project data
- `activeCompositionId: string` - Active composition
- `openCompositionIds: string[]` - Open composition tabs
- `compositionBreadcrumbs: string[]` - Navigation history
- `selectedAssetId: string | null` - Selected asset
- ~12 project/composition methods
- **Target:** `projectStore.ts` (new store)

**UI State Domain:**
- `segmentToolActive: boolean` - Segmentation tool state
- `segmentMode: "point" | "box"` - Segmentation mode
- `segmentPendingMask: {...}` - Pending mask data
- `segmentBoxStart: { x: number; y: number } | null` - Box start point
- `segmentIsLoading: boolean` - Loading state
- `shapeToolOptions: {...}` - Shape tool options
- `curveEditorVisible: boolean` - Curve editor visibility
- `hideMinimizedLayers: boolean` - Hide minimized toggle
- **Target:** `uiStore.ts` (new store)

**Autosave Domain:**
- `autosaveEnabled: boolean` - Autosave toggle
- `autosaveIntervalMs: number` - Autosave interval
- `autosaveTimerId: number | null` - Timer ID
- `lastSaveTime: number | null` - Last save timestamp
- `lastSaveProjectId: string | null` - Last saved project ID
- `hasUnsavedChanges: boolean` - Unsaved changes flag
- **Target:** `projectStore.ts` (with project domain)

**Frame Cache Domain:**
- `frameCacheEnabled: boolean` - Cache toggle
- `projectStateHash: string` - State hash for cache invalidation
- **Target:** `projectStore.ts` (with project domain)

**ComfyUI Domain:**
- `comfyuiNodeId: string | null` - ComfyUI node ID
- `sourceImage: string | null` - Source image
- `depthMap: string | null` - Depth map
- **Target:** `projectStore.ts` (with project domain)

**History Domain:**
- `historyStack: LatticeProject[]` - Undo/redo stack
- `historyIndex: number` - Current history index
- **Status:** ✅ Already exists as `historyStore.ts` (just needs cleanup)

---

## Circular Dependency Prevention

### ✅ Patterns Already Defined

**Pattern 1: Return Data, Don't Mutate**
```typescript
// historyStore.ts - ALREADY USES THIS
undo(): LatticeProject | null {
  return structuredClone(toRaw(this.stack[this.index]));
}
```

**Pattern 2: Callbacks Instead of Imports**
```typescript
// playbackStore.ts - ALREADY USES THIS
play(fps, frameCount, currentFrame, onFrame: (frame: number) => void) {
  onFrame(newFrame);  // Caller decides what to do
}
```

**Pattern 3: Parameter Passing**
```typescript
// audioStore.ts - ALREADY USES THIS
loadAudio(file: File, projectId: string): Promise<void> {
  // projectId passed in, not imported from compositorStore
}
```

**Pattern 4: Explicit Store-to-Store (When Necessary)**
```typescript
// keyframeStore.ts
addKeyframe(layerId: string, propertyPath: string, value: number, frame?: number) {
  // Read from other store
  const layer = useLayerStore().getLayerById(layerId);
  
  // Mutate own domain
  this.keyframes[layerId][propertyPath].push({ frame, value });
  
  // Explicit history push
  useHistoryStore().pushState(this.getSnapshot());
}
```

### ✅ Dependency Graph (Target)

```
                    historyStore
                         ↑
                         │ (pushState)
    ┌────────────────────┼────────────────────┐
    │                    │                    │
layerStore ←──── keyframeStore ←──── audioStore
    │                    │                    │
    │                    │                    │
    └────────────────────┼────────────────────┘
                         │
                    projectStore
                         ↑
                    (reads project)
```

**Rules:**
- ✅ Stores can call other stores via `useXStore()` for reads
- ✅ Stores can call other stores' actions for writes
- ❌ NO circular action chains (Store A → Store B → Store A)
- ✅ History is explicit (the initiating store pushes)

---

## Do We Need CompositorStore After Migration?

### ❌ NO - Phase 5 DELETES compositorStore

**From MASTER_REFACTOR_PLAN.md:**
- **Phase 5 Goal:** "Migrate project domain methods and **DELETE compositorStore**"
- **Exit Criteria:** "compositorStore.ts DELETED"
- **Final Step:** "DELETE compositorStore - Final step"

**Timeline:**
1. Phase 1-4: Migrate all domains to new stores
2. Phase 5: Migrate remaining project/UI state
3. Phase 5: Update all consumers to use domain stores directly
4. Phase 5: **DELETE compositorStore.ts** (3,292 lines)

**After Phase 5:**
- ✅ All functionality in domain stores
- ✅ No compositorStore file exists
- ✅ No references to compositorStore remain
- ✅ 13 focused domain stores replace 1 god object

---

## Lazy Code Fixes - Where Do They Come In?

### Strategy: Fix During Migration (Prevents Spreading Bad Patterns)

**From MASTER_REFACTOR_STATUS.md:**

| Phase | Lazy Code Fixes | Rationale |
|-------|----------------|----------|
| **Phase 1** | ✅ Fixed `as any` in migrated code | Prevent spreading bad patterns |
| **Phase 2** | Fix ~100 `\|\| 0` in expression code<br>Fix ~30 `: any` in expression code<br>Fix ~20 `as any` in keyframe code | Fix types as code moves |
| **Phase 3** | Fix ~50 `: any` in effect types<br>Fix ~30 `as any` in effect renderers<br>Fix ~20 `??`/`?.` unnecessary | Fix types as code moves |
| **Phase 4** | Fix types in camera/physics code | Fix types as code moves |
| **Phase 5** | Fix types in project/UI code | Fix types as code moves |

**Total Planned Fixes:** ~360 issues (~7% of total ~5,289)

**Why Only 7%?**
- Focus on fixing types **during migration** (prevents spreading)
- Most defensive code (`|| 0`, `??`, `?.`) becomes unnecessary **after** types are fixed
- Remaining ~93% can be cleaned up **after** all stores are migrated

**Example from Phase 1:**
```typescript
// BEFORE (lazy code):
const layer = compositorStore.getLayerById?.(layerId) ?? null;

// AFTER (fixed during migration):
const layer = getLayerById(compositorStore, layerId);
// ✅ Proper type, no optional chaining needed
```

---

## Summary

### What's Left in CompositorStore:
1. ✅ **Layer Domain** - COMPLETE (delegates to layerStore)
2. ⏳ **Keyframes** - Phase 2 → keyframeStore
3. ⏳ **Animation** - Phase 2 → animationStore
4. ⏳ **Expressions** - Phase 2 → expressionStore
5. ⏳ **Audio** - Phase 3 → audioStore (CRITICAL: duplicate state)
6. ⏳ **Effects** - Phase 3 → effectStore
7. ⏳ **Camera** - Phase 4 → cameraStore
8. ⏳ **Physics** - Phase 4 → physicsStore
9. ⏳ **Project** - Phase 5 → projectStore
10. ⏳ **UI State** - Phase 5 → uiStore
11. ⏳ **Autosave** - Phase 5 → projectStore
12. ⏳ **History** - Already in historyStore (just cleanup)

### Circular Dependencies:
- ✅ **NO** - Patterns prevent circular dependencies
- ✅ Stores can call other stores for reads/writes
- ❌ NO circular action chains

### CompositorStore After Migration:
- ❌ **NO** - Phase 5 DELETES compositorStore entirely
- ✅ All functionality in 13 domain stores
- ✅ No god object remains

### Lazy Code Fixes:
- ✅ Fix during migration (prevents spreading)
- ✅ ~360 issues planned (~7% of total)
- ✅ Remaining ~93% cleaned up after migration

---

*Created: 2026-01-12*  
*Purpose: Answer user questions about compositorStore breakdown*
