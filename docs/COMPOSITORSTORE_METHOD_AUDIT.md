# CompositorStore Method Migration Audit

**Date:** 2026-01-12
**Purpose:** Verify EVERY method in compositorStore.ts is properly migrated

## Methods with Implementation Code (NOT Just Delegation)

### 1. `getActiveCompLayers()` - Line 409-412
**Status:** ⚠️ HAS IMPLEMENTATION
```typescript
getActiveCompLayers(): Layer[] {
  const comp = this.project.compositions[this.activeCompositionId];
  return comp?.layers || [];
}
```
**Should be:** Helper method, acceptable to stay OR migrate to projectStore
**Files calling:** Need to check

### 2. `getActiveComp()` - Line 417-419
**Status:** ⚠️ HAS IMPLEMENTATION
```typescript
getActiveComp(): Composition | null {
  return this.project.compositions[this.activeCompositionId] || null;
}
```
**Should be:** Helper method, acceptable to stay OR migrate to projectStore
**Files calling:** Need to check

### 3. `freezeFrameAtPlayhead()` - Line 931-940
**Status:** ⚠️ HAS IMPLEMENTATION
```typescript
freezeFrameAtPlayhead(layerId: string): void {
  const comp = this.getActiveComp();
  const storeWithFrame = {
    ...this,
    currentFrame: comp?.currentFrame ?? 0,
    fps: comp?.settings.fps ?? 30,
    pushHistory: this.pushHistory.bind(this),
  };
  useLayerStore().freezeFrameAtPlayhead(storeWithFrame, layerId);
}
```
**Should be:** Migrated to layerStore, but wrapper creates storeWithFrame
**Files calling:** Need to check

### 4. `splitLayerAtPlayhead()` - Line 949-959
**Status:** ⚠️ HAS IMPLEMENTATION
```typescript
splitLayerAtPlayhead(layerId: string): Layer | null {
  const comp = this.getActiveComp();
  const storeWithFrame = {
    ...this,
    currentFrame: comp?.currentFrame ?? 0,
    fps: comp?.settings.fps ?? 30,
    pushHistory: this.pushHistory.bind(this),
  };
  return useLayerStore().splitLayerAtPlayhead(storeWithFrame, layerId);
}
```
**Should be:** Migrated to layerStore, but wrapper creates storeWithFrame
**Files calling:** Need to check

### 5. `setPropertyAnimated()` - Line 1314-1335
**Status:** ⚠️ HAS IMPLEMENTATION
```typescript
setPropertyAnimated(
  layerId: string,
  propertyPath: string,
  animated: boolean,
): void {
  useKeyframeStore().setPropertyAnimated(
    this,
    layerId,
    propertyPath,
    animated,
    () => {
      this.addKeyframe(  // <-- CALLS THIS METHOD
        layerId,
        propertyPath,
        findPropertyByPath(
          this.getActiveCompLayers().find((l) => l.id === layerId)!,
          propertyPath,
        )?.value,
      );
    },
  );
}
```
**Should be:** Migrated to keyframeStore, but callback calls `this.addKeyframe`
**Files calling:** Need to check

### 6. `clearAudio()` - Line 2138-2141
**Status:** ⚠️ HAS IMPLEMENTATION
```typescript
clearAudio(): void {
  useAudioStore().clear();
  this.pathAnimators.clear();  // <-- DIRECT STATE MUTATION
}
```
**Should be:** Migrated to audioStore, but also clears pathAnimators
**Files calling:** Need to check

### 7. `getAllMappedValuesAtFrame()` - Line 2190-2193
**Status:** ⚠️ HAS IMPLEMENTATION
```typescript
getAllMappedValuesAtFrame(frame?: number): Map<TargetParameter, number> {
  const targetFrame = frame ?? this.getActiveComp()?.currentFrame ?? 0;
  return useAudioStore().getAllMappedValuesAtFrame(targetFrame);
}
```
**Should be:** Migrated to audioStore, but wrapper gets currentFrame
**Files calling:** Need to check

### 8. `isBeatAtCurrentFrame()` - Line 2203-2206
**Status:** ⚠️ HAS IMPLEMENTATION
```typescript
isBeatAtCurrentFrame(): boolean {
  const frame = this.getActiveComp()?.currentFrame ?? 0;
  return useAudioStore().isBeatAtFrame(frame);
}
```
**Should be:** Migrated to audioStore, but wrapper gets currentFrame
**Files calling:** Need to check

### 9. `confirmSegmentMask()` - Line 1086-1103
**Status:** ⚠️ HAS IMPLEMENTATION
```typescript
async confirmSegmentMask(layerName?: string): Promise<Layer | null> {
  if (!this.segmentPendingMask || !this.sourceImage) {
    return null;
  }
  const layer = await segmentationActions.createLayerFromMask(
    this,
    this.sourceImage,
    this.segmentPendingMask,
    layerName,
    false,
  );
  this.clearSegmentPendingMask();
  return layer;
}
```
**Should be:** Delegates to segmentationActions, but has wrapper logic
**Files calling:** Need to check

### 10. `loadInputs()` - Line 503-515
**Status:** ✅ DELEGATES (but has pushHistory call)
```typescript
loadInputs(inputs: {...}): void {
  useProjectStore().loadInputs(this, inputs);
  this.pushHistory();  // <-- EXTRA CALL
}
```
**Should be:** Delegates but adds pushHistory
**Files calling:** Need to check

## Getters with Implementation Code

### 1. `currentFrame` - Line 304-307
**Status:** ⚠️ HAS IMPLEMENTATION
```typescript
currentFrame(state): number {
  const comp = state.project.compositions[state.activeCompositionId];
  return comp?.currentFrame || 0;
}
```
**Should be:** Reads from composition state
**Files calling:** Need to check

### 2. `layers` - Line 313-316
**Status:** ⚠️ HAS IMPLEMENTATION
```typescript
layers(state): Layer[] {
  const comp = state.project.compositions[state.activeCompositionId];
  return comp?.layers || [];
}
```
**Should be:** Reads from composition state
**Files calling:** Need to check

### 3. `visibleLayers` - Line 317-321
**Status:** ⚠️ HAS IMPLEMENTATION
```typescript
visibleLayers(state): Layer[] {
  const comp = state.project.compositions[state.activeCompositionId];
  const layers = comp?.layers || [];
  return layers.filter((l: Layer) => l.visible);
}
```
**Should be:** Filters layers
**Files calling:** Need to check

### 4. `displayedLayers` - Line 323-331
**Status:** ⚠️ HAS IMPLEMENTATION
```typescript
displayedLayers(state): Layer[] {
  const comp = state.project.compositions[state.activeCompositionId];
  const layers = comp?.layers || [];
  const uiStore = useUIStore();
  if (uiStore.hideMinimizedLayers) {
    return layers.filter((l: Layer) => !l.minimized);
  }
  return layers;
}
```
**Should be:** Filters layers based on UI state
**Files calling:** Need to check

### 5. `selectedLayers` - Line 349-355
**Status:** ⚠️ HAS IMPLEMENTATION
```typescript
selectedLayers(state): Layer[] {
  const comp = state.project.compositions[state.activeCompositionId];
  const selectionStore = useSelectionStore();
  return (comp?.layers || []).filter((l: Layer) =>
    selectionStore.selectedLayerIds.includes(l.id),
  );
}
```
**Should be:** Filters layers based on selection
**Files calling:** Need to check

### 6. `selectedLayer` - Line 356-365
**Status:** ⚠️ HAS IMPLEMENTATION
```typescript
selectedLayer(state): Layer | null {
  const selectionStore = useSelectionStore();
  if (selectionStore.selectedLayerIds.length !== 1) return null;
  const comp = state.project.compositions[state.activeCompositionId];
  return (
    (comp?.layers || []).find(
      (l: Layer) => l.id === selectionStore.selectedLayerIds[0],
    ) || null
  );
}
```
**Should be:** Finds single selected layer
**Files calling:** Need to check

### 7. `cameraLayers` - Line 394-398
**Status:** ⚠️ HAS IMPLEMENTATION
```typescript
cameraLayers(state): Layer[] {
  const comp = state.project.compositions[state.activeCompositionId];
  const layers = comp?.layers || [];
  return layers.filter((l: Layer) => l.type === "camera");
}
```
**Should be:** Filters camera layers
**Files calling:** Need to check

## Next Steps

1. Find ALL files that call these methods
2. Verify each method is properly migrated
3. Check if consumers need updates
4. Document migration status
