# compositorStore.ts Modularization Plan

> Generated: 2026-01-10
> File: `ui/src/stores/compositorStore.ts`
> Lines: 3,292 | Users: 101

## Executive Summary

The compositorStore is the central state store with 101 dependents. It already delegates to 16 action modules, making it a **facade pattern** store. The best modularization approach is to extract state slices to separate stores while keeping thin wrappers in compositorStore for backwards compatibility.

---

## State Slices Analysis

### 1. Core Project State (MUST STAY)
**Lines:** ~50 | **Coupling:** Critical

```typescript
project: LatticeProject;
activeCompositionId: string;
openCompositionIds: string[];
compositionBreadcrumbs: string[];
```

**Why it must stay:** Everything depends on `project.compositions[activeCompositionId]`. This is the heart of the store.

---

### 2. Audio State (EXTRACT FIRST - Biggest Win)
**Lines:** ~20 state properties + ~50 action wrappers | **Coupling:** Self-contained

```typescript
// Audio core
audioBuffer: AudioBuffer | null;
audioAnalysis: AudioAnalysis | null;
audioFile: File | null;
audioVolume: number;
audioMuted: boolean;

// Audio loading
audioLoadingState: "idle" | "decoding" | "analyzing" | "complete" | "error";
audioLoadingProgress: number;
audioLoadingPhase: string;
audioLoadingError: string | null;

// Audio mappings (legacy)
audioMappings: Map<string, AudioParticleMapping[]>;

// Audio reactive system
peakData: PeakData | null;
audioReactiveMappings: AudioMapping[];
audioReactiveMapper: AudioReactiveMapper | null;
pathAnimators: Map<string, AudioPathAnimator>;
```

**Actions to migrate (lines 2228-2335, 2392-2422):**
- `loadAudio`, `cancelAudioLoad`, `clearAudio`
- `setAudioVolume`, `setAudioMuted`, `toggleAudioMute`
- `getAudioFeatureAtFrame`, `applyAudioToParticles`, `removeLegacyAudioMapping`
- `getAudioMappingsForLayer`, `setPeakData`, `detectAudioPeaks`
- `addAudioMapping`, `removeAudioMapping`, `updateAudioMapping`, `getAudioMappings`
- `getMappedValueAtFrame`, `getAllMappedValuesAtFrame`, `getActiveMappingsForLayer`
- `getAudioReactiveValuesForLayer`, `isBeatAtCurrentFrame`
- `convertAudioToKeyframes`, `getAudioAmplitudeAtFrame`
- `convertFrequencyBandsToKeyframes`, `convertAllAudioFeaturesToKeyframes`
- `getFrequencyBandAtFrame`
- Path animator methods: `createPathAnimator`, `setPathAnimatorPath`, etc.
- `initializeAudioReactiveMapper`

**Target:** `useAudioStore()` (already exists but underused)

**Estimated reduction:** ~600 lines

---

### 3. Camera System State (EXTRACT SECOND)
**Lines:** ~10 state + ~30 action wrappers | **Coupling:** Moderate

```typescript
cameras: Map<string, Camera3D>;
cameraKeyframes: Map<string, CameraKeyframe[]>;
activeCameraId: string | null;
viewportState: ViewportState;
viewOptions: ViewOptions;
```

**Actions to migrate (lines 2187-2222):**
- `createCameraLayer`, `getCamera`, `updateCamera`, `setActiveCamera`, `deleteCamera`
- `getCameraKeyframes`, `addCameraKeyframe`, `removeCameraKeyframe`
- `getCameraAtFrame`, `getActiveCameraAtFrame`
- `updateViewportState`, `updateViewOptions`

**Target:** New `useCameraStore()`

**Estimated reduction:** ~150 lines

---

### 4. History State (KEEP - Tightly Coupled)
**Lines:** ~10 state + ~20 action lines | **Coupling:** Critical to project

```typescript
historyStack: LatticeProject[];
historyIndex: number;
```

**Why keep:** `pushHistory()` requires access to `project` state. Extracting would add complexity with no benefit.

---

### 5. UI State (CONSIDER EXTRACTING)
**Lines:** ~10 state + ~20 action lines | **Coupling:** Low

```typescript
curveEditorVisible: boolean;
hideMinimizedLayers: boolean;
timelineZoom: number;
selectedAssetId: string | null;
```

**Actions:**
- `toggleCurveEditor`, `setCurveEditorVisible`
- `toggleHideMinimizedLayers`, `setHideMinimizedLayers`
- `setTimelineZoom`, `selectAsset`

**Target:** Could merge into `useSelectionStore()` or new `useUIStateStore()`

**Estimated reduction:** ~50 lines

---

### 6. Segmentation State (KEEP FOR NOW)
**Lines:** ~15 state + ~40 action lines | **Coupling:** Feature-specific

```typescript
segmentToolActive: boolean;
segmentMode: "point" | "box";
segmentPendingMask: { mask, bounds, area, score } | null;
segmentBoxStart: { x, y } | null;
segmentIsLoading: boolean;
```

**Why keep for now:** Segmentation is a specialized feature. Extract when/if it grows.

---

### 7. ComfyUI Connection (KEEP)
**Lines:** ~5 state | **Coupling:** Core integration

```typescript
comfyuiNodeId: string | null;
sourceImage: string | null;
depthMap: string | null;
```

---

### 8. Autosave State (KEEP - Small)
**Lines:** ~10 state + ~20 action lines | **Coupling:** Low but small

```typescript
autosaveEnabled: boolean;
autosaveIntervalMs: number;
autosaveTimerId: number | null;
lastSaveTime: number | null;
lastSaveProjectId: string | null;
hasUnsavedChanges: boolean;
```

**Why keep:** Small footprint, would add complexity to extract.

---

### 9. Other Small State (KEEP)
- `snapConfig` - Timeline snapping (~15 lines)
- `clipboard` - Copy/paste (~10 lines)
- `frameCacheEnabled`, `projectStateHash` (~5 lines)
- `shapeToolOptions` (~10 lines)
- `propertyDriverSystem`, `propertyDrivers` (~15 lines)

---

## Action Module Delegation (Already Done)

The store already imports and delegates to 16 action modules:

| Module | Purpose | Lines (est) |
|--------|---------|-------------|
| audioActions | Audio loading, reactive | ~1,100 |
| keyframeActions | Keyframe CRUD | ~2,000 |
| layerActions | Layer CRUD | ~1,000 |
| projectActions | Project I/O, history | ~800 |
| cameraActions | Camera system | ~400 |
| effectActions | Effect management | ~300 |
| textAnimatorActions | Text animation | ~600 |
| compositionActions | Multi-comp support | ~200 |
| videoActions | Video layer import | ~200 |
| segmentationActions | SAM2/MatSeg | ~300 |
| particleLayerActions | Particle layers | ~200 |
| depthflowActions | Depthflow layers | ~100 |
| propertyDriverActions | Expression system | ~300 |
| markerActions | Timeline markers | ~200 |
| playbackActions | Play/pause | ~100 |
| cacheActions | Frame caching | ~200 |

**Total delegated:** ~8,000 lines in action modules

---

## Modularization Phases

### Phase 1: Extract Audio State (RECOMMENDED FIRST)

**Before:**
```typescript
// compositorStore.ts (3,292 lines)
state: {
  audioBuffer: AudioBuffer | null;
  audioAnalysis: AudioAnalysis | null;
  // ... 18 more audio properties
}

async loadAudio(file: File): Promise<void> {
  return audioActions.loadAudio(this, file);
}
```

**After:**
```typescript
// audioStore.ts (expanded, ~800 lines)
state: {
  audioBuffer: AudioBuffer | null;
  audioAnalysis: AudioAnalysis | null;
  // ... all audio state
}

// compositorStore.ts (~2,700 lines)
// Thin wrapper for backwards compatibility
async loadAudio(file: File): Promise<void> {
  return useAudioStore().loadAudio(file);
}
```

**Migration steps:**
1. Move all audio state properties to audioStore
2. Move audio action implementations to audioStore
3. Keep thin wrappers in compositorStore (public API preserved)
4. Update audioActions.ts to work with audioStore instead of compositorStore
5. Verify all 101 dependents still work

**Risk:** LOW - audioStore already exists, just needs state moved

---

### Phase 2: Extract Camera State

**After:**
```typescript
// cameraStore.ts (new, ~300 lines)
state: {
  cameras: Map<string, Camera3D>;
  cameraKeyframes: Map<string, CameraKeyframe[]>;
  activeCameraId: string | null;
  viewportState: ViewportState;
  viewOptions: ViewOptions;
}

// compositorStore.ts (~2,400 lines)
// Thin wrappers
createCameraLayer(name?: string) {
  return useCameraStore().createCameraLayer(name);
}
```

**Risk:** MEDIUM - Creates new store, requires careful testing

---

### Phase 3: Extract UI State (Optional)

**After:**
```typescript
// Merge into selectionStore or create uiStateStore
// compositorStore.ts (~2,350 lines)
```

**Risk:** LOW - Simple state, few dependencies

---

## Line Count Projection

| Phase | Before | After | Reduction |
|-------|--------|-------|-----------|
| Current | 3,292 | - | - |
| Phase 1 (Audio) | 3,292 | ~2,700 | ~600 |
| Phase 2 (Camera) | 2,700 | ~2,400 | ~300 |
| Phase 3 (UI) | 2,400 | ~2,350 | ~50 |
| **Final** | - | **~2,350** | **~942** |

**Note:** 2,350 lines still exceeds the 500-line rule, but the remaining code is:
- Thin wrapper methods (delegating to action modules)
- Core project state getters/setters
- Tightly-coupled state that can't be easily extracted

---

## What Must Stay Together

1. **project + activeCompositionId** - Foundation of everything
2. **historyStack + historyIndex** - Needs project access
3. **All getters** - Depend on project.compositions[activeCompositionId]
4. **Thin wrapper actions** - Preserve public API

---

## Public API Preservation Strategy

**Key insight:** The 101 dependents use the compositorStore API. Any modularization MUST keep thin wrappers:

```typescript
// BAD - breaks 101 dependents
// Removing loadAudio() from compositorStore

// GOOD - preserves API
// compositorStore.ts
async loadAudio(file: File): Promise<void> {
  return useAudioStore().loadAudio(file);
}
```

This "facade" pattern is already used for selection state (delegates to selectionStore).

---

## Risks and Mitigations

| Risk | Severity | Mitigation |
|------|----------|------------|
| State sync issues | HIGH | Use Pinia's `$subscribe` for cross-store sync |
| Breaking 101 dependents | HIGH | Keep all wrapper methods |
| Circular imports | MEDIUM | Action modules import stores, not vice versa |
| Performance | LOW | Pinia stores are lightweight |

---

## Recommended Order

1. **Phase 1: Audio extraction** - Biggest win, lowest risk (audioStore exists)
2. **Phase 2: Camera extraction** - Moderate win, moderate risk
3. **Skip Phase 3** - Diminishing returns

After Phase 2: ~2,400 lines (73% reduction from ideal, but manageable)

---

## Verification Checklist

Before each phase:
- [ ] Run full test suite
- [ ] Verify TypeScript compiles
- [ ] Test all 16 action module imports
- [ ] Smoke test compositor functionality

After each phase:
- [ ] Run full test suite
- [ ] Verify no store initialization errors
- [ ] Test undo/redo still works
- [ ] Test audio/camera features specifically
