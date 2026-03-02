# Target Architecture: Domain-Driven Store Design

> Goal: Replace the 3,292-line god object with focused domain stores
> Rule: Each store ≤500 lines, single responsibility

---

## Current Problem

`compositorStore` is a **god object** that:
- Holds 14 unrelated state slices
- Has 101 dependents because everything routes through it
- Delegates to 16 action modules (hiding complexity, not solving it)
- Makes every component depend on everything

---

## Target Architecture

### Domain Stores (12 stores, each <500 lines)

```
stores/
├── project/
│   ├── projectStore.ts      # Project file, assets (~200 lines)
│   └── compositionStore.ts  # Active comp, multi-comp (~150 lines)
├── layers/
│   └── layerStore.ts        # Layer CRUD, hierarchy (~300 lines)
├── animation/
│   ├── keyframeStore.ts     # Keyframe CRUD (~400 lines)
│   └── expressionStore.ts   # Expressions, drivers (~300 lines)
├── playback/
│   └── playbackStore.ts     # Time authority (~150 lines)
├── selection/
│   └── selectionStore.ts    # Already exists, good design (~200 lines)
├── audio/
│   └── audioStore.ts        # Audio, reactive mappings (~400 lines)
├── camera/
│   └── cameraStore.ts       # 3D cameras, viewport (~300 lines)
├── history/
│   └── historyStore.ts      # Undo/redo (~200 lines)
├── ui/
│   └── uiStore.ts           # Panel visibility, tools (~150 lines)
└── integration/
    ├── comfyuiStore.ts      # ComfyUI connection (~100 lines)
    └── segmentationStore.ts # SAM2/MatSeg (~200 lines)
```

**Total: ~2,650 lines across 12 stores** (vs 3,292 in one file)

---

## Store Definitions

### 1. projectStore (~200 lines)
**Responsibility:** Project file I/O, asset management

```typescript
interface ProjectState {
  project: LatticeProject;
  hasUnsavedChanges: boolean;
  lastSaveTime: number | null;
  autosaveEnabled: boolean;
}

// Actions
newProject(width, height)
loadProject(file: File)
saveProject()
exportProject(): string
importProject(json: string)
addAsset(asset: AssetReference)
removeAsset(assetId: string)
getAsset(assetId: string)
```

**Does NOT contain:** layers, keyframes, playback, selection

---

### 2. compositionStore (~150 lines)
**Responsibility:** Multi-composition navigation

```typescript
interface CompositionState {
  activeCompositionId: string;
  openCompositionIds: string[];
  breadcrumbs: string[];
}

// Getters (read from projectStore.project)
activeComposition: Composition
width, height, fps, frameCount, duration, backgroundColor

// Actions
openComposition(id: string)
closeComposition(id: string)
createComposition(settings: CompositionSettings)
deleteComposition(id: string)
navigateToNestedComp(id: string)
navigateBack()
```

**Depends on:** projectStore (reads project.compositions)

---

### 3. layerStore (~300 lines)
**Responsibility:** Layer CRUD, hierarchy, properties

```typescript
// No state - layers live in projectStore.project.compositions[id].layers

// Getters
layers: Layer[]  // from active composition
visibleLayers: Layer[]
getLayerById(id: string): Layer | null
getLayersByType(type: LayerType): Layer[]

// Actions
createLayer(type: LayerType, name?: string): Layer
deleteLayer(layerId: string)
duplicateLayers(layerIds: string[]): Layer[]
moveLayers(layerIds: string[], targetIndex: number)
updateLayerProperty(layerId: string, path: string, value: any)
setLayerVisible(layerId: string, visible: boolean)
setLayerLocked(layerId: string, locked: boolean)
groupLayers(layerIds: string[]): Layer
ungroupLayer(groupId: string)
```

**Depends on:** projectStore, compositionStore

---

### 4. keyframeStore (~400 lines)
**Responsibility:** Keyframe CRUD, interpolation

```typescript
// No state - keyframes live on layer properties

// Actions
addKeyframe(layerId, propertyPath, value, frame?): Keyframe
removeKeyframe(layerId, propertyPath, keyframeId)
moveKeyframe(layerId, propertyPath, keyframeId, newFrame)
moveKeyframes(selections[], frameDelta)
setKeyframeValue(layerId, propertyPath, keyframeId, value)
setKeyframeInterpolation(layerId, propertyPath, keyframeId, type)
setKeyframeHandle(layerId, propertyPath, keyframeId, handleType, handle)
copyKeyframes(selections[]): ClipboardKeyframe[]
pasteKeyframes(targetLayerId, targetPropertyPath?)
clearKeyframes(layerId, propertyPath)
timeReverseKeyframes(layerId, propertyPath?)
scaleKeyframeTiming(layerId, propertyPath, scaleFactor, anchorFrame)

// Queries
getKeyframesForProperty(layerId, propertyPath): Keyframe[]
getAllKeyframeFrames(layerId): number[]
findNextKeyframeFrame(currentFrame, layerIds?): number | null
findPrevKeyframeFrame(currentFrame, layerIds?): number | null
```

**Depends on:** projectStore, compositionStore, layerStore

---

### 5. expressionStore (~300 lines)
**Responsibility:** Expressions, property drivers, property links

```typescript
interface ExpressionState {
  propertyDrivers: PropertyDriver[];
  // Runtime system initialized on demand
}

// Actions
setPropertyExpression(layerId, propertyPath, expression)
enablePropertyExpression(layerId, propertyPath, expressionName, params)
disablePropertyExpression(layerId, propertyPath)
removePropertyExpression(layerId, propertyPath)
updateExpressionParams(layerId, propertyPath, params)

addPropertyDriver(driver: PropertyDriver)
removePropertyDriver(driverId: string)
updatePropertyDriver(driverId, updates)
createAudioPropertyDriver(targetLayerId, targetProperty, audioFeature, options)
createPropertyLink(targetLayerId, targetProperty, sourceLayerId, sourceProperty)

// Queries
getPropertyExpression(layerId, propertyPath)
hasPropertyExpression(layerId, propertyPath)
getDriversForLayer(layerId)
evaluateDrivers(frame: number)
```

**Depends on:** layerStore, audioStore (for audio drivers)

---

### 6. playbackStore (~150 lines)
**Responsibility:** TIME AUTHORITY - playback state, frame navigation

```typescript
interface PlaybackState {
  isPlaying: boolean;
  playbackRate: number;
  loopEnabled: boolean;
  // currentFrame is PER COMPOSITION in compositionStore
}

// Actions
play()
pause()
togglePlayback()
stop()  // pause + go to frame 0
setFrame(frame: number)  // Updates compositionStore
nextFrame()
prevFrame()
jumpFrames(n: number)
goToStart()
goToEnd()
setPlaybackRate(rate: number)
toggleLoop()

// Frame is stored on composition, not here
// This store controls playback BEHAVIOR
```

**Depends on:** compositionStore (to set currentFrame)

---

### 7. audioStore (~400 lines)
**Responsibility:** Audio loading, analysis, reactive mappings

```typescript
interface AudioState {
  audioBuffer: AudioBuffer | null;
  audioAnalysis: AudioAnalysis | null;
  audioFile: File | null;
  volume: number;
  muted: boolean;
  loadingState: 'idle' | 'decoding' | 'analyzing' | 'complete' | 'error';
  loadingProgress: number;
  loadingError: string | null;
  peakData: PeakData | null;
  reactiveMappings: AudioMapping[];
  pathAnimators: Map<string, AudioPathAnimator>;
}

// Actions
loadAudio(file: File)
clearAudio()
setVolume(volume: number)
setMuted(muted: boolean)
toggleMute()
detectPeaks(config: PeakDetectionConfig)
addMapping(mapping: AudioMapping)
removeMapping(mappingId: string)
updateMapping(mappingId, updates)

// Path animators
createPathAnimator(layerId, config)
updatePathAnimator(layerId, config)
removePathAnimator(layerId)

// Queries
getFeatureAtFrame(feature: string, frame: number): number
getAmplitudeAtFrame(channel, frame): number
getFrequencyBandAtFrame(band, frame): number
getMappedValueAtFrame(mappingId, frame): number
getAllMappedValuesAtFrame(frame): Map<TargetParameter, number>
getBeatFrames(): number[]
getPeakFrames(): number[]
```

**Depends on:** Nothing (self-contained)

---

### 8. cameraStore (~300 lines)
**Responsibility:** 3D camera system, viewport state

```typescript
interface CameraState {
  cameras: Map<string, Camera3D>;
  cameraKeyframes: Map<string, CameraKeyframe[]>;
  activeCameraId: string | null;
  viewportState: ViewportState;
  viewOptions: ViewOptions;
}

// Actions
createCamera(name?: string): Camera3D
updateCamera(cameraId, updates)
deleteCamera(cameraId)
setActiveCamera(cameraId)
addCameraKeyframe(cameraId, keyframe)
removeCameraKeyframe(cameraId, frame)
updateViewportState(updates)
updateViewOptions(updates)

// Queries
getCamera(cameraId): Camera3D | null
getCameraAtFrame(cameraId, frame): Camera3D
getActiveCameraAtFrame(frame?): Camera3D | null
getCameraKeyframes(cameraId): CameraKeyframe[]
```

**Depends on:** Nothing (self-contained)

---

### 9. historyStore (~200 lines)
**Responsibility:** Undo/redo

```typescript
interface HistoryState {
  stack: LatticeProject[];
  index: number;
  maxSize: number;
}

// Actions
pushState()  // Snapshot current project state
undo()
redo()
clear()

// Getters
canUndo: boolean
canRedo: boolean
undoDescription: string
redoDescription: string
```

**Depends on:** projectStore (reads/writes project state)

**Key design:** Stores explicitly call `historyStore.pushState()` when a user-initiated action completes. No magic auto-watching.

---

### 10. uiStore (~150 lines)
**Responsibility:** UI state, panel visibility, tool options

```typescript
interface UIState {
  curveEditorVisible: boolean;
  hideMinimizedLayers: boolean;
  timelineZoom: number;
  selectedAssetId: string | null;
  shapeToolOptions: ShapeToolOptions;
  snapConfig: SnapConfig;
}

// Actions
toggleCurveEditor()
setCurveEditorVisible(visible)
toggleHideMinimizedLayers()
setTimelineZoom(zoom)
selectAsset(assetId)
setShapeToolOptions(options)
setSnapConfig(config)
toggleSnapping()
toggleSnapType(type)

// Queries
findSnapPoint(frame, pixelsPerFrame, selectedLayerId?)
```

**Depends on:** audioStore (for beat/peak snap points)

---

### 11. comfyuiStore (~100 lines)
**Responsibility:** ComfyUI node connection

```typescript
interface ComfyUIState {
  nodeId: string | null;
  sourceImage: string | null;
  depthMap: string | null;
}

// Actions
setNodeId(nodeId)
setSourceImage(imageUrl)
setDepthMap(depthUrl)
clearConnection()
```

**Depends on:** Nothing (self-contained)

---

### 12. segmentationStore (~200 lines)
**Responsibility:** SAM2/MatSeg segmentation tool

```typescript
interface SegmentationState {
  toolActive: boolean;
  mode: 'point' | 'box';
  pendingMask: PendingMask | null;
  boxStart: { x: number; y: number } | null;
  isLoading: boolean;
}

// Actions
setToolActive(active)
setMode(mode)
setPendingMask(mask)
setBoxStart(point)
clearPendingMask()
segmentByPoint(point, options)
segmentByBox(box, options)
segmentByMultiplePoints(foreground, background, options)
autoSegment(options)
confirmMask(layerName?): Layer
```

**Depends on:** layerStore (to create layers from masks), comfyuiStore (for source image)

---

## Dependency Graph

```
                    ┌─────────────┐
                    │ projectStore │ ← Source of truth for project data
                    └──────┬──────┘
                           │
              ┌────────────┼────────────┐
              │            │            │
              ▼            ▼            ▼
      ┌───────────┐ ┌────────────┐ ┌───────────┐
      │ composition│ │ historyStore│ │ layerStore │
      │   Store   │ │            │ │           │
      └─────┬─────┘ └────────────┘ └─────┬─────┘
            │                            │
            │         ┌──────────────────┤
            │         │                  │
            ▼         ▼                  ▼
      ┌──────────┐ ┌──────────┐  ┌──────────────┐
      │ playback │ │ keyframe │  │ expression   │
      │  Store   │ │  Store   │  │    Store     │
      └──────────┘ └──────────┘  └──────────────┘
                                        │
                                        ▼
      ┌──────────┐ ┌──────────┐  ┌──────────────┐
      │  audio   │ │  camera  │  │ segmentation │
      │  Store   │ │  Store   │  │    Store     │
      └──────────┘ └──────────┘  └──────────────┘

      ┌──────────┐ ┌──────────┐  ┌──────────────┐
      │    ui    │ │ selection│  │   comfyui    │
      │  Store   │ │  Store   │  │    Store     │
      └──────────┘ └──────────┘  └──────────────┘
```

---

## Cross-Store Coordination Patterns

### The Problem

"Add keyframe to layer property" touches:
1. **layerStore** - Find the layer
2. **keyframeStore** - Add the keyframe to layer.transform.position.keyframes
3. **historyStore** - Snapshot for undo

How do we coordinate without a god object?

### Pattern: Store-to-Store Calls (Recommended)

Stores can import and call other stores. The **action owner** is the store that owns the primary mutation.

```typescript
// keyframeStore.ts
import { useLayerStore } from '@/stores/layers/layerStore';
import { useHistoryStore } from '@/stores/history/historyStore';

export const useKeyframeStore = defineStore('keyframe', {
  actions: {
    addKeyframe(layerId: string, propertyPath: string, value: any, frame?: number) {
      // 1. Get layer from layerStore
      const layer = useLayerStore().getLayerById(layerId);
      if (!layer) return null;

      // 2. Find property and add keyframe (this store's responsibility)
      const property = this.findProperty(layer, propertyPath);
      const keyframe = this.createKeyframe(value, frame ?? usePlaybackStore().currentFrame);
      property.keyframes.push(keyframe);

      // 3. Mark project modified
      useProjectStore().markModified();

      // 4. Push history (explicit, not magic)
      useHistoryStore().pushState();

      return keyframe;
    }
  }
});
```

### Pattern: History is Always Explicit

```typescript
// WRONG - magic auto-snapshot
projectStore.$subscribe(() => historyStore.pushState()); // Creates noise, duplicates

// RIGHT - explicit snapshot at action boundaries
addKeyframe(...) {
  // ... do work ...
  useHistoryStore().pushState(); // One snapshot per user action
}
```

### Pattern: Query vs Mutate

Stores expose both queries (read) and mutations (write):

```typescript
// layerStore.ts
export const useLayerStore = defineStore('layer', {
  getters: {
    // QUERIES - other stores can read freely
    layers: (state) => useCompositionStore().activeComposition?.layers ?? [],
    getLayerById: (state) => (id: string) => state.layers.find(l => l.id === id),
  },
  actions: {
    // MUTATIONS - only this store mutates layers
    createLayer(type: LayerType, name?: string): Layer { ... },
    deleteLayer(layerId: string): void { ... },
    updateLayerProperty(layerId: string, path: string, value: any): void { ... },
  }
});
```

**Rule:** A store can READ from any store, but only MUTATES its own domain.

### Example: Complex Operation

"Paste keyframes to multiple layers" spans:
- selectionStore (get selected layers)
- keyframeStore (get clipboard, add keyframes)
- historyStore (one undo entry for entire paste)

```typescript
// keyframeStore.ts
pasteKeyframes(targetLayerId?: string) {
  const selection = useSelectionStore();
  const targets = targetLayerId ? [targetLayerId] : selection.selectedLayerIds;

  // Batch all keyframes into one operation
  const created: Keyframe[] = [];
  for (const layerId of targets) {
    for (const clipboardKf of this.clipboard) {
      created.push(this.addKeyframeInternal(layerId, clipboardKf)); // No history push
    }
  }

  // ONE history entry for entire paste
  useHistoryStore().pushState();
  return created;
}

// Internal helper - no history push
private addKeyframeInternal(layerId: string, kf: ClipboardKeyframe): Keyframe {
  const layer = useLayerStore().getLayerById(layerId);
  // ... add keyframe without pushState()
}
```

### Pattern: Where Does Data Live?

| Data | Lives In | Accessed Via |
|------|----------|--------------|
| `project.compositions` | projectStore.state | projectStore.project |
| `activeCompositionId` | compositionStore.state | compositionStore.activeCompositionId |
| `layers[]` | project.compositions[id].layers | layerStore.layers (getter) |
| `keyframes[]` | layer.transform.position.keyframes | keyframeStore reads via layerStore |
| `historyStack[]` | historyStore.state | historyStore only |
| `audioBuffer` | audioStore.state | audioStore only |

**Key insight:** Keyframes don't have their own state - they live ON layers. keyframeStore is about OPERATIONS, not storage.

### Anti-Patterns to Avoid

```typescript
// BAD: Circular dependency
// keyframeStore imports layerStore
// layerStore imports keyframeStore  <-- CYCLE

// GOOD: One-way dependency
// keyframeStore imports layerStore (keyframes need layers)
// layerStore does NOT import keyframeStore
```

```typescript
// BAD: Component orchestrates everything
function handleAddKeyframe() {
  const layer = layerStore.getLayerById(id);
  const kf = { frame, value };
  layer.transform.position.keyframes.push(kf); // Bypasses store
  historyStore.pushState();
}

// GOOD: Component calls one store action
function handleAddKeyframe() {
  keyframeStore.addKeyframe(id, 'transform.position', value, frame);
  // Store handles everything internally
}
```

---

## What compositorStore Becomes

**Option A: Delete it entirely**
Components import the stores they need directly.

**Option B: Tiny coordinator (~50 lines)**
```typescript
// compositorStore.ts - DEPRECATED, use domain stores directly
export const useCompositorStore = defineStore('compositor', {
  // No state
  // Only high-level orchestration actions that MUST coordinate multiple stores

  actions: {
    // Example: Creating a new project requires resetting multiple stores
    async newProject(width: number, height: number) {
      useProjectStore().newProject(width, height);
      useHistoryStore().clear();
      useAudioStore().clearAudio();
      useCameraStore().clearCameras();
      useSelectionStore().clearSelection();
    }
  }
});
```

**Recommendation: Option A** - Delete compositorStore. The "coordination" use case is rare and can be handled by the component that needs it.

---

## Migration Impact

### Files to Update

The 101 dependents currently do:
```typescript
import { useCompositorStore } from '@/stores/compositorStore';
const store = useCompositorStore();
store.addKeyframe(...);
store.loadAudio(...);
store.setFrame(...);
```

After migration:
```typescript
import { useKeyframeStore } from '@/stores/animation/keyframeStore';
import { useAudioStore } from '@/stores/audio/audioStore';
import { usePlaybackStore } from '@/stores/playback/playbackStore';

useKeyframeStore().addKeyframe(...);
useAudioStore().loadAudio(...);
usePlaybackStore().setFrame(...);
```

### Migration Strategy

1. **Create new stores** with proper APIs
2. **Update imports file by file** (not wrappers)
3. **Delete compositorStore** when all 101 files migrated
4. **Delete action modules** - logic moves into stores

---

## Benefits

| Metric | Before | After |
|--------|--------|-------|
| Largest store | 3,292 lines | ~400 lines |
| God object | Yes | No |
| Single responsibility | No | Yes |
| Testable in isolation | No | Yes |
| Clear dependencies | No | Yes |
| Import what you need | No | Yes |

---

## Action Module Fate

The 16 action modules (~8,000 lines) get **absorbed into their domain stores**:

| Module | Target Store |
|--------|--------------|
| audioActions | audioStore |
| keyframeActions | keyframeStore |
| layerActions | layerStore |
| projectActions | projectStore |
| cameraActions | cameraStore |
| effectActions | layerStore (effects are layer properties) |
| textAnimatorActions | layerStore (text animators are layer data) |
| compositionActions | compositionStore |
| videoActions | layerStore (video is a layer type) |
| segmentationActions | segmentationStore |
| particleLayerActions | layerStore (particles are layer data) |
| depthflowActions | layerStore (depthflow is layer data) |
| propertyDriverActions | expressionStore |
| markerActions | compositionStore (markers per composition) |
| playbackActions | playbackStore |
| cacheActions | (move to services, not store-related) |

---

## Implementation Order

1. **audioStore** - Most self-contained, no dependencies on other stores
2. **cameraStore** - Self-contained
3. **comfyuiStore** - Self-contained, small
4. **segmentationStore** - Small, depends on layerStore
5. **uiStore** - Small, few dependencies
6. **playbackStore** - Small, depends on compositionStore
7. **historyStore** - Depends on projectStore
8. **projectStore** - Core, many things depend on it
9. **compositionStore** - Depends on projectStore
10. **layerStore** - Depends on projectStore, compositionStore
11. **keyframeStore** - Depends on layerStore
12. **expressionStore** - Depends on layerStore, audioStore
13. **Delete compositorStore**
