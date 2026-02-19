# SYSTEM MAP - Lattice Compositor Architecture

**Generated:** December 24, 2025
**Purpose:** Post-refactor structural validation audit
**Total Codebase:** ~539,000 lines

---

## 1. PINIA STORE ARCHITECTURE

### 1.1 Store Hierarchy

```
compositorStore (MAIN - 2097 lines)
├── selectionStore (417 lines) - Selection state
├── playbackStore (214 lines) - Playback control
├── audioStore (708 lines) - Audio analysis
├── assetStore (818 lines) - Asset management
├── historyStore (123 lines) - Undo/redo
├── presetStore (432 lines) - Presets
├── toastStore (88 lines) - Notifications
└── themeStore (52 lines) - Theme settings
```

### 1.2 CompositorStore State Shape

```typescript
interface CompositorState {
  // PROJECT DATA (Source of Truth)
  project: LatticeProject;
  activeCompositionId: string;
  openCompositionIds: string[];
  compositionBreadcrumbs: string[];

  // COMFYUI INTEGRATION
  comfyuiNodeId: string | null;
  sourceImage: string | null;
  depthMap: string | null;

  // PLAYBACK (delegates to playbackStore)
  isPlaying: boolean;

  // SEGMENTATION
  segmentToolActive: boolean;
  segmentMode: 'point' | 'box';
  segmentPendingMask: {...} | null;
  segmentIsLoading: boolean;

  // UI STATE
  curveEditorVisible: boolean;
  hideMinimizedLayers: boolean;
  shapeToolOptions: {...};

  // HISTORY
  historyStack: LatticeProject[];
  historyIndex: number;

  // AUDIO (duplicated in audioStore for performance)
  audioBuffer: AudioBuffer | null;
  audioAnalysis: AudioAnalysis | null;
  audioFile: File | null;
  audioVolume: number;
  audioMuted: boolean;
  audioLoadingState: 'idle' | 'decoding' | 'analyzing' | 'complete' | 'error';
  audioMappings: Map<string, AudioParticleMapping[]>;
  peakData: PeakData | null;
  audioReactiveMappings: AudioMapping[];

  // CAMERA SYSTEM
  cameras: Map<string, Camera3D>;
  cameraKeyframes: Map<string, CameraKeyframe[]>;
  activeCameraId: string | null;
  viewportState: ViewportState;
  viewOptions: ViewOptions;

  // PROPERTY DRIVERS
  propertyDriverSystem: PropertyDriverSystem | null;
  propertyDrivers: PropertyDriver[];

  // TIMELINE
  snapConfig: SnapConfig;
  clipboard: { layers: Layer[]; keyframes: ClipboardKeyframe[] };

  // AUTOSAVE
  autosaveEnabled: boolean;
  autosaveIntervalMs: number;
  hasUnsavedChanges: boolean;

  // CACHE
  frameCacheEnabled: boolean;
  projectStateHash: string;

  // UI
  timelineZoom: number;
  selectedAssetId: string | null;
}
```

### 1.3 SelectionStore State Shape

```typescript
interface SelectionState {
  selectedLayerIds: string[];
  lastSelectedLayerId: string | null;
  selectedKeyframeIds: string[];
  selectedControlPoints: ControlPointSelection[];
  selectedPropertyPath: string | null;
  currentTool: 'select' | 'pen' | 'text' | 'hand' | 'zoom';
}
```

### 1.4 PlaybackStore State Shape

```typescript
interface PlaybackState {
  isPlaying: boolean;
  playbackRequestId: number | null;
  playbackStartTime: number | null;
  playbackStartFrame: number;
  loopPlayback: boolean;
  workAreaStart: number | null;
  workAreaEnd: number | null;
}
```

### 1.5 AudioStore State Shape

```typescript
interface AudioState {
  audioBuffer: AudioBuffer | null;
  audioAnalysis: AudioAnalysis | null;
  audioFile: File | null;
  loadingState: 'idle' | 'decoding' | 'analyzing' | 'complete' | 'error';
  loadingProgress: number;
  audioContext: AudioContext | null;
  isPlayingAudio: boolean;
  peakData: PeakData | null;
  legacyMappings: Map<string, AudioParticleMapping[]>;
  reactiveMappings: AudioMapping[];
  reactiveMapper: AudioReactiveMapper | null;
  stemBuffers: Map<string, StemData>;
  activeStemName: string | null;
}
```

---

## 2. ACTION MODULE MAP

### 2.1 Action Modules (stores/actions/)

| Module | Lines | Purpose | Critical Functions |
|--------|-------|---------|-------------------|
| layerActions | 1512 | Layer CRUD, transforms | createLayer, deleteLayer, updateLayer, setLayerParent |
| audioActions | 1011 | Audio loading, mappings | loadAudio, addAudioMapping, getAudioFeatureAtFrame |
| keyframeActions | 865 | Keyframe operations | addKeyframe, removeKeyframe, moveKeyframe, setKeyframeHandle |
| layerStyleActions | 709 | Layer styles | addDropShadow, updateStyleProperty |
| physicsActions | 684 | Physics simulation | enableLayerPhysics, stepPhysics, bakePhysicsToKeyframes |
| projectActions | 643 | Project save/load | exportProject, importProject, saveProjectToServer |
| compositionActions | 397 | Multi-comp management | createComposition, switchComposition, nestSelectedLayers |
| layerDecompositionActions | 394 | AI decomposition | decomposeImage |
| cameraActions | 299 | Camera management | createCameraLayer, getCameraAtFrame |
| segmentationActions | 267 | SAM segmentation | segmentToLayerByPoint, autoSegmentToLayers |
| videoActions | 264 | Video layers | createVideoLayer, onVideoMetadataLoaded |
| propertyDriverActions | 230 | Property linking | createAudioPropertyDriver, createPropertyLinkDriver |
| particleLayerActions | 221 | Particle config | createParticleLayer, updateParticleEmitter |
| effectActions | 210 | Effect stack | addEffectToLayer, updateEffectParameter |
| cacheActions | 158 | Frame caching | initializeCache, cacheFrame, invalidateFrameCache |
| depthflowActions | 93 | Depthflow config | createDepthflowLayer, updateDepthflowConfig |

### 2.2 Action → Store Binding Pattern

```typescript
// Actions are bound to store via delegation pattern:
// compositorStore.ts:
export const useCompositorStore = defineStore('compositor', {
  actions: {
    // Delegate to action module, passing 'this' as store context
    createLayer(type, name) {
      return layerActions.createLayer(this, type, name);
    }
  }
});

// layerActions.ts:
export function createLayer(store: CompositorStore, type: LayerType, name?: string): Layer {
  const comp = store.project.compositions[store.activeCompositionId];
  // ... implementation
  store.pushHistory(); // Call back to store
  return layer;
}
```

---

## 3. ENGINE ARCHITECTURE

### 3.1 Engine Files

| File | Lines | Purpose |
|------|-------|---------|
| LatticeEngine.ts | 1666 | Main Three.js rendering engine |
| MotionEngine.ts | 1090 | Pure frame evaluation (deterministic) |
| ParticleSimulationController.ts | 450 | Particle checkpoint/simulation |
| TransformControlsManager.ts | 286 | Gizmo controls |
| NestedCompRenderer.ts | 183 | Nested composition rendering |
| BackgroundManager.ts | 182 | Background/depth map display |

### 3.2 Data Flow: Store → Engine → Render

```
1. User Action (UI)
        ↓
2. compositorStore.action()
        ↓
3. Store mutates project state
        ↓
4. Component watches store.currentFrame
        ↓
5. Component calls store.getFrameState()
        ↓
6. MotionEngine.evaluate(frame, project)
        ↓
7. Returns immutable FrameState
        ↓
8. LatticeEngine.applyFrameState(frameState)
        ↓
9. Three.js WebGL Render
```

### 3.3 MotionEngine (CRITICAL - Pure Function)

```typescript
// MotionEngine is PURE: same inputs = same outputs
// NO side effects, NO state mutation

evaluate(
  frame: number,
  project: LatticeProject,
  audioAnalysis?: AudioAnalysis,
  activeCameraId?: string,
  useCache?: boolean,
  audioReactive?: AudioReactiveInput
): FrameState;

// Returns immutable snapshot:
interface FrameState {
  readonly frame: number;
  readonly composition: CompositionSettings;
  readonly layers: readonly EvaluatedLayer[];
  readonly camera: EvaluatedCamera | null;
  readonly audio: EvaluatedAudio;
  readonly particleSnapshots: Record<string, ParticleSnapshot>;
}
```

### 3.4 LatticeEngine Responsibilities

```typescript
class LatticeEngine {
  // THREE.JS SCENE MANAGEMENT
  private scene: THREE.Scene;
  private renderer: THREE.WebGLRenderer;
  private camera: THREE.PerspectiveCamera;

  // LAYER MANAGEMENT
  private layerManager: LayerManager;

  // RENDERING
  applyFrameState(frameState: FrameState): void;
  render(): void;

  // RESOURCE MANAGEMENT
  dispose(): void;
}
```

---

## 4. TYPE SYSTEM

### 4.1 Core Types (types/)

| File | Lines | Purpose |
|------|-------|---------|
| project.ts | 1988 | Core project/layer/composition types |
| effects.ts | 1391 | Effect definitions |
| physics.ts | 987 | Physics types |
| shapes.ts | 828 | Shape layer types |
| presets.ts | 787 | Preset definitions |
| layerStyles.ts | 661 | Layer style types |
| layerData.ts | 544 | Layer-specific data |
| particles.ts | 407 | Particle system types |
| export.ts | 391 | Export format types |
| spline.ts | 338 | Spline/path types |
| camera.ts | 278 | Camera types |

### 4.2 LatticeProject Structure

```typescript
interface LatticeProject {
  version: "1.0.0";
  schemaVersion?: number;
  meta: ProjectMeta;
  compositions: Record<string, Composition>;
  mainCompositionId: string;
  composition: CompositionSettings; // Legacy alias
  assets: Record<string, AssetReference>;
  dataAssets?: Record<string, DataAssetReference>;
  layers: Layer[]; // Legacy
  currentFrame: number;
}

interface Composition {
  id: string;
  name: string;
  settings: CompositionSettings;
  layers: Layer[];
  currentFrame: number;
  isNestedComp: boolean;
  templateConfig?: TemplateConfig;
  globalLight?: GlobalLightSettings;
}

interface Layer {
  id: string;
  name: string;
  type: LayerType;
  visible: boolean;
  locked: boolean;
  threeD: boolean;
  motionBlur: boolean;
  startFrame: number;
  endFrame: number;
  parentId: string | null;
  blendMode: BlendMode;
  opacity: AnimatableProperty<number>;
  transform: LayerTransform;
  masks?: LayerMask[];
  matteType?: MatteType;
  properties: AnimatableProperty<any>[];
  effects: EffectInstance[];
  layerStyles?: LayerStyles;
  data: LayerData | null;
}
```

### 4.3 LayerType Enum (26 types)

```typescript
type LayerType =
  | 'depth' | 'normal' | 'spline' | 'path' | 'text'
  | 'shape' | 'particle' | 'particles' | 'depthflow'
  | 'image' | 'video' | 'audio' | 'generated' | 'camera'
  | 'light' | 'solid' | 'control' | 'null' | 'group'
  | 'nestedComp' | 'matte' | 'model' | 'pointcloud'
  | 'pose' | 'effectLayer' | 'adjustment';
```

---

## 5. COMPOSABLES (Component-Store Wiring)

### 5.1 Composable Map

| Composable | Lines | Store Dependencies |
|------------|-------|-------------------|
| useKeyboardShortcuts | 1612 | compositorStore, selectionStore, playbackStore |
| useSplineInteraction | 817 | compositorStore, selectionStore |
| useCurveEditorInteraction | 544 | compositorStore, selectionStore |
| useCanvasSelection | 412 | compositorStore, selectionStore |
| useShapeDrawing | 369 | compositorStore |
| useMenuActions | 293 | compositorStore, playbackStore |
| useViewportControls | 203 | compositorStore |
| useCanvasSegmentation | 209 | compositorStore |

### 5.2 Composable Pattern

```typescript
// Composables encapsulate store access + business logic
export function useKeyboardShortcuts(options: Options) {
  const store = useCompositorStore();
  const selectionStore = useSelectionStore();
  const playbackStore = usePlaybackStore();

  const handleKeyDown = (e: KeyboardEvent) => {
    switch (e.key) {
      case ' ':
        store.togglePlayback();
        break;
      case 'Delete':
        store.deleteSelectedLayers();
        break;
      // ... 86+ shortcuts
    }
  };

  onMounted(() => window.addEventListener('keydown', handleKeyDown));
  onUnmounted(() => window.removeEventListener('keydown', handleKeyDown));
}
```

---

## 6. SERVICE LAYER

### 6.1 Service Categories (167 services)

| Category | Count | Key Services |
|----------|-------|--------------|
| Animation | 3 | interpolation.ts, easing.ts, bezierMath.ts |
| Audio | 6 | audioFeatures.ts, audioReactiveMapping.ts, audioWorkerClient.ts |
| Particles | 5 | particleSystem.ts, particleExpression.ts |
| Effects | 17 | effectProcessor.ts, blur.ts, colorAdjust.ts, etc. |
| Export | 8 | matteExporter.ts, svgExport.ts, modelExport.ts |
| AI | 6 | aiCompositorAgent.ts, decomposition.ts |
| Camera | 4 | cameraTrajectory.ts, cameraEnhancements.ts |
| Text | 5 | textAnimator.ts, textToVector.ts |

### 6.2 Critical Services

```typescript
// interpolation.ts - Keyframe evaluation
interpolateProperty<T>(property: AnimatableProperty<T>, frame: number): T;

// expressions.ts - Expression evaluation
evaluateExpression(expr: string, context: ExpressionContext): any;

// particleSystem.ts - Particle simulation
class ParticleSimulation {
  evaluate(frame: number): Particle[];
  checkpoint(frame: number): void;
  loadCheckpoint(frame: number): void;
}

// effectProcessor.ts - Effect stack processing
processEffects(layer: Layer, frame: number): ProcessedLayer;
```

---

## 7. COMPONENT STRUCTURE (112 Vue Components)

### 7.1 Component Hierarchy

```
App.vue
├── WorkspaceLayout.vue (main layout)
│   ├── ThreeCanvas.vue (WebGL viewport)
│   ├── TimelineContainer.vue
│   │   ├── TimelineRuler.vue
│   │   ├── LayerTrack.vue
│   │   └── PropertyTrack.vue
│   ├── PropertiesPanel.vue
│   │   ├── TransformPanel.vue
│   │   ├── EffectsPanel.vue
│   │   └── [layer-type]Panel.vue
│   ├── ProjectPanel.vue
│   └── CurveEditor.vue
```

### 7.2 Component → Store Bindings

| Component | Store Access | Pattern |
|-----------|--------------|---------|
| ThreeCanvas | compositorStore.getFrameState() | Computed + watch |
| TimelineContainer | compositorStore.layers, currentFrame | Direct refs |
| LayerTrack | selectionStore.selectedLayerIds | Computed |
| PropertiesPanel | compositorStore.selectedLayer | Computed |
| CurveEditor | compositorStore, selectionStore | Multiple refs |

---

## 8. POTENTIAL FAILURE POINTS

### 8.1 Cross-Store State Duplication

**RISK: Audio state in BOTH compositorStore AND audioStore**
```
compositorStore.audioBuffer ↔ audioStore.audioBuffer
compositorStore.audioAnalysis ↔ audioStore.audioAnalysis
compositorStore.audioMappings ↔ audioStore.reactiveMappings
```
**Impact:** State desync if one is updated without the other

### 8.2 Legacy Alias Drift

**RISK: Deprecated properties may not be synced**
```typescript
layer.startFrame vs layer.inPoint
layer.endFrame vs layer.outPoint
layer.matteType vs layer.trackMatteType
transform.origin vs transform.anchorPoint
```

### 8.3 Action Module Circular Dependencies

**RISK: Action modules importing each other**
```
layerActions → compositionActions (for nestSelectedLayers)
compositionActions → layerActions (for layer creation)
```

### 8.4 Engine Initialization Order

**RISK: LatticeEngine depends on LayerManager registry**
- LayerManager must register all layer types before engine use
- Missing registration = silent fallback to ControlLayer

### 8.5 Frame Cache Invalidation

**RISK: Cache not invalidated on all state changes**
```typescript
// These should invalidate cache:
- Layer add/remove
- Keyframe changes
- Effect parameter changes
- Property value changes
```

---

## 9. CRITICAL INTEGRATION PATHS

### 9.1 Layer Creation Flow

```
1. UI: Click "Add Layer"
2. compositorStore.createLayer(type, name)
3. → layerActions.createLayer()
4. → Creates Layer object with defaults
5. → Adds to composition.layers[]
6. → LayerManager.createLayerObject() [3D]
7. → Registers with scene
8. → pushHistory()
```

### 9.2 Keyframe Evaluation Flow

```
1. Timeline scrub or playback tick
2. compositorStore.setFrame(frame)
3. Component reactivity triggers
4. store.getFrameState(frame)
5. → MotionEngine.evaluate()
6. → For each layer:
   → interpolateProperty() for each animated prop
   → Apply audio reactive modifiers
   → Apply expressions
7. → Returns frozen FrameState
8. LatticeEngine.applyFrameState()
9. → Updates Three.js scene objects
10. renderer.render()
```

### 9.3 Project Save/Load Flow

```
SAVE:
1. compositorStore.exportProject()
2. → projectActions.exportProject()
3. → JSON.stringify(project)
4. → POST to /lattice/project/save

LOAD:
1. compositorStore.importProject(json)
2. → projectActions.importProject()
3. → JSON.parse()
4. → Validate/migrate schema
5. → Replace store.project
6. → Clear all particle simulations
7. → Invalidate frame cache
8. → pushHistory()
```

---

## 10. NEXT STEPS: INTEGRATION TESTS

Based on this map, the following integration tests are critical:

1. **Store Initialization Chain** - All stores initialize correctly with defaults
2. **Layer CRUD Pipeline** - Create/Read/Update/Delete through full stack
3. **Frame Evaluation Determinism** - Same frame = same output
4. **Project Round-Trip** - Export → Import = identical state
5. **Cross-Store Sync** - Audio state syncs between stores
6. **Cache Invalidation** - All mutations invalidate cache correctly
7. **Layer Type Registration** - All 26 types register with LayerManager
8. **Effect Stack Processing** - Effects apply in correct order
9. **Parenting Chain** - Transform inheritance works through hierarchy
10. **Nested Composition** - Render-to-texture pipeline works

---

*This map serves as the foundation for systematic integration testing.*
