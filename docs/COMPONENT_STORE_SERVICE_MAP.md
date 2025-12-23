# COMPONENT → STORE → SERVICE DEPENDENCY MAP

**Weyl Compositor - Complete Dependency Graph**

**HYPER-CRITICAL FOR HANDOFF**: This document maps every Vue component to its store and service dependencies.

---

## Architecture Overview

```
┌─────────────────────────────────────────────────────────────┐
│                    DEPENDENCY FLOW                          │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│   ┌──────────────┐                                         │
│   │  Components  │ ──▶ User interactions                   │
│   │  (55 total)  │                                         │
│   └──────┬───────┘                                         │
│          │                                                  │
│          ▼                                                  │
│   ┌──────────────┐                                         │
│   │    Stores    │ ──▶ State management (Pinia)            │
│   │ (1 central)  │                                         │
│   └──────┬───────┘                                         │
│          │                                                  │
│          ▼                                                  │
│   ┌──────────────┐                                         │
│   │   Services   │ ──▶ Business logic (42 services)        │
│   │  (42 total)  │                                         │
│   └──────┬───────┘                                         │
│          │                                                  │
│          ▼                                                  │
│   ┌──────────────┐                                         │
│   │    Engine    │ ──▶ Rendering (Three.js/WebGL2)         │
│   │ (WeylEngine) │                                         │
│   └──────────────┘                                         │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

---

## Component Dependency Tables

### Canvas Components (4)

| Component | File | Stores | Services |
|-----------|------|--------|----------|
| MaskEditor | `canvas/MaskEditor.vue` | compositorStore | - |
| PathPreviewOverlay | `canvas/PathPreviewOverlay.vue` | - | - |
| SplineEditor | `canvas/SplineEditor.vue` | compositorStore | interpolation |
| ThreeCanvas | `canvas/ThreeCanvas.vue` | compositorStore | segmentation, propertyDriver |

### Controls Components (7)

| Component | File | Stores | Services |
|-----------|------|--------|----------|
| AngleDial | `controls/AngleDial.vue` | - | - |
| ColorPicker | `controls/ColorPicker.vue` | - | colorUtils |
| CurveEditor | `controls/CurveEditor.vue` | - | - |
| PropertyLink | `controls/PropertyLink.vue` | - | propertyDriver |
| PositionXY | `controls/PositionXY.vue` | - | - |
| ScrubableNumber | `controls/ScrubableNumber.vue` | - | - |
| SliderInput | `controls/SliderInput.vue` | - | - |

### Dialogs Components (4)

| Component | File | Stores | Services |
|-----------|------|--------|----------|
| ExportDialog | `dialogs/ExportDialog.vue` | compositorStore | matteExporter |
| FontPicker | `dialogs/FontPicker.vue` | - | fontService |
| PathSuggestionDialog | `dialogs/PathSuggestionDialog.vue` | compositorStore | visionAuthoring |
| CompositionSettingsDialog | `dialogs/CompositionSettingsDialog.vue` | compositorStore | - |

### Export Components (1)

| Component | File | Stores | Services |
|-----------|------|--------|----------|
| ComfyUIExportDialog | `export/ComfyUIExportDialog.vue` | compositorStore | exportPipeline, comfyuiClient, exportPresets |

### Curve Editor Components (1)

| Component | File | Stores | Services |
|-----------|------|--------|----------|
| CurveEditor | `curve-editor/CurveEditor.vue` | compositorStore | interpolation, easing |

### Layout Components (1)

| Component | File | Stores | Services |
|-----------|------|--------|----------|
| WorkspaceLayout | `layout/WorkspaceLayout.vue` | compositorStore | - |

### Materials Components (4)

| Component | File | Stores | Services |
|-----------|------|--------|----------|
| AssetUploader | `materials/AssetUploader.vue` | - | - |
| EnvironmentSettings | `materials/EnvironmentSettings.vue` | - | - |
| MaterialEditor | `materials/MaterialEditor.vue` | - | - |
| TextureUpload | `materials/TextureUpload.vue` | - | - |

### Panels Components (10)

| Component | File | Stores | Services |
|-----------|------|--------|----------|
| AssetsPanel | `panels/AssetsPanel.vue` | compositorStore | - |
| AudioPanel | `panels/AudioPanel.vue` | compositorStore | audioFeatures |
| CameraProperties | `panels/CameraProperties.vue` | compositorStore | - |
| DriverList | `panels/DriverList.vue` | compositorStore | propertyDriver |
| EffectControlsPanel | `panels/EffectControlsPanel.vue` | compositorStore | - |
| EffectsPanel | `panels/EffectsPanel.vue` | compositorStore | - |
| ExportPanel | `panels/ExportPanel.vue` | compositorStore | videoEncoder |
| PreviewPanel | `panels/PreviewPanel.vue` | compositorStore | - |
| ProjectPanel | `panels/ProjectPanel.vue` | compositorStore | - |
| PropertiesPanel | `panels/PropertiesPanel.vue` | compositorStore | propertyDriver |

### Properties Components (10)

| Component | File | Stores | Services |
|-----------|------|--------|----------|
| AudioProperties | `properties/AudioProperties.vue` | compositorStore | audioFeatures |
| CameraProperties | `properties/CameraProperties.vue` | compositorStore | - |
| DepthflowProperties | `properties/DepthflowProperties.vue` | compositorStore | - |
| KeyframeToggle | `properties/KeyframeToggle.vue` | compositorStore | - |
| LightProperties | `properties/LightProperties.vue` | compositorStore | - |
| ParticleProperties | `properties/ParticleProperties.vue` | compositorStore | particleSystem |
| PrecompProperties | `properties/PrecompProperties.vue` | compositorStore | - |
| ShapeProperties | `properties/ShapeProperties.vue` | compositorStore | - |
| TextProperties | `properties/TextProperties.vue` | compositorStore | - |
| VideoProperties | `properties/VideoProperties.vue` | compositorStore | - |

### Timeline Components (9)

| Component | File | Stores | Services |
|-----------|------|--------|----------|
| AudioMappingCurve | `timeline/AudioMappingCurve.vue` | compositorStore | - |
| AudioTrack | `timeline/AudioTrack.vue` | compositorStore | audioFeatures |
| CompositionTabs | `timeline/CompositionTabs.vue` | compositorStore | - |
| EnhancedLayerTrack | `timeline/EnhancedLayerTrack.vue` | compositorStore | - |
| CurveEditorCanvas | `curve-editor/CurveEditorCanvas.vue` | compositorStore | interpolation |
| LayerTrack | `timeline/LayerTrack.vue` | compositorStore | - |
| Playhead | `timeline/Playhead.vue` | compositorStore | - |
| PropertyTrack | `timeline/PropertyTrack.vue` | compositorStore | - |
| TimelinePanel | `timeline/TimelinePanel.vue` | compositorStore | timelineSnap |

### Viewport Components (2)

| Component | File | Stores | Services |
|-----------|------|--------|----------|
| ViewOptionsToolbar | `viewport/ViewOptionsToolbar.vue` | compositorStore | - |
| ViewportRenderer | `viewport/ViewportRenderer.vue` | compositorStore | - |

---

## Store Architecture

### Central Store: compositorStore

**Location**: `ui/src/stores/compositorStore.ts`

All 39 store-using components depend on the single `compositorStore`. This store delegates to modular sub-stores:

```typescript
// compositorStore structure
compositorStore
├── State
│   ├── project: WeylProject
│   ├── compositions: Composition[]
│   ├── activeCompositionId: string
│   └── ... (see full definition)
│
├── Delegated Stores
│   ├── playbackStore      // Play/pause, frame control
│   ├── selectionStore     // Layer/keyframe selection
│   ├── historyStore       // Undo/redo
│   └── projectActions     // Project-level operations
│
└── Actions
    ├── Layer manipulation
    ├── Keyframe operations
    ├── Effect management
    └── Composition control
```

### Modular Sub-Stores

| Store | Purpose | Key Methods |
|-------|---------|-------------|
| `playbackStore` | Playback state | `play()`, `pause()`, `setFrame()` |
| `selectionStore` | Selection state | `selectLayer()`, `selectKeyframes()` |
| `historyStore` | Undo/redo | `push()`, `undo()`, `redo()` |

---

## Service Usage Heatmap

Services sorted by number of component dependencies:

| Service | Components Using | Category |
|---------|------------------|----------|
| `propertyDriver` | 4 | Animation |
| `audioFeatures` | 3 | Audio |
| `compositorStore` (actions) | 39 | State |
| `matteExporter` | 1 | Export |
| `fontService` | 1 | Asset |
| `particleSystem` | 1 | Particle |
| `timelineSnap` | 1 | Utility |
| `interpolation` | 1 | Animation |
| `segmentation` | 1 | AI |
| `visionAuthoring` | 1 | AI |
| `videoEncoder` | 1 | Export |
| `exportPipeline` | 1 | Export |
| `comfyuiClient` | 1 | Integration |
| `colorUtils` | 1 | Utility |

---

## Data Flow Examples

### Example 1: Adding a Keyframe

```
User clicks "Add Keyframe" in KeyframeToggle.vue
    │
    ▼
KeyframeToggle calls compositorStore.addKeyframe(layerId, propertyPath, frame, value)
    │
    ▼
compositorStore updates layer.properties[prop].keyframes
    │
    ▼
historyStore.push() records the change
    │
    ▼
Vue reactivity triggers TimelinePanel to re-render
    │
    ▼
layerEvaluationCache marks layer dirty
```

### Example 2: Audio Analysis

```
User loads audio file in AudioPanel.vue
    │
    ▼
AudioPanel calls audioFeatures.loadAudioFile(file)
    │
    ▼
audioFeatures.analyzeAudio(buffer, config)
    │
    ▼
Returns AudioAnalysis { amplitude, beats, bpm, ... }
    │
    ▼
compositorStore.setAudioAnalysis(analysis)
    │
    ▼
AudioTrack.vue renders waveform from analysis.amplitude
    │
    ▼
TimelinePanel shows beat markers from analysis.beats
```

### Example 3: Property Linking (PropertyLink)

```
User drags property link from PropertyLink.vue to target property
    │
    ▼
PropertyLink.vue calls propertyDriver.createPropertyLink(source, target)
    │
    ▼
PropertyDriverSystem.addDriver(driver)
    │
    ▼
PropertyDriverSystem.buildDependencyGraph()
    │
    ▼
On each frame evaluation:
    propertyDriver.evaluate(frame, audioAnalysis)
    │
    ▼
Target property receives source property value
```

---

## Component Count Summary

| Category | Count | Store Usage | Service Usage |
|----------|-------|-------------|---------------|
| Canvas | 4 | 75% | 50% |
| Controls | 7 | 0% | 29% |
| Dialogs | 4 | 75% | 50% |
| Export | 1 | 100% | 100% |
| Graph Editor | 1 | 0% | 0% |
| Layout | 1 | 100% | 0% |
| Materials | 4 | 0% | 0% |
| Panels | 10 | 100% | 40% |
| Properties | 10 | 100% | 20% |
| Timeline | 9 | 100% | 11% |
| Viewport | 2 | 100% | 0% |
| **Total** | **55** | **71%** | **25%** |

---

## Key Insights

1. **Centralized State**: All store-dependent components use `compositorStore` exclusively
2. **Service Isolation**: Most components don't directly call services; they go through the store
3. **Audio Integration**: Audio services are used by 3 components (AudioPanel, AudioTrack, AudioProperties)
4. **Property Driver**: Most connected service (4 components for property linking)
5. **Stateless Controls**: Control components (sliders, dials) are pure UI, no store dependencies

---

**See also**:
- [ARCHITECTURE.md](./ARCHITECTURE.md) - System architecture
- [SERVICE_API_REFERENCE.md](./SERVICE_API_REFERENCE.md) - Service API index

*Generated: December 23, 2025*
