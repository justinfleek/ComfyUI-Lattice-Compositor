# compositorStore.ts Dependency Analysis

> Generated: 2026-01-10
> Recon only - no changes

## File Stats
- **Lines:** 3,292
- **Location:** `ui/src/stores/compositorStore.ts`
- **Role:** Central state management for the compositor

---

## IMPORTS (What it depends on) - 32 dependencies

### External Libraries
| Import | From |
|--------|------|
| `defineStore` | `pinia` |

### Engine Layer (5)
| Import | From |
|--------|------|
| `VideoMetadata` (type) | `@/engine/layers/VideoLayer` |
| `FrameState` (type), `motionEngine` | `@/engine/MotionEngine` |
| `ParticleSnapshot` (type), `particleSimulationRegistry` | `@/engine/ParticleSimulationController` |

### Services (12)
| Import | From |
|--------|------|
| `AudioAnalysis`, `PeakData`, `PeakDetectionConfig` (types) | `@/services/audioFeatures` |
| `AudioPathAnimator`, `PathAnimatorConfig` (types) | `@/services/audioPathAnimator` |
| `AudioMapping`, `AudioReactiveMapper`, `TargetParameter` (types) | `@/services/audioReactiveMapping` |
| `CacheStats` (type) | `@/services/frameCache` |
| `interpolateProperty` | `@/services/interpolation` |
| `markLayerDirty` | `@/services/layerEvaluationCache` |
| `PropertyDriver`, `PropertyDriverSystem`, `PropertyPath` | `@/services/propertyDriver` |
| `SegmentationPoint` (type) | `@/services/segmentation` |
| `DEFAULT_SNAP_CONFIG`, `findNearestSnap`, `getBeatFrames`, `getPeakFrames`, `SnapConfig`, `SnapResult` | `@/services/timelineSnap` |

### Types (3)
| Import | From |
|--------|------|
| `Camera3D`, `CameraKeyframe`, `ViewOptions`, `ViewportState`, `createDefaultViewOptions`, `createDefaultViewportState` | `@/types/camera` |
| 18 types including `Layer`, `Composition`, `LatticeProject`, etc. | `@/types/project` |
| `createEmptyProject` | `@/types/project` |

### Utils (1)
| Import | From |
|--------|------|
| `storeLogger` | `@/utils/logger` |

### Internal Store Actions (16 action modules)
| Import | From |
|--------|------|
| `* as audioActions` | `./actions/audioActions` |
| `* as cacheActions` | `./actions/cacheActions` |
| `* as cameraActions` | `./actions/cameraActions` |
| `* as compositionActions` | `./actions/compositionActions` |
| `* as depthflowActions` | `./actions/depthflowActions` |
| `* as effectActions` | `./actions/effectActions` |
| `* as keyframeActions` | `./actions/keyframeActions` |
| `* as layerActions` | `./actions/layerActions` |
| `* as markerActions` | `./actions/markerActions` |
| `* as particleLayerActions` | `./actions/particleLayerActions` |
| `* as playbackActions` | `./actions/playbackActions` |
| `* as projectActions` | `./actions/projectActions` |
| `* as propertyDriverActions` | `./actions/propertyDriverActions` |
| `* as segmentationActions` | `./actions/segmentationActions` |
| `* as textAnimatorActions` | `./actions/textAnimatorActions` |
| `* as videoActions` | `./actions/videoActions` |

### Sibling Stores (2)
| Import | From |
|--------|------|
| `useAudioStore` | `./audioStore` |
| `useSelectionStore` | `./selectionStore` |

---

## DEPENDENTS (What imports it) - 101 files (VERIFIED)

**Blast radius: 101 production files actually use `useCompositorStore`**

> Verified 2026-01-10 via: `grep -r "useCompositorStore" | cut -d: -f1 | sort -u | wc -l`

### By Category

| Category | Count |
|----------|-------|
| Components | 88 |
| Composables | 7 |
| Services | 4 |
| Store Actions | 8 |
| Sibling Stores | 3 |

### Components (88 files)

#### components/canvas/ (5)
- MaskEditor.vue
- MeshWarpPinEditor.vue
- MotionPathOverlay.vue
- SplineEditor.vue
- ThreeCanvas.vue

#### components/curve-editor/ (2)
- CurveEditor.vue
- CurveEditorCanvas.vue

#### components/dialogs/ (12)
- CompositionSettingsDialog.vue
- DecomposeDialog.vue
- ExportDialog.vue
- FrameInterpolationDialog.vue
- MotionSketchPanel.vue
- PathSuggestionDialog.vue
- SmootherPanel.vue
- TemplateBuilderDialog.vue
- TimeStretchDialog.vue
- VectorizeDialog.vue

#### components/export/ (1)
- ComfyUIExportDialog.vue

#### components/layout/ (4)
- MenuBar.vue
- RightSidebar.vue
- WorkspaceLayout.vue
- WorkspaceToolbar.vue

#### components/panels/ (19)
- AIGeneratePanel.vue
- AlignPanel.vue
- AssetsPanel.vue
- AudioPanel.vue
- AudioValuePreview.vue
- CameraProperties.vue
- DriverList.vue
- EffectControlsPanel.vue
- EffectsPanel.vue
- ExportPanel.vue
- ExposedPropertyControl.vue
- GenerativeFlowPanel.vue
- LayerDecompositionPanel.vue
- Model3DProperties.vue
- PreviewPanel.vue
- ProjectPanel.vue
- PropertiesPanel.vue
- RenderQueuePanel.vue
- ScopesPanel.vue

#### components/preview/ (1)
- HDPreviewWindow.vue

#### components/properties/ (24)
- AudioProperties.vue
- CameraProperties.vue
- DepthflowProperties.vue
- DepthProperties.vue
- ExpressionInput.vue
- GeneratedProperties.vue
- GroupProperties.vue
- KeyframeToggle.vue
- LightProperties.vue
- MatteProperties.vue
- NestedCompProperties.vue
- ParticleProperties.vue
- PathProperties.vue
- PhysicsProperties.vue
- PoseProperties.vue
- ShapeLayerProperties.vue
- ShapeProperties.vue
- SolidProperties.vue
- TextProperties.vue
- VideoProperties.vue
- styles/LayerStylesPanel.vue

#### components/properties/shape-editors/ (17)
- EllipseEditor.vue
- FillEditor.vue
- GradientFillEditor.vue
- GradientStrokeEditor.vue
- OffsetPathsEditor.vue
- PolygonEditor.vue
- PuckerBloatEditor.vue
- RectangleEditor.vue
- RepeaterEditor.vue
- RoundedCornersEditor.vue
- StarEditor.vue
- StrokeEditor.vue
- TransformEditor.vue
- TrimPathsEditor.vue
- TwistEditor.vue
- WigglePathsEditor.vue
- ZigZagEditor.vue

#### components/timeline/ (6)
- CompositionTabs.vue
- EnhancedLayerTrack.vue
- LayerTrack.vue
- Playhead.vue
- PropertyTrack.vue
- TimelinePanel.vue

#### components/viewport/ (2)
- ViewOptionsToolbar.vue
- ViewportRenderer.vue

### Composables (7)
- useAssetHandlers.ts
- useCanvasSegmentation.ts
- useExpressionEditor.ts
- useKeyboardShortcuts.ts
- useMenuActions.ts
- useShapeDrawing.ts
- useViewportGuides.ts

### Services (4)
- ai/actionExecutor.ts
- ai/stateSerializer.ts
- cameraTrackingImport.ts
- preprocessorService.ts

### Store Actions (8)
- actions/audioActions.ts
- actions/cacheActions.ts
- actions/compositionActions.ts
- actions/depthflowActions.ts
- actions/particleLayerActions.ts
- actions/playbackActions.ts
- actions/propertyDriverActions.ts
- actions/videoActions.ts

### Sibling Stores (3)
- audioStore.ts
- audioSync.ts
- historyStore.ts
- playbackStore.ts
- selectionStore.ts
- stores/index.ts

---

## Dependency Graph

```
┌─────────────────────────────────────────────────────────────┐
│                    compositorStore.ts                        │
│                      (3,292 lines)                          │
├─────────────────────────────────────────────────────────────┤
│  IMPORTS FROM (32 dependencies)                             │
│  ├── 1 external (pinia)                                     │
│  ├── 5 engine modules                                       │
│  ├── 12 services                                            │
│  ├── 3 type modules                                         │
│  ├── 1 utils                                                │
│  ├── 16 action modules (./actions/*)                        │
│  └── 2 sibling stores                                       │
├─────────────────────────────────────────────────────────────┤
│  IMPORTED BY (101 files) ← BLAST RADIUS (VERIFIED)          │
│  ├── 88 components                                          │
│  ├── 7 composables                                          │
│  ├── 4 services                                             │
│  ├── 8 store actions                                        │
│  └── 3 sibling stores                                       │
└─────────────────────────────────────────────────────────────┘
```

---

## Risk Assessment

**Risk Level: HIGH**

This is the central nervous system of the application. Any modularization must preserve the exact same public API or it will break 110 files.

### Modularization Strategy (if attempted)

1. **Extract state slices** - Move related state into separate stores
   - `audioState` → dedicated audio store (partially done with audioStore)
   - `cameraState` → dedicated camera store
   - `segmentationState` → dedicated segmentation store

2. **Keep facade** - compositorStore becomes a thin facade that re-exports from sub-stores

3. **Preserve API** - All existing method signatures must remain unchanged

4. **Incremental migration** - One state slice at a time with full test coverage
