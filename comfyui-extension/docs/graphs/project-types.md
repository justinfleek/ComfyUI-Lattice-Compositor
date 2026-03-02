# types/project.ts Dependency Analysis

> Generated: 2026-01-10
> Recon only - no changes

## File Stats
- **Lines:** 2,194
- **Location:** `ui/src/types/project.ts`
- **Role:** Core type definitions - the schema for the entire project

---

## IMPORTS (What it depends on) - 10 type modules

| Import | From |
|--------|------|
| `AnimatableProperty`, `createAnimatableProperty` | `./animation` |
| `EffectInstance` | `./effects` |
| `GlobalLightSettings`, `LayerStyles` | `./layerStyles` |
| `LayerMask`, `MatteType` | `./masks` |
| `ParticleData`, `ParticleLayerData` | `./particles` |
| `ShapeLayerData` | `./shapes` |
| `PathLayerData`, `SplineData` | `./spline` |
| `TemplateConfig` | `./templateBuilder` |
| `TextData` | `./text` |
| `LayerTransform`, `Vec3` | `./transform` |

### Re-exports (Barrel Pattern)
This file re-exports types from modular files for backwards compatibility:
- `./animation` - Keyframe, InterpolationType, BezierHandle, etc.
- `./effects` - EffectInstance
- `./layerStyles` - LayerStyles, GlobalLightSettings
- `./masks` - LayerMask, MaskMode, MatteType, etc.
- `./particles` - All particle types (30+)
- `./shapes` - ShapeLayerData
- `./spline` - ControlPoint, SplineData, PathLayerData, etc.
- `./templateBuilder` - TemplateConfig
- `./text` - TextData, TextAnimator, etc.
- `./transform` - LayerTransform, Vec2, Vec3

---

## DEPENDENTS (What imports it) - 168 direct imports, 95+ actual users (VERIFIED)

**Blast radius: 95+ files use `Layer` type alone (verified via symbol usage)**

> Verified 2026-01-10: Direct import count was 168, but actual symbol usage varies by export.
> Key symbols: Layer (95+ files), Composition (56 files), Keyframe (54 files)

### By Category

| Category | Count |
|----------|-------|
| Components | 59 |
| Services | 41 |
| Engine | 26 |
| Stores/Actions | 22 |
| Composables | 8 |
| Types | 2 |

---

### Components (59 files)

#### components/canvas/ (4)
- MaskEditor.vue
- MotionPathOverlay.vue
- SplineEditor.vue
- ThreeCanvas.vue

#### components/curve-editor/ (4)
- CurveEditor.vue
- CurveEditorCanvas.vue
- CurveEditorPropertyList.vue

#### components/dialogs/ (6)
- KeyframeInterpolationDialog.vue
- SmootherPanel.vue
- TemplateBuilderDialog.vue
- TimeStretchDialog.vue
- VectorizeDialog.vue

#### components/export/ (1)
- ComfyUIExportDialog.vue

#### components/layout/ (1)
- WorkspaceLayout.vue

#### components/materials/ (3)
- AssetUploader.vue
- MaterialEditor.vue
- TextureUpload.vue

#### components/panels/ (2)
- ExposedPropertyControl.vue
- PropertiesPanel.vue

#### components/properties/ (20)
- CameraProperties.vue
- ControlProperties.vue
- DepthflowProperties.vue
- DepthProperties.vue
- ExpressionInput.vue
- GeneratedProperties.vue
- GroupProperties.vue
- KeyframeToggle.vue
- LightProperties.vue
- MatteProperties.vue
- NestedCompProperties.vue
- NormalProperties.vue
- ParticleProperties.vue
- PathProperties.vue
- PoseProperties.vue
- ShapeLayerProperties.vue
- ShapeProperties.vue
- SolidProperties.vue
- TextProperties.vue
- VideoProperties.vue

#### components/properties/particle/ (8)
- ParticleAudioBindingsSection.vue
- ParticleCollisionSection.vue
- ParticleFlockingSection.vue
- ParticleForceFieldsSection.vue
- ParticleModulationsSection.vue
- ParticleRenderSection.vue
- ParticleSubEmittersSection.vue
- ParticleTurbulenceSection.vue

#### components/properties/styles/ (9)
- BevelEmbossEditor.vue
- ColorOverlayEditor.vue
- DropShadowEditor.vue
- GradientOverlayEditor.vue
- InnerGlowEditor.vue
- InnerShadowEditor.vue
- OuterGlowEditor.vue
- SatinEditor.vue
- StrokeEditor.vue

#### components/timeline/ (4)
- CompositionTabs.vue
- LayerTrack.vue
- PropertyTrack.vue
- TimelinePanel.vue

---

### Services (41 files)

#### services/ai/ (2)
- actionExecutor.ts
- stateSerializer.ts

#### services/effects/ (3)
- layerStyleRenderer.ts
- maskRenderer.ts

#### services/export/ (2)
- depthRenderer.ts
- exportPipeline.ts

#### services/expressions/ (6)
- audioExpressions.ts
- expressionHelpers.ts
- expressionValidator.ts
- loopExpressions.ts
- motionExpressions.ts
- types.ts

#### services/visionAuthoring/ (2)
- MotionIntentTranslator.ts
- types.ts

#### services/ (root - 26)
- blendModes.ts
- effectProcessor.ts
- globalLight.ts
- interpolation.ts
- layerEvaluationCache.ts
- layerTime.ts
- materialSystem.ts
- matteExporter.ts
- meshDeformation3D.ts
- meshWarpDeformation.ts
- midiToKeyframes.ts
- modelExport.ts
- motionReactivity.ts
- motionRecording.ts
- persistenceService.ts
- projectCollection.ts
- projectStorage.ts
- rovingKeyframes.ts
- segmentToMask.ts
- svgExport.ts
- templateBuilder.ts
- textAnimator.ts
- textOnPath.ts
- textToVector.ts
- timelineSnap.ts
- timewarp.ts
- vectorize.ts
- vectorLOD.ts

---

### Engine (26 files)

#### engine/core/ (3)
- CameraController.ts
- LayerManager.ts
- ResourceManager.ts

#### engine/animation/ (1)
- KeyframeEvaluator.ts

#### engine/layers/ (20 - ALL layer types)
- AudioLayer.ts
- BaseLayer.ts
- CameraLayer.ts
- ControlLayer.ts
- DepthflowLayer.ts
- DepthLayer.ts
- EffectLayer.ts
- GeneratedLayer.ts
- GroupLayer.ts
- ImageLayer.ts
- LightLayer.ts
- ModelLayer.ts
- NestedCompLayer.ts
- NormalLayer.ts
- ParticleLayer.ts
- PathLayer.ts
- PointCloudLayer.ts
- PoseLayer.ts
- ProceduralMatteLayer.ts
- ShapeLayer.ts
- SolidLayer.ts
- SplineLayer.ts
- TextLayer.ts
- VideoLayer.ts

#### engine/ (root - 3)
- LatticeEngine.ts
- MotionEngine.ts
- NestedCompRenderer.ts
- types.ts

---

### Stores & Actions (22 files)

#### stores/actions/ (18)
- audioActions.ts
- cameraActions.ts
- compositionActions.ts
- depthflowActions.ts
- effectActions.ts
- keyframeActions.ts
- layerActions.ts
- layerDecompositionActions.ts
- layerStyleActions.ts
- markerActions.ts
- particleLayerActions.ts
- physicsActions.ts
- playbackActions.ts
- projectActions.ts
- segmentationActions.ts
- textAnimatorActions.ts
- videoActions.ts
- keyframes/keyframeExpressions.ts
- layer/layerDefaults.ts
- layer/splineActions.ts
- layers/layerTimeActions.ts

#### stores/ (3)
- audioStore.ts
- compositorStore.ts
- historyStore.ts

---

### Composables (8 files)
- useCurveEditorCoords.ts
- useCurveEditorDraw.ts
- useCurveEditorInteraction.ts
- useCurveEditorKeyboard.ts
- useCurveEditorView.ts
- useExpressionEditor.ts
- useSplineInteraction.ts
- useSplineUtils.ts

---

### Types (2 files)
- types/index.ts (barrel)
- types/project.ts (self-reference for re-exports)

---

## Dependency Graph

```
┌─────────────────────────────────────────────────────────────┐
│                    types/project.ts                          │
│                      (2,194 lines)                          │
├─────────────────────────────────────────────────────────────┤
│  IMPORTS FROM (10 type modules)                             │
│  ├── ./animation                                            │
│  ├── ./effects                                              │
│  ├── ./layerStyles                                          │
│  ├── ./masks                                                │
│  ├── ./particles                                            │
│  ├── ./shapes                                               │
│  ├── ./spline                                               │
│  ├── ./templateBuilder                                      │
│  ├── ./text                                                 │
│  └── ./transform                                            │
├─────────────────────────────────────────────────────────────┤
│  IMPORTED BY (168 files) ← BLAST RADIUS                     │
│  ├── 59 components                                          │
│  ├── 41 services                                            │
│  ├── 26 engine files                                        │
│  ├── 22 stores/actions                                      │
│  ├── 8 composables                                          │
│  └── 2 types                                                │
└─────────────────────────────────────────────────────────────┘
```

---

## Risk Assessment

**Risk Level: CRITICAL**

This is the foundational type system. Every change propagates to 168 files. The file acts as a "barrel" re-exporting from 10 modular type files.

### Already Partially Modularized

The types have been split into domain modules:
- `animation.ts` - Keyframes, interpolation
- `effects.ts` - Effect definitions
- `layerStyles.ts` - Layer style types
- `masks.ts` - Mask and matte types
- `particles.ts` - Particle system types
- `shapes.ts` - Shape layer types
- `spline.ts` - Spline/path types
- `text.ts` - Text layer types
- `transform.ts` - Transform types

### Remaining in project.ts

Types defined directly in this file (not extracted):
- `LatticeProject` - Root project type
- `Composition` - Composition container
- `CompositionSettings` - Dimensions, FPS, etc.
- `Layer` - Base layer type (union of all layer types)
- `AssetReference` - Asset metadata
- `WorkflowInput/Output` - ComfyUI integration
- Various layer data types (ImageData, VideoData, etc.)

### Modularization Strategy

1. **Do NOT change the public API** - 168 files depend on importing from `@/types/project`
2. **Continue extracting types** to domain modules
3. **Keep re-exports** in project.ts for backwards compatibility
4. **Never remove re-exports** - only add new ones
