# MASTER REFACTOR PLAN

> **Target:** Modularize 232 files over 500 lines to ≤500 lines each
> **Scope:** Full codebase refactoring - stores, services, engine, components, types
> **Duration:** 12 months (42 weeks store migration + 6 weeks lazy code cleanup + file modularization)
> **Generated:** 2026-01-10
> **Updated:** 2026-01-12 (Added Phase 5.5: Lazy Code Cleanup - prevents pattern spreading during modularization)

---

## Related Documents

| Document | Purpose |
|----------|---------|
| [STORE_MIGRATION_CONSUMERS.md](STORE_MIGRATION_CONSUMERS.md) | All 99 consumer files with exact method usage |
| [CROSS_DOMAIN_ACTIONS.md](CROSS_DOMAIN_ACTIONS.md) | 19 cross-domain actions with coordination patterns |
| [compositorStore-target-architecture.md](graphs/compositorStore-target-architecture.md) | 12 domain store design |

---

## Table of Contents

1. [Executive Summary](#1-executive-summary)
2. [Complete File Inventory](#2-complete-file-inventory)
3. [Store Architecture](#3-store-architecture)
4. [Modularization Patterns](#4-modularization-patterns)
5. [Execution Phases](#5-execution-phases)
6. [Rollback Strategy](#6-rollback-strategy)
7. [Testing Checkpoints](#7-testing-checkpoints)
8. [Timeline](#8-timeline)

---

## 1. Executive Summary

### 🔴 CRITICAL: Security Pre-Requisite

> **Before ANY distribution:** Complete security hardening per `docs/SECURITY_THREAT_MODEL.md`

This system operates in a **HIGH-RISK threat environment**:
- Autonomous LLM agent with tool execution
- Untrusted templates from internet/users
- Third-party ComfyUI nodes executing arbitrary code
- Distributed via Nix packages to untrusted machines

**Security Phases (125-170 hours, Weeks 1-3):**
1. Schema validation at all untrusted boundaries (45-60 hrs)
2. LLM agent scope system with default deny (45-60 hrs)
3. Path traversal prevention (15-20 hrs)
4. ComfyUI output validation (20-30 hrs)

**Reference:** `docs/SECURITY_THREAT_MODEL.md` for complete threat analysis and implementation details.

---

### Current State
- **232 files** exceed the 500-line limit
- **293,457 total lines** in oversized files
- **compositorStore.ts** (3,292 lines, 101 users) is the critical bottleneck
- Previous refactor attempts failed due to chicken-and-egg dependencies
- **~4,954 lazy code patterns** in production code (verified 2026-01-13)
- **0 TypeScript errors** in production (96 in test files)

### Target State
- All files ≤500 lines
- **13 domain stores** replace compositorStore god object
- Clear separation of concerns with documented patterns
- No facades, no wrapper methods, no technical debt
- **Security-hardened** for untrusted input handling
- **Zero TypeScript errors**

### Breaking the Chicken-and-Egg Cycle

The December 2025 refactor stalled because cross-domain actions (like `convertAudioToKeyframes`) need multiple stores that don't exist yet. We break this by:

1. **Security FIRST** - Harden input validation before any distribution
2. **Create layerStore FIRST** - Most cross-domain actions need layer access
3. **Action modules already use dependency injection** - They accept `store` as first parameter
4. **Migrate incrementally** - One domain at a time, updating all consumers

---

## 2. Complete File Inventory

### Priority Classification

| Priority | Criteria | Files (Original) | Files (Verified 2026-01-13) | Action |
|----------|----------|------------------|------------------------------|--------|
| **P0** | >2000 lines | 12 | **5** | Modularize first |
| **P1** | 1500-2000 lines | 21 | **~27** | Second wave |
| **P2** | 1000-1500 lines | 45 | TBD | Third wave |
| **P3** | 500-1000 lines | 154 | TBD | Final wave |

**Note (2026-01-13):** File line counts have decreased. Only 5 files remain >2000 lines:
- types/effects.ts: 3,233
- compositorStore.ts: 2,683
- workflowTemplates.ts: 2,449
- ParticleProperties.vue: 2,449
- GPUParticleSystem.ts: 2,083

---

### 2.1 Types (9 files, 12,996 lines)

| File | Lines | Priority | Domain | Strategy |
|------|-------|----------|--------|----------|
| `types/effects.ts` | 3,319 | **P0** | effects | Split by effect category (color, blur, distort, stylize, time, etc.) |
| `types/project.ts` | 2,194 | **P0** | core | Extract Layer types, Composition types, Animation types to separate files |
| `types/physics.ts` | 990 | P3 | physics | Split: RigidBody, Constraints, Forces, Particles |
| `types/shapes.ts` | 844 | P3 | shapes | Split: Path, BezierCurve, ShapeOperations, PathModifiers |
| `types/presets.ts` | 824 | P3 | presets | Split by preset category |
| `types/layerStyles.ts` | 721 | P3 | effects | Merge with effect types or keep |
| `types/particles.ts` | 630 | P3 | particles | Split: Emitter, Physics, Rendering, Audio-reactive |
| `types/layerData.ts` | 559 | P3 | layers | Split by layer type |
| `types/transform.ts` | 549 | P3 | core | Can likely stay as-is |

---

### 2.2 Stores (11 files, 13,975 lines)

| File | Documented Lines | **Verified Lines** | Priority | Domain | Strategy |
|------|-----------------|-------------------|----------|--------|----------|
| `stores/compositorStore.ts` | 3,292 | **2,683** | **P0** | god object | **DELETE** - Replace with 12 domain stores |
| `stores/actions/keyframeActions.ts` | 2,023 | **TBD** | **P0** | keyframes | Move to keyframeStore |
| `stores/actions/layerActions.ts` | 1,847 | **TBD** | P1 | layers | Move to layerStore |
| `stores/actions/audioActions.ts` | 1,170 | P2 | audio | Move to audioStore |
| `stores/actions/textAnimatorActions.ts` | 1,134 | P2 | animation | Move to animationStore |
| `stores/assetStore.ts` | 1,015 | P2 | assets | Already domain store, needs internal split |
| `stores/actions/layerStyleActions.ts` | 864 | P3 | effects | Move to effectStore |
| `stores/actions/projectActions.ts` | 856 | P3 | project | Move to projectStore |
| `stores/audioStore.ts` | 746 | P3 | audio | **KEEP** - Expand with audioActions |
| `stores/actions/physicsActions.ts` | 708 | P3 | physics | Move to physicsStore |
| `stores/actions/videoActions.ts` | 673 | P3 | video | Split or move to layerStore |
| `stores/actions/layer/splineActions.ts` | 663 | P3 | layers | Move to layerStore |
| `stores/actions/compositionActions.ts` | 513 | P3 | compositions | Move to compositionStore |
| `stores/selectionStore.ts` | 511 | P3 | selection | Already domain store, keep |

---

### 2.3 Engine - Core (5 files, 6,479 lines)

| File | Lines | Priority | Domain | Strategy |
|------|-------|----------|--------|----------|
| `engine/LatticeEngine.ts` | 1,812 | P1 | engine | Extract: LayerRenderer, EffectPipeline, ViewportManager |
| `engine/MotionEngine.ts` | 1,486 | P1 | animation | Extract: PropertyResolver, CurveEvaluator, ExpressionCache |
| `engine/core/LayerManager.ts` | 1,433 | P2 | layers | Extract: LayerFactory, LayerLifecycle, LayerCache |
| `engine/core/RenderPipeline.ts` | 1,234 | P2 | rendering | Extract: PassManager, PostProcessing, OutputComposite |
| `engine/core/CameraController.ts` | 1,162 | P2 | camera | Extract: OrbitControls, CameraAnimator, ViewportSync |
| `engine/core/SceneManager.ts` | 1,138 | P2 | scene | Extract: SceneGraph, LightManager, EnvironmentManager |
| `engine/core/ResourceManager.ts` | 512 | P3 | resources | Can likely stay |

---

### 2.4 Engine - Layers (15 files, 16,714 lines)

| File | Lines | Priority | Domain | Strategy |
|------|-------|----------|--------|----------|
| `engine/layers/ParticleLayer.ts` | 2,201 | **P0** | particles | Extract: AudioBinding, SplineEmission, FrameCache, PropertyAnim |
| `engine/layers/BaseLayer.ts` | 2,120 | **P0** | layers | Extract: TransformManager, EffectApplicator, BlendModeHandler |
| `engine/layers/SplineLayer.ts` | 1,750 | P1 | shapes | Extract: SplineRenderer, SplineInteraction, SplineExport |
| `engine/layers/TextLayer.ts` | 1,523 | P1 | text | Extract: TextRenderer, TextAnimator, TextPath |
| `engine/layers/PointCloudLayer.ts` | 1,247 | P2 | 3d | Extract: PointRenderer, PointLoader, PointInteraction |
| `engine/layers/VideoLayer.ts` | 1,244 | P2 | video | Extract: VideoDecoder, VideoSync, VideoCache |
| `engine/layers/LightLayer.ts` | 1,208 | P2 | 3d | Extract by light type |
| `engine/layers/ProceduralMatteLayer.ts` | 1,051 | P2 | mattes | Extract: MatteGenerator, MatteBlending |
| `engine/layers/ShapeLayer.ts` | 1,009 | P2 | shapes | Extract: ShapeRenderer, ShapeOperations |
| `engine/layers/ModelLayer.ts` | 934 | P3 | 3d | Extract: ModelLoader, ModelMaterial, ModelAnimation |
| `engine/layers/CameraLayer.ts` | 818 | P3 | camera | Extract: CameraRenderer, CameraPath |
| `engine/layers/PoseLayer.ts` | 742 | P3 | pose | Extract: PoseRenderer, PoseImport |
| `engine/layers/PathLayer.ts` | 623 | P3 | paths | Can likely stay |
| `engine/layers/DepthflowLayer.ts` | 614 | P3 | depthflow | Can likely stay |
| `engine/layers/NestedCompLayer.ts` | 601 | P3 | composition | Can likely stay |

---

### 2.5 Engine - Particles (10 files, 9,074 lines)

| File | Lines | Priority | Domain | Strategy |
|------|-------|----------|--------|----------|
| `engine/particles/GPUParticleSystem.ts` | 2,330 | **P0** | particles | Extract: GPUEmitter, GPUPhysics, GPURenderer, GPUState |
| `engine/particles/ParticleGPUPhysics.ts` | 890 | P3 | particles | Can likely stay |
| `engine/particles/types.ts` | 763 | P3 | particles | Split by concern |
| `engine/particles/webgpuParticleCompute.ts` | 696 | P3 | particles | Can likely stay |
| `engine/particles/ParticleSpringSystem.ts` | 682 | P3 | particles | Can likely stay |
| `engine/particles/particleShaders.ts` | 675 | P3 | particles | Split by shader type |
| `engine/particles/ParticleCollisionSystem.ts` | 631 | P3 | particles | Can likely stay |
| `engine/particles/GPUSpringSystem.ts` | 619 | P3 | particles | Can likely stay |
| `engine/particles/GPUSPHSystem.ts` | 515 | P3 | particles | Can likely stay |
| `engine/particles/ParticleSPHSystem.ts` | 507 | P3 | particles | Can likely stay |

---

### 2.6 Services - Effects (12 files, 11,673 lines)

| File | Lines | Priority | Domain | Strategy |
|------|-------|----------|--------|----------|
| `services/effects/colorRenderer.ts` | 1,800 | P1 | effects | Split by color effect type |
| `services/effects/blurRenderer.ts` | 1,428 | P2 | effects | Split: GaussianBlur, DirectionalBlur, RadialBlur |
| `services/effects/distortRenderer.ts` | 1,254 | P2 | effects | Split: Wave, Ripple, Displacement, Bulge |
| `services/effects/stylizeRenderer.ts` | 1,151 | P2 | effects | Split: Posterize, Mosaic, Glow, etc. |
| `services/effects/layerStyleRenderer.ts` | 1,135 | P2 | effects | Split: DropShadow, InnerShadow, Stroke, Fill |
| `services/effects/timeRenderer.ts` | 1,046 | P2 | effects | Split: Echo, TimeWarp, FrameBlend |
| `services/effects/meshDeformRenderer.ts` | 926 | P3 | effects | Can likely stay |
| `services/effects/generateRenderer.ts` | 865 | P3 | effects | Split by generator type |
| `services/effects/cinematicBloom.ts` | 841 | P3 | effects | Can likely stay |
| `services/effects/colorGrading.ts` | 772 | P3 | effects | Can likely stay |
| `services/effects/maskRenderer.ts` | 707 | P3 | effects | Can likely stay |
| `services/effects/matteEdge.ts` | 687 | P3 | effects | Can likely stay |
| `services/effects/hdrRenderer.ts` | 673 | P3 | effects | Can likely stay |
| `services/effects/audioVisualizer.ts` | 570 | P3 | effects | Can likely stay |

---

### 2.7 Services - Export (7 files, 6,360 lines)

| File | Lines | Priority | Domain | Strategy |
|------|-------|----------|--------|----------|
| `services/export/wanMoveExport.ts` | 1,791 | P1 | export | Split by export type |
| `services/export/exportPipeline.ts` | 1,044 | P2 | export | Extract: FrameRenderer, OutputWriter, FormatConverter |
| `services/export/depthRenderer.ts` | 987 | P3 | export | Can likely stay |
| `services/export/cameraExportFormats.ts` | 796 | P3 | export | Can likely stay |
| `services/export/wanMoveFlowGenerators.ts` | 677 | P3 | export | Can likely stay |
| `services/export/vaceControlExport.ts` | 639 | P3 | export | Can likely stay |
| `services/export/meshDeformExport.ts` | 576 | P3 | export | Can likely stay |

---

### 2.8 Services - AI (6 files, 5,551 lines)

| File | Lines | Priority | Domain | Strategy |
|------|-------|----------|--------|----------|
| `services/ai/actionExecutor.ts` | 1,869 | P1 | ai | Split by action category |
| `services/ai/toolDefinitions.ts` | 1,300 | P2 | ai | Split by tool category |
| `services/ai/stateSerializer.ts` | 788 | P3 | ai | Can likely stay |
| `services/ai/AICompositorAgent.ts` | 619 | P3 | ai | Can likely stay |
| `services/ai/systemPrompt.ts` | 560 | P3 | ai | Can likely stay |
| `services/ai/cameraTrackingAI.ts` | 551 | P3 | ai | Can likely stay |

---

### 2.9 Services - Audio (5 files, 4,552 lines)

| File | Lines | Priority | Domain | Strategy |
|------|-------|----------|--------|----------|
| `services/audioFeatures.ts` | 1,710 | P1 | audio | Split: FFTAnalysis, BeatDetection, FeatureExtraction |
| `services/audioReactiveMapping.ts` | 1,345 | P2 | audio | Split: MappingEngine, MappingPresets, MappingUI |
| `services/audioPathAnimator.ts` | 726 | P3 | audio | Can likely stay |
| `services/audio/enhancedBeatDetection.ts` | 601 | P3 | audio | Can likely stay |
| `workers/audioWorker.ts` | 1,152 | P2 | audio | Split: FFTProcessor, PeakDetector, FeatureWorker |

---

### 2.10 Services - Physics (3 files, 3,221 lines)

| File | Lines | Priority | Domain | Strategy |
|------|-------|----------|--------|----------|
| `services/physics/PhysicsEngine.ts` | 1,883 | P1 | physics | Extract: RigidBodySim, CollisionDetection, ForceApplicator |
| `services/physics/JointSystem.ts` | 732 | P3 | physics | Can likely stay |
| `services/physics/RagdollBuilder.ts` | 606 | P3 | physics | Can likely stay |

---

### 2.11 Services - ComfyUI (2 files, 3,366 lines)

| File | Lines | Priority | Domain | Strategy |
|------|-------|----------|--------|----------|
| `services/comfyui/workflowTemplates.ts` | 2,715 | **P0** | comfyui | Split by workflow type (TTM, Uni3C, SCAIL, etc.) |
| `services/comfyui/comfyuiClient.ts` | 651 | P3 | comfyui | Can likely stay |

---

### 2.12 Services - Other (45 files, 32,137 lines)

| File | Lines | Priority | Domain | Strategy |
|------|-------|----------|--------|----------|
| `services/particleSystem.ts` | 2,299 | **P0** | particles | Extract: CPUEmitter, CPUPhysics, CPURenderer |
| `services/depthflow.ts` | 1,787 | P1 | depthflow | Split: DepthAnalysis, FlowGeneration, Rendering |
| `services/shapeOperations.ts` | 1,713 | P1 | shapes | Split: Boolean, Offset, Simplify operations |
| `services/index.ts` | 1,692 | P1 | barrel | **Consider removal** - barrel files cause circular deps |
| `services/webgpuRenderer.ts` | 1,517 | P1 | rendering | Split: PipelineManager, ShaderCompiler, BufferManager |
| `services/particleGPU.ts` | 1,324 | P2 | particles | Split: GPUBuffer, GPUShader, GPUState |
| `services/svgExtrusion.ts` | 1,206 | P2 | 3d | Can likely stay |
| `services/glsl/ShaderEffects.ts` | 1,150 | P2 | glsl | Split by shader category |
| `services/math3d.ts` | 1,047 | P2 | math | Split: Transforms, Quaternions, Matrices, Projections |
| `services/textAnimator.ts` | 1,002 | P2 | text | Split: CharacterAnimator, TextPath, TextEffects |
| `services/propertyDriver.ts` | 973 | P3 | expressions | Can likely stay |
| `services/blendModes.ts` | 934 | P3 | rendering | Can likely stay |
| `services/gpuEffectDispatcher.ts` | 926 | P3 | effects | Can likely stay |
| `services/effectProcessor.ts` | 913 | P3 | effects | **CRITICAL** - Fix canvas leaks first |
| `services/preprocessorService.ts` | 901 | P3 | comfyui | Can likely stay |
| `services/colorManagement/ColorProfileService.ts` | 896 | P3 | color | Can likely stay |
| `services/interpolation.ts` | 884 | P3 | animation | Can likely stay |
| `services/visionAuthoring/MotionIntentTranslator.ts` | 883 | P3 | ai | Can likely stay |
| `services/cameraTrackingImport.ts` | 854 | P3 | camera | Can likely stay |
| `services/renderQueue/RenderQueueManager.ts` | 840 | P3 | rendering | Can likely stay |
| `services/glsl/GLSLEngine.ts` | 837 | P3 | glsl | **CRITICAL** - Fix WebGL context loss first |
| `services/materialSystem.ts` | 821 | P3 | 3d | Can likely stay |
| `services/conditioningRenderer.ts` | 816 | P3 | comfyui | Can likely stay |
| `services/templateBuilder.ts` | 807 | P3 | templates | Can likely stay |
| `services/midiToKeyframes.ts` | 806 | P3 | midi | Can likely stay |
| `services/colorDepthReactivity.ts` | 793 | P3 | color | Can likely stay |
| `services/pathMorphing.ts` | 790 | P3 | shapes | Can likely stay |
| `services/video/transitions.ts` | 777 | P3 | video | Can likely stay |
| `services/midi/MIDIService.ts` | 777 | P3 | midi | Can likely stay |
| `services/motionBlur.ts` | 763 | P3 | effects | Can likely stay |
| `services/cameraEnhancements.ts` | 756 | P3 | camera | Can likely stay |
| `services/maskGenerator.ts` | 745 | P3 | masks | Can likely stay |
| `services/shape/pathModifiers.ts` | 737 | P3 | shapes | Can likely stay |
| `services/textShaper.ts` | 734 | P3 | text | Can likely stay |
| `services/meshWarpDeformation.ts` | 705 | P3 | mesh | Can likely stay |
| `services/meshParticleManager.ts` | 704 | P3 | particles | Can likely stay |
| `services/gpuParticleRenderer.ts` | 699 | P3 | particles | Can likely stay |
| `services/cameraTrajectory.ts` | 693 | P3 | camera | Can likely stay |
| `services/aiGeneration.ts` | 693 | P3 | ai | Can likely stay |
| `services/frameCache.ts` | 690 | P3 | cache | Can likely stay |
| `services/gaussianSplatting.ts` | 687 | P3 | 3d | Can likely stay |
| `services/imageTrace.ts` | 683 | P3 | vectorize | Can likely stay |
| `services/persistenceService.ts` | 681 | P3 | persistence | Can likely stay |
| `services/security/auditLog.ts` | 674 | P3 | security | Can likely stay |
| `services/textToVector.ts` | 673 | P3 | text | Can likely stay |
| `services/videoDecoder.ts` | 666 | P3 | video | Can likely stay |
| `services/dataImport.ts` | 665 | P3 | import | Can likely stay |
| `services/layerDecomposition.ts` | 656 | P3 | layers | Can likely stay |
| `services/expressions/expressionEvaluator.ts` | 651 | P3 | expressions | Can likely stay |
| `services/alphaToMesh.ts` | 644 | P3 | mesh | Can likely stay |
| `services/bezierBoolean.ts` | 635 | P3 | shapes | Can likely stay |
| `services/spriteSheet.ts` | 630 | P3 | sprites | Can likely stay |
| `services/segmentToMask.ts` | 628 | P3 | masks | Can likely stay |
| `services/motionRecording.ts` | 611 | P3 | recording | Can likely stay |
| `services/visionAuthoring/MotionIntentResolver.ts` | 603 | P3 | ai | Can likely stay |
| `services/vectorize.ts` | 601 | P3 | vectorize | Can likely stay |
| `services/particles/particleRenderer.ts` | 601 | P3 | particles | Can likely stay |
| `services/matteExporter.ts` | 597 | P3 | export | Can likely stay |
| `services/colorAnalysis/histogramService.ts` | 587 | P3 | color | Can likely stay |
| `services/trackPointService.ts` | 570 | P3 | tracking | Can likely stay |
| `services/memoryBudget.ts` | 559 | P3 | memory | Can likely stay |
| `services/plugins/PluginManager.ts` | 555 | P3 | plugins | Can likely stay |
| `services/meshDeformation3D.ts` | 551 | P3 | mesh | Can likely stay |
| `services/video/frameInterpolation.ts` | 530 | P3 | video | Can likely stay |
| `services/security/templateVerifier.ts` | 515 | P3 | security | Can likely stay |
| `services/expressions/sesEvaluator.ts` | 615 | P3 | expressions | Can likely stay |

---

### 2.13 Components - Properties (15 files, 16,051 lines)

| File | Lines | Priority | Domain | Strategy |
|------|-------|----------|--------|----------|
| `components/properties/ParticleProperties.vue` | 2,683 | **P0** | particles | Extract: EmitterSection, PhysicsSection, RenderingSection |
| `components/properties/TextProperties.vue` | 1,633 | P1 | text | Extract: FontSection, AnimatorSection, PathSection |
| `components/properties/ShapeProperties.vue` | 1,391 | P2 | shapes | Extract: PathSection, StrokeSection, FillSection |
| `components/panels/CameraProperties.vue` | 1,324 | P2 | camera | Extract: TransformSection, AnimationSection, LensSection |
| `components/properties/CameraProperties.vue` | 1,179 | P2 | camera | Merge with above or differentiate |
| `components/properties/DepthflowProperties.vue` | 990 | P3 | depthflow | Can likely stay |
| `components/properties/AudioProperties.vue` | 876 | P3 | audio | Can likely stay |
| `components/properties/PhysicsProperties.vue` | 799 | P3 | physics | Can likely stay |
| `components/properties/ExpressionInput.vue` | 680 | P3 | expressions | Can likely stay |
| `components/properties/VideoProperties.vue` | 626 | P3 | video | Can likely stay |
| `components/properties/styles/LayerStylesPanel.vue` | 595 | P3 | styles | Can likely stay |
| `components/properties/PoseProperties.vue` | 571 | P3 | pose | Can likely stay |
| `components/properties/PathProperties.vue` | 544 | P3 | paths | Can likely stay |
| `components/properties/particle/ParticleSPHSection.vue` | 535 | P3 | particles | Can likely stay |
| `components/properties/particle/ParticleSpringSection.vue` | 520 | P3 | particles | Can likely stay |

---

### 2.14 Components - Panels (16 files, 13,621 lines)

| File | Lines | Priority | Domain | Strategy |
|------|-------|----------|--------|----------|
| `components/panels/AudioPanel.vue` | 1,851 | P1 | audio | Extract: WaveformSection, MappingSection, AnalysisSection |
| `components/panels/PropertiesPanel.vue` | 1,707 | P1 | properties | Extract: PropertyRouter (decides which properties to show) |
| `components/panels/ProjectPanel.vue` | 1,451 | P2 | project | Extract: CompositionList, AssetBrowser, SettingsSection |
| `components/panels/AssetsPanel.vue` | 1,311 | P2 | assets | Extract: AssetGrid, AssetUpload, AssetPreview |
| `components/panels/LayerDecompositionPanel.vue` | 807 | P3 | decomposition | Can likely stay |
| `components/panels/RenderQueuePanel.vue` | 797 | P3 | render | Can likely stay |
| `components/panels/ExportPanel.vue` | 789 | P3 | export | Can likely stay |
| `components/panels/AIGeneratePanel.vue` | 740 | P3 | ai | Can likely stay |
| `components/panels/ExposedPropertyControl.vue` | 628 | P3 | properties | Can likely stay |
| `components/panels/AIChatPanel.vue` | 620 | P3 | ai | Can likely stay |
| `components/panels/PreviewPanel.vue` | 615 | P3 | preview | Can likely stay |
| `components/panels/Model3DProperties.vue` | 610 | P3 | 3d | Can likely stay |
| `components/panels/EffectControlsPanel.vue` | 605 | P3 | effects | Can likely stay |
| `components/panels/EffectsPanel.vue` | 604 | P3 | effects | Can likely stay |
| `components/panels/GenerativeFlowPanel.vue` | 587 | P3 | generative | Can likely stay |
| `components/panels/OutputModulePanel.vue` | 536 | P3 | output | Can likely stay |

---

### 2.15 Components - Canvas (6 files, 6,232 lines)

| File | Lines | Priority | Domain | Strategy |
|------|-------|----------|--------|----------|
| `components/canvas/ThreeCanvas.vue` | 2,197 | **P0** | canvas | Extract: useThreeScene, useCanvasInteraction, useCoordinates |
| `components/curve-editor/CurveEditorCanvas.vue` | 1,247 | P2 | curves | Extract logic to composables |
| `components/canvas/SplineEditor.vue` | 1,049 | P2 | splines | Extract logic to composables |
| `components/canvas/MaskEditor.vue` | 725 | P3 | masks | Can likely stay |
| `components/canvas/MeshWarpPinEditor.vue` | 647 | P3 | mesh | Can likely stay |
| `components/canvas/PathPreviewOverlay.vue` | 565 | P3 | paths | Can likely stay |

---

### 2.16 Components - Dialogs (13 files, 11,298 lines)

| File | Lines | Priority | Domain | Strategy |
|------|-------|----------|--------|----------|
| `components/dialogs/TemplateBuilderDialog.vue` | 1,591 | P1 | templates | Extract: TemplateForm, TemplatePreview, TemplateExport |
| `components/dialogs/PreferencesDialog.vue` | 1,376 | P2 | preferences | Split by preference category |
| `components/dialogs/ExportDialog.vue` | 1,061 | P2 | export | Extract: FormatSelector, QualitySettings, OutputPreview |
| `components/dialogs/DecomposeDialog.vue` | 997 | P3 | decomposition | Can likely stay |
| `components/dialogs/PathSuggestionDialog.vue` | 951 | P3 | paths | Can likely stay |
| `components/dialogs/CompositionSettingsDialog.vue` | 926 | P3 | composition | Can likely stay |
| `components/dialogs/VectorizeDialog.vue` | 862 | P3 | vectorize | Can likely stay |
| `components/dialogs/SmootherPanel.vue` | 692 | P3 | smoothing | Can likely stay |
| `components/dialogs/FrameInterpolationDialog.vue` | 687 | P3 | interpolation | Can likely stay |
| `components/dialogs/MotionSketchPanel.vue` | 665 | P3 | motion | Can likely stay |
| `components/dialogs/CameraTrackingImportDialog.vue` | 585 | P3 | camera | Can likely stay |
| `components/dialogs/TimeStretchDialog.vue` | 533 | P3 | time | Can likely stay |

---

### 2.17 Components - Timeline (4 files, 4,184 lines)

| File | Lines | Priority | Domain | Strategy |
|------|-------|----------|--------|----------|
| `components/timeline/EnhancedLayerTrack.vue` | 1,402 | P2 | timeline | Extract: TrackHeader, TrackContent, TrackInteraction |
| `components/timeline/TimelinePanel.vue` | 1,140 | P2 | timeline | Extract: TimeRuler, PlaybackControls, TimelineState |
| `components/timeline/PropertyTrack.vue` | 1,113 | P2 | timeline | Extract: KeyframeRenderer, PropertyEditor |
| `components/timeline/CompositionTabs.vue` | 529 | P3 | timeline | Can likely stay |

---

### 2.18 Components - Layout (5 files, 4,453 lines)

| File | Lines | Priority | Domain | Strategy |
|------|-------|----------|--------|----------|
| `components/layout/WorkspaceLayout.vue` | 1,768 | P1 | layout | Extract: PanelManager, SplitPaneController |
| `components/layout/WorkspaceToolbar.vue` | 797 | P3 | layout | Can likely stay |
| `components/layout/MenuBar.vue` | 772 | P3 | layout | Can likely stay |
| `components/layout/CenterViewport.vue` | 558 | P3 | layout | Can likely stay |

---

### 2.19 Components - Other (15 files, 10,181 lines)

| File | Lines | Priority | Domain | Strategy |
|------|-------|----------|--------|----------|
| `components/curve-editor/CurveEditor.vue` | 2,006 | **P0** | curves | Extract logic to composables (already partially done) |
| `components/export/ComfyUIExportDialog.vue` | 1,087 | P2 | export | Extract: WorkflowSelector, ParameterEditor, Preview |
| `components/viewport/ViewportRenderer.vue` | 922 | P3 | viewport | Can likely stay |
| `components/controls/ColorPicker.vue` | 862 | P3 | controls | Can likely stay |
| `components/materials/MaterialEditor.vue` | 670 | P3 | materials | Can likely stay |
| `components/materials/AssetUploader.vue` | 588 | P3 | materials | Can likely stay |
| `components/preferences/ParticlePreferencesPanel.vue` | 560 | P3 | preferences | Can likely stay |
| `components/preview/HDPreviewWindow.vue` | 529 | P3 | preview | Can likely stay |

---

### 2.20 Composables (4 files, 3,799 lines)

| File | Lines | Priority | Domain | Strategy |
|------|-------|----------|--------|----------|
| `composables/useKeyboardShortcuts.ts` | 1,766 | P1 | input | Split by shortcut category (edit, view, playback, tools) |
| `composables/useSplineInteraction.ts` | 908 | P3 | splines | Can likely stay |
| `composables/useCurveEditorInteraction.ts` | 617 | P3 | curves | Can likely stay |
| `composables/useSplineUtils.ts` | 508 | P3 | splines | Can likely stay |

---

### 2.21 Config & Utils (2 files, 1,633 lines)

| File | Lines | Priority | Domain | Strategy |
|------|-------|----------|--------|----------|
| `config/exportPresets.ts` | 1,071 | P2 | config | Split by export target |
| `utils/labColorUtils.ts` | 562 | P3 | utils | Can likely stay |

---

## 3. Store Architecture

### 3.1 Current State: God Object

```
compositorStore.ts (3,292 lines, 101 users)
├── Project state
├── Audio state
├── Camera state
├── History state
├── UI state
├── Selection state (delegated)
├── Segmentation state
├── Autosave state
└── 16 action module delegations
```

### 3.2 Target State: 13 Domain Stores

```
stores/
├── projectStore.ts       (project, compositions, settings)
├── layerStore.ts         (layers, transforms, hierarchy, TEXT ANIMATORS)
├── keyframeStore.ts      (keyframes, curves, interpolation)
├── animationStore.ts     (playback, scrubbing, preview)
├── audioStore.ts         (audio buffer, analysis, mappings)
├── effectStore.ts        (effects, styles, blend modes)
├── cameraStore.ts        (cameras, viewports, 3D view)
├── expressionStore.ts    (expressions, drivers, property links) ← NEW
├── selectionStore.ts     (selection state) ← EXISTS
├── historyStore.ts       (undo/redo stack) ← EXISTS
├── assetStore.ts         (assets, imports) ← EXISTS
├── physicsStore.ts       (physics simulation state)
└── uiStore.ts            (panels, layout, preferences, SEGMENTATION)
```

**Architecture Decisions:**
- **Text Animator methods** → layerStore (they operate on layer data)
- **Segmentation methods** → uiStore (UI tool state, not core data)
- **Expression methods** → expressionStore (complex enough for own domain)

### 3.3 Cross-Store Coordination Patterns

**Pattern 1: Return Data, Don't Mutate**
```typescript
// historyStore.ts - ALREADY USES THIS
undo(): LatticeProject | null {
  if (!this.canUndo) return null;
  this.index--;
  return structuredClone(toRaw(this.stack[this.index]));
}
```

**Pattern 2: Callbacks Instead of Imports**
```typescript
// playbackStore.ts - ALREADY USES THIS
play(fps, frameCount, currentFrame, onFrame: (frame: number) => void) {
  // ...
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
  this.keyframes[layerId] = this.keyframes[layerId] || {};
  this.keyframes[layerId][propertyPath].push({ frame, value });

  // Explicit history push
  useHistoryStore().pushState(this.getSnapshot());
}
```

### 3.4 Migration Order

1. **layerStore** - FIRST (breaks chicken-and-egg cycle, includes text animators)
2. **keyframeStore** - Depends on layerStore
3. **expressionStore** - Depends on layerStore, works with keyframeStore
4. **audioStore** - Expand existing store
5. **effectStore** - New store
6. **cameraStore** - New store
7. **animationStore** - New store
8. **physicsStore** - New store
9. **uiStore** - New store (includes segmentation)
10. **projectStore** - Last (inherits remaining compositorStore state)
11. **DELETE compositorStore** - Final step

---

## 4. Modularization Patterns

### 4.1 Pattern: Large Vue Component → Composables

**Before:** Single 2,000+ line component
```vue
<script setup lang="ts">
// 2,000 lines of mixed concerns
</script>
```

**After:** Component + Composables
```typescript
// useThreeScene.ts (~300 lines)
export function useThreeScene() { ... }

// useCanvasInteraction.ts (~400 lines)
export function useCanvasInteraction() { ... }

// useCoordinateSystems.ts (~200 lines)
export function useCoordinateSystems() { ... }
```

```vue
<script setup lang="ts">
// Component is now ~300 lines - orchestration only
import { useThreeScene } from './useThreeScene';
import { useCanvasInteraction } from './useCanvasInteraction';
import { useCoordinateSystems } from './useCoordinateSystems';

const { scene, camera, renderer } = useThreeScene();
const { onMouseDown, onMouseMove } = useCanvasInteraction(scene, camera);
const { screenToScene, sceneToScreen } = useCoordinateSystems(camera);
</script>
```

### 4.2 Pattern: Large Service → Domain Split

**Before:** Single 2,000+ line service
```typescript
// effectProcessor.ts (816 lines + growing)
export function processEffectStack() { ... }
export function applyBlur() { ... }
export function applyColor() { ... }
export function applyDistort() { ... }
```

**After:** Domain modules
```
services/effects/
├── effectProcessor.ts    (orchestrator, ~200 lines)
├── blurEffects.ts        (~300 lines)
├── colorEffects.ts       (~300 lines)
├── distortEffects.ts     (~300 lines)
└── index.ts              (public API)
```

### 4.3 Pattern: Large Type File → Category Split

**Before:** Single 3,000+ line type file
```typescript
// types/effects.ts (3,319 lines)
export interface BlurEffect { ... }
export interface ColorEffect { ... }
export interface DistortEffect { ... }
// ... 80+ more interfaces
```

**After:** Category files
```
types/effects/
├── blur.ts           (~300 lines)
├── color.ts          (~400 lines)
├── distort.ts        (~300 lines)
├── stylize.ts        (~300 lines)
├── time.ts           (~300 lines)
├── generate.ts       (~300 lines)
├── common.ts         (~200 lines)
└── index.ts          (re-exports all)
```

### 4.4 Pattern: Large Class → Composition

**Before:** Single 2,000+ line class
```typescript
class ParticleLayer extends BaseLayer {
  // 2,201 lines
  private updateAudio() { ... }
  private emitAlongSpline() { ... }
  private cacheFrame() { ... }
  private animateProperties() { ... }
}
```

**After:** Main class + helpers
```typescript
// ParticleLayer.ts (~500 lines)
class ParticleLayer extends BaseLayer {
  private audioBinding: ParticleAudioBinding;
  private splineEmitter: ParticleSplineEmission;
  private frameCache: ParticleFrameCache;
  private propertyAnim: ParticlePropertyAnim;
}

// ParticleAudioBinding.ts (~300 lines)
// ParticleSplineEmission.ts (~200 lines)
// ParticleFrameCache.ts (~400 lines)
// ParticlePropertyAnim.ts (~300 lines)
```

---

## 5. Execution Phases

### Phase 0: Critical Bug Fixes (Weeks 1-2) - MUST COMPLETE FIRST

**Goal:** Fix bugs that would corrupt test results or cause instability during refactor

| Bug | File | Fix | Why First |
|-----|------|-----|-----------|
| Canvas leak in processEffectStack | effectProcessor.ts:471-482 | Use CanvasPool.acquire() | ~500MB/sec GC pressure corrupts memory tests |
| Canvas leak in layerStyleRenderer | layerStyleRenderer.ts:80-89 | Integrate with CanvasPool | 7,500 leaked canvases/sec |
| WebGL context loss | GLSLEngine.ts | Add webglcontextlost handler | Crashes during long tests |
| URL.createObjectURL leak | exportPipeline.ts:1301 | Add revokeObjectURL | Memory growth during export tests |
| Cleanup functions never called | effectProcessor.ts:323-347 | Add cleanup in main.ts startup | Resources never released |
| releaseCanvas never called | All renderers | Add finally blocks | Canvas pool grows forever |

**Exit Criteria:**
- [x] No canvas leaks detected in 10-minute stress test ✅ 2026-01-10
- [x] WebGL context loss recovery tested ✅ 2026-01-10
- [x] Memory profile stable over 30-minute session ✅ 2026-01-10
- [x] All existing tests still pass ✅ 2026-01-10

**Phase 0 COMPLETE** (2026-01-10)
- BUG-243: Canvas leak in effectProcessor.ts → canvasPool.acquire()
- BUG-244: Canvas leak in layerStyleRenderer.ts → integrated with shared CanvasPool
- BUG-245: WebGL context loss → added event listeners in GLSLEngine.ts
- BUG-246: URL.createObjectURL leak → added revokeObjectURL in exportPipeline.ts
- BUG-247: Cleanup never called → added setInterval in main.ts
- BUG-248: releaseCanvas never called → added try/finally to all render functions

**Rollback Checkpoint:** Git tag `refactor/phase0-complete`

---

### Phase 1: Foundation (Weeks 3-10)

**Goal:** Create layerStore, break the chicken-and-egg cycle

| Week | Tasks |
|------|-------|
| 3-4 | Create layerStore interface, migrate createLayer/deleteLayer |
| 5-6 | Migrate layer transforms, hierarchy operations |
| 7-8 | Migrate remaining layerActions, update all consumers |
| 9-10 | Verification: All layer operations use layerStore |

**Files to Update (from STORE_MIGRATION_CONSUMERS.md):**
- 45 layer methods to migrate
- 99 consumer files, ~60 use layer methods
- CRITICAL files: useKeyboardShortcuts.ts, actionExecutor.ts, ThreeCanvas.vue

**Exit Criteria:**
- [ ] layerStore.ts < 500 lines
- [ ] layerActions.ts deleted or < 500 lines
- [ ] All layer consumers updated (see STORE_MIGRATION_CONSUMERS.md Section 2)
- [ ] Tests pass

**Rollback Checkpoint:** Git tag `refactor/phase1-complete`

---

### Phase 2: Keyframes, Animation & Expressions (Weeks 11-18)

**Goal:** Create keyframeStore, animationStore, expressionStore, and propertyEvaluator service

| Week | Tasks |
|------|-------|
| 11-12 | Create keyframeStore, migrate keyframeActions |
| 13-14 | Create animationStore, migrate playback logic |
| 15-16 | Create expressionStore, migrate expression methods |
| 17-18 | Create `services/propertyEvaluator.ts` for cross-domain property evaluation |

**New Service: propertyEvaluator.ts**
```typescript
// services/propertyEvaluator.ts (~200 lines)
// Handles cross-domain property evaluation without circular imports
export function evaluatePropertyAtFrame(layerId: string, propertyPath: string, frame: number): number {
  // 1. Check expressionStore for expression
  // 2. Check audioStore for audio mapping
  // 3. Fall back to keyframeStore interpolation
}
```

**Files to Update:**
- 35 keyframe methods, 20 animation methods, 15 expression methods to migrate
- CurveEditor.vue, CurveEditorCanvas.vue, TimelinePanel.vue, PropertyTrack.vue
- ExpressionInput.vue, ExposedPropertyControl.vue
- Cross-domain: jumpToNextKeyframe, jumpToPrevKeyframe, convertExpressionToKeyframes

**Exit Criteria:**
- [ ] keyframeStore.ts < 500 lines
- [ ] animationStore.ts < 500 lines
- [ ] expressionStore.ts < 500 lines
- [ ] propertyEvaluator.ts < 300 lines
- [ ] keyframeActions.ts deleted
- [ ] Tests pass

**Rollback Checkpoint:** Git tag `refactor/phase2-complete`

---

### Phase 3: Audio & Effects (Weeks 19-26)

**Goal:** Expand audioStore, create effectStore, resolve audio state duplication

| Week | Tasks |
|------|-------|
| 19-20 | **AUDIO DEDUPLICATION:** Remove duplicate state from compositorStore |
| 21-22 | Expand audioStore with remaining audioActions |
| 23-24 | Create effectStore, migrate effect state |
| 25-26 | Verification: All audio/effect operations use new stores |

**Audio State Deduplication (CRITICAL):**

Current state: Both `compositorStore` and `audioStore` have audio state:
```
compositorStore:           audioStore:
├── audioBuffer            ├── audioBuffer (duplicate!)
├── audioAnalysis          ├── audioAnalysis (duplicate!)
├── audioFile              ├── currentTrack
├── audioVolume            ├── volume
├── audioMuted             ├── muted
├── audioLoadingState      ├── loadingState
├── audioMappings          └── ...
├── audioReactiveMappings
└── pathAnimators
```

**Resolution:**
1. audioStore is the SINGLE source of truth
2. Week 19-20: Update AudioPanel.vue (27 compositorStore.audio* usages → audioStore)
3. Week 19-20: Update all other consumers (see STORE_MIGRATION_CONSUMERS.md)
4. Week 19-20: DELETE duplicate state from compositorStore
5. Cross-domain action `convertAudioToKeyframes` → Lives in audioStore, calls keyframeStore

**Files to Update:**
- AudioPanel.vue: 27 → 0 compositorStore audio usages
- AudioProperties.vue: 3 usages
- 5 other files with audio usages

**Exit Criteria:**
- [ ] audioStore.ts < 500 lines
- [ ] effectStore.ts < 500 lines
- [ ] audioActions.ts deleted
- [ ] **No audio state in compositorStore**
- [ ] Tests pass

**Rollback Checkpoint:** Git tag `refactor/phase3-complete`

---

### Phase 4: Camera & Physics (Weeks 27-34)

**Goal:** Create cameraStore and physicsStore

| Week | Tasks |
|------|-------|
| 27-28 | Create cameraStore, migrate camera state |
| 29-30 | Create physicsStore, migrate physics state |
| 31-32 | Migrate camera/physics panels and components |
| 33-34 | Verification: All camera/physics uses new stores |

**Files to Update:**
- 15 camera methods, viewportState, viewOptions
- CameraProperties.vue, ViewOptionsToolbar.vue, ThreeCanvas.vue
- PhysicsProperties.vue

**Exit Criteria:**
- [ ] cameraStore.ts < 500 lines
- [ ] physicsStore.ts < 500 lines
- [ ] Tests pass

**Rollback Checkpoint:** Git tag `refactor/phase4-complete`

---

### Phase 5: Project & Cleanup (Weeks 35-42)

**Goal:** Create projectStore, delete compositorStore

| Week | Tasks |
|------|-------|
| 35-36 | Create projectStore, migrate remaining state |
| 37-38 | Create uiStore, migrate UI state (tools, preferences, clipboard) |
| 39-40 | Update all remaining compositorStore consumers |
| 41-42 | **DELETE compositorStore.ts** |

**Final Consumer Migration:**
- 5 CRITICAL files remain: useKeyboardShortcuts.ts, useMenuActions.ts, actionExecutor.ts
- These files use 40+ methods across ALL domains
- Must be updated LAST after all domain stores exist

**Exit Criteria:**
- [ ] **compositorStore.ts DELETED**
- [ ] All 12 domain stores < 500 lines
- [ ] All 99 consumers migrated (verified via grep)
- [ ] Full integration test pass
- [ ] Manual smoke test all features

**Rollback Checkpoint:** Git tag `refactor/phase5-complete` (CRITICAL - last safe point before deletion)

---

### Phase 5.5: Lazy Code Cleanup (Weeks 43-48) - MUST COMPLETE BEFORE PHASE 6

**Goal:** Fix ~4,929 remaining lazy code patterns BEFORE modularization

**CRITICAL:** This phase MUST happen AFTER Phase 5 (compositorStore deleted) and BEFORE Phase 6 (file modularization). If we modularize files with lazy code patterns, we'll copy those patterns into new modules.

| Week | Tasks |
|------|-------|
| 43-44 | Automated detection: Find all lazy code patterns<br>- `as any`, `as unknown as`<br>- `!` non-null assertions<br>- `??`, `|| 0`, `|| []`, `|| {}` fallbacks<br>- `?.` optional chaining abuse<br>- `@ts-ignore`, `@ts-expect-error`<br>- NaN, Infinity, null handling<br>- `isFinite`, `isNaN` checks |
| 45-46 | Systematic fixes: Fix by pattern type, verify with tests<br>- Fix type assertions first<br>- Fix defensive guards<br>- Fix NaN/Infinity handling<br>- Replace with proper types/validation |
| 47-48 | Verification & cleanup<br>- TypeScript strict mode enabled<br>- All tests pass<br>- No new patterns introduced<br>- Document justified exceptions |

**Patterns to Fix:**
- `as any`, `as unknown as` type assertions
- `!` non-null assertions
- `??`, `|| 0`, `|| []`, `|| {}` fallbacks
- `?.` optional chaining abuse
- `@ts-ignore`, `@ts-expect-error`
- NaN, Infinity, null handling
- `isFinite`, `isNaN` checks
- And other lazy code patterns

**Why Before Phase 6:**
- Prevents spreading bad patterns into new modules
- Clean foundation for modularization
- Easier to fix in existing files than after splitting
- Prevents regression during modularization

**Exit Criteria:**
- [ ] ~4,929 patterns fixed (or justified exceptions documented)
- [ ] TypeScript strict mode enabled
- [ ] No `as any` in production code
- [ ] Proper NaN/Infinity handling everywhere
- [ ] All defensive guards replaced with proper types
- [ ] All tests pass
- [ ] No new patterns introduced

**Rollback Checkpoint:** Git tag `refactor/phase5.5-complete`

---

### Phase 6: P0 Files (Weeks 49-54) - NOW RUNS AFTER LAZY CODE CLEANUP

**Goal:** Modularize all P0 files (>2000 lines) - NOT compositorStore (handled in Phase 5)

| Week | Tasks |
|------|-------|
| 43-44 | types/effects.ts → split by category |
| 45-46 | types/project.ts → split by domain |
| 47-48 | Engine files (GPUParticleSystem, BaseLayer, ParticleLayer) |

**P0 Files (excluding compositorStore):**
1. types/effects.ts (3,319) → Split into blur, color, distort, stylize, time, generate types
2. workflowTemplates.ts (2,715) → Split by workflow type (TTM, Uni3C, SCAIL, etc.)
3. ParticleProperties.vue (2,683) → Extract sections to sub-components
4. GPUParticleSystem.ts (2,330) → Extract: GPUEmitter, GPUPhysics, GPURenderer
5. particleSystem.ts (2,299) → Extract: CPUEmitter, CPUPhysics (legacy fallback)
6. ParticleLayer.ts (2,201) → Extract: AudioBinding, SplineEmission, FrameCache
7. ThreeCanvas.vue (2,197) → Extract to composables (useThreeScene, etc.)
8. types/project.ts (2,194) → Extract: Layer types, Composition types, Animation types
9. BaseLayer.ts (2,120) → Extract: TransformManager, EffectApplicator
10. keyframeActions.ts (2,023) → Absorbed into keyframeStore in Phase 2
11. CurveEditor.vue (2,006) → Logic already partially in composables

**Exit Criteria:**
- [ ] All 11 remaining P0 files < 500 lines
- [ ] Tests pass

---

### Phase 7: P1 Files (Parallel with Phase 4-5)

**Goal:** Modularize all P1 files (1500-2000 lines)

Files: 21 total
- Services: colorRenderer, actionExecutor, audioFeatures, depthflow, etc.
- Engine: LatticeEngine, MotionEngine, SplineLayer, TextLayer
- Components: AudioPanel, PropertiesPanel, WorkspaceLayout, etc.

**Exit Criteria:**
- [ ] All 21 P1 files < 500 lines
- [ ] Tests pass

### Phase 8: P2 Files (Weeks 57-72)

**Goal:** Modularize all P2 files (1000-1500 lines)

Files: 45 total

**Exit Criteria:**
- [ ] All 45 P2 files < 500 lines
- [ ] Tests pass

### Phase 8-9: P2 & P3 Files (Ongoing, parallel with main phases)

**Goal:** Modularize P2 (45 files) and P3 (154 files) as capacity allows

**Note:** Many P3 files (500-1000 lines) may stay as-is after review. Focus effort on files with actual complexity, not just line count.

**Exit Criteria:**
- [ ] All files < 500 lines OR justified exception documented
- [ ] Tests pass
- [ ] Documentation complete

---

## 6. Rollback Strategy

### Git Tag Checkpoints

| Checkpoint | Tag | Trigger to Create |
|------------|-----|-------------------|
| Pre-refactor baseline | `refactor/baseline` | Before Phase 0 starts |
| Bug fixes complete | `refactor/phase0-complete` | Phase 0 exit criteria met |
| layerStore complete | `refactor/phase1-complete` | Phase 1 exit criteria met |
| Keyframes complete | `refactor/phase2-complete` | Phase 2 exit criteria met |
| Audio/effects complete | `refactor/phase3-complete` | Phase 3 exit criteria met |
| Camera/physics complete | `refactor/phase4-complete` | Phase 4 exit criteria met |
| **Pre-deletion** | `refactor/phase5-pre-delete` | Before compositorStore.ts deleted |
| compositorStore deleted | `refactor/phase5-complete` | compositorStore.ts successfully deleted |
| Lazy code cleanup complete | `refactor/phase5.5-complete` | All lazy code patterns fixed |

### Rollback Procedures

**If Phase N breaks:**
1. Identify the breaking change via git bisect
2. If fixable in <4 hours, fix forward
3. If not fixable, rollback to `refactor/phase(N-1)-complete`
4. Document what went wrong in REFACTOR_LOG.md
5. Create new branch for retry

**Critical Rollback: compositorStore deletion fails**
```bash
# If Phase 5 deletion breaks everything:
git checkout refactor/phase5-pre-delete
git checkout -b refactor/phase5-retry

# Investigate what consumers were missed
grep -r "useCompositorStore" --include="*.ts" --include="*.vue"
```

### Contingency: Discovery of New Cross-Domain Dependencies

If during any phase we discover additional cross-domain actions not in CROSS_DOMAIN_ACTIONS.md:

1. STOP current work
2. Document the new dependency
3. Assess impact on current phase
4. If minor: add to current phase
5. If major: complete current phase, handle in next phase

### No-Go Criteria

**Do NOT proceed to next phase if:**
- TypeScript errors > 0
- Any test suite fails
- Manual smoke test shows regression
- Memory leak detected
- Performance regression > 20%

---

## 7. Testing Checkpoints

### Checkpoint 0: After Phase 0 (Week 2)

| Test | Expected |
|------|----------|
| Memory stress test (10 min) | No canvas leaks |
| WebGL context loss test | Recovery works |
| Memory profile (30 min) | Stable |
| All existing tests | Pass |

### Checkpoint 1: After Phase 1 (Week 10)

| Test | Expected |
|------|----------|
| `npm run typecheck` | 0 errors |
| `npm run test:unit` | All pass |
| `npm run test:integration` | All pass |
| Layer CRUD operations | Working |
| Layer transforms | Working |
| Undo/redo for layers | Working |
| `grep "useCompositorStore.*layer"` | 0 results in migrated files |

### Checkpoint 2: After Phase 2 (Week 18)

| Test | Expected |
|------|----------|
| Keyframe CRUD | Working |
| Curve editor | Working |
| Playback | Working |
| Animation preview | Working |
| Undo/redo for keyframes | Working |

### Checkpoint 3: After Phase 3 (Week 26)

| Test | Expected |
|------|----------|
| Audio import | Working |
| Audio-reactive | Working |
| Effect application | Working |
| No canvas memory leaks | Verified |
| **No audio state in compositorStore** | `grep "audio" compositorStore.ts` returns 0 |

### Checkpoint 4: After Phase 5 (Week 42)

| Test | Expected |
|------|----------|
| **compositorStore.ts deleted** | File does not exist |
| `grep "useCompositorStore"` | 0 results in src/ |
| All consumers migrated | Verified via grep |
| Full app functional | Manual smoke test |

### Checkpoint 4.5: After Phase 5.5 (Week 48)

| Test | Expected |
|------|----------|
| `grep "as any"` | 0 results in production code |
| `grep "as unknown as"` | 0 results (or justified exceptions) |
| TypeScript strict mode | Enabled |
| NaN/Infinity handling | Proper validation everywhere |
| All tests pass | Verified |
| No new lazy patterns | Verified via automated checks |

### Checkpoint 5: Final (Week 54)

| Test | Expected |
|------|----------|
| All P0 files < 500 lines | `wc -l` verified |
| All P1 files < 500 lines | `wc -l` verified |
| Test coverage > 60% | Coverage report |
| No TypeScript errors | `npm run typecheck` |
| Full integration tests | All pass |

---

## 8. Timeline

### Summary (Corrected)

| Phase | Weeks | Focus |
|-------|-------|-------|
| 0 | 1-2 | Critical bug fixes |
| 1 | 3-10 | layerStore (includes text animators) |
| 2 | 11-18 | keyframeStore, animationStore, expressionStore, propertyEvaluator |
| 3 | 19-26 | audioStore, effectStore, audio dedup |
| 4 | 27-34 | cameraStore, physicsStore |
| 5 | 35-42 | projectStore, uiStore (includes segmentation), DELETE compositorStore |
| 6 | 43-48 | P0 files (11 remaining) |
| 7+ | Parallel | P1/P2/P3 files as capacity allows |

**Total: 13 Domain Stores** (3 already exist: selectionStore, historyStore, assetStore)

### Realistic 10-Month Schedule

**Store migration (Phases 0-5):** 42 weeks = 10.5 months
**Lazy code cleanup (Phase 5.5):** 6 weeks = 1.5 months
**File modularization (Phases 6+):** Runs AFTER Phase 5.5 (prevents pattern spreading)

| Month | Main Track (Sequential) | Parallel Track |
|-------|-------------------------|----------------|
| 1 | Phase 0: Bug fixes (Weeks 1-2) + Phase 1 start | - |
| 2 | Phase 1: layerStore (Weeks 3-10) | - |
| 3 | Phase 1 finish + Phase 2 start | - |
| 4 | Phase 2: keyframeStore (Weeks 11-18) | - |
| 5 | Phase 2 finish + Phase 3 start | Phase 6: P0 types/effects.ts |
| 6 | Phase 3: audio/effects (Weeks 19-26) | Phase 6: P0 engine files |
| 7 | Phase 3 finish + Phase 4 start | Phase 7: P1 services |
| 8 | Phase 4: camera/physics (Weeks 27-34) | Phase 7: P1 components |
| 9 | Phase 5: project/ui (Weeks 35-42) | Phase 7: P1 engine |
| 10 | Phase 5: DELETE compositorStore | - |
| 11 | Phase 5.5: Lazy code cleanup (Weeks 43-48) | - |
| 12 | Phase 6: P0 files (Weeks 49-54) | - |
| 13+ | Phase 7+: P1/P2/P3 files | - |

**Why 10 months, not 9:**
- Phase 0 (bug fixes) adds 2 weeks
- Each phase needs buffer for unexpected issues
- compositorStore deletion requires extra verification time
- Parallel work helps but doesn't eliminate sequential dependencies

---

## Appendix A: Files Already Under 500 Lines

These files do not need modularization:

- All files in `composables/` except useKeyboardShortcuts.ts
- All files in `workers/` except audioWorker.ts
- All files in `utils/` except labColorUtils.ts
- Many service files already properly sized
- Many component files already properly sized

---

## Appendix B: Barrel File Warning

The `services/index.ts` (1,692 lines) is a barrel file that re-exports everything. This:
1. Causes circular dependency issues
2. Increases bundle size (tree-shaking problems)
3. Makes imports ambiguous

**Recommendation:** Replace with direct imports. Example:
```typescript
// BAD
import { loadAudio, AudioBuffer } from '@/services';

// GOOD
import { loadAudio } from '@/services/audioFeatures';
import type { AudioBuffer } from '@/types/audio';
```

---

## Appendix C: Critical Bug Fixes (Now Scheduled in Phase 0)

These bugs are now scheduled in **Phase 0 (Weeks 1-2)** and must be completed before store migration begins.

| Bug | File | Impact | Phase 0 Task |
|-----|------|--------|--------------|
| Canvas leak in processEffectStack | effectProcessor.ts:471-482 | ~500MB/sec GC | Use CanvasPool.acquire() |
| Canvas leak in layerStyleRenderer | layerStyleRenderer.ts:80-89 | ~7,500 leaks/sec | Integrate with CanvasPool |
| WebGL context loss | GLSLEngine.ts | App crash | Add webglcontextlost handler |
| URL.createObjectURL leak | exportPipeline.ts:1301 | Memory growth | Add revokeObjectURL |
| Cleanup functions never called | effectProcessor.ts:323-347 | Resources never released | Add cleanup in main.ts |
| releaseCanvas never called | All renderers | Canvas pool grows | Add finally blocks |

---

## Appendix D: COMPLETE LAZY CODE PATTERN ANALYSIS (Verified 2026-01-13)

### Production Code Issues (~7,071 total)

| Category | Pattern | Count | Files | Priority |
|----------|---------|-------|-------|----------|
| **TYPE ESCAPES** | `as any` | **216** | 78 | 🔴 HIGH |
| | `: any` | **196** | 70 | 🔴 HIGH |
| | `as unknown` | **67** | 27 | 🟡 MEDIUM |
| | `as [Type]` | **1,589** | 362 | 🟡 MEDIUM |
| **LAZY DEFAULTS** | `\|\| 0` | **205** | 64 | 🔴 HIGH (hides NaN) |
| | `\|\| []` | **105** | 50 | 🟡 MEDIUM |
| | `\|\| {}`, `''`, etc. | **30** | 23 | 🟡 MEDIUM |
| **NULLISH GUARDS** | `??` | **2,377** | 256 | 🟡 REVIEW |
| | `?.` | **2,136** | 280 | 🟡 REVIEW |
| **NON-NULL ASSERT** | `variable!` | **~100** | 98 | 🔴 HIGH |
| **NaN/INFINITY** | Unguarded uses | **~645** | ~200 | 🔴 HIGH |
| | `isFinite()` guards | **~1,933** | 164 | ✅ GOOD |

### Top 10 Files to Fix First

| Rank | File | Issues | Key Patterns |
|------|------|--------|--------------|
| 1 | `services/expressions/expressionEvaluator.ts` | **81** | 81 `??` |
| 2 | `engine/particles/GPUParticleSystem.ts` | **67** | 65 `??` |
| 3 | `components/properties/ParticleProperties.vue` | **58** | 18 `\|\| 0`, 15 `: any` |
| 4 | `engine/layers/TextLayer.ts` | **58** | 15 `as any`, 42 `??` |
| 5 | `engine/layers/LightLayer.ts` | **54** | 9 `as any`, 45 `??` |
| 6 | `services/ai/actionExecutor.ts` | **38** | 16 `as any`, 17 `??` |
| 7 | `services/particleSystem.ts` | **29** | 9 `as any`, 16 `??` |
| 8 | `composables/useSplineInteraction.ts` | **23** | 11 `: any` |
| 9 | `components/canvas/MaskEditor.vue` | **19** | 12 `\|\| 0` |
| 10 | `engine/TransformControlsManager.ts` | **12** | 9 `as any` |

### Phase-Specific Fix Targets

| Phase | Target Patterns | Count |
|-------|----------------|-------|
| **Phase 1 (Layer Store)** | 50 `as any`, 10 `\|\| 0`, 20 `: any` in layer code | ~80 |
| **Phase 2 (Keyframe/Expression)** | 100 `\|\| 0`, 30 `: any`, 20 `as any` in keyframe/expression code | ~150 |
| **Phase 3 (Effects)** | 50 `: any`, 30 `as any`, 20 unnecessary `??`/`?.` in effect code | ~100 |
| **Phase 4 (Export)** | 30 `\|\| 0`, 20 `as any`, 10 `: any` in export code | ~60 |
| **Incremental** | Remaining ~5,500 patterns fixed as code is touched | ~5,500 |

### Type Suppression Status (✅ EXCELLENT)

| Pattern | Count | Status |
|---------|-------|--------|
| `@ts-ignore` | **0** | ✅ None |
| `@ts-expect-error` | **1** | ✅ Minimal |
| `@ts-nocheck` | **0** | ✅ None |
| `eslint-disable` | **2** | ✅ Test setup only |

---

## Appendix E: Document Change Log

| Date | Change |
|------|--------|
| 2026-01-10 | Initial version |
| 2026-01-10 | Added Phase 0 for critical bug fixes |
| 2026-01-10 | Added Section 6: Rollback Strategy |
| 2026-01-10 | Fixed timeline math (9 months → 10 months) |
| 2026-01-10 | Added audio state deduplication to Phase 3 |
| 2026-01-10 | Added rollback checkpoints to each phase |
| 2026-01-10 | Linked to STORE_MIGRATION_CONSUMERS.md and CROSS_DOMAIN_ACTIONS.md |
| 2026-01-13 | **VERIFIED STATUS:** Added complete lazy code pattern analysis |
| 2026-01-13 | Updated file sizes with verified counts (5 P0 files, not 12) |
| 2026-01-13 | Added Top 10 files to fix first |
| 2026-01-13 | Added phase-specific fix targets |

---

*Document Version: 1.3*
*Last Updated: 2026-01-13 (Complete lazy code analysis verified against codebase)*
