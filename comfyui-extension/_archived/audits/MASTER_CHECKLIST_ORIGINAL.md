# MASTER CHECKLIST - Complete File-by-File Test Coverage Status

**Last Updated:** 2026-01-09 (Stripped NEEDS comments to reduce tokens; verified 6 services entries; added speedGraph.ts)
**Purpose:** This is the SINGLE SOURCE OF TRUTH for test coverage. Updated EVERY time tests are added/modified.
**Total Source Files:** 502 (476 TypeScript/Vue + 26 Python)

**Recent Additions (2026-01-07):**
- ✅ Memory leak tests: `ui/src/__tests__/performance/memory.test.ts` (reintegrated from deprecated)
- ✅ Performance benchmarks: `ui/src/__tests__/performance/benchmarks.test.ts` (reintegrated from deprecated)
- ✅ Integration tests: `ui/src/__tests__/integration/store-engine.integration.test.ts` (reintegrated from deprecated)
- ✅ Security tests: `ui/src/__tests__/security/promptInjection.test.ts` (reintegrated from deprecated)
- ✅ Determinism tests: `ui/src/__tests__/services/determinism.property.test.ts` (reintegrated with API updates)
- ✅ DepthRenderer browser tests: Added to `ui/src/__tests__/export/depthRenderer.property.test.ts` (browser-only, skipped in Node.js)
- ✅ SeededRandom enhanced tests: Merged into `ui/src/__tests__/services/SeededRandom.property.test.ts` (1000-number tests, distribution quality)
- ✅ Interpolation edge case probes: Merged into `ui/src/__tests__/services/interpolation.property.test.ts` (3D/2D transitions, malformed colors, bezier handles)
- ✅ Strict interpolation tests: Added NaN/Infinity handling, division by zero, cache determinism to `ui/src/__tests__/services/interpolation.property.test.ts`
- ✅ Regression test suite: Created 14 Phase 1 regression tests for critical bugs (interpolation, camera, project, animation, physics, actions, effectProcessor)
- ✅ TypeScript fixes: `ui/src/__tests__/engine/layerEvaluation.property.test.ts` fully fixed (22 errors resolved - corrected AnimatableProperty, Keyframe, Layer, LayerTransform, LatticeProject, CompositionSettings structures to match actual codebase types)
- ✅ TypeScript fixes: `ui/src/__tests__/export/svgExport.property.test.ts` fully fixed (40 errors resolved - fixed ControlPoint arbitrary generator with realistic handle configurations, all test cases use realistic corner/smooth points, closed paths require 3+ points, mixed handle scenarios for ramps)
- ✅ TypeScript fixes: `ui/src/__tests__/export/cameraExportFormats.property.test.ts` fully fixed (2 errors resolved - fixed Camera3D arbitrary generator with all required properties: pointOfInterest, x/y/zRotation, measureFilmSize, iris, highlight, autoOrient, depthOfField.fStop/lockToZoom)
- ✅ TypeScript fixes: `ui/src/__tests__/export/cameraExport.test.ts` fully fixed (3 errors resolved - fixed createTestCamera with all Camera3D required properties, removed invalid CameraKeyframe.id property, added depthOfField.fStop/lockToZoom)
- ✅ TypeScript fixes: `ui/src/__tests__/export/cameraExportFormats.test.ts` fully fixed (2 errors resolved - fixed createTestCamera and createKeyframe functions with all required properties)
- ✅ TypeScript fixes: `ui/src/__tests__/export/export-format-contracts.test.ts` fully fixed (20 errors resolved - fixed Camera3D type from "perspective" to "one-node", added all required properties, removed all invalid CameraKeyframe.id properties)
- ✅ TypeScript fixes: `ui/src/__tests__/export/exportPipeline.test.ts` fully fixed (5 errors resolved - fixed ExportStage values to use "rendering_frames"/"rendering_depth"/"rendering_control" instead of "rendering"/"encoding", fixed ExportTarget values to match actual type definitions)

## Update Rules
- ✅ = Has complete test coverage for this metric
- ⚠️ = Has partial test coverage
- ❌ = No test coverage
- N/A = Not applicable (e.g., TypeScript for Python files)

## Legend
- **Unit**: Unit tests (Vitest)
- **Property**: Property tests (fast-check/Hypothesis)
- **Regression**: Regression tests for fixed bugs
- **TypeScript**: TypeScript errors resolved
- **Memory**: Memory leak tests
- **E2E**: End-to-end tests (Playwright)
- **Integration**: Integration tests
- **Browser**: Browser-only tests
- **Performance**: Performance benchmarks
- **Security**: Security/audit tests

---

**⚠️ IMPORTANT:** This checklist is extracted from [MASTER_AUDIT.md](MASTER_AUDIT.md). To update, modify MASTER_AUDIT.md's table section (starting at line 3059) and then regenerate this file.

**To regenerate:** Run `python extract_checklist_from_audit.py` after updating MASTER_AUDIT.md.

---

## ENGINE CORE (13 files)

| File | Unit | Property | Regression | TypeScript | Memory | E2E | Integration | Browser | Performance | Security | Status |
|------|------|----------|------------|------------|--------|-----|-------------|---------|-------------|----------|--------|
| `ui/src/engine/LatticeEngine.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | **CRITICAL GAP** |
| `ui/src/engine/MotionEngine.ts` | ✅ | ✅ | ⚠️ | ✅ | ⚠️ | ❌ | ⚠️ | ❌ | ⚠️ | ❌ | |
| `ui/src/engine/core/RenderPipeline.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | **CRITICAL GAP** (13 TS errors fixed) |
| `ui/src/engine/core/CameraController.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | **CRITICAL GAP** |
| `ui/src/engine/core/ResourceManager.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ⚠️ | |
| `ui/src/engine/core/SceneManager.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | **CRITICAL GAP** (TS errors fixed) |
| `ui/src/engine/core/LayerManager.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | |
| `ui/src/engine/TransformControlsManager.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/engine/NestedCompRenderer.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/engine/animation/EasingFunctions.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/engine/animation/KeyframeEvaluator.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/engine/index.ts` | ❌ | ❌ | ❌ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/engine/types.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |

---

## ENGINE LAYERS (25 files)

| File | Unit | Property | Regression | TypeScript | Memory | E2E | Integration | Browser | Performance | Security | Status |
|------|------|----------|------------|------------|--------|-----|-------------|---------|-------------|----------|--------|
| `ui/src/engine/layers/AudioLayer.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/engine/layers/BaseLayer.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/engine/layers/blendModeUtils.ts` | ❌ | ❌ | ❌ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/engine/layers/CameraLayer.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/engine/layers/ControlLayer.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/engine/layers/DepthflowLayer.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/engine/layers/DepthLayer.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/engine/layers/EffectLayer.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/engine/layers/GeneratedLayer.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/engine/layers/GroupLayer.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/engine/layers/ImageLayer.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/engine/layers/LightLayer.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/engine/layers/ModelLayer.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/engine/layers/NestedCompLayer.ts` | ❌ | ❌ | ❌ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/engine/layers/NormalLayer.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/engine/layers/ParticleLayer.ts` | ✅ | ✅ | ⚠️ | ✅ | ⚠️ | ❌ | ⚠️ | ❌ | ❌ | ❌ | |
| `ui/src/engine/layers/PathLayer.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/engine/layers/PointCloudLayer.ts` | ❌ | ❌ | ❌ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/engine/layers/PoseLayer.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/engine/layers/ProceduralMatteLayer.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/engine/layers/ShapeLayer.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/engine/layers/SolidLayer.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/engine/layers/SplineLayer.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/engine/layers/TextLayer.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/engine/layers/VideoLayer.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |

---

## ENGINE PARTICLES (27 files)

| File | Unit | Property | Regression | TypeScript | Memory | E2E | Integration | Browser | Performance | Security | Status |
|------|------|----------|------------|------------|--------|-----|-------------|---------|-------------|----------|--------|
| `ui/src/engine/particles/GPUParticleSystem.ts` | ✅ | ✅ | ⚠️ | ✅ | ⚠️ | ❌ | ⚠️ | ❌ | ❌ | ❌ | |
| `ui/src/engine/particles/ParticleModulationCurves.ts` | ✅ | ✅ | ⚠️ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/engine/particles/ParticleConnectionSystem.ts` | ✅ | ✅ | ⚠️ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/engine/particles/ParticleFlockingSystem.ts` | ✅ | ✅ | ⚠️ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/engine/particles/ParticleFrameCache.ts` | ✅ | ✅ | ⚠️ | ✅ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/engine/particles/SpatialHashGrid.ts` | ✅ | ✅ | ⚠️ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/engine/particles/ParticleCollisionSystem.ts` | ✅ | ✅ | ⚠️ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/engine/particles/ParticleForceCalculator.ts` | ✅ | ✅ | ⚠️ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/engine/particles/ParticleEmitterLogic.ts` | ✅ | ✅ | ⚠️ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/engine/particles/ParticleAudioReactive.ts` | ✅ | ✅ | ⚠️ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/engine/particles/ParticleSubEmitter.ts` | ✅ | ✅ | ⚠️ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/engine/particles/ParticleTrailSystem.ts` | ✅ | ✅ | ⚠️ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/engine/particles/ParticleSPHSystem.ts` | ✅ | ✅ | ⚠️ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/engine/particles/ParticleSpringSystem.ts` | ✅ | ✅ | ⚠️ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/engine/particles/ParticleGroupSystem.ts` | ✅ | ✅ | ⚠️ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/engine/particles/GPUSpringSystem.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/engine/particles/GPUSPHSystem.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/engine/particles/ParticleTextureSystem.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/engine/particles/ParticleGPUPhysics.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/engine/particles/webgpuParticleCompute.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/engine/particles/particleShaders.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/engine/particles/types.ts` | ⚠️ | ⚠️ | ❌ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/engine/particles/index.ts` | ❌ | ❌ | ❌ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/engine/ParticleSimulationController.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/engine/BackgroundManager.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/engine/utils/PerformanceMonitor.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/engine/utils/colormapShader.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |

---

## SERVICES (182 files)

| File | Unit | Property | Regression | TypeScript | Memory | E2E | Integration | Browser | Performance | Security | Status |
|------|------|----------|------------|------------|--------|-----|-------------|---------|-------------|----------|--------|
| `ui/src/services/ai/actionExecutor.ts` | ✅ | ❌ | ⚠️ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ⚠️ | |
| `ui/src/services/ai/AICompositorAgent.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ⚠️ | |
| `ui/src/services/ai/cameraTrackingAI.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ⚠️ | |
| `ui/src/services/ai/depthEstimation.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ⚠️ | |
| `ui/src/services/ai/index.ts` | ❌ | ❌ | ❌ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/ai/sapiensIntegration.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ⚠️ | |
| `ui/src/services/ai/stateSerializer.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ✅ | |
| `ui/src/services/ai/systemPrompt.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ⚠️ | |
| `ui/src/services/ai/toolDefinitions.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ⚠️ | |
| `ui/src/services/aiGeneration.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ⚠️ | |
| `ui/src/services/alphaToMesh.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/animation/PropertyEvaluator.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/arcLength.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/audio/enhancedBeatDetection.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/audio/index.ts` | ❌ | ❌ | ❌ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/audio/stemSeparation.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/audioFeatures.ts` | ✅ | ✅ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/audioPathAnimator.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/audioReactiveMapping.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/audioWorkerClient.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/bezierBoolean.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/blendModes.ts` | ✅ | ✅ | ❌ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/camera3DVisualization.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/cameraEnhancements.ts` | ✅ | ✅ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/cameraExport.ts` | ❌ | ❌ | ⚠️ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/cameraTrackingImport.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/cameraTrajectory.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/colorAnalysis/histogramService.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/colorDepthReactivity.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/colorManagement/ColorProfileService.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/colorManagement/index.ts` | ❌ | ❌ | ❌ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/comfyui/comfyuiClient.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ⚠️ | |
| `ui/src/services/comfyui/index.ts` | ❌ | ❌ | ❌ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/comfyui/workflowTemplates.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ⚠️ | |
| `ui/src/services/conditioningRenderer.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/dataImport.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ⚠️ | |
| `ui/src/services/depthflow.ts` | ✅ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/easing.ts` | ✅ | ✅ | ⚠️ | ✅ | ❌ | ❌ | ❌ | ❌ | ⚠️ | ❌ | |
| `ui/src/services/effectProcessor.ts` | ✅ | ✅ | ⚠️ | ✅ | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | |
| `ui/src/services/effects/audioVisualizer.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/effects/blurRenderer.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/effects/cinematicBloom.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/effects/colorGrading.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/effects/colorRenderer.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/effects/distortRenderer.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/effects/expressionControlRenderer.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ⚠️ | |
| `ui/src/services/effects/generateRenderer.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/effects/hdrRenderer.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/effects/index.ts` | ❌ | ❌ | ❌ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/effects/layerStyleRenderer.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/effects/maskRenderer.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/effects/matteEdge.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/effects/meshDeformRenderer.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/effects/perspectiveRenderer.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/effects/stylizeRenderer.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/effects/timeRenderer.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/export/cameraExportFormats.ts` | ✅ | ✅ | ⚠️ | ✅ | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | |
| `ui/src/services/export/depthRenderer.ts` | ✅ | ✅ | ⚠️ | ✅ | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | |
| `ui/src/services/export/exportPipeline.ts` | ✅ | ❌ | ⚠️ | ✅ | ❌ | ❌ | ⚠️ | ⚠️ | ❌ | ❌ | |
| `ui/src/services/export/frameSequenceExporter.ts` | ✅ | ❌ | ⚠️ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/export/index.ts` | ❌ | ❌ | ❌ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/export/meshDeformExport.ts` | ✅ | ❌ | ⚠️ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/export/poseExport.ts` | ✅ | ✅ | ⚠️ | ✅ | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | |
| `ui/src/services/export/vaceControlExport.ts` | ✅ | ✅ | ⚠️ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/export/videoEncoder.ts` | ✅ | ❌ | ⚠️ | ✅ | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | |
| `ui/src/services/export/wanMoveExport.ts` | ✅ | ✅ | ⚠️ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/export/wanMoveFlowGenerators.ts` | ✅ | ✅ | ⚠️ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/export/cameraExport.ts` | ❌ | ❌ | ⚠️ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/exportTemplates.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/expressions.ts` | ❌ | ❌ | ❌ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/expressions/audioExpressions.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/expressions/coordinateConversion.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/expressions/easing.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/expressions/expressionEvaluator.ts` | ⚠️ | ✅ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ⚠️ | |
| `ui/src/services/expressions/expressionHelpers.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/expressions/expressionNamespaces.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/expressions/expressionPresets.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/expressions/expressionValidation.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ⚠️ | |
| `ui/src/services/expressions/expressionValidator.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ⚠️ | |
| `ui/src/services/expressions/index.ts` | ❌ | ❌ | ❌ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/expressions/jitterExpressions.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/expressions/layerContentExpressions.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/expressions/loopExpressions.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/expressions/motionExpressions.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/expressions/sesEvaluator.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ⚠️ | |
| `ui/src/services/expressions/textAnimator.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/expressions/types.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/expressions/vectorMath.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/expressions/workerEvaluator.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ⚠️ | |
| `ui/src/services/fontService.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/frameCache.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/gaussianSplatting.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/globalLight.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/glsl/GLSLEngine.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/glsl/index.ts` | ❌ | ❌ | ❌ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/glsl/ShaderEffects.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/gpuBenchmark.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/gpuDetection.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/gpuEffectDispatcher.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/gpuParticleRenderer.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/imageTrace.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/index.ts` | ❌ | ❌ | ❌ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/interpolation.ts` | ✅ | ✅ | ⚠️ | ✅ | ❌ | ❌ | ❌ | ❌ | ⚠️ | ❌ | |
| `ui/src/services/jsonValidation.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ⚠️ | |
| `ui/src/services/layerDecomposition.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/layerEvaluationCache.ts` | ✅ | ✅ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/layerTime.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/lazyLoader.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/maskGenerator.ts` | ✅ | ✅ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/materialSystem.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/math3d.ts` | ✅ | ✅ | ⚠️ | ✅ | ❌ | ❌ | ❌ | ❌ | ⚠️ | ❌ | |
| `ui/src/services/matteExporter.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/memoryBudget.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/meshDeformation3D.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/meshParticleManager.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/meshWarpDeformation.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/midi/index.ts` | ❌ | ❌ | ❌ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/midi/MIDIService.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/midiToKeyframes.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/modelExport.ts` | ✅ | ❌ | ⚠️ | ⚠️ | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | |
| `ui/src/services/motionBlur.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/motionReactivity.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/motionRecording.ts` | ✅ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/onionSkinning.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/particleGPU.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/particles/index.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/particles/particleDefaults.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/particles/particleRenderer.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/particles/particleTypes.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/particles/SeededRandom.ts` | ✅ | ✅ | ⚠️ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/particleSystem.ts` | ✅ | ✅ | ⚠️ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/pathMorphing.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/persistenceService.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ⚠️ | |
| `ui/src/services/physics/index.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/physics/JointSystem.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/physics/PhysicsEngine.ts` | ✅ | ❌ | ⚠️ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/physics/RagdollBuilder.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/plugins/index.ts` | ❌ | ❌ | ❌ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/plugins/PluginManager.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ⚠️ | |
| `ui/src/services/preprocessorService.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/projectCollection.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ⚠️ | |
| `ui/src/services/projectMigration.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ⚠️ | |
| `ui/src/services/projectStorage.ts` | ✅ | ✅ | ⚠️ | ✅ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ⚠️ | |
| `ui/src/services/propertyDriver.ts` | ✅ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/renderQueue/index.ts` | ❌ | ❌ | ❌ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/renderQueue/RenderQueueManager.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/rovingKeyframes.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/security/auditLog.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ⚠️ | |
| `ui/src/services/security/jsonSanitizer.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ⚠️ | |
| `ui/src/services/security/rateLimits.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ⚠️ | |
| `ui/src/services/security/templateVerifier.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ⚠️ | |
| `ui/src/services/security/urlValidator.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ⚠️ | |
| `ui/src/services/segmentation.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/segmentToMask.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/shape/index.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/shape/pathModifiers.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/shapeOperations.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/spriteSheet.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/spriteValidation.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/speedGraph.ts` | ✅ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/svgExport.ts` | ✅ | ✅ | ⚠️ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/svgExtrusion.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/templateBuilder.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ⚠️ | |
| `ui/src/services/textAnimator.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/textMeasurement.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/textOnPath.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/textShaper.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/textToVector.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/timelineSnap.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/timelineWaveform.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/timewarp.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/trackPointService.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/vectorize.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/vectorLOD.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/video/frameInterpolation.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/video/index.ts` | ❌ | ❌ | ❌ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/video/transitions.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/videoDecoder.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/visionAuthoring/index.ts` | ❌ | ❌ | ❌ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/visionAuthoring/MotionIntentResolver.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/visionAuthoring/MotionIntentTranslator.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/visionAuthoring/types.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/webgpuRenderer.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/services/workerPool.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |

---

## STORES (37 files)

| File | Unit | Property | Regression | TypeScript | Memory | E2E | Integration | Browser | Performance | Security | Status |
|------|------|----------|------------|------------|--------|-----|-------------|---------|-------------|----------|--------|
| `ui/src/stores/actions/audioActions.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/stores/actions/cacheActions.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/stores/actions/cameraActions.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/stores/actions/compositionActions.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/stores/actions/depthflowActions.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/stores/actions/effectActions.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/stores/actions/index.ts` | ❌ | ❌ | ❌ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/stores/actions/keyframeActions.ts` | ✅ | ❌ | ⚠️ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/stores/actions/keyframes/keyframeExpressions.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ⚠️ | |
| `ui/src/stores/actions/layer/index.ts` | ❌ | ❌ | ❌ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/stores/actions/layer/layerDefaults.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/stores/actions/layer/splineActions.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/stores/actions/layerActions.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/stores/actions/layerDecompositionActions.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/stores/actions/layers/layerTimeActions.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/stores/actions/layerStyleActions.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/stores/actions/markerActions.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/stores/actions/particleLayerActions.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/stores/actions/physicsActions.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/stores/actions/playbackActions.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/stores/actions/projectActions.ts` | ✅ | ❌ | ⚠️ | ✅ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ⚠️ | |
| `ui/src/stores/actions/propertyDriverActions.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/stores/actions/segmentationActions.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/stores/actions/textAnimatorActions.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/stores/actions/videoActions.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/stores/assetStore.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/stores/audioStore.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/stores/audioSync.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/stores/compositorStore.ts` | ❌ | ❌ | ❌ | ⚠️ | ⚠️ | ⚠️ | ⚠️ | ❌ | ⚠️ | ❌ | **CRITICAL GAP** (Memory + Integration + Performance tests added) |
| `ui/src/stores/historyStore.ts` | ❌ | ❌ | ⚠️ | ⚠️ | ❌ | ⚠️ | ✅ | ❌ | ❌ | ❌ | |
| `ui/src/stores/index.ts` | ❌ | ❌ | ❌ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/stores/particlePreferences.ts` | ✅ | ✅ | ❌ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/stores/playbackStore.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/stores/presetStore.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/stores/selectionStore.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/stores/themeStore.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/stores/toastStore.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |

---

## TYPES (24 files)

| File | Unit | Property | Regression | TypeScript | Memory | E2E | Integration | Browser | Performance | Security | Status |
|------|------|----------|------------|------------|--------|-----|-------------|---------|-------------|----------|--------|
| `ui/src/types/animation.ts` | ✅ | ✅ | ⚠️ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/types/assets.ts` | ⚠️ | ⚠️ | ❌ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/types/blendModes.ts` | ✅ | ✅ | ❌ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/types/camera.ts` | ✅ | ✅ | ❌ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/types/cameraTracking.ts` | ⚠️ | ⚠️ | ❌ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/types/dataAsset.ts` | ✅ | ✅ | ❌ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/types/effects.ts` | ✅ | ✅ | ❌ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/types/export.ts` | ⚠️ | ⚠️ | ❌ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/types/index.ts` | ❌ | ❌ | ❌ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/types/layerData.ts` | ✅ | ✅ | ❌ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/types/layerStyles.ts` | ✅ | ✅ | ❌ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/types/masks.ts` | ✅ | ✅ | ❌ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/types/meshWarp.ts` | ✅ | ✅ | ❌ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/types/modules.d.ts` | ❌ | ❌ | ❌ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/types/particles.ts` | ⚠️ | ⚠️ | ❌ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/types/physics.ts` | ⚠️ | ⚠️ | ❌ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/types/presets.ts` | ⚠️ | ⚠️ | ❌ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/types/project.ts` | ✅ | ✅ | ⚠️ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/types/shapes.ts` | ✅ | ✅ | ❌ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/types/spline.ts` | ✅ | ✅ | ❌ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/types/templateBuilder.ts` | ✅ | ✅ | ❌ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/types/text.ts` | ✅ | ✅ | ❌ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/types/transform.ts` | ✅ | ✅ | ⚠️ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |

---

## COMPOSABLES (18 files)

| File | Unit | Property | Regression | TypeScript | Memory | E2E | Integration | Browser | Performance | Security | Status |
|------|------|----------|------------|------------|--------|-----|-------------|---------|-------------|----------|--------|
| `ui/src/composables/useAssetHandlers.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/composables/useCanvasSegmentation.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/composables/useCanvasSelection.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/composables/useCurveEditorCoords.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/composables/useCurveEditorDraw.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/composables/useCurveEditorInteraction.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/composables/useCurveEditorKeyboard.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/composables/useCurveEditorView.ts` | ❌ | ❌ | ❌ | ⚠️ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/composables/useExpressionEditor.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/composables/useGuides.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/composables/useKeyboardShortcuts.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/composables/useMenuActions.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/composables/useShapeDrawing.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/composables/useSplineInteraction.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/composables/useSplineUtils.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/composables/useViewportControls.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/composables/useViewportGuides.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/composables/index.ts` | ❌ | ❌ | ❌ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |

---

## WORKERS (4 files)

| File | Unit | Property | Regression | TypeScript | Memory | E2E | Integration | Browser | Performance | Security | Status |
|------|------|----------|------------|------------|--------|-----|-------------|---------|-------------|----------|--------|
| `ui/src/workers/audioWorker.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ⚠️ | |
| `ui/src/workers/computeWorker.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ⚠️ | |
| `ui/src/workers/expressionWorker.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ⚠️ | ⚠️ | ❌ | ⚠️ | |
| `ui/src/workers/scopeWorker.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | |

---

## UTILS (8 files)

| File | Unit | Property | Regression | TypeScript | Memory | E2E | Integration | Browser | Performance | Security | Status |
|------|------|----------|------------|------------|--------|-----|-------------|---------|-------------|----------|--------|
| `ui/src/utils/arrayUtils.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/utils/colorUtils.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/utils/fpsUtils.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/utils/icons.ts` | ❌ | ❌ | ❌ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/utils/labColorUtils.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/utils/logger.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/utils/security.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ⚠️ | |
| `ui/src/utils/validation.ts` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |

---

## COMPONENTS (165 Vue files)

*Note: Vue components are primarily tested via E2E. Unit tests are rare. All components need E2E tests.*

### canvas/ (8 files)

| File | Unit | Property | Regression | TypeScript | Memory | E2E | Integration | Browser | Performance | Security | Status |
|------|------|----------|------------|------------|--------|-----|-------------|---------|-------------|----------|--------|
| `ui/src/components/canvas/MaskEditor.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/canvas/MeshWarpPinEditor.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/canvas/MotionPathOverlay.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/canvas/PathPreviewOverlay.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/canvas/SplineEditor.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/canvas/SplineToolbar.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/canvas/ThreeCanvas.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/canvas/TrackPointOverlay.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |

### common/ (1 file)

| File | Unit | Property | Regression | TypeScript | Memory | E2E | Integration | Browser | Performance | Security | Status |
|------|------|----------|------------|------------|--------|-----|-------------|---------|-------------|----------|--------|
| `ui/src/components/common/MemoryIndicator.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |

### controls/ (9 files)

| File | Unit | Property | Regression | TypeScript | Memory | E2E | Integration | Browser | Performance | Security | Status |
|------|------|----------|------------|------------|--------|-----|-------------|---------|-------------|----------|--------|
| `ui/src/components/controls/AngleDial.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/controls/ColorPicker.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/controls/CurveEditor.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/controls/EyedropperTool.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/controls/index.ts` | ❌ | ❌ | ❌ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/controls/PositionXY.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/controls/PropertyLink.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/controls/ScrubableNumber.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/controls/SliderInput.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |

### curve-editor/ (4 files)

| File | Unit | Property | Regression | TypeScript | Memory | E2E | Integration | Browser | Performance | Security | Status |
|------|------|----------|------------|------------|--------|-----|-------------|---------|-------------|----------|--------|
| `ui/src/components/curve-editor/CurveEditor.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/curve-editor/CurveEditorCanvas.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/curve-editor/CurveEditorHeader.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/curve-editor/CurveEditorPropertyList.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |

### dialogs/ (18 files)

| File | Unit | Property | Regression | TypeScript | Memory | E2E | Integration | Browser | Performance | Security | Status |
|------|------|----------|------------|------------|--------|-----|-------------|---------|-------------|----------|--------|
| `ui/src/components/dialogs/CameraTrackingImportDialog.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ⚠️ | |
| `ui/src/components/dialogs/CompositionSettingsDialog.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/dialogs/DecomposeDialog.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/dialogs/ExportDialog.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/dialogs/FontPicker.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/dialogs/FpsMismatchDialog.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/dialogs/FpsSelectDialog.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/dialogs/KeyboardShortcutsModal.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/dialogs/KeyframeInterpolationDialog.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/dialogs/KeyframeVelocityDialog.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/dialogs/MotionSketchPanel.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/dialogs/PathSuggestionDialog.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/dialogs/PrecomposeDialog.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/dialogs/PreferencesDialog.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/dialogs/SmootherPanel.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/dialogs/TemplateBuilderDialog.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ⚠️ | |
| `ui/src/components/dialogs/TimeStretchDialog.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/dialogs/VectorizeDialog.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |

### export/ (1 file)

| File | Unit | Property | Regression | TypeScript | Memory | E2E | Integration | Browser | Performance | Security | Status |
|------|------|----------|------------|------------|--------|-----|-------------|---------|-------------|----------|--------|
| `ui/src/components/export/ComfyUIExportDialog.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |

### layout/ (6 files)

| File | Unit | Property | Regression | TypeScript | Memory | E2E | Integration | Browser | Performance | Security | Status |
|------|------|----------|------------|------------|--------|-----|-------------|---------|-------------|----------|--------|
| `ui/src/components/layout/CenterViewport.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/layout/LeftSidebar.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/layout/MenuBar.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/layout/RightSidebar.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/layout/WorkspaceLayout.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/layout/WorkspaceToolbar.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |

### materials/ (5 files)

| File | Unit | Property | Regression | TypeScript | Memory | E2E | Integration | Browser | Performance | Security | Status |
|------|------|----------|------------|------------|--------|-----|-------------|---------|-------------|----------|--------|
| `ui/src/components/materials/AssetUploader.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ⚠️ | |
| `ui/src/components/materials/EnvironmentSettings.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/materials/index.ts` | ❌ | ❌ | ❌ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/materials/MaterialEditor.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/materials/TextureUpload.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ⚠️ | |

### panels/ (28 files)

| File | Unit | Property | Regression | TypeScript | Memory | E2E | Integration | Browser | Performance | Security | Status |
|------|------|----------|------------|------------|--------|-----|-------------|---------|-------------|----------|--------|
| `ui/src/components/panels/AIChatPanel.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ⚠️ | |
| `ui/src/components/panels/AIGeneratePanel.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ⚠️ | |
| `ui/src/components/panels/AlignPanel.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/panels/AssetsPanel.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/panels/AudioPanel.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/panels/AudioValuePreview.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/panels/CameraProperties.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/panels/CollapsiblePanel.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/panels/CommentControl.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/panels/DriverList.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/panels/EffectControlsPanel.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/panels/EffectsPanel.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/panels/ExportPanel.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/panels/ExposedPropertyControl.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/panels/GenerativeFlowPanel.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ⚠️ | |
| `ui/src/components/panels/LayerDecompositionPanel.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/panels/Model3DProperties.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/panels/OutputModulePanel.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/panels/PreviewPanel.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/panels/ProjectPanel.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/panels/PropertiesPanel.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/panels/RenderQueuePanel.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/panels/RenderSettingsPanel.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/panels/scopes/HistogramScope.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/panels/scopes/RGBParadeScope.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/panels/scopes/VectorscopeScope.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/panels/scopes/WaveformScope.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/panels/ScopesPanel.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |

### preferences/ (1 file)

| File | Unit | Property | Regression | TypeScript | Memory | E2E | Integration | Browser | Performance | Security | Status |
|------|------|----------|------------|------------|--------|-----|-------------|---------|-------------|----------|--------|
| `ui/src/components/preferences/ParticlePreferencesPanel.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |

### preview/ (1 file)

| File | Unit | Property | Regression | TypeScript | Memory | E2E | Integration | Browser | Performance | Security | Status |
|------|------|----------|------------|------------|--------|-----|-------------|---------|-------------|----------|--------|
| `ui/src/components/preview/HDPreviewWindow.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |

### properties/ (72 files)

*Note: Properties components are user-facing UI. All need E2E tests.*

| File | Unit | Property | Regression | TypeScript | Memory | E2E | Integration | Browser | Performance | Security | Status |
|------|------|----------|------------|------------|--------|-----|-------------|---------|-------------|----------|--------|
| `ui/src/components/properties/AudioProperties.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/CameraProperties.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/ControlProperties.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/DepthflowProperties.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/DepthProperties.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/ExpressionInput.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ⚠️ | |
| `ui/src/components/properties/GeneratedProperties.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/GroupProperties.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/KeyframeToggle.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/LightProperties.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/MatteProperties.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/NestedCompProperties.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/NormalProperties.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/particle/index.ts` | ❌ | ❌ | ❌ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/particle/ParticleAudioBindingsSection.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/particle/ParticleCollisionPlanesSection.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/particle/ParticleCollisionSection.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/particle/ParticleDOFSection.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/particle/ParticleFlockingSection.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/particle/ParticleForceFieldsSection.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/particle/ParticleGroupsSection.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/particle/ParticleLODSection.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/particle/ParticleModulationsSection.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/particle/ParticleRenderingToggle.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/particle/ParticleRenderSection.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/particle/ParticleSPHSection.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/particle/ParticleSpringSection.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/particle/ParticleSubEmittersSection.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/particle/ParticleTurbulenceSection.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/particle/ParticleVisualizationSection.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/ParticleProperties.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/PathProperties.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/PhysicsProperties.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/PoseProperties.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/shape-editors/EllipseEditor.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/shape-editors/FillEditor.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/shape-editors/GradientFillEditor.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/shape-editors/GradientStrokeEditor.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/shape-editors/GroupEditor.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/shape-editors/MergePathsEditor.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/shape-editors/OffsetPathsEditor.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/shape-editors/PathEditor.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/shape-editors/PolygonEditor.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/shape-editors/PuckerBloatEditor.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/shape-editors/RectangleEditor.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/shape-editors/RepeaterEditor.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/shape-editors/RoundedCornersEditor.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/shape-editors/StarEditor.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/shape-editors/StrokeEditor.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/shape-editors/TransformEditor.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/shape-editors/TrimPathsEditor.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/shape-editors/TwistEditor.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/shape-editors/WigglePathsEditor.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/shape-editors/ZigZagEditor.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/ShapeContentItem.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/ShapeLayerProperties.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/ShapeProperties.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/SolidProperties.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/styles/BevelEmbossEditor.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/styles/BlendingOptionsEditor.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/styles/ColorOverlayEditor.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/styles/DropShadowEditor.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/styles/GradientOverlayEditor.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/styles/InnerGlowEditor.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/styles/InnerShadowEditor.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/styles/LayerStylesPanel.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/styles/OuterGlowEditor.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/styles/SatinEditor.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/styles/StrokeEditor.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/styles/StyleSection.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/TextProperties.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/properties/VideoProperties.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |

### timeline/ (10 files)

| File | Unit | Property | Regression | TypeScript | Memory | E2E | Integration | Browser | Performance | Security | Status |
|------|------|----------|------------|------------|--------|-----|-------------|---------|-------------|----------|--------|
| `ui/src/components/timeline/AudioMappingCurve.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/timeline/AudioTrack.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/timeline/CompositionTabs.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/timeline/EnhancedLayerTrack.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/timeline/LayerTrack.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/timeline/NodeConnection.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/timeline/OnionSkinControls.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/timeline/Playhead.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/timeline/PropertyTrack.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/timeline/TimelinePanel.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |

### ui/ (2 files)

| File | Unit | Property | Regression | TypeScript | Memory | E2E | Integration | Browser | Performance | Security | Status |
|------|------|----------|------------|------------|--------|-----|-------------|---------|-------------|----------|--------|
| `ui/src/components/ui/ThemeSelector.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/ui/ToastContainer.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |

### viewport/ (2 files)

| File | Unit | Property | Regression | TypeScript | Memory | E2E | Integration | Browser | Performance | Security | Status |
|------|------|----------|------------|------------|--------|-----|-------------|---------|-------------|----------|--------|
| `ui/src/components/viewport/ViewOptionsToolbar.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/components/viewport/ViewportRenderer.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |

---

## PYTHON BACKEND (26 files)

### nodes/ (8 files)

| File | Unit | Property | Regression | TypeScript | Memory | E2E | Integration | Browser | Performance | Security | Status |
|------|------|----------|------------|------------|--------|-----|-------------|---------|-------------|----------|--------|
| `src/lattice/__init__.py` | ❌ | ❌ | ❌ | N/A | ❌ | ❌ | ❌ | N/A | ❌ | ❌ | |
| `src/lattice/nodes/__init__.py` | ❌ | ❌ | ❌ | N/A | ❌ | ❌ | ❌ | N/A | ❌ | ❌ | |
| `src/lattice/nodes/compositor_node.py` | ✅ | ✅ | ❌ | N/A | ❌ | ❌ | ⚠️ | N/A | ❌ | ⚠️ | |
| `src/lattice/nodes/controlnet_preprocessors.py` | ❌ | ❌ | ❌ | N/A | ❌ | ❌ | ❌ | N/A | ❌ | ❌ | |
| `src/lattice/nodes/lattice_api_proxy.py` | ⚠️ | ❌ | ❌ | N/A | ❌ | ❌ | ⚠️ | N/A | ❌ | ⚠️ | |
| `src/lattice/nodes/lattice_frame_interpolation.py` | ❌ | ❌ | ❌ | N/A | ❌ | ❌ | ❌ | N/A | ❌ | ❌ | |
| `src/lattice/nodes/lattice_layer_decomposition.py` | ❌ | ❌ | ❌ | N/A | ❌ | ❌ | ❌ | N/A | ❌ | ❌ | |
| `src/lattice/nodes/lattice_stem_separation.py` | ❌ | ❌ | ❌ | N/A | ❌ | ❌ | ❌ | N/A | ❌ | ❌ | |
| `src/lattice/nodes/lattice_vectorize.py` | ❌ | ❌ | ❌ | N/A | ❌ | ❌ | ❌ | N/A | ❌ | ❌ | |

### scripts/ (14 files)

| File | Unit | Property | Regression | TypeScript | Memory | E2E | Integration | Browser | Performance | Security | Status |
|------|------|----------|------------|------------|--------|-----|-------------|---------|-------------|----------|--------|
| `src/lattice/scripts/decomp_local.py` | ❌ | ❌ | ❌ | N/A | ❌ | ❌ | ❌ | N/A | ❌ | ❌ | |
| `src/lattice/scripts/decomp_run.py` | ❌ | ❌ | ❌ | N/A | ❌ | ❌ | ❌ | N/A | ❌ | ❌ | |
| `src/lattice/scripts/run_decomp_comfyui.py` | ❌ | ❌ | ❌ | N/A | ❌ | ❌ | ❌ | N/A | ❌ | ❌ | |
| `src/lattice/scripts/run_decomp_now.py` | ❌ | ❌ | ❌ | N/A | ❌ | ❌ | ❌ | N/A | ❌ | ❌ | |
| `src/lattice/scripts/run_decomposition_gpu.py` | ❌ | ❌ | ❌ | N/A | ❌ | ❌ | ❌ | N/A | ❌ | ❌ | |
| `src/lattice/scripts/test_decomp_fp8.py` | ❌ | ❌ | ❌ | N/A | ❌ | ❌ | ❌ | N/A | ❌ | ❌ | |
| `src/lattice/scripts/test_decomp_gpu.py` | ❌ | ❌ | ❌ | N/A | ❌ | ❌ | ❌ | N/A | ❌ | ❌ | |
| `src/lattice/scripts/test_decomp_minimal.py` | ❌ | ❌ | ❌ | N/A | ❌ | ❌ | ❌ | N/A | ❌ | ❌ | |
| `src/lattice/scripts/test_load_all.py` | ❌ | ❌ | ❌ | N/A | ❌ | ❌ | ❌ | N/A | ❌ | ❌ | |
| `src/lattice/scripts/test_load.py` | ❌ | ❌ | ❌ | N/A | ❌ | ❌ | ❌ | N/A | ❌ | ❌ | |
| `src/lattice/scripts/test_manual_load.py` | ❌ | ❌ | ❌ | N/A | ❌ | ❌ | ❌ | N/A | ❌ | ❌ | |
| `src/lattice/scripts/test_transformer.py` | ❌ | ❌ | ❌ | N/A | ❌ | ❌ | ❌ | N/A | ❌ | ❌ | |
| `src/lattice/scripts/run_decomp.bat` | N/A | N/A | N/A | N/A | N/A | N/A | N/A | N/A | N/A | N/A | **Not Python** |
| `src/lattice/scripts/test_decomposition.sh` | N/A | N/A | N/A | N/A | N/A | N/A | N/A | N/A | N/A | N/A | **Not Python** |

### tests/ (5 files)

| File | Unit | Property | Regression | TypeScript | Memory | E2E | Integration | Browser | Performance | Security | Status |
|------|------|----------|------------|------------|--------|-----|-------------|---------|-------------|----------|--------|
| `src/lattice/tests/conftest.py` | ⚠️ | ❌ | ❌ | N/A | ❌ | ❌ | ⚠️ | N/A | ❌ | ❌ | |
| `src/lattice/tests/hypothesis_strategies.py` | ⚠️ | ⚠️ | ❌ | N/A | ❌ | ❌ | ⚠️ | N/A | ❌ | ❌ | |
| `src/lattice/tests/test_compositor_node_hypothesis.py` | ✅ | ✅ | ❌ | N/A | ❌ | ❌ | ⚠️ | N/A | ❌ | ❌ | |
| `src/lattice/tests/test_compositor_node_validation.py` | ✅ | ❌ | ❌ | N/A | ❌ | ❌ | ⚠️ | N/A | ❌ | ❌ | |
| `src/lattice/tests/test_route_registration.py` | ✅ | ❌ | ❌ | N/A | ❌ | ❌ | ⚠️ | N/A | ❌ | ❌ | |

---

## CONFIG, STYLES, MAIN, APP (4 files)

| File | Unit | Property | Regression | TypeScript | Memory | E2E | Integration | Browser | Performance | Security | Status |
|------|------|----------|------------|------------|--------|-----|-------------|---------|-------------|----------|--------|
| `ui/src/config/exportPresets.ts` | ❌ | ❌ | ❌ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/styles/keyframe-shapes.ts` | ❌ | ❌ | ❌ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/main.ts` | ❌ | ❌ | ❌ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |
| `ui/src/App.vue` | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | |

---

