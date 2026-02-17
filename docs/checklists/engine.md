# Checklist: engine

## engine
| File | Unit | Property | Regression | TypeScript | Memory | E2E | Integration | Browser | Performance | Security |
|:-----|:----:|:--------:|:----------:|:----------:|:------:|:---:|:-----------:|:-------:|:-----------:|:--------:|
| BackgroundManager.ts | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ |
| LatticeEngine.ts | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ |
| MotionEngine.ts | ✅ | ✅ | ⚠️ | ✅ | ⚠️ | ❌ | ⚠️ | ❌ | ⚠️ | ❌ |
| NestedCompRenderer.ts | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ |
| ParticleSimulationController.ts | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ |
| TransformControlsManager.ts | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ |
| index.ts | ❌ | ❌ | ❌ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ |
| types.ts | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ |


## engine/animation
| File | Unit | Property | Regression | TypeScript | Memory | E2E | Integration | Browser | Performance | Security |
|:-----|:----:|:--------:|:----------:|:----------:|:------:|:---:|:-----------:|:-------:|:-----------:|:--------:|
| EasingFunctions.ts | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ |
| KeyframeEvaluator.ts | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ |


## engine/core
| File | Unit | Property | Regression | TypeScript | Memory | E2E | Integration | Browser | Performance | Security |
|:-----|:----:|:--------:|:----------:|:----------:|:------:|:---:|:-----------:|:-------:|:-----------:|:--------:|
| CameraController.ts | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ |
| LayerManager.ts | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ |
| RenderPipeline.ts | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ |
| ResourceManager.ts | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ⚠️ |
| SceneManager.ts | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ |


## engine/layers
| File | Unit | Property | Regression | TypeScript | Memory | E2E | Integration | Browser | Performance | Security |
|:-----|:----:|:--------:|:----------:|:----------:|:------:|:---:|:-----------:|:-------:|:-----------:|:--------:|
| AudioLayer.ts | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ |
| BaseLayer.ts | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ |
| CameraLayer.ts | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ |
| ControlLayer.ts | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ |
| DepthLayer.ts | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ |
| DepthflowLayer.ts | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ |
| EffectLayer.ts | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ |
| GeneratedLayer.ts | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ |
| GroupLayer.ts | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ |
| ImageLayer.ts | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ |
| LightLayer.ts | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ |
| ModelLayer.ts | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ |
| NestedCompLayer.ts | ❌ | ❌ | ❌ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ |
| NormalLayer.ts | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ |
| ParticleLayer.ts | ✅ | ✅ | ⚠️ | ✅ | ⚠️ | ❌ | ⚠️ | ❌ | ❌ | ❌ |
| PathLayer.ts | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ |
| PointCloudLayer.ts | ❌ | ❌ | ❌ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ |
| PoseLayer.ts | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ |
| ProceduralMatteLayer.ts | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ |
| ShapeLayer.ts | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ |
| SolidLayer.ts | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ |
| SplineLayer.ts | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ |
| TextLayer.ts | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ |
| VideoLayer.ts | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ |
| blendModeUtils.ts | ❌ | ❌ | ❌ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ |


## engine/particles
| File | Unit | Property | Regression | TypeScript | Memory | E2E | Integration | Browser | Performance | Security |
|:-----|:----:|:--------:|:----------:|:----------:|:------:|:---:|:-----------:|:-------:|:-----------:|:--------:|
| GPUParticleSystem.ts | ❌ | ✅ | ⚠️ | ✅ | ⚠️ | ❌ | ⚠️ | ❌ | ❌ | ❌ |
| GPUSPHSystem.ts | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ |
| GPUSpringSystem.ts | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ |
| ParticleAudioReactive.ts | ❌ | ✅ | ⚠️ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ |
| ParticleCollisionSystem.ts | ❌ | ✅ | ⚠️ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ |
| ParticleConnectionSystem.ts | ❌ | ✅ | ⚠️ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ |
| ParticleEmitterLogic.ts | ❌ | ✅ | ⚠️ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ |
| ParticleFlockingSystem.ts | ❌ | ✅ | ⚠️ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ |
| ParticleForceCalculator.ts | ❌ | ✅ | ⚠️ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ |
| ParticleFrameCache.ts | ❌ | ✅ | ⚠️ | ✅ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ |
| ParticleGPUPhysics.ts | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ |
| ParticleGroupSystem.ts | ❌ | ✅ | ⚠️ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ |
| ParticleModulationCurves.ts | ❌ | ✅ | ⚠️ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ |
| ParticleSPHSystem.ts | ❌ | ✅ | ⚠️ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ |
| ParticleSpringSystem.ts | ❌ | ✅ | ⚠️ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ |
| ParticleSubEmitter.ts | ❌ | ✅ | ⚠️ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ |
| ParticleTextureSystem.ts | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ |
| ParticleTrailSystem.ts | ❌ | ✅ | ⚠️ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ |
| SpatialHashGrid.ts | ❌ | ✅ | ⚠️ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ |
| index.ts | ❌ | ❌ | ❌ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ |
| particleShaders.ts | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ |
| types.ts | ⚠️ | ⚠️ | ❌ | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ |
| webgpuParticleCompute.ts | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ |


## engine/utils
| File | Unit | Property | Regression | TypeScript | Memory | E2E | Integration | Browser | Performance | Security |
|:-----|:----:|:--------:|:----------:|:----------:|:------:|:---:|:-----------:|:-------:|:-----------:|:--------:|
| PerformanceMonitor.ts | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ |
| colormapShader.ts | ❌ | ❌ | ❌ | ⚠️ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ |


