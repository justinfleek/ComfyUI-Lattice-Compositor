# LATTICE COMPOSITOR - FEATURE INVENTORY
Generated from code analysis
Source: Actual codebase (not documentation)

---

## SUMMARY

| Metric | Count |
|--------|-------|
| Layer Types | 24 |
| Effects | 102 (77 TypeScript + 25 GLSL) |
| Store Actions | 251+ |
| Vue Components | 156 |
| Engine Classes | 59 |
| Services | 160+ |
| Easing Functions | 45 |
| Shape Modifiers | 14 |
| Layer Styles | 10 |
| **Total Audit Items** | **127** |

---

## TIER 1: FOUNDATION (7 items)
*Audit these FIRST - bugs here cascade everywhere*

| ID | Feature | Primary File | Store Action | Engine | UI |
|----|---------|--------------|--------------|--------|-----|
| 1.1 | Layer Creation/Deletion | layerActions.ts | createLayer, deleteLayer | BaseLayer.ts | ProjectPanel.vue |
| 1.2 | Layer Transform | transformActions.ts | setPosition, setScale, setRotation | BaseLayer.ts | TransformProperties.vue |
| 1.3 | Keyframe CRUD | keyframeActions.ts | addKeyframe, removeKeyframe, updateKeyframe | KeyframeEvaluator.ts | Timeline.vue |
| 1.4 | Interpolation Engine | interpolation.ts | N/A (service) | KeyframeEvaluator.ts | CurveEditor.vue |
| 1.5 | Expression Evaluation | expressions/index.ts | setPropertyExpression | ExpressionEngine | ExpressionInput.vue |
| 1.6 | Render Loop | LatticeEngine.ts | N/A (engine) | LatticeEngine.ts | ThreeCanvas.vue |
| 1.7 | Project Save/Load | projectActions.ts | saveProject, loadProject | N/A | ProjectPanel.vue |

---

## TIER 2: LAYER TYPES (23 items)

| ID | Layer Type | Engine File | Store Action | Properties UI |
|----|------------|-------------|--------------|---------------|
| 2.1 | SolidLayer | SolidLayer.ts | createLayer('solid') | SolidProperties.vue |
| 2.2 | ImageLayer | ImageLayer.ts | createLayer('image') | ImageProperties.vue |
| 2.3 | VideoLayer | VideoLayer.ts | createLayer('video') | VideoProperties.vue |
| 2.4 | TextLayer | TextLayer.ts | createTextLayer | TextProperties.vue |
| 2.5 | ShapeLayer | ShapeLayer.ts | createShapeLayer | ShapeProperties.vue |
| 2.6 | AudioLayer | AudioLayer.ts | createLayer('audio') | AudioProperties.vue |
| 2.7 | CameraLayer | CameraLayer.ts | createCameraLayer | CameraProperties.vue |
| 2.8 | LightLayer | LightLayer.ts | createLightLayer | LightProperties.vue |
| 2.9 | ControlLayer (Null) | ControlLayer.ts | createLayer('control') | ControlProperties.vue |
| 2.10 | GroupLayer | GroupLayer.ts | createGroupLayer | GroupProperties.vue |
| 2.11 | NestedCompLayer | NestedCompLayer.ts | createNestedComp | NestedCompProperties.vue |
| 2.12 | EffectLayer (Adjustment) | EffectLayer.ts | createAdjustmentLayer | EffectLayerProperties.vue |
| 2.13 | ParticleLayer | ParticleLayer.ts | createParticleLayer | ParticleProperties.vue |
| 2.14 | PathLayer | PathLayer.ts | createPathLayer | PathProperties.vue |
| 2.15 | SplineLayer | SplineLayer.ts | createSplineLayer | SplineProperties.vue |
| 2.16 | ModelLayer | ModelLayer.ts | createModelLayer | ModelProperties.vue |
| 2.17 | PointCloudLayer | PointCloudLayer.ts | createPointCloudLayer | PointCloudProperties.vue |
| 2.18 | DepthLayer | DepthLayer.ts | createDepthLayer | DepthProperties.vue |
| 2.19 | DepthflowLayer | DepthflowLayer.ts | createDepthflowLayer | DepthflowProperties.vue |
| 2.20 | NormalLayer | NormalLayer.ts | createNormalLayer | NormalProperties.vue |
| 2.21 | PoseLayer | PoseLayer.ts | createPoseLayer | PoseProperties.vue |
| 2.22 | GeneratedLayer | GeneratedLayer.ts | createGeneratedLayer | GeneratedProperties.vue |
| 2.23 | ProceduralMatteLayer | ProceduralMatteLayer.ts | createProceduralMatte | ProceduralMatteProperties.vue |

---

## TIER 3: ANIMATION SUBSYSTEMS (10 items)

| ID | Feature | Primary Files | Dependencies |
|----|---------|---------------|--------------|
| 3.1 | Text Animators | textAnimator.ts, textAnimatorActions.ts | TextLayer |
| 3.2 | Text on Path | textOnPath.ts | TextLayer, PathLayer |
| 3.3 | Shape Modifiers | pathModifiers.ts | ShapeLayer |
| 3.4 | Shape Booleans | bezierBoolean.ts, shapeOperations.ts | ShapeLayer |
| 3.5 | Path Morphing | pathMorphing.ts | ShapeLayer, PathLayer |
| 3.6 | Roving Keyframes | rovingKeyframes.ts | Keyframe System |
| 3.7 | Time Warp/Remapping | timewarp.ts | Layer System |
| 3.8 | Motion Expressions | motionExpressions.ts | Expression System |
| 3.9 | Loop Expressions | loopExpressions.ts | Expression System |
| 3.10 | Audio Expressions | audioExpressions.ts | Expression System, Audio |

---

## TIER 4: EFFECTS SYSTEM (12 items by category)

| ID | Category | Count | Primary Location | Sample Effects |
|----|----------|-------|------------------|----------------|
| 4.1 | Blur/Sharpen | 6 | effects/blur-sharpen/ | Gaussian, Directional, Radial, Box |
| 4.2 | Color Correction | 23 | effects/color-correction/ | Levels, Curves, LUT, Color Balance |
| 4.3 | Distort | 12 | effects/distort/ | Warp, Bulge, Twirl, Ripple, Wave |
| 4.4 | Generate | 5 | effects/generate/ | Fill, Gradient, Fractal Noise |
| 4.5 | Stylize | 10 | effects/stylize/ | Glow, Bloom, Emboss, Mosaic |
| 4.6 | Time | 4 | effects/time/ | Echo, Posterize Time, Freeze Frame |
| 4.7 | Noise/Grain | 4 | effects/noise-grain/ | Add Grain, RGB Split, Scanlines |
| 4.8 | Matte | 2 | effects/matte/ | Fog 3D, Depth Matte |
| 4.9 | Utility | 7 | effects/utility/ | Slider, Checkbox, Color Controls |
| 4.10 | GLSL Shaders | 25 | effects/glsl/ | GPU-accelerated versions |
| 4.11 | Effect Application | 1 | effectActions.ts | addEffectToLayer, removeEffect |
| 4.12 | Effect Ordering | 1 | effectActions.ts | reorderEffects |

---

## TIER 5: PARTICLE SYSTEM (12 items)

| ID | Feature | Primary File | Dependencies |
|----|---------|--------------|--------------|
| 5.1 | GPU Particle Core | GPUParticleSystem.ts | WebGPU |
| 5.2 | Emitter Logic | ParticleEmitterLogic.ts | Core |
| 5.3 | Force Calculator | ParticleForceCalculator.ts | Core |
| 5.4 | Collision System | ParticleCollisionSystem.ts | SpatialHashGrid |
| 5.5 | Flocking/Boids | ParticleFlockingSystem.ts | Core |
| 5.6 | Trail System | ParticleTrailSystem.ts | Core |
| 5.7 | Sub-Emitters | ParticleSubEmitter.ts | Emitter |
| 5.8 | Audio Reactive | ParticleAudioReactive.ts | Audio System |
| 5.9 | Connection System | ParticleConnectionSystem.ts | SpatialHashGrid |
| 5.10 | Frame Cache | ParticleFrameCache.ts | Core |
| 5.11 | Texture/Sprites | ParticleTextureSystem.ts | Core |
| 5.12 | Modulation Curves | ParticleModulationCurves.ts | Core |

---

## TIER 6: AUDIO SYSTEM (7 items)

| ID | Feature | Primary File | Store Actions |
|----|---------|--------------|---------------|
| 6.1 | FFT Analysis | audioFeatures.ts | getFrequencyBandAtFrame |
| 6.2 | Beat Detection | enhancedBeatDetection.ts | detectAudioPeaks |
| 6.3 | Stem Separation | stemSeparation.ts | separateStems |
| 6.4 | Property Mapping | audioReactiveMapping.ts | addAudioMapping |
| 6.5 | Path Animation | audioPathAnimator.ts | N/A |
| 6.6 | Timeline Waveform | timelineWaveform.ts | N/A |
| 6.7 | MIDI Import | audioActions.ts | midiToKeyframes |

---

## TIER 7: 3D/CAMERA SYSTEM (10 items)

| ID | Feature | Primary File | Dependencies |
|----|---------|--------------|--------------|
| 7.1 | Camera Creation | CameraLayer.ts | Layer System |
| 7.2 | Camera Keyframes | cameraActions.ts | Keyframe System |
| 7.3 | Depth of Field | CameraLayer.ts (DOF) | Camera |
| 7.4 | Two-Node Camera | cameraActions.ts | Camera |
| 7.5 | Camera Tracking Import | cameraTrackingImport.ts | Camera |
| 7.6 | AI Camera Tracking | cameraTrackingAI.ts | Camera, AI |
| 7.7 | 3D Layer Transform | BaseLayer.ts | Layer System |
| 7.8 | Lights | LightLayer.ts | 3D System |
| 7.9 | 3D Models | ModelLayer.ts | 3D System |
| 7.10 | Point Clouds | PointCloudLayer.ts | 3D System |

---

## TIER 8: PHYSICS SYSTEM (5 items)

| ID | Feature | Primary File | Dependencies |
|----|---------|--------------|--------------|
| 8.1 | Physics Engine | PhysicsEngine.ts | Rapier.js |
| 8.2 | Rigid Bodies | PhysicsEngine.ts | Physics Engine |
| 8.3 | Joint System | JointSystem.ts | Physics Engine |
| 8.4 | Ragdoll Builder | RagdollBuilder.ts | Joint System |
| 8.5 | Bake to Keyframes | physicsActions.ts | Keyframe System |

---

## TIER 9: LAYER STYLES (10 items)

| ID | Style | Service | UI |
|----|-------|---------|-----|
| 9.1 | Drop Shadow | layerStyles.ts | LayerStylesPanel.vue |
| 9.2 | Inner Shadow | layerStyles.ts | LayerStylesPanel.vue |
| 9.3 | Outer Glow | layerStyles.ts | LayerStylesPanel.vue |
| 9.4 | Inner Glow | layerStyles.ts | LayerStylesPanel.vue |
| 9.5 | Bevel & Emboss | layerStyles.ts | LayerStylesPanel.vue |
| 9.6 | Satin | layerStyles.ts | LayerStylesPanel.vue |
| 9.7 | Color Overlay | layerStyles.ts | LayerStylesPanel.vue |
| 9.8 | Gradient Overlay | layerStyles.ts | LayerStylesPanel.vue |
| 9.9 | Stroke | layerStyles.ts | LayerStylesPanel.vue |
| 9.10 | Blending Options | layerStyles.ts | LayerStylesPanel.vue |

---

## TIER 10: EXPORT SYSTEM (6 items)

| ID | Export Type | Primary File | Dependencies |
|----|-------------|--------------|--------------|
| 10.1 | Frame Sequences | frameSequenceExporter.ts | Render Loop |
| 10.2 | Video Encoding | videoEncoder.ts | Frame Sequences |
| 10.3 | Depth Maps | depthRenderer.ts | Depth System |
| 10.4 | Camera Data | cameraExportFormats.ts | Camera System |
| 10.5 | Pose Data | poseExport.ts | Pose System |
| 10.6 | ComfyUI Workflows | comfyuiClient.ts | All Systems |

---

## TIER 11: AI INTEGRATIONS (5 items)

| ID | Feature | Primary File | External Deps |
|----|---------|--------------|---------------|
| 11.1 | Depth Estimation | depthEstimation.ts | ML Model |
| 11.2 | Pose Estimation | sapiensIntegration.ts | Sapiens |
| 11.3 | Segmentation | segmentation.ts | ML Model |
| 11.4 | Layer Decomposition | layerDecomposition.ts | Segmentation |
| 11.5 | Mask Generator | maskGenerator.ts | Segmentation |

---

## TIER 12: DATA & TEMPLATES (4 items)

| ID | Feature | Primary File | Dependencies |
|----|---------|--------------|--------------|
| 12.1 | JSON Data Import | dataExpressions.ts | Expression System |
| 12.2 | CSV/TSV Import | dataExpressions.ts | Expression System |
| 12.3 | Template Builder | essentialGraphicsActions.ts | All Systems |
| 12.4 | Expression Controls | utility effects | Effect System |

---

## ORPHANED CODE (Investigate)

| Feature | Location | Status |
|---------|----------|--------|
| Plugin System | PluginManager.ts | Stub only |
| Gaussian Splatting | gaussianSplatting.ts | No UI |
| Motion Recording | motionRecording.ts | No UI trigger |
| Sprite Sheet Export | spriteSheet.ts | No UI |
| Vision Authoring | visionAuthoring/*.ts | Experimental |

---

## WIRING STATUS LEGEND

- ✅ **WIRED** - UI → Store → Engine → Render verified connected
- ⚠️ **PARTIAL** - Some connections missing
- ❌ **BROKEN** - Connection exists but doesn't work
- 🔇 **ORPHANED** - Code exists but no UI access