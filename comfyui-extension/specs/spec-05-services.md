# SPEC 05: SERVICES

**Last Updated:** December 23, 2025

---

## Overview

| Metric | Value |
|--------|-------|
| **Total Service Files** | 160 |
| **Effect Renderers** | 16 |
| **AI Services** | 8 |
| **Audio Services** | 6 |
| **Camera/3D Services** | 8 |
| **Export Services** | 5 |

---

## Service Categories

### Animation Services

| Service | File | Purpose |
|---------|------|---------|
| interpolation | `interpolation.ts` | Keyframe interpolation engine |
| easing | `easing.ts` | 45 easing functions |
| expressions | `expressions.ts` | Expression language parser |
| propertyDriver | `propertyDriver.ts` | PropertyLink system |
| layerEvaluationCache | `layerEvaluationCache.ts` | Property evaluation caching |
| rovingKeyframes | `rovingKeyframes.ts` | Roving keyframe conversion |

### Audio Services

| Service | File | Purpose |
|---------|------|---------|
| audioFeatures | `audioFeatures.ts` | FFT, beat detection, BPM |
| audioReactiveMapping | `audioReactiveMapping.ts` | Audio-to-property mapping |
| audioPathAnimator | `audioPathAnimator.ts` | Audio-driven animation |
| audioWorkerClient | `audioWorkerClient.ts` | Web Worker communication |
| timelineWaveform | `timelineWaveform.ts` | Waveform visualization |
| midiToKeyframes | `midiToKeyframes.ts` | MIDI to keyframe conversion |

### Geometry Services

| Service | File | Purpose |
|---------|------|---------|
| arcLength | `arcLength.ts` | Arc-length parameterization (Three.js) |
| textOnPath | `textOnPath.ts` | Text along spline paths |
| shapeOperations | `shapeOperations.ts` | Path boolean operations |
| bezierBoolean | `bezierBoolean.ts` | Bezier path booleans (Paper.js) |
| pathMorphing | `pathMorphing.ts` | Shape morphing |
| svgExtrusion | `svgExtrusion.ts` | SVG to 3D mesh |
| imageTrace | `imageTrace.ts` | Image vectorization |
| textToVector | `textToVector.ts` | Text to vector paths |

### Camera/3D Services

| Service | File | Purpose |
|---------|------|---------|
| cameraTrajectory | `cameraTrajectory.ts` | 22 camera presets |
| cameraEnhancements | `cameraEnhancements.ts` | Shake, DOF, rack focus |
| camera3DVisualization | `camera3DVisualization.ts` | Frustum visualization |
| cameraExport | `cameraExport.ts` | Camera animation export |
| cameraTrackingImport | `cameraTrackingImport.ts` | COLMAP/Blender import |
| math3d | `math3d.ts` | Vec3, Mat4, Quat operations |
| materialSystem | `materialSystem.ts` | PBR materials |
| gaussianSplatting | `gaussianSplatting.ts` | 3DGS rendering |

### Particle Services

| Service | File | Purpose |
|---------|------|---------|
| particleSystem | `particleSystem.ts` | CPU simulation with SeededRNG |
| particleGPU | `particleGPU.ts` | GPU particle system |
| gpuParticleRenderer | `gpuParticleRenderer.ts` | WebGL2 Transform Feedback |
| meshParticleManager | `meshParticleManager.ts` | Mesh-based particles |
| spriteSheet | `spriteSheet.ts` | Sprite animation |

### Export Services

| Service | File | Purpose |
|---------|------|---------|
| matteExporter | `matteExporter.ts` | Matte sequence export |
| modelExport | `modelExport.ts` | glTF, OBJ, camera export |
| svgExport | `svgExport.ts` | SVG export |
| projectStorage | `projectStorage.ts` | Project save/load |
| persistenceService | `persistenceService.ts` | IndexedDB persistence |

### Effect Pipeline

| Service | File | Purpose |
|---------|------|---------|
| effectProcessor | `effectProcessor.ts` | Effect stack pipeline |
| gpuEffectDispatcher | `gpuEffectDispatcher.ts` | Route to WebGPU/WebGL/Canvas2D |

---

## Effect Renderers (16 files: 15 renderers + index.ts)

| Renderer | File | Effects |
|----------|------|---------|
| blurRenderer | `effects/blurRenderer.ts` | Gaussian, Directional, Radial, Box |
| colorRenderer | `effects/colorRenderer.ts` | Brightness, Contrast, Hue/Sat, Levels, Glow, Shadow |
| distortRenderer | `effects/distortRenderer.ts` | Transform, Warp, Displacement |
| generateRenderer | `effects/generateRenderer.ts` | Fill, Gradient, Noise |
| stylizeRenderer | `effects/stylizeRenderer.ts` | Emboss, Find Edges, Mosaic |
| perspectiveRenderer | `effects/perspectiveRenderer.ts` | 3D perspective transforms |
| timeRenderer | `effects/timeRenderer.ts` | Pixel motion, optical flow |
| cinematicBloom | `effects/cinematicBloom.ts` | Cinematic bloom effect |
| colorGrading | `effects/colorGrading.ts` | LUT-based color grading |
| hdrRenderer | `effects/hdrRenderer.ts` | HDR tonemapping |
| layerStyleRenderer | `effects/layerStyleRenderer.ts` | Layer styles (shadow, glow) |
| maskRenderer | `effects/maskRenderer.ts` | Mask processing |
| matteEdge | `effects/matteEdge.ts` | Matte edge refinement |
| audioVisualizer | `effects/audioVisualizer.ts` | Audio visualization |
| expressionControlRenderer | `effects/expressionControlRenderer.ts` | Expression controls |

---

## AI Services (8 files)

| Service | File | Purpose |
|---------|------|---------|
| AICompositorAgent | `ai/AICompositorAgent.ts` | LLM agent with tool calling |
| systemPrompt | `ai/systemPrompt.ts` | Agent system prompt |
| toolDefinitions | `ai/toolDefinitions.ts` | 30+ tool definitions |
| actionExecutor | `ai/actionExecutor.ts` | Tool call execution |
| stateSerializer | `ai/stateSerializer.ts` | Project state serialization |
| cameraTrackingAI | `ai/cameraTrackingAI.ts` | VLM camera motion detection |
| sapiensIntegration | `ai/sapiensIntegration.ts` | Meta AI human vision |
| depthEstimation | `ai/depthEstimation.ts` | Depth map estimation |

---

## Key Implementation Details

### Arc-Length Parameterization

Uses **Three.js curves** (not bezier-js):

```typescript
import * as THREE from 'three';
import { ArcLengthParameterizer } from './arcLength';

// Create a cubic bezier curve
const curve = new THREE.CubicBezierCurve3(
  new THREE.Vector3(0, 0, 0),
  new THREE.Vector3(50, 100, 0),
  new THREE.Vector3(100, 100, 0),
  new THREE.Vector3(150, 0, 0)
);

// Create parameterizer
const param = new ArcLengthParameterizer(curve);

// Get point at 50% of curve length
const midPoint = param.getPointAtDistance(param.totalLength * 0.5);

// Get evenly spaced points
const points = param.getEvenlySpacedPoints(10);
```

**Key methods:**
- `distanceToT(distance)` - Convert arc length to parametric t
- `getPointAtDistance(distance)` - Get point and tangent at distance
- `getEvenlySpacedPoints(count)` - Get evenly distributed points

### Particle System Determinism

Uses **SeededRandom** (Mulberry32) for scrub-safe simulation:

```typescript
export class SeededRandom {
  private state: number;

  constructor(seed: number) {
    this.state = seed;
  }

  next(): number {
    // Mulberry32 algorithm - DETERMINISTIC
    let t = this.state += 0x6D2B79F5;
    t = Math.imul(t ^ t >>> 15, t | 1);
    t ^= t + Math.imul(t ^ t >>> 7, t | 61);
    return ((t ^ t >>> 14) >>> 0) / 4294967296;
  }
}
```

**Checkpoint system** saves state every 30 frames for instant scrubbing.

### GPU Effect Dispatcher

Routes effects to optimal renderer:

```typescript
import { dispatchEffect } from './gpuEffectDispatcher';

// Automatically selects WebGPU, WebGL2, or Canvas2D
const result = await dispatchEffect({
  effect: 'gaussian-blur',
  input: imageData,
  params: { radius: 10 }
});
```

### Property Linking (PropertyLink)

Connect properties across layers:

```typescript
import { PropertyDriver } from './propertyDriver';

const driver = new PropertyDriver();

// Link layer2 opacity to layer1 scale
driver.link({
  sourceLayer: 'layer1',
  sourceProperty: 'transform.scale.x',
  targetLayer: 'layer2',
  targetProperty: 'transform.opacity',
  expression: 'value * 0.5'  // Optional transform
});
```

---

## Utility Services

| Service | File | Purpose |
|---------|------|---------|
| fontService | `fontService.ts` | Font loading, Local Font Access API |
| gpuDetection | `gpuDetection.ts` | GPU capability detection |
| gpuBenchmark | `gpuBenchmark.ts` | GPU performance testing |
| workerPool | `workerPool.ts` | Web Worker management |
| lazyLoader | `lazyLoader.ts` | Lazy loading system |
| frameCache | `frameCache.ts` | LRU frame caching |
| memoryBudget | `memoryBudget.ts` | Memory management |
| timelineSnap | `timelineSnap.ts` | Snap to beats/keyframes |
| jsonValidation | `jsonValidation.ts` | Project JSON validation |
| projectMigration | `projectMigration.ts` | Schema versioning |

---

## Video Services

| Service | File | Purpose |
|---------|------|---------|
| videoDecoder | `videoDecoder.ts` | WebCodecs frame-accurate decoder |
| motionBlur | `motionBlur.ts` | Motion blur post-processing |
| timewarp | `timewarp.ts` | Speed curve integration |
| depthflow | `depthflow.ts` | 2.5D parallax rendering |
| onionSkinning | `onionSkinning.ts` | Onion skin preview |

---

## Render Queue

| Service | File | Purpose |
|---------|------|---------|
| RenderQueueManager | `renderQueue/RenderQueueManager.ts` | Background rendering |
| ColorProfileService | `colorManagement/ColorProfileService.ts` | ICC profile support |

---

## Plugin System

| Service | File | Purpose |
|---------|------|---------|
| PluginManager | `plugins/PluginManager.ts` | Plugin lifecycle management |

---

*Generated: December 23, 2025*
