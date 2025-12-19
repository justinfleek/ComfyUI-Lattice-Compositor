# Weyl Compositor API Documentation

This document provides API reference for the core services in Weyl Compositor.

## Table of Contents

- [Interpolation Service](#interpolation-service)
- [Effect System](#effect-system)
- [Particle System](#particle-system)
- [Layer Evaluation Cache](#layer-evaluation-cache)
- [Matte Exporter](#matte-exporter)
- [WebGPU Renderer](#webgpu-renderer)
- [Arc Length Parameterizer](#arc-length-parameterizer)
- [Audio Features](#audio-features)

---

## Interpolation Service

Location: `ui/src/services/interpolation.ts`

Handles property animation interpolation with bezier caching for performance.

### Core Functions

```typescript
/**
 * Interpolate an animated property at a specific frame
 * @param property - The animatable property to interpolate
 * @param frame - The frame number
 * @returns The interpolated value
 */
function interpolateProperty<T>(property: AnimatableProperty<T>, frame: number): T
```

```typescript
/**
 * Interpolate between two keyframes
 * @param kf1 - Start keyframe
 * @param kf2 - End keyframe
 * @param progress - Progress between 0-1
 * @returns Interpolated value
 */
function interpolateKeyframes<T>(kf1: Keyframe<T>, kf2: Keyframe<T>, progress: number): T
```

### Easing Functions

Built-in easing functions available via `getEasingFunction(name)`:

- `linear` - No easing
- `easeIn`, `easeOut`, `easeInOut` - Quadratic
- `easeInCubic`, `easeOutCubic`, `easeInOutCubic` - Cubic
- `easeInQuart`, `easeOutQuart`, `easeInOutQuart` - Quartic
- `easeInBack`, `easeOutBack`, `easeInOutBack` - Overshoot
- `easeInElastic`, `easeOutElastic`, `easeInOutElastic` - Elastic
- `easeInBounce`, `easeOutBounce`, `easeInOutBounce` - Bounce

### Bezier Cache

```typescript
/**
 * Get bezier cache statistics
 */
function getBezierCacheStats(): { hits: number; misses: number; size: number }

/**
 * Clear the bezier cache
 */
function clearBezierCache(): void
```

---

## Effect System

Location: `ui/src/services/effects/`

Modular effect rendering system with GPU acceleration.

### Initialization

```typescript
import { initializeEffects } from '@/services/effects';

// Initialize all effect renderers (call once at startup)
initializeEffects();
```

### Effect Types

#### Blur Effects
- `gaussianBlurRenderer` - Standard gaussian blur
- `directionalBlurRenderer` - Motion blur in a direction
- `radialBlurRenderer` - Zoom blur from center
- `boxBlurRenderer` - Fast box blur
- `sharpenRenderer` - Unsharp mask sharpening

#### Color Effects
- `brightnessContrastRenderer` - Brightness/contrast adjustment
- `hueSaturationRenderer` - HSL adjustments
- `levelsRenderer` - Input/output levels
- `curvesRenderer` - Curves adjustment
- `tintRenderer` - Color tint
- `glowRenderer` - Soft glow
- `dropShadowRenderer` - Drop shadow
- `vibranceRenderer` - Selective saturation
- `invertRenderer` - Invert colors
- `posterizeRenderer` - Reduce color levels

#### Distort Effects
- `transformRenderer` - Scale, rotate, translate
- `warpRenderer` - Mesh deformation
- `displacementMapRenderer` - Displacement mapping

#### Generate Effects
- `fillRenderer` - Solid color fill
- `gradientRampRenderer` - Gradient generation
- `fractalNoiseRenderer` - Procedural noise

### Processing Effects

```typescript
import { processEffectStack } from '@/services/effectProcessor';

/**
 * Process a stack of effects on image data
 * @param imageData - Source image data
 * @param effects - Array of effect definitions
 * @param frame - Current frame for animation
 * @returns Processed image data
 */
const result = await processEffectStack(imageData, effects, frame);
```

### Canvas Pool

```typescript
import { getCanvas, releaseCanvas, getPoolStats } from '@/services/effectProcessor';

// Get a canvas from the pool
const canvas = getCanvas(width, height);

// Return canvas to pool when done
releaseCanvas(canvas);

// Monitor pool usage
const stats = getPoolStats();
// { poolSize: number, inUse: number, created: number }
```

---

## Particle System

Location: `ui/src/services/particleSystem.ts`

Deterministic particle simulation with pooling.

### Creating a System

```typescript
import { ParticleSystem, createDefaultSystemConfig, createDefaultEmitterConfig } from '@/services/particleSystem';

const system = new ParticleSystem(createDefaultSystemConfig({
  maxParticles: 10000,
  warmupPeriod: 30,
  seed: 12345  // For determinism
}));
```

### Emitters

```typescript
// Add an emitter
system.addEmitter(createDefaultEmitterConfig('main', {
  position: { x: 500, y: 500 },
  shape: 'circle',
  radius: 50,
  rate: 100,  // particles per frame
  particleConfig: {
    lifetime: { min: 30, max: 60 },
    speed: { min: 2, max: 5 },
    size: { min: 2, max: 8 },
    color: { r: 255, g: 200, b: 100, a: 1 }
  }
}));

// Update emitter
system.updateEmitter('main', { rate: 200 });

// Remove emitter
system.removeEmitter('main');
```

### Force Fields

```typescript
// Add gravity well (attractor/repeller)
system.addGravityWell({
  id: 'attractor',
  position: { x: 960, y: 540 },
  strength: 100,  // Positive attracts, negative repels
  radius: 200,
  falloff: 'inverse_square'
});

// Add vortex (rotational force)
system.addVortex({
  id: 'spin',
  position: { x: 960, y: 540 },
  strength: 50,
  radius: 300,
  direction: 'clockwise'
});
```

### Simulation

```typescript
// Step simulation forward one frame
system.step();

// Get current particle state
const particles = system.getParticles();
// Returns: Array<{ x, y, vx, vy, size, color, alpha, life, maxLife }>

// Reset to initial state
system.reset();

// Render to mask for matte export
const maskData = system.renderToMask(1920, 1080);
```

### Statistics

```typescript
const stats = system.getStats();
// { activeParticles, poolSize, emitterCount }
```

---

## Layer Evaluation Cache

Location: `ui/src/services/layerEvaluationCache.ts`

Caches evaluated layer properties for performance.

### Version Tracking

```typescript
import {
  markLayerDirty,
  markAllLayersDirty,
  getLayerVersion,
  getGlobalVersion
} from '@/services/layerEvaluationCache';

// Mark layer as changed (increments version)
markLayerDirty('layer-id');

// Reset all layer versions
markAllLayersDirty();

// Get current version
const version = getLayerVersion('layer-id');
const globalVer = getGlobalVersion();
```

### Cached Evaluation

```typescript
import { evaluateLayerCached, evaluateLayersCached } from '@/services/layerEvaluationCache';

// Evaluate single layer with caching
const evaluated = evaluateLayerCached(layer, frame);
// Returns: EvaluatedLayer (frozen object)

// Batch evaluate multiple layers
const allEvaluated = evaluateLayersCached(layers, frame);
```

### EvaluatedLayer Structure

```typescript
interface EvaluatedLayer {
  id: string;
  type: LayerType;
  visible: boolean;
  inRange: boolean;  // Within in/out points
  opacity: number;
  blendMode: BlendMode;
  transform: {
    position: { x: number; y: number; z?: number };
    scale: { x: number; y: number; z?: number };
    rotation: number;
    rotationX?: number;
    rotationY?: number;
    rotationZ?: number;
    anchor: { x: number; y: number; z?: number };
  };
  threeD: boolean;
  effects: EvaluatedEffect[];
  properties: EvaluatedProperty[];
  data: unknown;
}
```

### Cache Management

```typescript
import {
  clearLayerCache,
  clearEvaluationCache,
  getEvaluationCacheStats
} from '@/services/layerEvaluationCache';

// Clear specific layer's cache
clearLayerCache('layer-id');

// Clear entire cache
clearEvaluationCache();

// Get statistics
const stats = getEvaluationCacheStats();
// { size: number, maxSize: number }
```

---

## Matte Exporter

Location: `ui/src/services/matteExporter.ts`

Generates black/white mattes for Wan video generation.

### Dimension Validation

```typescript
import { matteExporter } from '@/services/matteExporter';

// Validate dimensions (must be divisible by 8, min 256px)
const validation = matteExporter.validateDimensions(1920, 1080);
// { valid: boolean, correctedWidth: number, correctedHeight: number, message?: string }

// Get standard presets
const presets = matteExporter.getResolutionPresets();
// [{ label: '720p (1280x720)', width: 1280, height: 720 }, ...]
```

### Generating Mattes

```typescript
// Generate full sequence
const frames = await matteExporter.generateMatteSequence(
  project,
  { width: 1920, height: 1080, matteMode: 'exclude_text' },
  (progress) => console.log(`${progress.percent}%`)
);
// Returns: Blob[]

// Generate single preview frame
const previewUrl = await matteExporter.generatePreviewFrame(project, 0, options);
// Returns: blob URL string
```

### Matte Modes

- `exclude_text` - Text layers rendered as black (excluded from generation)
- `include_all` - Full white frame (include everything)

### Export to ZIP

```typescript
await matteExporter.downloadAsZip(
  frames,
  'my_export',
  (percent) => console.log(`Zipping: ${percent}%`)
);
```

---

## WebGPU Renderer

Location: `ui/src/services/webgpuRenderer.ts`

GPU-accelerated image processing with Canvas2D fallback.

### Initialization

```typescript
import { webgpuRenderer, getWebGPUStats } from '@/services/webgpuRenderer';

// Initialize (auto-detects capability)
const available = await webgpuRenderer.initialize();

// Check availability
if (webgpuRenderer.isAvailable()) {
  console.log('WebGPU available');
}

// Get capabilities
const caps = webgpuRenderer.getCapabilities();
// { available: boolean, features: string[], limits: GPULimits }
```

### Blur Effect

```typescript
const blurred = await webgpuRenderer.blur(imageData, {
  radius: 10,
  quality: 'high',  // 'low' | 'medium' | 'high'
  direction: 'both'  // 'horizontal' | 'vertical' | 'both'
});
```

### Color Correction

```typescript
const corrected = await webgpuRenderer.colorCorrect(imageData, {
  brightness: 0.1,   // -1 to 1
  contrast: 0.2,     // -1 to 1
  saturation: 0,     // -1 to 1
  hue: 0             // -180 to 180 degrees
});
```

### Cleanup

```typescript
webgpuRenderer.dispose();
```

---

## Arc Length Parameterizer

Location: `ui/src/services/arcLength.ts`

Enables even spacing of elements along bezier curves.

### Usage

```typescript
import { ArcLengthParameterizer, pathCommandsToBezier } from '@/services/arcLength';

// Parse SVG path to bezier
const bezier = pathCommandsToBezier([
  ['M', 0, 0],
  ['C', 100, 0, 200, 100, 300, 100]
]);

// Create parameterizer
const param = new ArcLengthParameterizer(bezier, { sampleCount: 100 });

// Get total length
const length = param.totalLength;

// Get point at specific distance along curve
const { point, tangent } = param.getPointAtDistance(150);
// point: { x: number, y: number }
// tangent: { x: number, y: number } (unit vector)

// Get distance at parameter t
const distance = param.getDistanceAtT(0.5);

// Get parameter t at distance
const t = param.getTAtDistance(150);
```

---

## Audio Features

Location: `ui/src/services/audioFeatures.ts`

Audio analysis for reactive animations.

### Loading Audio

```typescript
import { audioFeatures } from '@/services/audioFeatures';

// Load from file
await audioFeatures.loadAudioFile(file);

// Load from URL
await audioFeatures.loadAudioUrl('path/to/audio.mp3');
```

### Feature Extraction

```typescript
// Get features at specific frame
const features = audioFeatures.getFeaturesAtFrame(frame, fps);
// Returns: AudioFeatures

interface AudioFeatures {
  amplitude: number;        // 0-1, overall loudness
  bass: number;            // 0-1, low frequency energy
  mid: number;             // 0-1, mid frequency energy
  treble: number;          // 0-1, high frequency energy
  spectralCentroid: number; // Hz, "brightness"
  onsetStrength: number;   // 0-1, beat/transient detection
  rms: number;             // Root mean square energy
}
```

### Audio Reactive Mapping

```typescript
import { mapAudioToProperty } from '@/services/audioReactiveMapping';

// Map audio feature to property value
const value = mapAudioToProperty(features, {
  feature: 'bass',
  min: 0,
  max: 100,
  smoothing: 0.3,
  threshold: 0.1,
  curve: 'exponential'
});
```

---

## Lazy Loading

Location: `ui/src/services/lazyLoader.ts`

On-demand module loading for bundle optimization.

```typescript
import {
  loadWebGPURenderer,
  loadMatteExporter,
  loadParticleSystem,
  preloadCommonModules,
  preloadExportModules
} from '@/services/lazyLoader';

// Load modules on demand
const webgpu = await loadWebGPURenderer();
const matte = await loadMatteExporter();

// Preload during idle time
preloadCommonModules();

// Preload when user opens export dialog
preloadExportModules();
```

---

## Store Actions

### Layer Actions

Location: `ui/src/stores/actions/layerActions.ts`

```typescript
import { useCompositorStore } from '@/stores/compositorStore';

const store = useCompositorStore();

// Create layers
const solid = store.createSolidLayer();
const text = store.createTextLayer();
const spline = store.createSplineLayer();
const particle = store.createParticleLayer();

// Layer operations
store.selectLayer(layerId);
store.deleteLayer(layerId);
store.duplicateLayer(layerId);
store.renameLayer(layerId, 'New Name');
store.moveLayer(layerId, newIndex);

// Update layer properties
store.updateLayer(layerId, { visible: false });
store.updateLayerData(layerId, { text: 'Hello' });
store.setLayerVisibility(layerId, false);
```

### Keyframe Actions

Location: `ui/src/stores/actions/keyframeActions.ts`

```typescript
// Add keyframe
store.addKeyframe(layerId, 'transform.position', 30, { x: 100, y: 200 });

// Remove keyframe
store.removeKeyframe(layerId, 'opacity', keyframeId);

// Update keyframe
store.setKeyframeValue(layerId, 'transform.rotation', keyframeId, 45);
store.setKeyframeInterpolation(layerId, 'opacity', keyframeId, 'bezier');

// Bezier handles
store.setKeyframeHandle(layerId, 'transform.scale', keyframeId, 'in', {
  frame: -5,
  value: 0.2,
  enabled: true
});
```

### Camera Actions

Location: `ui/src/stores/actions/cameraActions.ts`

```typescript
// Camera management
const camera = store.createCamera('Main Camera');
store.setActiveCamera(cameraId);
store.updateCamera(cameraId, { fov: 60 });
store.deleteCamera(cameraId);

// Camera animation
store.addCameraKeyframe(cameraId, 'position', 0, { x: 0, y: 0, z: 1000 });
store.addCameraKeyframe(cameraId, 'target', 0, { x: 0, y: 0, z: 0 });
```

---

## Types

Location: `ui/src/types/project.ts`

### Creating Default Values

```typescript
import {
  createDefaultTransform,
  createAnimatableProperty,
  createDefaultCamera,
  createDefaultKeyframe
} from '@/types/project';

// Default layer transform
const transform = createDefaultTransform();

// Animatable property
const opacity = createAnimatableProperty('opacity', 100, 'number');
const position = createAnimatableProperty('position', { x: 0, y: 0 }, 'vector2');

// Keyframe
const kf = createDefaultKeyframe(0, 100, 'linear');
```
