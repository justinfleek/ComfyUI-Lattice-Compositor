# SERVICE API REFERENCE

**Weyl Compositor - Complete Service Layer Documentation**

**HYPER-CRITICAL FOR HANDOFF**: This document provides exhaustive function signatures, parameters, return types, and usage examples for all 42 services in the Weyl Compositor.

---

## Table of Contents

1. [Animation Services](#1-animation-services)
2. [Audio Services](#2-audio-services)
3. [Camera & 3D Services](#3-camera--3d-services)
4. [Particle Services](#4-particle-services)
5. [Shape & Geometry Services](#5-shape--geometry-services)
6. [Effect Services](#6-effect-services)
7. [Export Services](#7-export-services)
8. [Cache Services](#8-cache-services)
9. [Asset & Storage Services](#9-asset--storage-services)
10. [Utility Services](#10-utility-services)

---

## 1. Animation Services

### 1.1 interpolation.ts

**Purpose**: Core keyframe interpolation engine. PURE MODULE - all functions are deterministic.

**Location**: `ui/src/services/interpolation.ts`

**Size**: ~21KB | **Lines**: ~700

#### Exports

```typescript
// Main interpolation function
export function interpolateProperty<T>(
  property: AnimatableProperty<T>,
  frame: number,
  fps?: number,          // Default: 30
  layerId?: string       // For expression context
): T;

// Easing presets (normalized 0-1 range)
export const EASING_PRESETS_NORMALIZED: Record<string, {
  x1: number;  // First control point X
  y1: number;  // First control point Y
  x2: number;  // Second control point X
  y2: number;  // Second control point Y
}>;

// Alias for EASING_PRESETS_NORMALIZED
export const EASING_PRESETS: typeof EASING_PRESETS_NORMALIZED;

// Create bezier handles for a preset
export function createHandlesForPreset(
  preset: string,
  frameDuration: number,
  valueDelta: number
): { outHandle: BezierHandle; inHandle: BezierHandle };

// Apply preset to keyframe pair
export function applyEasingPreset(
  keyframe1: Keyframe<any>,
  keyframe2: Keyframe<any>,
  preset: string
): void;

// Get point on bezier curve
export function getBezierCurvePoint(
  t: number,
  p0: number,
  p1: number,
  p2: number,
  p3: number
): number;

// Normalized version (0-1 range)
export function getBezierCurvePointNormalized(
  t: number,
  x1: number,
  y1: number,
  x2: number,
  y2: number
): number;

// Apply easing function by name
export function applyEasing(
  t: number,
  easingName: EasingName
): number;

// Cache management
export function clearBezierCache(): void;
export function getBezierCacheStats(): { size: number; maxSize: number };
```

#### Easing Presets Available

| Preset | Description | Cubic Bezier |
|--------|-------------|--------------|
| `linear` | No easing | (0.33, 0.33, 0.67, 0.67) |
| `ease` | Smooth start/end | (0.25, 0.1, 0.25, 1.0) |
| `ease-in` | Slow start | (0.42, 0, 1.0, 1.0) |
| `ease-out` | Slow end | (0, 0, 0.58, 1.0) |
| `ease-in-out` | Slow both | (0.42, 0, 0.58, 1.0) |
| `ease-in-quad` | Quadratic in | (0.55, 0.085, 0.68, 0.53) |
| `ease-out-quad` | Quadratic out | (0.25, 0.46, 0.45, 0.94) |
| `ease-in-cubic` | Cubic in | (0.55, 0.055, 0.675, 0.19) |
| `ease-out-cubic` | Cubic out | (0.215, 0.61, 0.355, 1.0) |
| `ease-in-back` | Overshoot start | (0.6, -0.28, 0.735, 0.045) |
| `ease-out-back` | Overshoot end | (0.175, 0.885, 0.32, 1.275) |

#### Usage Example

```typescript
import { interpolateProperty, EASING_PRESETS } from '@/services/interpolation';

const opacityProp: AnimatableProperty<number> = {
  value: 1,
  animated: true,
  keyframes: [
    { frame: 0, value: 0, interpolation: 'ease-out' },
    { frame: 30, value: 1, interpolation: 'linear' }
  ]
};

const value = interpolateProperty(opacityProp, 15); // Returns ~0.75
```

---

### 1.2 easing.ts

**Purpose**: Standalone easing functions (object-based, not individual exports).

**Location**: `ui/src/services/easing.ts`

**Size**: ~8KB

#### Exports

```typescript
// Type definitions
export type EasingFunction = (t: number) => number;
export type EasingName = keyof typeof easings;

// All easing functions as object
export const easings: Record<string, EasingFunction>;

// List of easing names
export const easingNames: string[];

// Grouped by category
export const easingGroups: Record<string, string[]>;

// Get easing function by name
export function getEasing(name: string): EasingFunction;

// Apply easing by name
export function applyEasing(t: number, name: string): number;

// Interpolate with easing
export function interpolateWithEasing(
  from: number,
  to: number,
  t: number,
  easing: string
): number;
```

#### Available Easings

```
easingGroups = {
  "Linear": ["linear"],
  "Quad": ["easeInQuad", "easeOutQuad", "easeInOutQuad"],
  "Cubic": ["easeInCubic", "easeOutCubic", "easeInOutCubic"],
  "Quart": ["easeInQuart", "easeOutQuart", "easeInOutQuart"],
  "Quint": ["easeInQuint", "easeOutQuint", "easeInOutQuint"],
  "Sine": ["easeInSine", "easeOutSine", "easeInOutSine"],
  "Expo": ["easeInExpo", "easeOutExpo", "easeInOutExpo"],
  "Circ": ["easeInCirc", "easeOutCirc", "easeInOutCirc"],
  "Back": ["easeInBack", "easeOutBack", "easeInOutBack"],
  "Elastic": ["easeInElastic", "easeOutElastic", "easeInOutElastic"],
  "Bounce": ["easeInBounce", "easeOutBounce", "easeInOutBounce"]
}
```

---

### 1.3 expressions.ts

**Purpose**: Expression evaluation system for dynamic property values.

**Location**: `ui/src/services/expressions.ts`

**Size**: ~15KB

#### Exports

```typescript
// Types
export interface ExpressionContext {
  frame: number;
  time: number;       // frame / fps
  fps: number;
  layerId: string;
  composition?: {
    width: number;
    height: number;
    frameCount: number;
    duration: number;
  };
}

export interface Expression {
  code: string;
  enabled: boolean;
}

// Main evaluation function
export function evaluateExpression(
  expression: Expression,
  context: ExpressionContext,
  currentValue: any
): any;

// Built-in expression helpers (available in expression code)
export const easing: {
  linear: (t: number) => number;
  easeIn: (t: number) => number;
  easeOut: (t: number) => number;
  // ... all easings
};

export const motion: {
  wiggle: (frequency: number, amplitude: number, time: number) => number;
  bounce: (elasticity: number, gravity: number, time: number) => number;
};

export const loop: {
  cycle: (value: number, min: number, max: number) => number;
  pingPong: (value: number, min: number, max: number) => number;
};

export const time: {
  seconds: (frame: number, fps: number) => number;
  frames: (seconds: number, fps: number) => number;
};

export const math: {
  clamp: (value: number, min: number, max: number) => number;
  lerp: (a: number, b: number, t: number) => number;
  map: (value: number, inMin: number, inMax: number, outMin: number, outMax: number) => number;
  random: (seed: number) => number;  // Deterministic!
};
```

#### Expression Example

```typescript
// In layer property expression:
const expr: Expression = {
  code: `
    const t = time.seconds(frame, fps);
    const wiggleAmount = motion.wiggle(2, 10, t);
    return currentValue + wiggleAmount;
  `,
  enabled: true
};
```

---

### 1.4 propertyDriver.ts

**Purpose**: Property linking system (pickwhip-style) with audio reactivity.

**Location**: `ui/src/services/propertyDriver.ts`

**Size**: ~25KB

#### Exports

```typescript
// Types
export type DriverSourceType =
  | 'property'      // Another layer's property
  | 'audio'         // Audio analysis feature
  | 'expression';   // Custom expression

export type PropertyPath =
  | 'position.x' | 'position.y' | 'position.z'
  | 'rotation.x' | 'rotation.y' | 'rotation.z'
  | 'scale.x' | 'scale.y' | 'scale.z'
  | 'opacity'
  | 'anchor.x' | 'anchor.y' | 'anchor.z'
  | `spline.cp.${number}.${'x' | 'y'}`  // Spline control points
  | 'light.intensity' | 'light.range' | 'light.color.r'
  // ... more paths

export type AudioFeatureType =
  | 'amplitude'
  | 'bass'
  | 'mid'
  | 'high'
  | 'beat'
  | 'spectralCentroid';

export interface PropertyDriver {
  id: string;
  name: string;
  sourceType: DriverSourceType;
  sourceLayerId?: string;
  sourceProperty?: PropertyPath;
  audioFeature?: AudioFeatureType;
  targetLayerId: string;
  targetProperty: PropertyPath;
  transform: DriverTransform;
  enabled: boolean;
}

export interface DriverTransform {
  scale: number;        // Multiply source value
  offset: number;       // Add to result
  min: number;          // Clamp minimum
  max: number;          // Clamp maximum
  invert: boolean;      // Flip direction
  smoothing: number;    // Temporal smoothing (0-1)
  curve?: 'linear' | 'exponential' | 'logarithmic';
}

// Main class
export class PropertyDriverSystem {
  constructor(
    propertyGetter: PropertyGetter,
    propertySetter: PropertySetter
  );

  addDriver(driver: PropertyDriver): void;
  removeDriver(id: string): void;
  getDriver(id: string): PropertyDriver | undefined;
  getAllDrivers(): PropertyDriver[];

  // Core evaluation
  evaluate(frame: number, audioAnalysis?: AudioAnalysis): void;

  // Dependency graph
  buildDependencyGraph(): void;
  hasCycle(): boolean;
  getEvaluationOrder(): string[];
}

// Factory functions
export function createPropertyDriver(
  sourceLayerId: string,
  sourceProperty: PropertyPath,
  targetLayerId: string,
  targetProperty: PropertyPath,
  transform?: Partial<DriverTransform>
): PropertyDriver;

export function createAudioDriver(
  audioFeature: AudioFeatureType,
  targetLayerId: string,
  targetProperty: PropertyPath,
  transform?: Partial<DriverTransform>
): PropertyDriver;

export function createPropertyLink(
  sourceLayerId: string,
  sourceProperty: PropertyPath,
  targetLayerId: string,
  targetProperty: PropertyPath
): PropertyDriver;

export function createGearDriver(
  sourceLayerId: string,
  targetLayerId: string,
  ratio?: number  // Default: 1.0
): PropertyDriver;

// Light-specific drivers
export function createAudioLightDriver(
  audioFeature: AudioFeatureType,
  lightLayerId: string
): PropertyDriver;

export function createAudioColorTempDriver(
  lightLayerId: string,
  coldTemp?: number,   // Default: 6500
  warmTemp?: number    // Default: 3200
): PropertyDriver;

export function createLightFollowDriver(
  lightLayerId: string,
  targetLayerId: string
): PropertyDriver;

// Utility
export function getPropertyPathDisplayName(path: PropertyPath): string;
export function getAllPropertyPaths(): PropertyPath[];
export function getLightPropertyPaths(): PropertyPath[];
export function getPropertyPathsForLayerType(layerType: string): PropertyPath[];
export function isSplineControlPointPath(path: string): boolean;
export function isLightPropertyPath(path: string): boolean;
export function parseSplineControlPointPath(path: string): { index: number; axis: 'x' | 'y' } | null;
export function createSplineControlPointPath(index: number, axis: 'x' | 'y'): PropertyPath;
```

---

## 2. Audio Services

### 2.1 audioFeatures.ts

**Purpose**: Audio analysis and feature extraction. Pre-computes all features for deterministic playback.

**Location**: `ui/src/services/audioFeatures.ts`

**Size**: ~36KB | **Lines**: ~1200

#### Exports

```typescript
// Types
export interface AudioAnalysis {
  /** Sample rate of source audio */
  sampleRate: number;
  /** Frames per second for frame indexing */
  fps: number;
  /** Total frame count */
  frameCount: number;
  /** Duration in seconds */
  duration: number;
  /** Per-frame amplitude envelope [0-1] */
  amplitude: Float32Array;
  /** Per-frame RMS energy [0-1] */
  rms: Float32Array;
  /** Per-frame frequency bands */
  frequencyBands: {
    bass: Float32Array;      // 20-250Hz
    lowMid: Float32Array;    // 250-500Hz
    mid: Float32Array;       // 500-2000Hz
    highMid: Float32Array;   // 2000-4000Hz
    high: Float32Array;      // 4000-20000Hz
  };
  /** Spectral centroid per frame */
  spectralCentroid: Float32Array;
  /** Spectral flux per frame */
  spectralFlux: Float32Array;
  /** Zero crossing rate per frame */
  zeroCrossingRate: Float32Array;
  /** Spectral rolloff per frame */
  spectralRolloff: Float32Array;
  /** Spectral flatness per frame */
  spectralFlatness: Float32Array;
  /** Chroma features (12-bin pitch class) */
  chroma?: Float32Array[];
  /** Detected beat frames */
  beats: number[];
  /** Detected BPM */
  bpm: number;
  /** Onset frames */
  onsets: number[];
}

export interface FrequencyBandRanges {
  bass: [number, number];      // Default: [20, 250]
  lowMid: [number, number];    // Default: [250, 500]
  mid: [number, number];       // Default: [500, 2000]
  highMid: [number, number];   // Default: [2000, 4000]
  high: [number, number];      // Default: [4000, 20000]
}

export interface ChromaFeatures {
  frameCount: number;
  chromagram: Float32Array[];  // 12 arrays (one per pitch class)
}

export interface AudioAnalysisConfig {
  fps: number;                    // Default: 30
  fftSize: number;                // Default: 2048
  frequencyBands: FrequencyBandRanges;
  beatDetection: boolean;         // Default: true
  chromaExtraction: boolean;      // Default: false
  onsetDetection: boolean;        // Default: true
}

export interface PeakDetectionConfig {
  threshold: number;              // Minimum peak height (0-1)
  minDistance: number;            // Minimum frames between peaks
}

export interface PeakData {
  frames: number[];
  values: number[];
}

// Core loading functions
export async function loadAudioFile(file: File): Promise<AudioBuffer>;
export async function loadAudioFromUrl(url: string): Promise<AudioBuffer>;

// Main analysis function
export async function analyzeAudio(
  buffer: AudioBuffer,
  config?: Partial<AudioAnalysisConfig>
): Promise<AudioAnalysis>;

// Individual feature extractors
export function extractAmplitudeEnvelope(
  buffer: AudioBuffer,
  fps: number
): number[];

export function extractRMSEnergy(
  buffer: AudioBuffer,
  fps: number
): number[];

export function extractFrequencyBands(
  buffer: AudioBuffer,
  fps: number,
  fftSize?: number,
  ranges?: FrequencyBandRanges
): {
  bass: Float32Array;
  lowMid: Float32Array;
  mid: Float32Array;
  highMid: Float32Array;
  high: Float32Array;
};

export function extractSpectralCentroid(
  buffer: AudioBuffer,
  fps: number,
  fftSize?: number
): Float32Array;

export function detectOnsets(
  buffer: AudioBuffer,
  fps: number,
  threshold?: number,      // Default: 0.1
  fftSize?: number
): number[];

export function extractSpectralFlux(
  buffer: AudioBuffer,
  fps: number
): number[];

export function extractZeroCrossingRate(
  buffer: AudioBuffer,
  fps: number
): number[];

export function extractSpectralRolloff(
  buffer: AudioBuffer,
  fps: number,
  rolloffPercent?: number  // Default: 0.85
): number[];

export function extractSpectralFlatness(
  buffer: AudioBuffer,
  fps: number
): number[];

export function extractChromaFeatures(
  buffer: AudioBuffer,
  fps: number
): ChromaFeatures;

export function detectBPM(buffer: AudioBuffer): number;

// Frame-indexed access
export function getFeatureAtFrame(
  analysis: AudioAnalysis,
  feature: keyof AudioAnalysis | 'bass' | 'mid' | 'high',
  frame: number
): number;

export function getSmoothedFeature(
  analysis: AudioAnalysis,
  feature: string,
  frame: number,
  windowSize?: number    // Default: 3
): number;

// Feature manipulation
export function normalizeFeature(
  values: Float32Array | number[],
  min?: number,          // Default: 0
  max?: number           // Default: 1
): Float32Array;

export function applyFeatureCurve(
  values: Float32Array,
  curve: 'linear' | 'exponential' | 'logarithmic' | 'scurve',
  strength?: number      // Default: 1.0
): Float32Array;

// Peak detection
export function detectPeaks(
  values: Float32Array | number[],
  config?: Partial<PeakDetectionConfig>
): PeakData;

export function generatePeakGraph(
  peaks: PeakData,
  frameCount: number,
  smoothing?: number
): Float32Array;

// Frame queries
export function isBeatAtFrame(analysis: AudioAnalysis, frame: number): boolean;
export function isPeakAtFrame(peaks: PeakData, frame: number): boolean;
```

#### Usage Example

```typescript
import { loadAudioFile, analyzeAudio, getFeatureAtFrame } from '@/services/audioFeatures';

// Load and analyze
const buffer = await loadAudioFile(audioFile);
const analysis = await analyzeAudio(buffer, { fps: 30, chromaExtraction: true });

// Get bass energy at frame 45
const bass = getFeatureAtFrame(analysis, 'bass', 45);

// Check if frame is a beat
const isBeat = isBeatAtFrame(analysis, 45);

console.log(`BPM: ${analysis.bpm}, Beats: ${analysis.beats.length}`);
```

---

### 2.2 audioReactiveMapping.ts

**Purpose**: Maps audio features to animation parameters with customizable transforms.

**Location**: `ui/src/services/audioReactiveMapping.ts`

**Size**: ~22KB

#### Exports

```typescript
// Types
export type AudioFeature =
  | 'amplitude'
  | 'rms'
  | 'bass'
  | 'lowMid'
  | 'mid'
  | 'highMid'
  | 'high'
  | 'spectralCentroid'
  | 'spectralFlux'
  | 'zeroCrossingRate'
  | 'beat'
  | 'onset';

export type TargetParameter =
  | 'position.x' | 'position.y' | 'position.z'
  | 'rotation.x' | 'rotation.y' | 'rotation.z'
  | 'scale.x' | 'scale.y' | 'scale'
  | 'opacity'
  | 'blur'
  | 'brightness'
  | 'hue'
  | 'saturation';

export interface AudioMapping {
  id: string;
  name: string;
  enabled: boolean;
  feature: AudioFeature;
  target: TargetParameter;
  layerId: string;

  // Transform settings
  sensitivity: number;      // Multiplier (default: 1.0)
  offset: number;           // Added to result (default: 0)
  min: number;              // Clamp minimum
  max: number;              // Clamp maximum
  smoothing: number;        // Temporal smoothing 0-1
  invert: boolean;          // Flip direction

  // Advanced
  curve: 'linear' | 'exponential' | 'logarithmic' | 'scurve';
  threshold: number;        // Minimum feature value to trigger
  attack: number;           // Rise time in frames
  decay: number;            // Fall time in frames
}

export interface IPAdapterTransition {
  fromStyle: string;
  toStyle: string;
  startFrame: number;
  endFrame: number;
  easing: string;
}

export interface WeightSchedule {
  frameCount: number;
  weights: Float32Array[];  // Per-style weights
  styles: string[];
}

// Main class
export class AudioReactiveMapper {
  constructor();

  addMapping(mapping: AudioMapping): void;
  removeMapping(id: string): void;
  updateMapping(id: string, updates: Partial<AudioMapping>): void;
  getMapping(id: string): AudioMapping | undefined;
  getAllMappings(): AudioMapping[];
  getMappingsForLayer(layerId: string): AudioMapping[];

  // Core evaluation
  evaluate(
    analysis: AudioAnalysis,
    frame: number
  ): Map<string, Map<TargetParameter, number>>;  // layerId -> param -> value

  // Get single value
  evaluateMapping(
    mapping: AudioMapping,
    analysis: AudioAnalysis,
    frame: number
  ): number;
}

// Factory functions
export function createDefaultAudioMapping(
  feature: AudioFeature,
  target: TargetParameter,
  layerId: string
): AudioMapping;

// IP-Adapter integration (style transitions)
export function createIPAdapterSchedule(
  transitions: IPAdapterTransition[],
  frameCount: number
): WeightSchedule;

export function getIPAdapterWeightsAtFrame(
  schedule: WeightSchedule,
  frame: number
): Map<string, number>;

// Feature/target metadata
export function getFeatureDisplayName(feature: AudioFeature): string;
export function getTargetDisplayName(target: TargetParameter): string;
export function getAllFeatures(): AudioFeature[];
export function getFeaturesByCategory(): Record<string, AudioFeature[]>;
export function getAllTargets(): TargetParameter[];
export function getTargetsByCategory(): Record<string, TargetParameter[]>;

// Spline control point targets
export function createSplineControlPointTargets(
  controlPointCount: number
): TargetParameter[];
```

---

### 2.3 audioPathAnimator.ts

**Purpose**: Animates objects along paths based on audio features.

**Location**: `ui/src/services/audioPathAnimator.ts`

**Size**: ~15KB

#### Exports

```typescript
export type MovementMode = 'amplitude' | 'accumulate';

export interface PathAnimatorConfig {
  pathLayerId: string;           // SplineLayer to follow
  sensitivity: number;           // Speed multiplier
  smoothing: number;             // Position smoothing
  mode: MovementMode;            // amplitude: oscillate, accumulate: progress
  audioFeature: AudioFeature;    // Which feature drives movement
  loop: boolean;                 // Loop at path end
  pingPong: boolean;             // Reverse at ends
  startOffset: number;           // Initial position on path (0-1)
}

export interface PathAnimatorState {
  currentT: number;              // Position on path (0-1)
  velocity: number;              // Current velocity
  direction: 1 | -1;             // Current direction (for pingPong)
  totalDistance: number;         // Total distance traveled
}

export class AudioPathAnimator {
  constructor(config: PathAnimatorConfig);

  setConfig(config: Partial<PathAnimatorConfig>): void;
  getConfig(): PathAnimatorConfig;
  reset(): void;

  // Core update
  update(
    analysis: AudioAnalysis,
    frame: number,
    pathLength: number
  ): PathAnimatorState;

  // Get position at frame
  getPositionAtFrame(
    analysis: AudioAnalysis,
    frame: number,
    path: Bezier[]
  ): { x: number; y: number; angle: number };
}

export function createDefaultPathAnimatorConfig(): PathAnimatorConfig;
```

---

### 2.4 audioWorkerClient.ts

**Purpose**: Web Worker client for background audio analysis.

**Location**: `ui/src/services/audioWorkerClient.ts`

**Size**: ~5KB

#### Exports

```typescript
export interface AudioAnalysisProgress {
  stage: string;
  progress: number;  // 0-1
  message?: string;
}

export interface AnalyzeOptions {
  fps?: number;
  onProgress?: (progress: AudioAnalysisProgress) => void;
}

// Analyze in worker thread
export async function analyzeAudioInWorker(
  buffer: AudioBuffer,
  options?: AnalyzeOptions
): Promise<AudioAnalysis>;

export function terminateWorker(): void;
export function cancelAnalysis(): void;
```

---

## 3. Camera & 3D Services

### 3.1 math3d.ts

**Purpose**: 3D math utilities (vectors, matrices, quaternions).

**Location**: `ui/src/services/math3d.ts`

**Size**: ~18KB

#### Exports

```typescript
// Types
export type Vec3 = [number, number, number];
export type Mat4 = [
  number, number, number, number,
  number, number, number, number,
  number, number, number, number,
  number, number, number, number
];
export type Quat = [number, number, number, number];  // x, y, z, w

// Vector operations
export function vec3(x: number, y: number, z: number): Vec3;
export function addVec3(a: Vec3, b: Vec3): Vec3;
export function subVec3(a: Vec3, b: Vec3): Vec3;
export function scaleVec3(v: Vec3, s: number): Vec3;
export function lengthVec3(v: Vec3): number;
export function normalizeVec3(v: Vec3): Vec3;
export function crossVec3(a: Vec3, b: Vec3): Vec3;
export function dotVec3(a: Vec3, b: Vec3): number;
export function lerpVec3(a: Vec3, b: Vec3, t: number): Vec3;
export function distanceVec3(a: Vec3, b: Vec3): number;

// Matrix operations
export function identityMat4(): Mat4;
export function multiplyMat4(a: Mat4, b: Mat4): Mat4;
export function perspectiveMat4(
  fovY: number,      // Field of view in radians
  aspect: number,    // Aspect ratio
  near: number,      // Near plane
  far: number        // Far plane
): Mat4;
export function orthographicMat4(
  left: number, right: number,
  bottom: number, top: number,
  near: number, far: number
): Mat4;
export function lookAtMat4(
  eye: Vec3,         // Camera position
  target: Vec3,      // Look-at point
  up: Vec3           // Up vector
): Mat4;
export function translateMat4(m: Mat4, v: Vec3): Mat4;
export function rotateXMat4(m: Mat4, angle: number): Mat4;
export function rotateYMat4(m: Mat4, angle: number): Mat4;
export function rotateZMat4(m: Mat4, angle: number): Mat4;
export function scaleMat4(m: Mat4, s: Vec3): Mat4;
export function transformPoint(m: Mat4, p: Vec3): Vec3;
export function transformDirection(m: Mat4, d: Vec3): Vec3;
export function invertMat4(m: Mat4): Mat4 | null;

// Quaternion operations
export function quatIdentity(): Quat;
export function quatFromEuler(x: number, y: number, z: number): Quat;
export function quatToEuler(q: Quat): Vec3;
export function slerpQuat(a: Quat, b: Quat, t: number): Quat;

// Utility conversions
export function focalLengthToFOV(focalLength: number, sensorWidth?: number): number;
export function fovToFocalLength(fov: number, sensorWidth?: number): number;
export function zoomToFocalLength(zoom: number, baseFocalLength?: number): number;
export function focalLengthToZoom(focalLength: number, baseFocalLength?: number): number;
export function degToRad(degrees: number): number;
export function radToDeg(radians: number): number;
```

---

### 3.2 cameraTrajectory.ts

**Purpose**: Camera trajectory presets and path generation.

**Location**: `ui/src/services/cameraTrajectory.ts`

**Size**: ~20KB

#### Exports

```typescript
export interface SphericalCoords {
  radius: number;       // Distance from target
  theta: number;        // Horizontal angle (azimuth)
  phi: number;          // Vertical angle (elevation)
  target: Vec3;         // Look-at target
}

export type TrajectoryType =
  // Orbital
  | 'orbit-horizontal'
  | 'orbit-vertical'
  | 'orbit-diagonal'
  | 'orbit-spiral'
  | 'orbit-figure8'
  // Linear
  | 'dolly-in'
  | 'dolly-out'
  | 'truck-left'
  | 'truck-right'
  | 'pedestal-up'
  | 'pedestal-down'
  | 'push-pull'
  // Complex
  | 'crane-up'
  | 'crane-down'
  | 'arc-left'
  | 'arc-right'
  | 'reveal'
  | 'flythrough'
  | 'zoom-crash'
  | 'parallax-shift'
  | 'dutch-tilt'
  | 'vertigo';

export interface TrajectoryConfig {
  type: TrajectoryType;
  duration: number;           // In frames
  easing: string;             // Easing function name
  intensity: number;          // Movement amount (0-2)
  startPosition: SphericalCoords;
  endPosition?: SphericalCoords;  // Auto-calculated if not set
  loops: number;              // For orbital moves
  reverse: boolean;           // Play backwards
}

export interface TrajectoryKeyframes {
  position: Array<{ frame: number; value: Vec3 }>;
  rotation: Array<{ frame: number; value: Vec3 }>;
  fov?: Array<{ frame: number; value: number }>;
}

// Default values
export const DEFAULT_SPHERICAL: SphericalCoords;
export const DEFAULT_TRAJECTORY: TrajectoryConfig;

// Presets for each trajectory type
export const TRAJECTORY_PRESETS: Record<TrajectoryType, Partial<TrajectoryConfig>>;

// Coordinate conversions
export function sphericalToCartesian(
  coords: SphericalCoords
): Vec3;

export function cartesianToSpherical(
  position: Vec3,
  target?: Vec3
): SphericalCoords;

// Get position at normalized time (0-1)
export function getTrajectoryPosition(
  config: TrajectoryConfig,
  t: number
): SphericalCoords;

// Generate keyframes for full trajectory
export function generateTrajectoryKeyframes(
  config: TrajectoryConfig,
  keyframeInterval?: number  // Default: 5 frames
): TrajectoryKeyframes;

// Apply to existing camera layer
export function applyCameraTrajectory(
  cameraLayerId: string,
  config: TrajectoryConfig,
  startFrame?: number
): void;

// Create from preset with overrides
export function createTrajectoryFromPreset(
  type: TrajectoryType,
  overrides?: Partial<TrajectoryConfig>
): TrajectoryConfig;

// Metadata
export function getTrajectoryDescription(type: TrajectoryType): string;
export function getTrajectoryCategory(type: TrajectoryType): string;
export function getTrajectoryTypesByCategory(): Record<string, TrajectoryType[]>;
```

#### Trajectory Categories

```
{
  "Orbital": ["orbit-horizontal", "orbit-vertical", "orbit-diagonal", "orbit-spiral", "orbit-figure8"],
  "Linear": ["dolly-in", "dolly-out", "truck-left", "truck-right", "pedestal-up", "pedestal-down", "push-pull"],
  "Complex": ["crane-up", "crane-down", "arc-left", "arc-right", "reveal", "flythrough", "zoom-crash", "parallax-shift", "dutch-tilt", "vertigo"]
}
```

---

### 3.3 camera3DVisualization.ts

**Purpose**: Generate 3D visualization geometry for camera frustum and helpers.

**Location**: `ui/src/services/camera3DVisualization.ts`

**Size**: ~15KB

#### Exports

```typescript
export interface LineSegment {
  start: Vec3;
  end: Vec3;
  color?: string;
}

export interface CameraVisualization {
  body: LineSegment[];          // Camera body wireframe
  frustum: LineSegment[];       // View frustum
  poi: LineSegment | null;      // Point of interest line
  focalPlane: LineSegment[];    // DOF focal plane
}

export interface ViewMatrices {
  view: Mat4;
  projection: Mat4;
  viewProjection: Mat4;
}

// Generate camera body wireframe
export function generateCameraBody(camera: Camera3D): LineSegment[];

// Generate frustum visualization
export function generateFrustum(
  camera: Camera3D,
  near?: number,
  far?: number,
  aspectRatio?: number
): LineSegment[];

// Generate composition bounds rectangle
export function generateCompositionBounds(
  width: number,
  height: number,
  depth: number
): LineSegment[];

// Point of interest line
export function generatePOILine(camera: Camera3D): LineSegment | null;

// DOF focal plane visualization
export function generateFocalPlane(
  camera: Camera3D,
  width: number,
  height: number
): LineSegment[];

// All visualizations combined
export function generateCameraVisualization(
  camera: Camera3D,
  compositionWidth: number,
  compositionHeight: number
): CameraVisualization;

// Get view/projection matrices for rendering
export function getCameraViewMatrices(
  camera: Camera3D,
  aspectRatio: number
): ViewMatrices;

// Orthographic view matrices (for 2D editor views)
export function getOrthoViewMatrices(
  view: 'front' | 'back' | 'left' | 'right' | 'top' | 'bottom',
  bounds: { left: number; right: number; top: number; bottom: number },
  zoom: number
): ViewMatrices;

// Project 3D point to screen coordinates
export function projectToScreen(
  point: Vec3,
  matrices: ViewMatrices,
  screenWidth: number,
  screenHeight: number
): { x: number; y: number; visible: boolean };

// Generate coordinate axes
export function generate3DAxes(
  length?: number,      // Default: 100
  origin?: Vec3         // Default: [0,0,0]
): LineSegment[];

// Generate ground grid
export function generateGrid(
  size?: number,        // Default: 1000
  divisions?: number,   // Default: 10
  y?: number            // Default: 0
): LineSegment[];
```

---

### 3.4 cameraExport.ts

**Purpose**: Export camera data for external tools (AE, ComfyUI, etc.)

**Location**: `ui/src/services/cameraExport.ts`

**Size**: ~12KB

#### Exports

```typescript
export interface Uni3CTrack {
  name: string;
  frames: Uni3CFrame[];
  fps: number;
  width: number;
  height: number;
}

export interface Uni3CFrame {
  frame: number;
  position: Vec3;
  rotation: Vec3;        // Euler XYZ in degrees
  fov: number;
  near: number;
  far: number;
}

// Export to Uni3C JSON format (ComfyUI compatible)
export function exportToUni3C(
  camera: Camera3D,
  keyframes: CameraKeyframe[],
  compositionSettings: CompositionSettings
): Uni3CTrack;

// Generic JSON export
export function exportCameraJSON(
  camera: Camera3D,
  keyframes: CameraKeyframe[]
): string;

// Import from JSON
export function importCameraJSON(
  json: string
): { camera: Camera3D; keyframes: CameraKeyframe[] } | null;

// Export to After Effects script
export function exportToAEScript(
  camera: Camera3D,
  keyframes: CameraKeyframe[],
  compositionSettings: CompositionSettings
): string;

// Download helper
export function downloadFile(
  content: string,
  filename: string,
  mimeType?: string     // Default: 'application/json'
): void;
```

---

### 3.5 cameraEnhancements.ts

**Purpose**: Camera effects (shake, rack focus, auto-focus).

**Location**: `ui/src/services/cameraEnhancements.ts`

**Size**: ~20KB

#### Exports

```typescript
export interface CameraShakeConfig {
  type: 'handheld' | 'earthquake' | 'explosion' | 'vehicle' | 'breathing';
  intensity: number;          // 0-1
  frequency: number;          // Oscillations per second
  decay: number;              // How fast it dampens (0-1)
  seed: number;               // For determinism
  enabled: boolean;
  affectsRotation: boolean;
  affectsPosition: boolean;
}

export interface RackFocusConfig {
  enabled: boolean;
  startDistance: number;      // Focus distance at start
  endDistance: number;        // Focus distance at end
  startFrame: number;
  endFrame: number;
  easing: string;
  holdAtStart: number;        // Frames to hold at start
  holdAtEnd: number;          // Frames to hold at end
}

export interface AutoFocusConfig {
  enabled: boolean;
  targetLayerId: string | null;  // Track this layer
  depthSource: 'layer' | 'manual' | 'click';
  smoothing: number;          // Focus transition smoothing
  offset: number;             // Focus offset from target
}

export interface MotionBlurEstimate {
  shutterAngle: number;       // Degrees
  samples: number;            // Blur samples needed
  velocity: Vec3;             // Camera velocity
}

// Preset configurations
export const SHAKE_PRESETS: Record<CameraShakeConfig['type'], Partial<CameraShakeConfig>>;
export const DEFAULT_SHAKE_CONFIG: CameraShakeConfig;
export const DEFAULT_RACK_FOCUS: RackFocusConfig;
export const DEFAULT_AUTOFOCUS: AutoFocusConfig;

// Camera shake class
export class CameraShake {
  constructor(config?: Partial<CameraShakeConfig>);

  setConfig(config: Partial<CameraShakeConfig>): void;
  getConfig(): CameraShakeConfig;
  reset(): void;

  // Get shake offset at frame
  evaluate(frame: number, fps: number): {
    position: Vec3;
    rotation: Vec3;
  };

  // Apply shake to camera
  applyToCamera(
    camera: Camera3D,
    frame: number,
    fps: number
  ): Camera3D;
}

// Rack focus evaluation
export function getRackFocusDistance(
  config: RackFocusConfig,
  frame: number
): number;

// Generate rack focus keyframes
export function generateRackFocusKeyframes(
  config: RackFocusConfig
): Array<{ frame: number; value: number }>;

// Auto-focus calculation
export function calculateAutoFocusDistance(
  config: AutoFocusConfig,
  targetPosition: Vec3,
  cameraPosition: Vec3,
  previousDistance: number
): number;

// Motion blur estimation
export function estimateMotionBlur(
  camera: Camera3D,
  previousCamera: Camera3D,
  fps: number,
  shutterAngle?: number
): MotionBlurEstimate;

// Generate motion blur keyframes
export function generateMotionBlurKeyframes(
  cameras: Camera3D[],
  fps: number
): Array<{ frame: number; blur: number }>;

// Factory functions
export function createCameraShake(
  type: CameraShakeConfig['type'],
  intensity?: number
): CameraShake;

export function createRackFocus(
  startDistance: number,
  endDistance: number,
  startFrame: number,
  endFrame: number
): RackFocusConfig;

export function createAutoFocus(
  targetLayerId: string
): AutoFocusConfig;
```

---

## 4. Particle Services

### 4.1 particleSystem.ts

**Purpose**: Deterministic particle simulation with seeded RNG.

**Location**: `ui/src/services/particleSystem.ts`

**Size**: ~65KB | **Lines**: ~2400

#### Exports

```typescript
// Reset ID counter (for determinism)
export function resetIdCounter(value?: number): void;

// Seeded random number generator (Mulberry32)
export class SeededRandom {
  constructor(seed: number);
  next(): number;                    // 0-1
  nextRange(min: number, max: number): number;
  nextInt(min: number, max: number): number;
  nextBool(probability?: number): boolean;
  nextVec2(range: number): { x: number; y: number };
  nextVec3(range: number): { x: number; y: number; z: number };
  nextColor(): { r: number; g: number; b: number; a: number };
  getSeed(): number;
  setSeed(seed: number): void;
}

// Particle structure
export interface Particle {
  id: number;
  position: Vec3;
  velocity: Vec3;
  acceleration: Vec3;
  age: number;                       // Current age in frames
  lifetime: number;                  // Max lifetime in frames
  size: number;
  sizeStart: number;
  sizeEnd: number;
  color: { r: number; g: number; b: number; a: number };
  colorStart: { r: number; g: number; b: number; a: number };
  colorEnd: { r: number; g: number; b: number; a: number };
  rotation: number;
  rotationSpeed: number;
  mass: number;
  alive: boolean;
  emitterId: string;
  spriteIndex: number;
  custom: Record<string, number>;    // Custom data
}

// Emitter shape types
export type EmitterShape = 'point' | 'line' | 'circle' | 'box' | 'sphere' | 'ring' | 'spline';

// Spline emission configuration
export interface SplinePathEmission {
  layerId: string;                   // SplineLayer to emit from
  distribution: 'uniform' | 'random' | 'sequential';
  alignToPath: boolean;
  spreadAngle: number;
}

// Sprite configuration
export interface SpriteConfig {
  enabled: boolean;
  textureUrl: string;
  columns: number;
  rows: number;
  startFrame: number;
  endFrame: number;
  animationMode: 'loop' | 'once' | 'pingPong' | 'random';
  frameRate: number;
}

// Full emitter configuration
export interface EmitterConfig {
  id: string;
  name: string;
  enabled: boolean;

  // Emission
  emissionRate: number;              // Particles per frame
  burstCount: number;                // Particles per burst
  burstInterval: number;             // Frames between bursts
  maxParticles: number;

  // Shape
  shape: EmitterShape;
  shapeRadius: number;
  shapeWidth: number;
  shapeHeight: number;
  shapeDepth: number;
  splinePath?: SplinePathEmission;

  // Initial values
  lifetime: { min: number; max: number };
  speed: { min: number; max: number };
  direction: Vec3;
  spread: number;                    // Cone angle in degrees

  // Size
  sizeStart: { min: number; max: number };
  sizeEnd: { min: number; max: number };

  // Color
  colorStart: { r: number; g: number; b: number; a: number };
  colorEnd: { r: number; g: number; b: number; a: number };

  // Rotation
  rotationStart: { min: number; max: number };
  rotationSpeed: { min: number; max: number };

  // Physics
  mass: { min: number; max: number };

  // Sprite
  sprite: SpriteConfig;
}

// Force configurations
export interface GravityWellConfig {
  id: string;
  enabled: boolean;
  position: Vec3;
  strength: number;
  radius: number;
  falloff: 'linear' | 'quadratic' | 'none';
}

export interface VortexConfig {
  id: string;
  enabled: boolean;
  position: Vec3;
  axis: Vec3;
  strength: number;
  radius: number;
  pull: number;                      // Inward force
}

export interface TurbulenceConfig {
  id: string;
  enabled: boolean;
  strength: number;
  scale: number;                     // Noise frequency
  speed: number;                     // Animation speed
  octaves: number;
}

// Collision configuration
export interface CollisionConfig {
  enabled: boolean;
  bounce: number;                    // 0-1 elasticity
  friction: number;
  killOnCollision: boolean;
  planes: Array<{ normal: Vec3; distance: number }>;
  spheres: Array<{ center: Vec3; radius: number }>;
}

// Sub-emitter configuration
export interface SubEmitterConfig {
  id: string;
  enabled: boolean;
  trigger: 'birth' | 'death' | 'collision' | 'lifetime';
  lifetimeThreshold?: number;        // For 'lifetime' trigger
  emitterConfig: EmitterConfig;
  inheritVelocity: number;           // 0-1
  inheritColor: boolean;
}

// Connection configuration (particle trails/lines)
export interface ConnectionConfig {
  enabled: boolean;
  maxDistance: number;
  maxConnections: number;
  lineWidth: number;
  opacity: number;
}

// Full system configuration
export interface ParticleSystemConfig {
  seed: number;
  gravity: Vec3;
  wind: Vec3;
  damping: number;
  worldScale: number;
  bounds?: { min: Vec3; max: Vec3 };
  killOutOfBounds: boolean;
}

// Render options
export interface RenderOptions {
  mode: 'points' | 'sprites' | 'trails' | 'mesh';
  blendMode: string;
  depthTest: boolean;
  depthWrite: boolean;
  sortByDepth: boolean;
  trailLength: number;
  trailWidth: number;
  meshGeometry?: 'quad' | 'triangle' | 'custom';
}

// Default creators
export function createDefaultSpriteConfig(): SpriteConfig;
export function createDefaultSplinePathEmission(layerId?: string): SplinePathEmission;
export function createDefaultCollisionConfig(): CollisionConfig;
export function createDefaultEmitterConfig(id?: string): EmitterConfig;
export function createDefaultTurbulenceConfig(id?: string): TurbulenceConfig;
export function createDefaultConnectionConfig(): ConnectionConfig;
export function createDefaultSubEmitterConfig(id?: string): SubEmitterConfig;
export function createDefaultGravityWellConfig(id?: string): GravityWellConfig;
export function createDefaultVortexConfig(id?: string): VortexConfig;
export function createDefaultSystemConfig(): ParticleSystemConfig;
export function createDefaultRenderOptions(): RenderOptions;

// Main particle system class
export class ParticleSystem {
  constructor(config?: Partial<ParticleSystemConfig>);

  // Configuration
  setConfig(config: Partial<ParticleSystemConfig>): void;
  getConfig(): ParticleSystemConfig;

  // Emitter management
  addEmitter(config: EmitterConfig): void;
  removeEmitter(id: string): void;
  updateEmitter(id: string, config: Partial<EmitterConfig>): void;
  getEmitter(id: string): EmitterConfig | undefined;
  getAllEmitters(): EmitterConfig[];

  // Force management
  addGravityWell(config: GravityWellConfig): void;
  removeGravityWell(id: string): void;
  addVortex(config: VortexConfig): void;
  removeVortex(id: string): void;
  addTurbulence(config: TurbulenceConfig): void;
  removeTurbulence(id: string): void;

  // Collision
  setCollision(config: CollisionConfig): void;

  // Sub-emitters
  addSubEmitter(config: SubEmitterConfig): void;
  removeSubEmitter(id: string): void;

  // Simulation - DETERMINISTIC
  reset(): void;
  evaluate(frame: number): Particle[];
  evaluateRange(startFrame: number, endFrame: number): Map<number, Particle[]>;

  // Checkpoint system (for scrubbing)
  saveCheckpoint(frame: number): void;
  loadCheckpoint(frame: number): boolean;
  getNearestCheckpoint(frame: number): number | null;

  // Particle access
  getParticles(): Particle[];
  getParticleCount(): number;
  getAliveCount(): number;

  // Statistics
  getStats(): {
    totalEmitted: number;
    totalDied: number;
    currentAlive: number;
    checkpoints: number;
  };
}
```

---

### 4.2 gpuParticleRenderer.ts

**Purpose**: GPU-accelerated particle rendering using Transform Feedback or instancing.

**Location**: `ui/src/services/gpuParticleRenderer.ts`

**Size**: ~20KB

#### Exports

```typescript
export interface GPUParticleRendererConfig {
  maxParticles: number;
  useTransformFeedback: boolean;
  sortParticles: boolean;
  enableBlending: boolean;
}

export interface GPUParticleData {
  positions: Float32Array;      // xyz per particle
  velocities: Float32Array;     // xyz per particle
  colors: Float32Array;         // rgba per particle
  sizes: Float32Array;          // size per particle
  ages: Float32Array;           // age per particle
  count: number;
}

// Transform Feedback based renderer
export class GPUParticleRenderer {
  constructor(
    gl: WebGL2RenderingContext,
    config?: Partial<GPUParticleRendererConfig>
  );

  setConfig(config: Partial<GPUParticleRendererConfig>): void;
  uploadParticles(particles: Particle[]): void;
  render(viewMatrix: Mat4, projectionMatrix: Mat4): void;
  dispose(): void;

  getStats(): {
    particleCount: number;
    drawCalls: number;
    gpuMemory: number;
  };
}

// Instanced mesh based renderer
export class InstancedParticleRenderer {
  constructor(
    gl: WebGL2RenderingContext,
    config?: Partial<GPUParticleRendererConfig>
  );

  setGeometry(geometry: 'quad' | 'triangle' | 'sphere'): void;
  setTexture(texture: WebGLTexture): void;
  uploadParticles(particles: Particle[]): void;
  render(viewMatrix: Mat4, projectionMatrix: Mat4): void;
  dispose(): void;
}

// Factory functions
export function createGPUParticleRenderer(
  gl: WebGL2RenderingContext,
  config?: Partial<GPUParticleRendererConfig>
): GPUParticleRenderer;

export function createInstancedParticleRenderer(
  gl: WebGL2RenderingContext,
  config?: Partial<GPUParticleRendererConfig>
): InstancedParticleRenderer;
```

---

### 4.3 meshParticleManager.ts

**Purpose**: Custom mesh particles (logo particles, 3D shapes).

**Location**: `ui/src/services/meshParticleManager.ts`

**Size**: ~12KB

#### Exports

```typescript
export type MeshParticleSource = 'primitive' | 'svg' | 'gltf' | 'custom';

export interface MeshParticleConfig {
  source: MeshParticleSource;
  primitiveType?: 'cube' | 'sphere' | 'tetrahedron' | 'torus';
  svgUrl?: string;
  gltfUrl?: string;
  customGeometry?: THREE.BufferGeometry;
  scale: number;
  randomRotation: boolean;
  lodLevels?: number;
}

export interface RegisteredMeshParticle {
  id: string;
  name: string;
  config: MeshParticleConfig;
  geometry: THREE.BufferGeometry;
  material: THREE.Material;
}

export interface InstancedMeshParticles {
  mesh: THREE.InstancedMesh;
  capacity: number;
  activeCount: number;
}

export class MeshParticleManager {
  constructor(scene: THREE.Scene);

  // Registration
  registerMesh(
    id: string,
    name: string,
    config: MeshParticleConfig
  ): Promise<void>;

  unregisterMesh(id: string): void;
  getMesh(id: string): RegisteredMeshParticle | undefined;
  getAllMeshes(): RegisteredMeshParticle[];

  // Instance pool
  createInstancePool(
    meshId: string,
    maxInstances: number
  ): InstancedMeshParticles;

  updateInstances(
    pool: InstancedMeshParticles,
    particles: Particle[]
  ): void;

  disposePool(pool: InstancedMeshParticles): void;
  dispose(): void;
}

// Singleton
export const meshParticleManager: MeshParticleManager;

export function createDefaultMeshParticleConfig(): MeshParticleConfig;
```

---

### 4.4 spriteSheet.ts

**Purpose**: Sprite sheet loading and animation for particle textures.

**Location**: `ui/src/services/spriteSheet.ts`

**Size**: ~15KB

#### Exports

```typescript
export interface SpriteFrame {
  x: number;                    // Pixel X in sheet
  y: number;                    // Pixel Y in sheet
  width: number;
  height: number;
  u0: number;                   // UV coordinates
  v0: number;
  u1: number;
  v1: number;
}

export interface SpriteAnimation {
  name: string;
  frames: number[];             // Frame indices
  fps: number;
  loop: boolean;
}

export interface SpriteSheetConfig {
  url: string;
  columns: number;
  rows: number;
  frameWidth?: number;          // Auto-calculated if not set
  frameHeight?: number;
  padding?: number;
  animations?: SpriteAnimation[];
}

export interface SpriteSheetMetadata {
  width: number;
  height: number;
  frameCount: number;
  frames: SpriteFrame[];
  animations: Map<string, SpriteAnimation>;
}

export interface ParticleSpriteConfig {
  spriteSheetId: string;
  animation: string;
  startFrame: 'random' | 'first' | number;
  playOnce: boolean;
  randomOffset: boolean;
}

export class SpriteSheetService {
  constructor();

  // Loading
  loadSpriteSheet(
    id: string,
    config: SpriteSheetConfig
  ): Promise<void>;

  loadFromJSON(
    id: string,
    url: string
  ): Promise<void>;

  unload(id: string): void;

  // Access
  getSpriteSheet(id: string): SpriteSheetMetadata | undefined;
  getTexture(id: string): THREE.Texture | undefined;
  getAllIds(): string[];

  // Frame lookup
  getFrame(id: string, frameIndex: number): SpriteFrame | undefined;
  getAnimationFrame(
    id: string,
    animationName: string,
    time: number,
    fps: number
  ): SpriteFrame | undefined;

  // UV generation for instanced rendering
  generateUVBuffer(
    id: string,
    frameIndices: number[]
  ): Float32Array;

  dispose(): void;
}

// Singleton
export const spriteSheetService: SpriteSheetService;

export function createDefaultParticleSpriteConfig(): ParticleSpriteConfig;
```

---

## 5. Shape & Geometry Services

### 5.1 arcLength.ts

**Purpose**: Arc-length parameterization for even spacing along curves.

**Location**: `ui/src/services/arcLength.ts`

**Size**: ~8KB

#### Exports

```typescript
// Main parameterizer class
export class ArcLengthParameterizer {
  constructor(curve: Bezier, samples?: number);  // Default: 100 samples

  // Get total curve length
  getTotalLength(): number;

  // Get t parameter for given arc length distance
  getTAtLength(length: number): number;

  // Get point at arc length distance
  getPointAtLength(length: number): { x: number; y: number };

  // Get tangent at arc length distance
  getTangentAtLength(length: number): { x: number; y: number };

  // Get normal at arc length distance
  getNormalAtLength(length: number): { x: number; y: number };

  // Resample curve at even intervals
  resample(count: number): Array<{ x: number; y: number }>;
}

// Convert SVG path commands to Bezier
export function pathCommandsToBezier(
  pathCommands: Array<{
    type: string;
    x?: number;
    y?: number;
    x1?: number;
    y1?: number;
    x2?: number;
    y2?: number;
  }>
): Bezier | null;

// Convert control points to Bezier curves
export function controlPointsToBeziers(
  controlPoints: Array<{
    x: number;
    y: number;
    handleIn?: { x: number; y: number };
    handleOut?: { x: number; y: number };
  }>
): Bezier[];

// Multi-segment parameterizer (for paths with multiple curves)
export class MultiSegmentParameterizer {
  constructor(curves: Bezier[]);

  getTotalLength(): number;
  getPointAtLength(length: number): { x: number; y: number };
  getTangentAtLength(length: number): { x: number; y: number };
  resample(count: number): Array<{ x: number; y: number }>;
}
```

---

### 5.2 textOnPath.ts

**Purpose**: Position text characters along a path with proper spacing.

**Location**: `ui/src/services/textOnPath.ts`

**Size**: ~12KB

#### Exports

```typescript
export interface TextOnPathConfig {
  text: string;
  fontSize: number;
  fontFamily: string;
  letterSpacing: number;        // Additional spacing
  startOffset: number;          // Start position on path (0-1)
  alignment: 'left' | 'center' | 'right';
  baselineShift: number;        // Perpendicular offset
  flip: boolean;                // Flip text direction
}

export interface PathPoint {
  x: number;
  y: number;
  angle: number;                // Tangent angle in radians
  t: number;                    // Original t parameter
}

export interface CharacterPlacement {
  char: string;
  x: number;
  y: number;
  angle: number;
  width: number;
}

export class TextOnPathService {
  constructor();

  // Set the path to place text on
  setPath(curves: Bezier[]): void;

  // Calculate character placements
  placeText(config: TextOnPathConfig): CharacterPlacement[];

  // Get path point at distance
  getPointAtDistance(distance: number): PathPoint;

  // Get total path length
  getPathLength(): number;
}

// Factory
export function createTextOnPathService(): TextOnPathService;

// Default configuration
export function createDefaultPathConfig(): TextOnPathConfig;
```

---

### 5.3 shapeOperations.ts

**Purpose**: Bezier path manipulation (offset, wiggle, boolean ops, etc.)

**Location**: `ui/src/services/shapeOperations.ts`

**Size**: ~45KB | **Lines**: ~1550

#### Exports

```typescript
// Point operations
export function distance(a: Point2D, b: Point2D): number;
export function lerpPoint(a: Point2D, b: Point2D, t: number): Point2D;
export function addPoints(a: Point2D, b: Point2D): Point2D;
export function subtractPoints(a: Point2D, b: Point2D): Point2D;
export function scalePoint(p: Point2D, s: number): Point2D;
export function normalize(p: Point2D): Point2D;
export function perpendicular(p: Point2D): Point2D;
export function dot(a: Point2D, b: Point2D): number;
export function cross(a: Point2D, b: Point2D): number;
export function rotatePoint(p: Point2D, angle: number): Point2D;
export function rotateAround(p: Point2D, center: Point2D, angle: number): Point2D;

// Clone functions
export function clonePoint(p: Point2D): Point2D;
export function cloneVertex(v: BezierVertex): BezierVertex;
export function clonePath(path: BezierPath): BezierPath;

// Bezier operations
export function cubicBezierPoint(
  t: number,
  p0: Point2D,
  p1: Point2D,
  p2: Point2D,
  p3: Point2D
): Point2D;

export function cubicBezierDerivative(
  t: number,
  p0: Point2D,
  p1: Point2D,
  p2: Point2D,
  p3: Point2D
): Point2D;

export function splitCubicBezier(
  t: number,
  p0: Point2D,
  p1: Point2D,
  p2: Point2D,
  p3: Point2D
): [Point2D[], Point2D[]];

export function cubicBezierLength(
  p0: Point2D,
  p1: Point2D,
  p2: Point2D,
  p3: Point2D,
  samples?: number
): number;

// Path operations
export function getPathLength(path: BezierPath): number;

export function getPointAtDistance(
  path: BezierPath,
  distance: number
): { point: Point2D; tangent: Point2D; t: number };

export function trimPath(
  path: BezierPath,
  start: number,    // 0-1
  end: number       // 0-1
): BezierPath;

export function mergePaths(
  paths: BezierPath[],
  mode: 'union' | 'intersect' | 'subtract' | 'xor'
): BezierPath[];

// Path modifiers
export function offsetPath(
  path: BezierPath,
  offset: number,
  joinType?: 'miter' | 'round' | 'bevel'
): BezierPath;

export function offsetPathMultiple(
  path: BezierPath,
  offsets: number[],
  joinType?: 'miter' | 'round' | 'bevel'
): BezierPath[];

export function puckerBloat(path: BezierPath, amount: number): BezierPath;

export function wigglePath(
  path: BezierPath,
  size: number,
  detail: number,
  seed?: number
): BezierPath;

export function zigZagPath(
  path: BezierPath,
  size: number,
  ridges: number,
  smooth?: boolean
): BezierPath;

export function twistPath(
  path: BezierPath,
  angle: number,
  center?: Point2D
): BezierPath;

export function roundCorners(path: BezierPath, radius: number): BezierPath;

export function simplifyPath(
  path: BezierPath,
  tolerance: number
): BezierPath;

export function smoothPath(path: BezierPath, amount: number): BezierPath;

export function applyRepeater(
  path: BezierPath,
  copies: number,
  offset?: Point2D,
  rotation?: number,
  scale?: number
): BezierPath[];

export function transformPath(
  path: BezierPath,
  matrix: [number, number, number, number, number, number]  // 2D transform
): BezierPath;

// Shape generators
export function generateRectangle(
  x: number, y: number,
  width: number, height: number,
  cornerRadius?: number
): BezierPath;

export function generateEllipse(
  cx: number, cy: number,
  rx: number, ry: number
): BezierPath;

export function generatePolygon(
  cx: number, cy: number,
  radius: number,
  sides: number,
  rotation?: number
): BezierPath;

export function generateStar(
  cx: number, cy: number,
  outerRadius: number,
  innerRadius: number,
  points: number,
  rotation?: number
): BezierPath;

// Bundled export object
export const ShapeOperations: {
  // All above functions as methods
};
```

---

### 5.4 imageTrace.ts

**Purpose**: Convert raster images to vector paths.

**Location**: `ui/src/services/imageTrace.ts`

**Size**: ~15KB

#### Exports

```typescript
export type TraceMode = 'blackAndWhite' | 'grayscale' | 'color';

export interface TraceOptions {
  mode: TraceMode;
  threshold: number;            // For B&W mode
  colorCount: number;           // For color mode
  cornerThreshold: number;
  optimizePaths: boolean;
  ignoreWhite: boolean;
  minPathLength: number;
}

export interface TraceResult {
  paths: BezierPath[];
  colors: string[];             // Hex colors for each path
  bounds: { x: number; y: number; width: number; height: number };
}

export const DEFAULT_TRACE_OPTIONS: TraceOptions;

// Trace image
export async function traceImage(
  imageSource: HTMLImageElement | HTMLCanvasElement | ImageData,
  options?: Partial<TraceOptions>
): Promise<TraceResult>;

// Class-based interface
export class ImageTrace {
  constructor(options?: Partial<TraceOptions>);

  setOptions(options: Partial<TraceOptions>): void;

  trace(
    imageSource: HTMLImageElement | HTMLCanvasElement | ImageData
  ): Promise<TraceResult>;

  traceToSVG(
    imageSource: HTMLImageElement | HTMLCanvasElement | ImageData
  ): Promise<string>;
}
```

---

## 6. Effect Services

### 6.1 effectProcessor.ts

**Purpose**: Effect stack processing and parameter evaluation.

**Location**: `ui/src/services/effectProcessor.ts`

**Size**: ~14KB

#### Exports

```typescript
export interface EvaluatedEffectParams {
  [key: string]: any;
}

export interface EffectStackResult {
  canvas: HTMLCanvasElement;
  ctx: CanvasRenderingContext2D;
}

export type EffectRenderer = (
  input: EffectStackResult,
  params: EvaluatedEffectParams
) => EffectStackResult;

// Register custom effect renderer
export function registerEffectRenderer(
  effectKey: string,
  renderer: EffectRenderer
): void;

// Evaluate effect parameters at frame
export function evaluateEffectParameters(
  effect: EffectInstance,
  frame: number
): EvaluatedEffectParams;

// Process full effect stack
export function processEffectStack(
  effects: EffectInstance[],
  inputCanvas: HTMLCanvasElement,
  frame: number,
  quality?: 'draft' | 'high'
): EffectStackResult;

// Canvas utilities
export function imageDataToCanvas(imageData: ImageData): HTMLCanvasElement;
export function canvasToImageData(canvas: HTMLCanvasElement): ImageData;
export function createMatchingCanvas(source: HTMLCanvasElement): EffectStackResult;
export function releaseCanvas(canvas: HTMLCanvasElement): void;

// Utility
export function hasEnabledEffects(effects: EffectInstance[]): boolean;
export function getRegisteredEffects(): string[];

// Cache management
export function clearEffectCaches(): void;
export function getEffectProcessorStats(): {
  effectCache: { size: number; maxSize: number };
  canvasPool: { total: number; inUse: number; available: number };
};
export function cleanupEffectResources(): void;
```

---

### 6.2 effects/blurRenderer.ts

**Purpose**: Blur effect implementations (Gaussian, directional, radial, etc.)

**Location**: `ui/src/services/effects/blurRenderer.ts`

#### Exports

```typescript
// Register all blur effects
export function registerBlurEffects(): void;

// Individual renderers
export const gaussianBlurRenderer: EffectRenderer;
export const directionalBlurRenderer: EffectRenderer;
export const radialBlurRenderer: EffectRenderer;
export const boxBlurRenderer: EffectRenderer;
export const sharpenRenderer: EffectRenderer;

// WebGL acceleration
export function isWebGLBlurAvailable(): boolean;
export function disposeWebGLBlur(): void;
```

---

### 6.3 effects/colorRenderer.ts

**Purpose**: Color correction and grading effects.

**Location**: `ui/src/services/effects/colorRenderer.ts`

#### Exports

```typescript
export function registerColorEffects(): void;

// Renderers
export const brightnessContrastRenderer: EffectRenderer;
export const hueSaturationRenderer: EffectRenderer;
export const levelsRenderer: EffectRenderer;
export const tintRenderer: EffectRenderer;
export const curvesRenderer: EffectRenderer;
export const glowRenderer: EffectRenderer;
export const dropShadowRenderer: EffectRenderer;
export const colorBalanceRenderer: EffectRenderer;
export const exposureRenderer: EffectRenderer;
export const vibranceRenderer: EffectRenderer;
export const invertRenderer: EffectRenderer;
export const posterizeRenderer: EffectRenderer;
export const thresholdRenderer: EffectRenderer;

// Curve utilities
export function createSCurve(contrast: number): number[];
export function createLiftCurve(shadows: number, midtones: number, highlights: number): number[];
```

---

### 6.4 effects/distortRenderer.ts

**Purpose**: Transform and warp effects.

**Location**: `ui/src/services/effects/distortRenderer.ts`

#### Exports

```typescript
export function registerDistortEffects(): void;

export const transformRenderer: EffectRenderer;
export const warpRenderer: EffectRenderer;
export const displacementMapRenderer: EffectRenderer;
```

---

### 6.5 effects/generateRenderer.ts

**Purpose**: Procedural generation effects.

**Location**: `ui/src/services/effects/generateRenderer.ts`

#### Exports

```typescript
export function registerGenerateEffects(): void;

export const fillRenderer: EffectRenderer;
export const gradientRampRenderer: EffectRenderer;
export const fractalNoiseRenderer: EffectRenderer;

// Cache management
export function clearNoiseTileCache(): void;
export function getNoiseTileCacheStats(): { size: number };
```

---

### 6.6 effects/maskRenderer.ts

**Purpose**: Mask rendering and compositing.

**Location**: `ui/src/services/effects/maskRenderer.ts`

#### Exports

```typescript
// Render single mask
export function renderMask(
  mask: MaskData,
  width: number,
  height: number
): HTMLCanvasElement;

// Combine multiple masks
export function combineMasks(
  masks: MaskData[],
  width: number,
  height: number,
  mode: 'add' | 'subtract' | 'intersect'
): HTMLCanvasElement;

// Apply track matte
export function applyTrackMatte(
  layer: HTMLCanvasElement,
  matte: HTMLCanvasElement,
  mode: 'alpha' | 'alphaInverted' | 'luma' | 'lumaInverted'
): HTMLCanvasElement;

// Apply masks to layer
export function applyMasksToLayer(
  layerCanvas: HTMLCanvasElement,
  masks: MaskData[]
): HTMLCanvasElement;
```

---

## 7. Export Services

### 7.1 matteExporter.ts

**Purpose**: Export matte sequences for ComfyUI/Wan integration.

**Location**: `ui/src/services/matteExporter.ts`

**Size**: ~20KB

#### Exports

```typescript
export interface ExportProgress {
  current: number;
  total: number;
  stage: 'preparing' | 'rendering' | 'encoding' | 'writing';
  layerName?: string;
}

export type ProgressCallback = (progress: ExportProgress) => void;

export interface ExportOptions {
  format: 'png' | 'webp' | 'jpeg';
  quality: number;              // 0-1 for lossy formats
  includeAlpha: boolean;
  padding: number;              // Frame padding (e.g., 4 = 0001.png)
  outputDir?: string;
}

export interface DimensionValidation {
  valid: boolean;
  width: number;
  height: number;
  adjustedWidth: number;
  adjustedHeight: number;
  message?: string;
}

class MatteExporter {
  constructor();

  // Validate dimensions (must be divisible by 8)
  validateDimensions(
    width: number,
    height: number
  ): DimensionValidation;

  // Export single layer as matte sequence
  exportLayerMatte(
    composition: Composition,
    layerId: string,
    startFrame: number,
    endFrame: number,
    options?: Partial<ExportOptions>,
    onProgress?: ProgressCallback
  ): Promise<Blob[]>;

  // Export all layers as matte sequences
  exportAllMattes(
    composition: Composition,
    options?: Partial<ExportOptions>,
    onProgress?: ProgressCallback
  ): Promise<Map<string, Blob[]>>;

  // Export combined matte
  exportCombinedMatte(
    composition: Composition,
    layerIds: string[],
    options?: Partial<ExportOptions>,
    onProgress?: ProgressCallback
  ): Promise<Blob[]>;

  // Export as ZIP
  exportAsZip(
    composition: Composition,
    options?: Partial<ExportOptions>,
    onProgress?: ProgressCallback
  ): Promise<Blob>;

  // Cancel export
  cancel(): void;
}

// Singleton
export const matteExporter: MatteExporter;
```

---

### 7.2 modelExport.ts

**Purpose**: Export for AI video models (Wan, ATI, TTM, LightX).

**Location**: `ui/src/services/modelExport.ts`

**Size**: ~35KB

#### Exports

```typescript
// Types
export interface CameraMatrix4x4 {
  frame: number;
  matrix: Mat4;
}

export interface CameraTrajectoryExport {
  format: 'weyl' | 'uni3c' | 'nvs';
  fps: number;
  frameCount: number;
  matrices: CameraMatrix4x4[];
}

export interface WanMoveTrajectoryExport {
  type: 'camera' | 'object';
  points: Array<{ frame: number; x: number; y: number }>;
}

export interface PointTrajectory {
  layerId: string;
  points: Array<{ frame: number; x: number; y: number; z?: number }>;
}

export interface ParticleTrajectoryExport {
  emitterId: string;
  particles: Array<{
    id: number;
    frames: Array<{ frame: number; x: number; y: number; z: number }>;
  }>;
}

export type ATITrajectoryType = 'bezier' | 'linear' | 'arc' | 'spiral';

export interface ATITrajectoryInstruction {
  type: ATITrajectoryType;
  startPoint: { x: number; y: number };
  endPoint: { x: number; y: number };
  controlPoints?: Array<{ x: number; y: number }>;
  description: string;
}

export interface TTMExport {
  layers: TTMLayerExport[];
  frameCount: number;
  fps: number;
}

export interface TTMLayerExport {
  id: string;
  name: string;
  trajectories: PointTrajectory[];
  mask?: string;  // Base64 PNG
}

export type LightXMotionStyle = 'static' | 'pan' | 'zoom' | 'rotate' | 'complex';

export interface LightXExport {
  motionStyle: LightXMotionStyle;
  intensity: number;
  direction?: { x: number; y: number };
  masks: string[];  // Base64 PNGs
}

export type ModelTarget = 'wan' | 'ati' | 'ttm' | 'lightx' | 'comfyui';

export interface UnifiedExportOptions {
  target: ModelTarget;
  includeDepth: boolean;
  includeNormals: boolean;
  includeAudio: boolean;
  compression: boolean;
}

export interface UnifiedExportResult {
  success: boolean;
  files: Map<string, Blob>;
  metadata: Record<string, any>;
  errors: string[];
}

// Camera export
export function camera3DToMatrix4x4(
  camera: Camera3D,
  aspectRatio: number
): Mat4;

export function exportCameraTrajectory(
  camera: CameraLayer,
  format: 'weyl' | 'uni3c' | 'nvs'
): CameraTrajectoryExport;

// Layer trajectory extraction
export function extractLayerTrajectory(
  layer: Layer,
  startFrame: number,
  endFrame: number
): PointTrajectory;

export function extractSplineTrajectories(
  splineLayer: SplineLayer,
  startFrame: number,
  endFrame: number
): PointTrajectory[];

// Model-specific exports
export function exportWanMoveTrajectories(
  composition: Composition
): WanMoveTrajectoryExport[];

export function exportATITrajectory(
  trajectory: PointTrajectory
): ATITrajectoryInstruction;

export function calculatePanSpeed(
  trajectory: PointTrajectory,
  fps: number
): number;

export function exportTTMLayer(
  layer: Layer,
  composition: Composition
): TTMLayerExport;

// Motion mask generation
export function generateMotionMask(
  trajectory: PointTrajectory,
  width: number,
  height: number
): ImageData;

export function generateCombinedMotionMask(
  trajectories: PointTrajectory[],
  width: number,
  height: number
): ImageData;

// Utility
export function imageDataToBase64(imageData: ImageData): string;

export function detectMotionStyle(
  trajectory: PointTrajectory
): LightXMotionStyle;

// NPY format (for ComfyUI)
export function createNpyHeader(
  shape: number[],
  dtype: string
): Uint8Array;

export function trajectoriesToNpy(
  trajectories: PointTrajectory[]
): Blob;
```

---

### 7.3 projectStorage.ts

**Purpose**: Save/load projects to API or local file.

**Location**: `ui/src/services/projectStorage.ts`

**Size**: ~10KB

#### Exports

```typescript
export interface ProjectInfo {
  id: string;
  name: string;
  created: Date;
  modified: Date;
  thumbnail?: string;
}

export interface SaveResult {
  success: boolean;
  projectId?: string;
  error?: string;
}

export interface LoadResult {
  success: boolean;
  project?: WeylProject;
  error?: string;
}

export interface ListResult {
  success: boolean;
  projects?: ProjectInfo[];
  error?: string;
}

// API-based storage
export async function saveProject(
  project: WeylProject,
  name?: string
): Promise<SaveResult>;

export async function loadProject(
  projectId: string
): Promise<LoadResult>;

export async function listProjects(): Promise<ListResult>;

export async function deleteProject(
  projectId: string
): Promise<{ success: boolean; error?: string }>;

export function isApiAvailable(): Promise<boolean>;

// File-based storage
export function exportProjectAsFile(
  project: WeylProject,
  filename?: string
): void;

export function importProjectFromFile(
  file: File
): Promise<LoadResult>;
```

---

## 8. Cache Services

### 8.1 frameCache.ts

**Purpose**: Frame caching for smooth timeline scrubbing.

**Location**: `ui/src/services/frameCache.ts`

**Size**: ~12KB

#### Exports

```typescript
export interface CachedFrame {
  frame: number;
  compositionId: string;
  data: ImageData | Blob;
  compressed: boolean;
  width: number;
  height: number;
  timestamp: number;
  size: number;
  stateHash: string;
}

export interface FrameCacheConfig {
  maxFrames: number;
  maxMemoryBytes: number;
  compression: boolean;
  compressionQuality: number;
  preCacheWindow: number;
  predictivePreCache: boolean;
}

export interface CacheStats {
  cachedFrames: number;
  memoryUsed: number;
  hitRatio: number;
  hits: number;
  misses: number;
}

export class FrameCache {
  constructor(config?: Partial<FrameCacheConfig>);

  // Configuration
  setConfig(config: Partial<FrameCacheConfig>): void;
  getConfig(): FrameCacheConfig;

  // Cache operations
  get(
    compositionId: string,
    frame: number,
    stateHash: string
  ): CachedFrame | null;

  set(
    compositionId: string,
    frame: number,
    data: ImageData,
    stateHash: string
  ): Promise<void>;

  has(compositionId: string, frame: number): boolean;

  invalidate(compositionId: string, frame?: number): void;
  invalidateAll(): void;

  // Pre-caching
  schedulePreCache(
    compositionId: string,
    currentFrame: number,
    direction: 1 | -1,
    renderFn: (frame: number) => Promise<ImageData>
  ): void;

  cancelPreCache(): void;

  // Statistics
  getStats(): CacheStats;

  // Cleanup
  dispose(): void;
}

// Singleton access
export function getFrameCache(): FrameCache;
export function initializeFrameCache(config?: Partial<FrameCacheConfig>): void;
```

---

### 8.2 layerEvaluationCache.ts

**Purpose**: Differential layer evaluation with version tracking.

**Location**: `ui/src/services/layerEvaluationCache.ts`

**Size**: ~8KB

#### Exports

```typescript
// Version tracking
export function markLayerDirty(layerId: string): void;
export function markAllLayersDirty(): void;
export function getLayerVersion(layerId: string): number;
export function getGlobalVersion(): number;

// Cache access
export function getCachedEvaluation(
  layerId: string,
  frame: number
): EvaluatedLayer | null;

export function setCachedEvaluation(
  layerId: string,
  frame: number,
  evaluatedLayer: EvaluatedLayer
): void;

// Utility
export function invalidateLayerCache(layerId: string): void;
export function invalidateAllCaches(): void;
export function getCacheStats(): {
  entries: number;
  maxSize: number;
  hitRate: number;
};

// Layer evaluation (uses cache)
export function evaluateLayerCached(
  layer: Layer,
  frame: number,
  evaluateFn: (layer: Layer, frame: number) => EvaluatedLayer
): EvaluatedLayer;
```

---

## 9. Asset & Storage Services

### 9.1 fontService.ts

**Purpose**: Font loading and management.

**Location**: `ui/src/services/fontService.ts`

**Size**: ~8KB

#### Exports

```typescript
export interface FontInfo {
  family: string;
  weight: number;
  style: 'normal' | 'italic';
  url?: string;
  loaded: boolean;
}

export interface FontCategory {
  name: string;
  fonts: string[];
}

class FontService {
  constructor();

  // Loading
  loadFont(family: string, url?: string): Promise<void>;
  loadGoogleFont(family: string, weights?: number[]): Promise<void>;

  // Font queries
  isLoaded(family: string): boolean;
  getLoadedFonts(): FontInfo[];
  getSystemFonts(): string[];

  // Categories
  getCategories(): FontCategory[];
  getFontsByCategory(category: string): string[];

  // Font measurement
  measureText(
    text: string,
    family: string,
    size: number,
    weight?: number
  ): { width: number; height: number };

  getCharacterWidths(
    text: string,
    family: string,
    size: number
  ): number[];
}

// Singleton
export const fontService: FontService;
```

---

### 9.2 lazyLoader.ts

**Purpose**: Lazy loading for assets and modules.

**Location**: `ui/src/services/lazyLoader.ts`

**Size**: ~5KB

#### Exports

```typescript
class LazyLoader {
  constructor();

  // Image loading
  loadImage(url: string): Promise<HTMLImageElement>;
  preloadImages(urls: string[]): Promise<void>;

  // Module loading
  loadModule<T>(path: string): Promise<T>;

  // Asset loading with caching
  loadAsset<T>(
    key: string,
    loader: () => Promise<T>
  ): Promise<T>;

  // Cache management
  isLoaded(key: string): boolean;
  unload(key: string): void;
  clear(): void;

  getStats(): {
    loaded: number;
    pending: number;
    failed: number;
  };
}

// Singleton
export const lazyLoader: LazyLoader;
```

---

## 10. Utility Services

### 10.1 gpuDetection.ts

**Purpose**: Detect GPU capabilities and tier.

**Location**: `ui/src/services/gpuDetection.ts`

**Size**: ~5KB

#### Exports

```typescript
export interface GPUTier {
  tier: 'cpu' | 'webgl' | 'webgpu' | 'blackwell';
  webglVersion: 1 | 2 | null;
  webgpuSupported: boolean;
  maxTextureSize: number;
  extensions: string[];
  renderer: string;
  vendor: string;
}

export function detectGPUTier(): GPUTier;
```

---

### 10.2 workerPool.ts

**Purpose**: Web Worker pool for parallel processing.

**Location**: `ui/src/services/workerPool.ts`

**Size**: ~10KB

#### Exports

```typescript
export interface WorkerPoolConfig {
  maxWorkers: number;
  workerUrl: string;
  idleTimeout: number;
}

export class WorkerPool {
  constructor(config?: Partial<WorkerPoolConfig>);

  // Task execution
  execute<T, R>(
    task: T,
    transferables?: Transferable[]
  ): Promise<R>;

  // Batch execution
  executeAll<T, R>(
    tasks: T[],
    onProgress?: (completed: number, total: number) => void
  ): Promise<R[]>;

  // Pool management
  getActiveCount(): number;
  getIdleCount(): number;

  // Cleanup
  terminate(): void;
}

// Singleton access
export function getWorkerPool(): WorkerPool;
export function disposeWorkerPool(): void;
```

---

### 10.3 motionBlur.ts

**Purpose**: Motion blur post-processing.

**Location**: `ui/src/services/motionBlur.ts`

**Size**: ~15KB

#### Exports

```typescript
export type MotionBlurType =
  | 'temporal'      // Frame averaging
  | 'directional'   // Direction-based
  | 'radial'        // Zoom blur
  | 'object';       // Per-object velocity

export type RadialBlurMode = 'zoom' | 'spin';

export interface MotionBlurSettings {
  enabled: boolean;
  type: MotionBlurType;
  samples: number;              // Number of blur samples
  shutterAngle: number;         // Degrees (0-360)
  shutterPhase: number;         // Phase offset
  adaptiveSampling: boolean;
  threshold: number;            // Velocity threshold
}

export interface VelocityData {
  dx: Float32Array;
  dy: Float32Array;
  width: number;
  height: number;
}

export interface MotionBlurFrame {
  frame: number;
  data: ImageData;
  velocity: VelocityData;
}

export class MotionBlurProcessor {
  constructor(settings?: Partial<MotionBlurSettings>);

  setSettings(settings: Partial<MotionBlurSettings>): void;
  getSettings(): MotionBlurSettings;

  // Calculate velocity between frames
  calculateVelocity(
    currentFrame: ImageData,
    previousFrame: ImageData
  ): VelocityData;

  // Apply motion blur
  apply(
    currentFrame: ImageData,
    previousFrames: ImageData[],  // For temporal
    velocity?: VelocityData        // For velocity-based
  ): ImageData;

  // Directional blur
  applyDirectional(
    frame: ImageData,
    angle: number,
    length: number
  ): ImageData;

  // Radial blur
  applyRadial(
    frame: ImageData,
    centerX: number,
    centerY: number,
    amount: number,
    mode: RadialBlurMode
  ): ImageData;
}

// Presets
export const MOTION_BLUR_PRESETS: Record<string, Partial<MotionBlurSettings>>;
export function createDefaultMotionBlurSettings(): MotionBlurSettings;
export function getMotionBlurPreset(name: string): MotionBlurSettings;
export function listMotionBlurPresets(): string[];
```

---

### 10.4 timelineSnap.ts

**Purpose**: Timeline snapping to beats, markers, and keyframes.

**Location**: `ui/src/services/timelineSnap.ts`

**Size**: ~6KB

#### Exports

```typescript
export type SnapType =
  | 'beat'
  | 'onset'
  | 'keyframe'
  | 'marker'
  | 'layer-bound'
  | 'work-area';

export interface SnapResult {
  frame: number;
  type: SnapType;
  distance: number;   // Pixels from original position
}

export interface SnapConfig {
  enabled: boolean;
  snapDistance: number;      // Pixels
  snapToBeats: boolean;
  snapToOnsets: boolean;
  snapToKeyframes: boolean;
  snapToMarkers: boolean;
  snapToLayerBounds: boolean;
  snapToWorkArea: boolean;
}

export interface SnapIndicator {
  frame: number;
  type: SnapType;
  color: string;
}

export const DEFAULT_SNAP_CONFIG: SnapConfig;

// Find nearest snap point
export function findNearestSnap(
  frame: number,
  config: SnapConfig,
  context: {
    audioAnalysis?: AudioAnalysis;
    keyframeFrames?: number[];
    markerFrames?: number[];
    layerBounds?: Array<{ inPoint: number; outPoint: number }>;
    workArea?: { start: number; end: number };
  }
): SnapResult | null;

// Get beat frames from analysis
export function getBeatFrames(analysis: AudioAnalysis): number[];

// Get peak frames
export function getPeakFrames(analysis: AudioAnalysis): number[];

// Check if near beat
export function isNearBeat(
  frame: number,
  analysis: AudioAnalysis,
  tolerance: number
): boolean;

// Get nearest beat
export function getNearestBeatFrame(
  frame: number,
  analysis: AudioAnalysis
): number;

// Get snap color for type
export function getSnapColor(type: SnapType): string;
```

---

## Quick Reference: Import Patterns

### Import Everything from Index

```typescript
// Import all services from central index
import {
  interpolateProperty,
  ParticleSystem,
  AudioReactiveMapper,
  matteExporter,
  fontService,
  // ... etc
} from '@/services';
```

### Import Specific Service

```typescript
// Animation
import { interpolateProperty, EASING_PRESETS } from '@/services/interpolation';
import { evaluateExpression, type ExpressionContext } from '@/services/expressions';

// Audio
import { analyzeAudio, loadAudioFile, getFeatureAtFrame } from '@/services/audioFeatures';
import { AudioReactiveMapper, createDefaultAudioMapping } from '@/services/audioReactiveMapping';

// Particles
import { ParticleSystem, SeededRandom, createDefaultEmitterConfig } from '@/services/particleSystem';

// Camera/3D
import { vec3, multiplyMat4, perspectiveMat4 } from '@/services/math3d';
import { generateTrajectoryKeyframes, TRAJECTORY_PRESETS } from '@/services/cameraTrajectory';

// Effects
import { processEffectStack, registerEffectRenderer } from '@/services/effectProcessor';
import { initializeEffects } from '@/services/effects';

// Export
import { matteExporter } from '@/services/matteExporter';
import { exportCameraTrajectory, trajectoriesToNpy } from '@/services/modelExport';
```

---

## Service Dependencies

```
┌─────────────────────────────────────────────────────────────┐
│                    SERVICE DEPENDENCIES                      │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  interpolation.ts ───▶ easing.ts                           │
│         │                                                   │
│         └───────────▶ expressions.ts                        │
│                                                             │
│  audioReactiveMapping.ts ───▶ audioFeatures.ts             │
│         │                                                   │
│         └────────────────────▶ propertyDriver.ts            │
│                                                             │
│  particleSystem.ts ───▶ math3d.ts                          │
│         │                                                   │
│         └─────────────▶ gpuParticleRenderer.ts              │
│                                                             │
│  textOnPath.ts ───▶ arcLength.ts                           │
│         │                                                   │
│         └─────────▶ fontService.ts                          │
│                                                             │
│  effectProcessor.ts ───▶ effects/blurRenderer.ts           │
│         │               effects/colorRenderer.ts            │
│         │               effects/distortRenderer.ts          │
│         │               effects/generateRenderer.ts         │
│         │               effects/maskRenderer.ts             │
│         │                                                   │
│         └─────────────▶ interpolation.ts                    │
│                                                             │
│  cameraTrajectory.ts ───▶ math3d.ts                        │
│         │                                                   │
│         └────────────────▶ cameraEnhancements.ts            │
│                                                             │
│  matteExporter.ts ───▶ layerEvaluationCache.ts             │
│         │                                                   │
│         └─────────────▶ frameCache.ts                       │
│                                                             │
│  frameCache.ts ───▶ gpuDetection.ts                        │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

---

**This document is HYPER-CRITICAL for the next Claude Code session.**
**Use it as API reference when implementing features or debugging.**

---

*Generated: December 19, 2024*
*Services: 42 total*
*Lines of Documentation: ~2000*
