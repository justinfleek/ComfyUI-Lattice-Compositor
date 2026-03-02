# 4. TYPE DEFINITIONS

---

# IMPLEMENTATION STATUS (Updated December 2025)

## Type System Overview

The actual implementation in `ui/src/types/project.ts` has been **significantly expanded** beyond this original spec.

| Category | Spec Types | Implemented Types | Status |
|----------|------------|-------------------|--------|
| Layer Types | 9 | 17+ | ✅ Exceeded |
| Blend Modes | 6 | 27 | ✅ Exceeded (AE-compatible) |
| Effect Types | 0 | 50+ | ✅ Added |
| Keyframe Types | 3 | 5 | ✅ Expanded |
| 3D Transform | Basic | Full XYZ | ✅ Added |

## Key Type Changes from Spec

### Layer Type Expansion
```typescript
// Original spec
export type LayerType = 'depth' | 'normal' | 'spline' | 'text' | 'shape' | 'particle' | 'image' | 'generated' | 'group';

// Actual implementation
export type LayerType =
  | 'image' | 'video' | 'solid' | 'text' | 'spline' | 'shape'
  | 'null' | 'camera' | 'light' | 'adjustment' | 'precomp'
  | 'particle' | 'depthflow' | 'procedural_matte' | 'model' | 'point_cloud';
```

### Keyframe System Expansion
```typescript
// Added interpolation types
export type InterpolationType = 'linear' | 'bezier' | 'hold' | 'auto-bezier' | 'continuous-bezier';

// Added control mode for linked/split handles
export interface Keyframe<T> {
  controlMode: 'linked' | 'split';  // NEW - handle linking
  temporalEase: EaseValue[];        // NEW - per-axis ease
  spatialTangent?: Vector3;         // NEW - motion path tangents
}
```

### Transform System - 3D Support
```typescript
// Actual implementation has full 3D transforms
export interface LayerTransform {
  position: AnimatableProperty<Vector3>;      // XYZ position
  anchor: AnimatableProperty<Vector3>;        // XYZ anchor
  scale: AnimatableProperty<Vector3>;         // XYZ scale
  rotation: AnimatableProperty<Vector3>;      // XYZ rotation (Euler)
  orientation?: AnimatableProperty<Vector3>;  // 3D orientation
  opacity: AnimatableProperty<number>;
}
```

### Blend Modes (27 total)
Full After Effects blend mode compatibility including:
- Normal, Dissolve
- Darken, Multiply, Color Burn, Classic Color Burn, Linear Burn, Darker Color
- Lighten, Screen, Color Dodge, Classic Color Dodge, Linear Dodge, Lighter Color
- Overlay, Soft Light, Hard Light, Linear Light, Vivid Light, Pin Light, Hard Mix
- Difference, Exclusion, Subtract, Divide
- Hue, Saturation, Color, Luminosity

## New Types Added (Not in Original Spec)

### Effect System Types
```typescript
export interface EffectInstance {
  id: string;
  type: EffectType;
  category: 'blur' | 'color' | 'distort' | 'stylize' | 'generate';
  enabled: boolean;
  parameters: Record<string, AnimatableProperty<any>>;
}

export type EffectType =
  | 'gaussian-blur' | 'motion-blur' | 'directional-blur'
  | 'curves' | 'levels' | 'hue-saturation' | 'color-balance'
  | 'displacement' | 'turbulent-displace' | 'mesh-warp'
  | 'glow' | 'drop-shadow' | 'bevel-emboss'
  // ... 50+ effect types
```

### Audio System Types
```typescript
export interface AudioTrack {
  id: string;
  name: string;
  source: string;
  duration: number;
  waveform?: Float32Array;
  beatMarkers?: BeatMarker[];
}

export interface AudioReactiveMapping {
  audioFeature: 'amplitude' | 'bass' | 'mid' | 'treble' | 'onset' | 'beat' | 'spectralCentroid' | 'spectralFlux' | 'chroma';
  targetProperty: string;
  sensitivity: number;
  smoothing: number;
}
```

### 3D Camera Types
```typescript
export interface CameraSettings {
  focalLength: AnimatableProperty<number>;
  aperture: AnimatableProperty<number>;
  focusDistance: AnimatableProperty<number>;
  depthOfField: boolean;
  projection: 'perspective' | 'orthographic';
}

export interface CameraTrajectoryPreset {
  name: string;
  type: 'orbit' | 'dolly' | 'crane' | 'spiral' | 'custom';
  // 22 trajectory presets implemented
}
```

---

## 4.1 Project Schema (types/project.ts)

```typescript
// ============================================================
// LATTICE PROJECT SCHEMA - Complete Type Definitions
// ============================================================

export interface LatticeProject {
  version: "1.0.0";
  meta: ProjectMeta;
  composition: CompositionSettings;
  assets: Record<string, AssetReference>;
  layers: Layer[];
  currentFrame: number;
}

export interface ProjectMeta {
  name: string;
  created: string;    // ISO 8601 date
  modified: string;   // ISO 8601 date
  author?: string;
}

export interface CompositionSettings {
  width: number;      // Must be divisible by 8
  height: number;     // Must be divisible by 8
  frameCount: 81;     // Fixed for Phase 1
  fps: 16;            // Fixed for Phase 1
  duration: number;   // Calculated: frameCount / fps
  backgroundColor: string;
}

export interface AssetReference {
  id: string;
  type: 'depth_map' | 'image' | 'video';
  source: 'comfyui_node' | 'file' | 'generated';
  nodeId?: string;
  width: number;
  height: number;
  data?: string;      // Base64 or URL
}

// ============================================================
// LAYER TYPES
// ============================================================

export interface Layer {
  id: string;
  name: string;
  type: LayerType;
  visible: boolean;
  locked: boolean;
  solo: boolean;
  inPoint: number;      // Start frame (0-80)
  outPoint: number;     // End frame (0-80)
  parentId: string | null;
  blendMode: BlendMode;
  opacity: AnimatableProperty<number>;
  transform: LayerTransform;
  properties: AnimatableProperty<any>[];
  data: SplineData | TextData | ParticleData | GeneratedMapData | null;
}

export type LayerType =
  | 'depth'      // Depth map visualization
  | 'normal'     // Normal map visualization
  | 'spline'     // Bezier path
  | 'text'       // Animated text
  | 'shape'      // Vector shapes
  | 'particle'   // Particle emitter
  | 'image'      // Static/animated image
  | 'generated'  // AI-generated map (depth, normal, edge, etc.)
  | 'group';     // Layer group

export type BlendMode = 'normal' | 'multiply' | 'screen' | 'overlay' | 'add' | 'difference';

// ============================================================
// GENERATED MAP DATA (AI-powered layer generation)
// ============================================================

export interface GeneratedMapData {
  sourceLayerId: string;      // Which layer to generate from
  mapType: GeneratedMapType;
  modelId: string;            // Which model to use
  parameters: Record<string, any>;
  cachedResult?: string;      // Base64 cached output
  lastGenerated?: string;     // ISO timestamp
}

export type GeneratedMapType =
  | 'depth'         // DepthAnything V3
  | 'normal'        // NormalCrafter
  | 'edge'          // Canny/HED
  | 'pose'          // DWPose/OpenPose
  | 'segment'       // SAM2/MatSeg
  | 'lineart'       // Lineart extraction
  | 'softedge';     // Soft edge detection

// ============================================================
// PARTICLE SYSTEM DATA
// ============================================================

export interface ParticleData {
  emitter: ParticleEmitter;
  texture: ParticleTexture;
  physics: ParticlePhysics;
  rendering: ParticleRendering;
}

export interface ParticleEmitter {
  type: 'point' | 'line' | 'circle' | 'box' | 'path';
  position: AnimatableProperty<{ x: number; y: number }>;

  // For path emitter - particles spawn along a spline
  pathLayerId?: string;

  // Emission parameters
  rate: AnimatableProperty<number>;           // Particles per frame
  lifetime: AnimatableProperty<number>;       // Frames until death
  lifetimeVariance: number;                   // 0-1 randomness

  // Initial velocity
  speed: AnimatableProperty<number>;
  speedVariance: number;
  direction: AnimatableProperty<number>;      // Degrees
  spread: AnimatableProperty<number>;         // Cone angle

  // Emission shape parameters
  radius?: AnimatableProperty<number>;        // For circle
  width?: AnimatableProperty<number>;         // For box
  height?: AnimatableProperty<number>;        // For box
}

export interface ParticleTexture {
  type: 'builtin' | 'image' | 'generated' | 'extracted';

  // Built-in shapes
  builtinShape?: 'circle' | 'square' | 'star' | 'spark' | 'smoke';

  // Custom image
  imageAssetId?: string;

  // AI-generated (SDXL)
  generatedPrompt?: string;

  // Extracted from image (MatSeg)
  extractedFromAssetId?: string;
  extractedRegion?: BoundingBox;

  // PBR maps (optional, for 3D-like rendering)
  albedo?: string;      // Base64
  normal?: string;
  roughness?: string;
}

export interface ParticlePhysics {
  gravity: AnimatableProperty<{ x: number; y: number }>;
  wind: AnimatableProperty<{ x: number; y: number }>;
  drag: AnimatableProperty<number>;           // 0-1, air resistance
  turbulence: AnimatableProperty<number>;     // Random motion
  turbulenceScale: number;                    // Noise scale

  // Collision (optional, uses depth map)
  depthCollision: boolean;
  depthLayerId?: string;
  bounciness: number;
}

export interface ParticleRendering {
  startSize: AnimatableProperty<number>;
  endSize: AnimatableProperty<number>;
  sizeVariance: number;

  startColor: AnimatableProperty<string>;     // Hex
  endColor: AnimatableProperty<string>;
  colorVariance: number;

  startOpacity: AnimatableProperty<number>;
  endOpacity: AnimatableProperty<number>;

  rotation: AnimatableProperty<number>;
  rotationSpeed: AnimatableProperty<number>;

  blendMode: BlendMode;

  // Advanced
  stretchToVelocity: boolean;
  stretchFactor: number;
}

// ============================================================
// EXTRACTED TEXTURE DATA (from MatSeg)
// ============================================================

export interface ExtractedTexture {
  id: string;
  sourceAssetId: string;
  region: BoundingBox;

  // The extracted tileable texture
  albedo: string;         // Base64 PNG

  // Generated PBR maps
  pbr: {
    roughness: string;
    metallic: string;
    normal: string;
    height: string;
    ao: string;
  };

  // Metadata
  extractionMethod: 'matseg' | 'manual' | 'sdxl';
  seamless: boolean;
  resolution: { width: number; height: number };
}

export interface LayerTransform {
  position: AnimatableProperty<{ x: number; y: number }>;
  anchor: { x: number; y: number };
  scale: AnimatableProperty<{ x: number; y: number }>;
  rotation: AnimatableProperty<number>;
}

// ============================================================
// ANIMATION TYPES
// ============================================================

export interface AnimatableProperty<T> {
  id: string;
  name: string;
  type: 'number' | 'position' | 'color' | 'enum';
  value: T;             // Default/current value
  animated: boolean;
  keyframes: Keyframe<T>[];
}

export interface Keyframe<T> {
  id: string;
  frame: number;        // 0-80
  value: T;
  interpolation: InterpolationType;
  inHandle: BezierHandle;
  outHandle: BezierHandle;
  handlesBroken: boolean;
}

export type InterpolationType = 'linear' | 'bezier' | 'hold';

export interface BezierHandle {
  x: number;  // 0-1, time influence (cannot go backwards)
  y: number;  // Unbounded, value influence (can overshoot)
}

// ============================================================
// SPLINE DATA
// ============================================================

export interface SplineData {
  pathData: string;     // SVG path commands (M, C, Q, L, Z)
  controlPoints: ControlPoint[];
  closed: boolean;
  stroke: string;
  strokeWidth: number;
  fill: string;
}

export interface ControlPoint {
  id: string;
  x: number;
  y: number;
  depth?: number;       // Sampled from depth map
  handleIn: { x: number; y: number } | null;
  handleOut: { x: number; y: number } | null;
  type: 'corner' | 'smooth' | 'symmetric';
}

// ============================================================
// TEXT DATA
// ============================================================

export interface TextData {
  text: string;
  fontFamily: string;
  fontSize: number;
  fontWeight: string;
  fontStyle: 'normal' | 'italic';
  fill: string;
  stroke: string;
  strokeWidth: number;
  letterSpacing: number;
  lineHeight: number;
  textAlign: 'left' | 'center' | 'right';

  // Text on path
  pathLayerId: string | null;
  pathOffset: number;     // 0-1, animatable
  pathAlign: 'left' | 'center' | 'right';
}

// ============================================================
// UTILITY TYPES
// ============================================================

export interface Point {
  x: number;
  y: number;
}

export interface BoundingBox {
  x: number;
  y: number;
  width: number;
  height: number;
}

export interface ExportOptions {
  format: 'png_sequence';
  matteMode: 'exclude_text' | 'include_all';
  resolution: { width: number; height: number };
}
```
