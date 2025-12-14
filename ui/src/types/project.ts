// ============================================================
// WEYL PROJECT SCHEMA - Complete Type Definitions
// ============================================================

import type { EffectInstance } from './effects';

export interface WeylProject {
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
  frameCount: number; // 81 for Phase 1
  fps: number;        // 16 for Phase 1
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
  effects: EffectInstance[];  // Effect stack - processed top to bottom
  data: SplineData | TextData | ParticleData | ParticleLayerData | DepthflowLayerData | GeneratedMapData | CameraLayerData | null;
}

export type LayerType =
  | 'depth'      // Depth map visualization
  | 'normal'     // Normal map visualization
  | 'spline'     // Bezier path
  | 'text'       // Animated text
  | 'shape'      // Vector shapes
  | 'particle'   // Particle emitter (legacy)
  | 'particles'  // New particle system layer
  | 'depthflow'  // Depthflow parallax layer
  | 'image'      // Static/animated image
  | 'generated'  // AI-generated map (depth, normal, edge, etc.)
  | 'camera'     // 2.5D/3D camera layer
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
// NEW PARTICLE SYSTEM LAYER DATA (matching RyanOnTheInside)
// ============================================================

export interface ParticleLayerData {
  systemConfig: ParticleSystemLayerConfig;
  emitters: ParticleEmitterConfig[];
  gravityWells: GravityWellConfig[];
  vortices: VortexConfig[];
  modulations: ParticleModulationConfig[];
  renderOptions: ParticleRenderOptions;
  turbulenceFields?: TurbulenceFieldConfig[];
  subEmitters?: SubEmitterConfig[];
}

export interface ParticleSystemLayerConfig {
  maxParticles: number;
  gravity: number;
  windStrength: number;
  windDirection: number;
  warmupPeriod: number;
  respectMaskBoundary: boolean;
  boundaryBehavior: 'bounce' | 'kill' | 'wrap';
  friction: number;
  turbulenceFields?: TurbulenceFieldConfig[];
  subEmitters?: SubEmitterConfig[];
}

export interface TurbulenceFieldConfig {
  id: string;
  enabled: boolean;
  scale: number;              // Noise frequency, 0.001-0.01 (smaller = larger swirls)
  strength: number;           // Force magnitude, 0-500
  evolutionSpeed: number;     // How fast noise changes over time, 0-1
}

export interface ConnectionRenderConfig {
  enabled: boolean;
  maxDistance: number;        // Pixels, connect if closer than this
  maxConnections: number;     // Per particle, 1-5 (HARD LIMIT for performance)
  lineWidth: number;          // 0.5-3
  lineOpacity: number;        // 0-1
  fadeByDistance: boolean;    // Opacity decreases with distance
}

export interface SubEmitterConfig {
  id: string;
  parentEmitterId: string;    // Which emitter's particles trigger this, or '*' for all
  trigger: 'death';           // Only death trigger for now
  spawnCount: number;         // 1-10 particles on trigger
  inheritVelocity: number;    // 0-1, how much parent velocity inherited
  size: number;
  sizeVariance: number;
  lifetime: number;           // Frames
  speed: number;
  spread: number;             // Degrees, emission cone
  color: [number, number, number];
  enabled: boolean;
}

export interface ParticleEmitterConfig {
  id: string;
  name: string;
  x: number;
  y: number;
  direction: number;
  spread: number;
  speed: number;
  speedVariance: number;
  size: number;
  sizeVariance: number;
  color: [number, number, number];
  emissionRate: number;
  initialBurst: number;
  particleLifetime: number;
  lifetimeVariance: number;
  enabled: boolean;
  burstOnBeat: boolean;
  burstCount: number;
}

export interface GravityWellConfig {
  id: string;
  name: string;
  x: number;
  y: number;
  strength: number;
  radius: number;
  falloff: 'linear' | 'quadratic' | 'constant';
  enabled: boolean;
}

export interface VortexConfig {
  id: string;
  name: string;
  x: number;
  y: number;
  strength: number;
  radius: number;
  rotationSpeed: number;
  inwardPull: number;
  enabled: boolean;
}

export interface ParticleModulationConfig {
  id: string;
  emitterId: string;
  property: 'size' | 'speed' | 'opacity' | 'colorR' | 'colorG' | 'colorB';
  startValue: number;
  endValue: number;
  easing: string;
}

export interface ParticleRenderOptions {
  blendMode: 'normal' | 'additive' | 'multiply' | 'screen';
  renderTrails: boolean;
  trailLength: number;
  trailOpacityFalloff: number;
  particleShape: 'circle' | 'square' | 'triangle' | 'star';
  glowEnabled: boolean;
  glowRadius: number;
  glowIntensity: number;
  // Motion blur settings
  motionBlur: boolean;
  motionBlurStrength: number;   // 0-1, how much to stretch based on velocity
  motionBlurSamples: number;    // Number of samples for blur (1-16)
  // Particle connection settings
  connections: ConnectionRenderConfig;
}

// ============================================================
// DEPTHFLOW PARALLAX LAYER DATA (matching akatz-ai)
// ============================================================

export type DepthflowPreset =
  | 'static'
  | 'zoom_in'
  | 'zoom_out'
  | 'dolly_zoom_in'
  | 'dolly_zoom_out'
  | 'pan_left'
  | 'pan_right'
  | 'pan_up'
  | 'pan_down'
  | 'circle_cw'
  | 'circle_ccw'
  | 'horizontal_swing'
  | 'vertical_swing'
  | 'custom';

export interface DepthflowLayerData {
  sourceLayerId: string;
  depthLayerId: string;
  config: DepthflowConfig;
  animatedZoom?: AnimatableProperty<number>;
  animatedOffsetX?: AnimatableProperty<number>;
  animatedOffsetY?: AnimatableProperty<number>;
  animatedRotation?: AnimatableProperty<number>;
  animatedDepthScale?: AnimatableProperty<number>;
}

export interface DepthflowConfig {
  preset: DepthflowPreset;
  zoom: number;
  offsetX: number;
  offsetY: number;
  rotation: number;
  depthScale: number;
  focusDepth: number;
  dollyZoom: number;
  orbitRadius: number;
  orbitSpeed: number;
  swingAmplitude: number;
  swingFrequency: number;
  edgeDilation: number;
  inpaintEdges: boolean;
}

// ============================================================
// CAMERA LAYER DATA
// ============================================================

export interface CameraLayerData {
  cameraId: string;      // Reference to the Camera3D object
  isActiveCamera: boolean;  // Is this the composition's active camera?
}

// ============================================================
// AUDIO REACTIVITY DATA
// ============================================================

export interface AudioParticleMapping {
  feature: 'amplitude' | 'rms' | 'bass' | 'mid' | 'high' | 'onsets';
  parameter: 'emissionRate' | 'speed' | 'size' | 'gravity' | 'windStrength';
  emitterId?: string;
  sensitivity: number;
  smoothing: number;
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
  controlMode: ControlMode;  // How handles behave when dragged
}

// Control mode for bezier handles (matches After Effects / Friction)
export type ControlMode = 'symmetric' | 'smooth' | 'corner';

// Base interpolation types
export type BaseInterpolationType = 'linear' | 'bezier' | 'hold';

// All easing function names
export type EasingType =
  | 'easeInSine' | 'easeOutSine' | 'easeInOutSine'
  | 'easeInQuad' | 'easeOutQuad' | 'easeInOutQuad'
  | 'easeInCubic' | 'easeOutCubic' | 'easeInOutCubic'
  | 'easeInQuart' | 'easeOutQuart' | 'easeInOutQuart'
  | 'easeInQuint' | 'easeOutQuint' | 'easeInOutQuint'
  | 'easeInExpo' | 'easeOutExpo' | 'easeInOutExpo'
  | 'easeInCirc' | 'easeOutCirc' | 'easeInOutCirc'
  | 'easeInBack' | 'easeOutBack' | 'easeInOutBack'
  | 'easeInElastic' | 'easeOutElastic' | 'easeInOutElastic'
  | 'easeInBounce' | 'easeOutBounce' | 'easeInOutBounce';

// Combined interpolation type (base types + easing functions)
export type InterpolationType = BaseInterpolationType | EasingType;

export interface BezierHandle {
  frame: number;   // Frame offset from keyframe (negative for inHandle, positive for outHandle)
  value: number;   // Value offset from keyframe (can be positive or negative)
  enabled: boolean; // Whether this handle is active (for graph editor)
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

// ============================================================
// HELPER FUNCTIONS
// ============================================================

/**
 * Create a new animatable property with default values
 */
export function createAnimatableProperty<T>(
  name: string,
  value: T,
  type: 'number' | 'position' | 'color' | 'enum' = 'number'
): AnimatableProperty<T> {
  return {
    id: `prop_${name}_${Date.now()}`,
    name,
    type,
    value,
    animated: false,
    keyframes: []
  };
}

/**
 * Create default layer transform
 */
export function createDefaultTransform(): LayerTransform {
  return {
    position: createAnimatableProperty('position', { x: 0, y: 0 }, 'position'),
    anchor: { x: 0, y: 0 },
    scale: createAnimatableProperty('scale', { x: 1, y: 1 }, 'position'),
    rotation: createAnimatableProperty('rotation', 0, 'number')
  };
}

/**
 * Create a new empty project
 */
export function createEmptyProject(width: number, height: number): WeylProject {
  return {
    version: "1.0.0",
    meta: {
      name: "Untitled",
      created: new Date().toISOString(),
      modified: new Date().toISOString()
    },
    composition: {
      width,
      height,
      frameCount: 81,
      fps: 16,
      duration: 81 / 16,
      backgroundColor: '#000000'
    },
    assets: {},
    layers: [],
    currentFrame: 0
  };
}
