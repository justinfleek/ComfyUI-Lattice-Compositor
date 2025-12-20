// ============================================================
// WEYL PROJECT SCHEMA - Complete Type Definitions
// ============================================================
//
// Architecture Overview:
// - Projects contain multiple Compositions
// - One composition is the "main" composition for export
// - Layers can reference other compositions (nested compositions)
// - Video assets store duration metadata for auto-sizing
// - ComfyUI sub-graph mapping via workflowId references
// ============================================================

import type { EffectInstance } from './effects';
import type { ShapeLayerData } from './shapes';

// Re-export EffectInstance for consumers who import from project.ts
export type { EffectInstance } from './effects';
export type { ShapeLayerData } from './shapes';

export interface WeylProject {
  version: "1.0.0";
  meta: ProjectMeta;

  // Multi-composition support (professional workflow)
  compositions: Record<string, Composition>;
  mainCompositionId: string;  // Which comp to export

  // Legacy single-comp alias (for backwards compatibility)
  composition: CompositionSettings;

  assets: Record<string, AssetReference>;
  layers: Layer[];  // Layers for main composition (legacy)
  currentFrame: number;
}

export interface ProjectMeta {
  name: string;
  created: string;    // ISO 8601 date
  modified: string;   // ISO 8601 date
  author?: string;
}

// ============================================================
// COMPOSITION - Independent timeline with its own layers
// ============================================================

export interface Composition {
  id: string;
  name: string;
  settings: CompositionSettings;
  layers: Layer[];
  currentFrame: number;

  // Nested composition metadata
  isNestedComp: boolean;
  parentCompositionId?: string;  // If this is used as a nested comp

  // ComfyUI sub-graph mapping
  workflowId?: string;           // Maps to ComfyUI sub-graph ID
  workflowInputs?: WorkflowInput[];
  workflowOutputs?: WorkflowOutput[];
}

export interface CompositionSettings {
  width: number;      // Must be divisible by 8
  height: number;     // Must be divisible by 8
  frameCount: number; // 81 default, auto-adjusted for video
  fps: number;        // 16 for Phase 1
  duration: number;   // Calculated: frameCount / fps
  backgroundColor: string;

  // Auto-adjustment behavior
  autoResizeToContent: boolean;  // Resize when video imported
}

// ============================================================
// COMFYUI WORKFLOW MAPPING
// ============================================================

export interface WorkflowInput {
  name: string;
  type: 'image' | 'video' | 'latent' | 'mask' | 'number' | 'string';
  nodeId: string;
  inputName: string;
}

export interface WorkflowOutput {
  name: string;
  type: 'image' | 'video' | 'latent';
  nodeId: string;
  outputName: string;
}

// ============================================================
// ASSET REFERENCES
// ============================================================

/** Asset types supported by the compositor */
export type AssetType =
  | 'depth_map'     // Depth map image
  | 'image'         // Standard image (PNG, JPG, WebP)
  | 'video'         // Video file (MP4, WebM)
  | 'audio'         // Audio file (MP3, WAV, OGG)
  | 'model'         // 3D model (GLTF, OBJ, FBX, USD)
  | 'pointcloud'    // Point cloud (PLY, PCD, LAS)
  | 'texture'       // PBR texture map
  | 'material'      // Material definition (with texture refs)
  | 'hdri'          // Environment map (HDR, EXR)
  | 'svg'           // Vector graphic (for extrusion)
  | 'spritesheet'   // Sprite sheet for particles
  | 'lut';          // Color lookup table

/** PBR texture map types */
export type TextureMapType =
  | 'albedo'        // Base color / diffuse
  | 'normal'        // Normal map
  | 'roughness'     // Roughness map
  | 'metalness'     // Metalness map
  | 'ao'            // Ambient occlusion
  | 'emissive'      // Emissive map
  | 'height'        // Height/displacement map
  | 'opacity'       // Alpha/opacity map
  | 'specular';     // Specular map (for non-PBR workflows)

export interface AssetReference {
  id: string;
  type: AssetType;
  source: 'comfyui_node' | 'file' | 'generated' | 'url';
  nodeId?: string;
  width: number;
  height: number;
  data?: string;      // Base64 or URL
  filename?: string;  // Original filename

  // Video/Audio specific metadata
  frameCount?: number;    // Total frames in video
  duration?: number;      // Duration in seconds
  fps?: number;           // Source FPS (for video)
  hasAudio?: boolean;     // Video has audio track
  audioChannels?: number; // 1=mono, 2=stereo
  sampleRate?: number;    // Audio sample rate

  // 3D Model metadata
  modelFormat?: ModelFormat;
  modelBoundingBox?: ModelBoundingBox;
  modelAnimations?: string[];   // Animation clip names
  modelMeshCount?: number;
  modelVertexCount?: number;

  // Point cloud metadata
  pointCloudFormat?: PointCloudFormat;
  pointCount?: number;

  // Texture metadata
  textureMapType?: TextureMapType;
  textureColorSpace?: 'srgb' | 'linear';

  // Material definition (references other texture assets)
  materialMaps?: {
    albedo?: string;      // Asset ID for albedo texture
    normal?: string;      // Asset ID for normal map
    roughness?: string;   // Asset ID for roughness map
    metalness?: string;   // Asset ID for metalness map
    ao?: string;          // Asset ID for AO map
    emissive?: string;    // Asset ID for emissive map
    height?: string;      // Asset ID for height map
    opacity?: string;     // Asset ID for opacity map
  };

  // HDRI metadata
  hdriExposure?: number;
  hdriRotation?: number;

  // SVG metadata (for extrusion)
  svgPaths?: number;      // Number of paths in SVG
  svgViewBox?: { x: number; y: number; width: number; height: number };

  // Sprite sheet metadata
  spriteColumns?: number;
  spriteRows?: number;
  spriteCount?: number;
  spriteFrameRate?: number;
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
  isolate: boolean;           // Isolate layer (show only this layer)
  minimized?: boolean;        // Minimized layer (hide when minimized mode enabled)
  threeD: boolean;            // 3D Layer Switch
  motionBlur: boolean;        // Motion Blur Switch
  motionBlurSettings?: LayerMotionBlurSettings;  // Detailed motion blur configuration
  flattenTransform?: boolean; // Flatten Transform / Continuously Rasterize
  quality?: 'draft' | 'best';   // Quality switch
  effectsEnabled?: boolean;     // Enable/disable all effects
  frameBlending?: boolean;      // Frame blending for time-remapped footage
  effectLayer?: boolean;        // Effects apply to layers below
  /** @deprecated Use effectLayer instead */
  adjustmentLayer?: boolean;    // Effects apply to layers below (legacy)
  audioEnabled?: boolean;       // Enable/disable audio for this layer
  labelColor?: string;          // Layer label color (hex)

  // 3D Material Options (for 3D layers)
  materialOptions?: LayerMaterialOptions;

  inPoint: number;      // Start frame (0-80)
  outPoint: number;     // End frame (0-80)
  parentId: string | null;
  blendMode: BlendMode;
  opacity: AnimatableProperty<number>;
  transform: LayerTransform;

  // Video/Audio specific properties
  audio?: {
    level: AnimatableProperty<number>; // Audio Levels in dB
  };

  // Masking system
  masks?: LayerMask[];           // Mask paths applied to this layer
  matteType?: MatteType;         // Matte source mode (uses layer above)
  matteLayerId?: string;         // ID of layer used as matte source
  matteCompositionId?: string;   // Optional: ID of composition containing matte layer (for cross-comp mattes)
  preserveTransparency?: boolean;   // Only paint on existing pixels

  // Deprecated aliases for backwards compatibility
  /** @deprecated Use matteType instead */
  trackMatteType?: MatteType;
  /** @deprecated Use matteLayerId instead */
  trackMatteLayerId?: string;
  /** @deprecated Use matteCompositionId instead */
  trackMatteCompositionId?: string;

  properties: AnimatableProperty<any>[];
  effects: EffectInstance[];  // Effect stack - processed top to bottom
  data: SplineData | TextData | ParticleData | ParticleLayerData | DepthflowLayerData | GeneratedMapData | CameraLayerData | ImageLayerData | VideoData | NestedCompData | ProceduralMatteData | ShapeLayerData | ModelLayerData | PointCloudLayerData | null;
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
  | 'video'      // Video layer
  | 'audio'      // Audio-only layer
  | 'generated'  // AI-generated map (depth, normal, edge, etc.)
  | 'camera'     // 2.5D/3D camera layer
  | 'light'      // 3D Light layer
  | 'solid'      // Solid color plane
  | 'control'    // Control layer (transform-only)
  | 'null'       // @deprecated Use 'control' instead
  | 'group'      // Layer group
  | 'nestedComp' // Nested composition
  | 'matte'      // Procedural matte (animated patterns for track mattes)
  | 'model'      // 3D model (GLTF, OBJ, FBX, USD)
  | 'pointcloud'; // Point cloud (PLY, PCD, LAS)

// ============================================================
// MOTION BLUR SETTINGS
// ============================================================

export type MotionBlurType =
  | 'standard'     // Standard shutter-based blur
  | 'pixel'        // Pixel motion blur (analyzes frame differences)
  | 'directional'  // Directional blur (fixed direction)
  | 'radial'       // Radial blur (spin/zoom from center)
  | 'vector'       // Vector-based (uses velocity data)
  | 'adaptive';    // Auto-selects based on motion

export interface LayerMotionBlurSettings {
  /** Blur type */
  type: MotionBlurType;
  /** Shutter angle in degrees (0-720, 180 = standard film) */
  shutterAngle: number;
  /** Shutter phase offset (-180 to 180) */
  shutterPhase: number;
  /** Samples per frame (2-64, higher = smoother but slower) */
  samplesPerFrame: number;
  /** For directional blur: angle in degrees */
  direction?: number;
  /** For directional blur: blur length in pixels */
  blurLength?: number;
  /** For radial blur: 'spin' or 'zoom' */
  radialMode?: 'spin' | 'zoom';
  /** For radial blur: center point (0-1 normalized) */
  radialCenterX?: number;
  radialCenterY?: number;
  /** For radial blur: amount (0-100) */
  radialAmount?: number;
}

// ============================================================
// 3D MATERIAL OPTIONS (Industry Standard)
// ============================================================

export interface LayerMaterialOptions {
  /** Whether this layer casts shadows */
  castsShadows: 'off' | 'on' | 'only';
  /** Light transmission percentage (0-100) */
  lightTransmission: number;
  /** Whether this layer accepts shadows from other layers */
  acceptsShadows: boolean;
  /** Whether this layer is affected by lights */
  acceptsLights: boolean;
  /** Ambient light response (0-100%) */
  ambient: number;
  /** Diffuse light response (0-100%) */
  diffuse: number;
  /** Specular highlight intensity (0-100%) */
  specularIntensity: number;
  /** Specular highlight shininess (0-100%) */
  specularShininess: number;
  /** Metallic appearance (0-100%) */
  metal: number;
}

// ============================================================
// LAYER DATA TYPE MAPPING
// Maps LayerType to its corresponding data type for type safety
// ============================================================

export type LayerDataMap = {
  spline: SplineData;
  text: TextData;
  particle: ParticleData;
  particles: ParticleLayerData;
  depthflow: DepthflowLayerData;
  generated: GeneratedMapData;
  camera: CameraLayerData;
  video: VideoData;
  nestedComp: NestedCompData;
  matte: ProceduralMatteData;
  shape: ShapeLayerData;
  model: ModelLayerData;
  pointcloud: PointCloudLayerData;
  // Layers with no special data
  depth: null;
  normal: null;
  image: null;
  audio: null;
  light: null;
  solid: null;
  null: null;
  group: null;
};

/**
 * Type guard to check if a layer has specific data type
 */
export function isLayerOfType<T extends keyof LayerDataMap>(
  layer: Layer,
  type: T
): layer is Layer & { type: T; data: LayerDataMap[T] } {
  return layer.type === type;
}

/**
 * Get typed data from a layer
 * Returns null if layer type doesn't match
 */
export function getLayerData<T extends keyof LayerDataMap>(
  layer: Layer,
  type: T
): LayerDataMap[T] | null {
  if (layer.type === type) {
    return layer.data as LayerDataMap[T];
  }
  return null;
}

export type BlendMode = 'normal' | 'multiply' | 'screen' | 'overlay' | 'add' | 'difference';

// ============================================================
// MASK SYSTEM - Professional mask paths and track mattes
// ============================================================

/**
 * Matte source types (uses layer above as matte source)
 */
export type MatteType =
  | 'none'           // No matte source
  | 'alpha'          // Use alpha channel of matte layer
  | 'alpha_inverted' // Invert alpha of matte layer
  | 'luma'           // Use luminance of matte layer
  | 'luma_inverted'; // Invert luminance of matte layer

/** @deprecated Use MatteType instead */
export type TrackMatteType = MatteType;

/**
 * Mask mode determines how multiple masks combine
 */
export type MaskMode =
  | 'add'           // Union of masks (default)
  | 'subtract'      // Subtract this mask from previous
  | 'intersect'     // Intersection with previous
  | 'lighten'       // Max of mask values
  | 'darken'        // Min of mask values
  | 'difference'    // Absolute difference
  | 'none';         // Mask is disabled

/**
 * Layer mask - bezier path that clips layer content
 */
export interface LayerMask {
  id: string;
  name: string;
  enabled: boolean;
  locked: boolean;
  mode: MaskMode;
  inverted: boolean;

  // Mask path (bezier curve)
  path: AnimatableProperty<MaskPath>;

  // Mask properties
  opacity: AnimatableProperty<number>;     // 0-100
  feather: AnimatableProperty<number>;     // Blur amount in pixels
  featherX?: AnimatableProperty<number>;   // Horizontal feather (if different)
  featherY?: AnimatableProperty<number>;   // Vertical feather (if different)
  expansion: AnimatableProperty<number>;   // Expand/contract mask boundary

  // Color tint for mask display in UI
  color: string;  // Hex color for visualization
}

/**
 * Mask path - collection of bezier vertices forming a closed shape
 */
export interface MaskPath {
  closed: boolean;
  vertices: MaskVertex[];
}

/**
 * Mask vertex - point with optional bezier handles
 */
export interface MaskVertex {
  // Position (relative to layer bounds, 0-1 or pixel coordinates)
  x: number;
  y: number;

  // Incoming tangent (from previous vertex)
  inTangentX: number;
  inTangentY: number;

  // Outgoing tangent (to next vertex)
  outTangentX: number;
  outTangentY: number;
}

/**
 * Helper to create a mask AnimatableProperty (uses late-bound createAnimatableProperty)
 */
function createMaskAnimatableProperty<T>(
  name: string,
  value: T,
  type: 'number' | 'position' | 'color' | 'enum' | 'vector3' = 'number'
): AnimatableProperty<T> {
  return {
    id: `mask_prop_${name}_${Date.now()}_${Math.random().toString(36).substr(2, 5)}`,
    name,
    type,
    value,
    animated: false,
    keyframes: [],
  };
}

/**
 * Create a default rectangular mask covering the full layer
 */
export function createDefaultMask(id: string, width: number, height: number): LayerMask {
  return {
    id,
    name: 'Mask 1',
    enabled: true,
    locked: false,
    mode: 'add',
    inverted: false,
    path: createMaskAnimatableProperty<MaskPath>('Mask Path', {
      closed: true,
      vertices: [
        { x: 0, y: 0, inTangentX: 0, inTangentY: 0, outTangentX: 0, outTangentY: 0 },
        { x: width, y: 0, inTangentX: 0, inTangentY: 0, outTangentX: 0, outTangentY: 0 },
        { x: width, y: height, inTangentX: 0, inTangentY: 0, outTangentX: 0, outTangentY: 0 },
        { x: 0, y: height, inTangentX: 0, inTangentY: 0, outTangentX: 0, outTangentY: 0 },
      ],
    }, 'position'),
    opacity: createMaskAnimatableProperty<number>('Mask Opacity', 100, 'number'),
    feather: createMaskAnimatableProperty<number>('Mask Feather', 0, 'number'),
    expansion: createMaskAnimatableProperty<number>('Mask Expansion', 0, 'number'),
    color: '#FFFF00',  // Yellow default
  };
}

/**
 * Create an elliptical mask
 */
export function createEllipseMask(
  id: string,
  centerX: number,
  centerY: number,
  radiusX: number,
  radiusY: number
): LayerMask {
  // Bezier approximation of ellipse (kappa = 4 * (sqrt(2) - 1) / 3)
  const kappa = 0.5522847498;
  const ox = radiusX * kappa;  // Control point offset horizontal
  const oy = radiusY * kappa;  // Control point offset vertical

  return {
    id,
    name: 'Mask 1',
    enabled: true,
    locked: false,
    mode: 'add',
    inverted: false,
    path: createMaskAnimatableProperty<MaskPath>('Mask Path', {
      closed: true,
      vertices: [
        {
          x: centerX, y: centerY - radiusY,
          inTangentX: -ox, inTangentY: 0,
          outTangentX: ox, outTangentY: 0,
        },
        {
          x: centerX + radiusX, y: centerY,
          inTangentX: 0, inTangentY: -oy,
          outTangentX: 0, outTangentY: oy,
        },
        {
          x: centerX, y: centerY + radiusY,
          inTangentX: ox, inTangentY: 0,
          outTangentX: -ox, outTangentY: 0,
        },
        {
          x: centerX - radiusX, y: centerY,
          inTangentX: 0, inTangentY: oy,
          outTangentX: 0, outTangentY: -oy,
        },
      ],
    }, 'position'),
    opacity: createMaskAnimatableProperty<number>('Mask Opacity', 100, 'number'),
    feather: createMaskAnimatableProperty<number>('Mask Feather', 0, 'number'),
    expansion: createMaskAnimatableProperty<number>('Mask Expansion', 0, 'number'),
    color: '#00FFFF',  // Cyan
  };
}

// ============================================================
// IMAGE LAYER DATA - Static image display
// ============================================================

export interface ImageLayerData {
  assetId: string | null;

  // Display options
  fit: 'none' | 'contain' | 'cover' | 'fill';  // How to fit image in layer bounds

  // Optional cropping (for segmented regions)
  cropEnabled?: boolean;
  cropRect?: {
    x: number;
    y: number;
    width: number;
    height: number;
  };

  // Source info (for regeneration/editing)
  sourceType?: 'file' | 'generated' | 'segmented';
  segmentationMaskId?: string;  // If created via segmentation
}

// ============================================================
// VIDEO DATA - Full video playback control
// ============================================================

export interface VideoData {
  assetId: string | null;

  // Playback control
  loop: boolean;              // Loop when reaching end
  pingPong: boolean;          // Reverse at end instead of restart
  startTime: number;          // Start offset in source video (seconds)
  endTime?: number;           // End time in source (undefined = full duration)
  speed: number;              // Playback speed (1 = normal, 2 = 2x, 0.5 = half)

  // Time remapping (professional feature)
  timeRemapEnabled: boolean;
  timeRemap?: AnimatableProperty<number>;  // Maps comp time to video time

  // Frame blending for speed changes
  frameBlending: 'none' | 'frame-mix' | 'pixel-motion';

  // Audio
  audioEnabled: boolean;
  audioLevel: number;         // 0-100

  // Poster frame (for thumbnails)
  posterFrame: number;        // Frame to show when paused at start
}

// ============================================================
// NESTED COMP DATA - Nested composition reference
// ============================================================

export interface NestedCompData {
  compositionId: string;      // Reference to composition in project.compositions

  // Time mapping
  timeRemapEnabled: boolean;
  timeRemap?: AnimatableProperty<number>;  // Maps parent time to nested comp time

  // Flatten transform (render nested layers in parent's 3D space)
  flattenTransform: boolean;

  // Override nested comp settings
  overrideFrameRate: boolean;
  frameRate?: number;
}

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
// PROCEDURAL MATTE DATA (Animated patterns for track mattes)
// ============================================================

/**
 * Procedural matte layer - generates animated patterns
 * Useful for creating track mattes without additional assets
 */
export interface ProceduralMatteData {
  /** Pattern type */
  patternType: ProceduralMatteType;

  /** Pattern-specific parameters */
  parameters: ProceduralMatteParams;

  /** Animation settings */
  animation: {
    /** Enable animation */
    enabled: boolean;
    /** Animation speed multiplier */
    speed: AnimatableProperty<number>;
    /** Animation phase offset (0-1) */
    phase: AnimatableProperty<number>;
    /** Animation direction (for gradients/wipes) */
    direction: AnimatableProperty<number>;  // Degrees
  };

  /** Invert the output (swap black/white) */
  inverted: boolean;

  /** Output levels (min/max black/white) */
  levels: {
    inputBlack: AnimatableProperty<number>;   // 0-255
    inputWhite: AnimatableProperty<number>;   // 0-255
    gamma: AnimatableProperty<number>;        // 0.1-10
    outputBlack: AnimatableProperty<number>;  // 0-255
    outputWhite: AnimatableProperty<number>;  // 0-255
  };
}

/**
 * Available procedural pattern types
 */
export type ProceduralMatteType =
  | 'linear_gradient'   // Linear gradient (supports animated direction)
  | 'radial_gradient'   // Radial gradient (center point animatable)
  | 'angular_gradient'  // Conical/angular gradient
  | 'ramp'              // Animated wipe/reveal
  | 'noise'             // Fractal noise (Perlin/Simplex)
  | 'checkerboard'      // Animated checkerboard
  | 'circle'            // Animated circle (grow/shrink)
  | 'rectangle'         // Animated rectangle
  | 'grid'              // Grid pattern
  | 'wave'              // Wave pattern (sine/triangle)
  | 'venetian_blinds'   // Venetian blinds transition
  | 'iris'              // Iris wipe (circular reveal)
  | 'radial_wipe'       // Clock wipe
  | 'dissolve';         // Random dissolve

/**
 * Pattern-specific parameters (varies by pattern type)
 */
export interface ProceduralMatteParams {
  // Linear/Angular gradient
  angle?: AnimatableProperty<number>;        // Direction in degrees
  blend?: AnimatableProperty<number>;        // Blend width (0-1)

  // Radial gradient
  centerX?: AnimatableProperty<number>;      // Center X (0-1)
  centerY?: AnimatableProperty<number>;      // Center Y (0-1)
  radius?: AnimatableProperty<number>;       // Radius (0-2)

  // Ramp/Wipe
  progress?: AnimatableProperty<number>;     // Wipe progress (0-1)
  softness?: AnimatableProperty<number>;     // Edge softness

  // Noise
  scale?: AnimatableProperty<number>;        // Noise scale
  octaves?: number;                          // Fractal octaves (1-8)
  persistence?: number;                      // Fractal persistence
  lacunarity?: number;                       // Fractal lacunarity
  seed?: number;                             // Random seed

  // Checkerboard/Grid
  tilesX?: AnimatableProperty<number>;       // Horizontal tiles
  tilesY?: AnimatableProperty<number>;       // Vertical tiles
  rotation?: AnimatableProperty<number>;     // Pattern rotation

  // Circle/Rectangle
  width?: AnimatableProperty<number>;        // Shape width
  height?: AnimatableProperty<number>;       // Shape height
  cornerRadius?: AnimatableProperty<number>; // Corner radius

  // Wave
  frequency?: AnimatableProperty<number>;    // Wave frequency
  amplitude?: AnimatableProperty<number>;    // Wave amplitude
  waveType?: 'sine' | 'triangle' | 'square' | 'sawtooth';

  // Venetian blinds
  slats?: AnimatableProperty<number>;        // Number of slats

  // Iris
  feather?: AnimatableProperty<number>;      // Edge feather

  // Dissolve
  randomness?: AnimatableProperty<number>;   // Dissolve randomness
  blockSize?: AnimatableProperty<number>;    // Dissolve block size
}

/**
 * Create default procedural matte data
 */
export function createDefaultProceduralMatteData(
  patternType: ProceduralMatteType = 'linear_gradient'
): ProceduralMatteData {
  return {
    patternType,
    parameters: {
      angle: createAnimatableProperty('Angle', 0, 'number'),
      blend: createAnimatableProperty('Blend', 0.5, 'number'),
      progress: createAnimatableProperty('Progress', 0.5, 'number'),
      centerX: createAnimatableProperty('Center X', 0.5, 'number'),
      centerY: createAnimatableProperty('Center Y', 0.5, 'number'),
      radius: createAnimatableProperty('Radius', 1, 'number'),
    },
    animation: {
      enabled: false,
      speed: createAnimatableProperty('Speed', 1, 'number'),
      phase: createAnimatableProperty('Phase', 0, 'number'),
      direction: createAnimatableProperty('Direction', 0, 'number'),
    },
    inverted: false,
    levels: {
      inputBlack: createAnimatableProperty('Input Black', 0, 'number'),
      inputWhite: createAnimatableProperty('Input White', 255, 'number'),
      gamma: createAnimatableProperty('Gamma', 1, 'number'),
      outputBlack: createAnimatableProperty('Output Black', 0, 'number'),
      outputWhite: createAnimatableProperty('Output White', 255, 'number'),
    },
  };
}

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
  useGPU?: boolean; // Enable WebGPU compute acceleration
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
  color?: [number, number, number];  // Optional RGB color override (0-255)
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

export type EmitterShape = 'point' | 'line' | 'circle' | 'box' | 'sphere' | 'ring' | 'spline' | 'depth-map' | 'mask';

// Depth map emission configuration
export interface DepthMapEmission {
  /** Layer ID containing the depth map */
  sourceLayerId: string;
  /** Emit from depth values in this range (0-1) */
  depthMin: number;
  depthMax: number;
  /** Emission density per pixel */
  density: number;
  /** Scale velocity by depth (far particles move slower) */
  velocityByDepth: boolean;
  /** Scale size by depth (far particles appear smaller) */
  sizeByDepth: boolean;
  /** Depth value interpretation */
  depthMode: 'near-white' | 'near-black';
}

// Mask emission configuration
export interface MaskEmission {
  /** Layer ID containing the mask/matte */
  sourceLayerId: string;
  /** Emit from pixels above this threshold (0-1) */
  threshold: number;
  /** Emission density per pixel */
  density: number;
  /** Use luminance or alpha channel */
  channel: 'luminance' | 'alpha' | 'red' | 'green' | 'blue';
  /** Invert the mask */
  invert: boolean;
  /** Sample rate (1 = every pixel, 2 = every 2nd pixel, etc.) */
  sampleRate: number;
}

// Spline path emission configuration
export interface SplinePathEmission {
  layerId: string;                // ID of the SplineLayer to emit along
  emitMode: 'uniform' | 'random' | 'start' | 'end' | 'sequential';
  parameter: number;              // For 'start'/'end': offset, for 'uniform': interval, for 'sequential': speed
  alignToPath: boolean;           // Align emission direction with path tangent
  offset: number;                 // Perpendicular offset from path (normalized)
  bidirectional: boolean;         // Emit from both directions along tangent
}

export interface SpriteConfig {
  enabled: boolean;
  imageUrl: string | null;
  imageData: ImageBitmap | HTMLImageElement | null;
  isSheet: boolean;
  columns: number;
  rows: number;
  totalFrames: number;
  frameRate: number;
  playMode: 'loop' | 'once' | 'pingpong' | 'random';
  billboard: boolean;
  rotationEnabled: boolean;
  rotationSpeed: number;
  rotationSpeedVariance: number;
  alignToVelocity: boolean;
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
  // Geometric emitter shape (required by EmitterConfig)
  shape: EmitterShape;
  shapeRadius: number;
  shapeWidth: number;
  shapeHeight: number;
  shapeDepth: number;
  shapeInnerRadius: number;
  emitFromEdge: boolean;
  emitFromVolume: boolean;
  // Spline path emission (when shape = 'spline')
  splinePath: SplinePathEmission | null;
  // Depth map emission (when shape = 'depth-map')
  depthMapEmission?: DepthMapEmission;
  // Mask emission (when shape = 'mask')
  maskEmission?: MaskEmission;
  // Sprite configuration
  sprite: SpriteConfig;
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
  // Sprite sheet settings
  spriteEnabled?: boolean;
  spriteImageUrl?: string;
  spriteColumns?: number;       // Number of columns in sprite sheet
  spriteRows?: number;          // Number of rows in sprite sheet
  spriteAnimate?: boolean;      // Animate through frames
  spriteFrameRate?: number;     // Frames per second
  spriteRandomStart?: boolean;  // Start at random frame
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

  // Camera sync - drives depthflow from 3D camera motion
  cameraSyncEnabled?: boolean;
  cameraSyncLayerId?: string;  // ID of the camera layer to sync from
  cameraSyncConfig?: CameraToDepthflowConfig;
}

// Camera → Depthflow sync configuration
export interface CameraToDepthflowConfig {
  sensitivityX: number;
  sensitivityY: number;
  sensitivityZ: number;
  sensitivityRotation: number;
  baseZoom: number;
  invertX: boolean;
  invertY: boolean;
  zoomClamp: { min: number; max: number };
  offsetClamp: { min: number; max: number };
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
// 3D MODEL LAYER DATA - GLTF, OBJ, FBX, USD Support
// ============================================================

/** Supported 3D model formats */
export type ModelFormat = 'gltf' | 'glb' | 'obj' | 'fbx' | 'usd' | 'usda' | 'usdc' | 'usdz' | 'dae';

/** Model material override options */
export interface ModelMaterialOverride {
  /** Override all materials with a single color */
  colorOverride?: string;
  /** Override opacity (0-1) */
  opacityOverride?: number;
  /** Use wireframe rendering */
  wireframe?: boolean;
  /** Wireframe color */
  wireframeColor?: string;
  /** Use flat shading */
  flatShading?: boolean;
  /** Override metalness (0-1) */
  metalness?: number;
  /** Override roughness (0-1) */
  roughness?: number;
  /** Emissive color */
  emissive?: string;
  /** Emissive intensity */
  emissiveIntensity?: number;
  /** Use depth material (for depth maps) */
  useDepthMaterial?: boolean;
  /** Use normal material (for normal maps) */
  useNormalMaterial?: boolean;
}

/** Model animation clip info */
export interface ModelAnimationClip {
  name: string;
  duration: number;  // In seconds
  frameCount: number;
}

/** Model bounding box info */
export interface ModelBoundingBox {
  min: { x: number; y: number; z: number };
  max: { x: number; y: number; z: number };
  center: { x: number; y: number; z: number };
  size: { x: number; y: number; z: number };
}

/** 3D Model layer data */
export interface ModelLayerData {
  /** Asset ID reference to the model file */
  assetId: string;

  /** Original format of the model */
  format: ModelFormat;

  /** Model scale (uniform or per-axis) */
  scale: AnimatableProperty<number> | { x: AnimatableProperty<number>; y: AnimatableProperty<number>; z: AnimatableProperty<number> };

  /** Use uniform scale */
  uniformScale: boolean;

  /** Material overrides */
  materialOverride?: ModelMaterialOverride;

  /** Animation settings */
  animation?: {
    /** Available animation clips in the model */
    clips: ModelAnimationClip[];
    /** Currently active clip name */
    activeClip?: string;
    /** Animation time (can be keyframed for scrubbing) */
    time: AnimatableProperty<number>;
    /** Playback speed multiplier */
    speed: number;
    /** Loop animation */
    loop: boolean;
    /** Auto-play animation */
    autoPlay: boolean;
  };

  /** Bounding box (calculated after load) */
  boundingBox?: ModelBoundingBox;

  /** Cast shadows */
  castShadow: boolean;

  /** Receive shadows */
  receiveShadow: boolean;

  /** Frustum culling */
  frustumCulled: boolean;

  /** Render order (for transparency sorting) */
  renderOrder: number;

  /** Show bounding box wireframe in editor */
  showBoundingBox: boolean;

  /** Show skeleton/bones for skinned meshes */
  showSkeleton: boolean;

  /** Environment map intensity (0-1) */
  envMapIntensity: number;

  /** LOD (Level of Detail) settings */
  lod?: {
    enabled: boolean;
    /** Distance thresholds for LOD levels */
    distances: number[];
    /** Asset IDs for lower-detail versions */
    lodAssetIds: string[];
  };
}

// ============================================================
// POINT CLOUD LAYER DATA - PLY, PCD, LAS Support
// ============================================================

/** Supported point cloud formats */
export type PointCloudFormat = 'ply' | 'pcd' | 'las' | 'laz' | 'xyz' | 'pts';

/** Point cloud coloring mode */
export type PointCloudColorMode =
  | 'rgb'           // Use embedded RGB colors
  | 'intensity'     // Color by intensity value
  | 'height'        // Color by Z position (height map)
  | 'depth'         // Color by distance from camera
  | 'normal'        // Color by surface normal
  | 'classification' // Color by point classification (LAS)
  | 'uniform';      // Single uniform color

/** Point cloud rendering mode */
export type PointCloudRenderMode =
  | 'points'        // Standard GL_POINTS
  | 'circles'       // Screen-space circles (anti-aliased)
  | 'squares'       // Screen-space squares
  | 'splats';       // Gaussian splats (3DGS-style)

/** Point cloud layer data */
export interface PointCloudLayerData {
  /** Asset ID reference to the point cloud file */
  assetId: string;

  /** Original format */
  format: PointCloudFormat;

  /** Total point count (from file) */
  pointCount: number;

  /** Point size (in world units or pixels depending on sizeAttenuation) */
  pointSize: AnimatableProperty<number>;

  /** Size attenuation (points get smaller with distance) */
  sizeAttenuation: boolean;

  /** Minimum point size (pixels) */
  minPointSize: number;

  /** Maximum point size (pixels) */
  maxPointSize: number;

  /** Coloring mode */
  colorMode: PointCloudColorMode;

  /** Uniform color (when colorMode = 'uniform') */
  uniformColor: string;

  /** Color gradient for height/depth/intensity modes */
  colorGradient?: {
    stops: Array<{ position: number; color: string }>;
  };

  /** Render mode */
  renderMode: PointCloudRenderMode;

  /** Point opacity (0-1) */
  opacity: AnimatableProperty<number>;

  /** Enable depth testing */
  depthTest: boolean;

  /** Write to depth buffer */
  depthWrite: boolean;

  /** Bounding box */
  boundingBox?: ModelBoundingBox;

  /** Show bounding box wireframe */
  showBoundingBox: boolean;

  /** Level of detail settings */
  lod?: {
    enabled: boolean;
    /** Max points to render at each LOD level */
    maxPoints: number[];
    /** Distance thresholds */
    distances: number[];
  };

  /** Octree acceleration (for large point clouds) */
  octree?: {
    enabled: boolean;
    /** Max depth of octree */
    maxDepth: number;
    /** Points per node before splitting */
    pointsPerNode: number;
  };

  /** Point budget (max points to render per frame) */
  pointBudget: number;

  /** EDL (Eye-Dome Lighting) for better depth perception */
  edl?: {
    enabled: boolean;
    strength: number;
    radius: number;
  };

  /** Clipping planes */
  clipPlanes?: Array<{
    normal: { x: number; y: number; z: number };
    constant: number;
    enabled: boolean;
  }>;

  /** Classification filter (for LAS files) */
  classificationFilter?: number[];

  /** Intensity range filter */
  intensityRange?: { min: number; max: number };
}

// ============================================================
// CAMERA LAYER DATA
// ============================================================

export interface CameraDepthOfField {
  enabled: boolean;
  focusDistance: number;
  aperture: number;
  blurLevel: number;
}

export interface Vec3 {
  x: number;
  y: number;
  z: number;
}

// Camera path following configuration
export interface CameraPathFollowing {
  enabled: boolean;
  pathLayerId: string;              // ID of SplineLayer to follow
  parameter: AnimatableProperty<number>;  // 0-1 position along path (can be keyframed)
  lookAhead: number;                // Distance ahead to look (0-1 path units)
  bankingStrength: number;          // How much to bank on turns (0-1)
  offsetY: number;                  // Height offset from path
  alignToPath: boolean;             // Auto-orient camera along path tangent
  autoAdvance: boolean;             // Automatically advance along path each frame
  autoAdvanceSpeed: number;         // Speed of auto-advance (path units per frame)
}

// Camera shake configuration
export interface CameraShakeData {
  enabled: boolean;
  type: 'handheld' | 'impact' | 'earthquake' | 'subtle' | 'custom';
  intensity: number;
  frequency: number;
  rotationEnabled: boolean;
  rotationScale: number;
  seed: number;
  decay: number;
  startFrame: number;
  duration: number;
}

// Rack focus configuration
export interface CameraRackFocusData {
  enabled: boolean;
  startDistance: number;
  endDistance: number;
  duration: number;
  startFrame: number;
  easing: 'linear' | 'ease-in' | 'ease-out' | 'ease-in-out' | 'snap';
  holdStart: number;
  holdEnd: number;
}

// Autofocus configuration
export interface CameraAutoFocusData {
  enabled: boolean;
  mode: 'center' | 'point' | 'nearest' | 'farthest';
  focusPoint: { x: number; y: number };
  smoothing: number;
  threshold: number;
  sampleRadius: number;
}

// Path following configuration (simplified for AI tools)
export interface CameraPathFollowingData {
  enabled: boolean;
  splineLayerId: string | null;
  lookMode: 'tangent' | 'target' | 'fixed';
  lookTarget: { x: number; y: number; z: number } | null;
  startOffset: number;
  speed: number;
  bankAmount: number;
  smoothing: number;
}

// Trajectory keyframes storage
export interface CameraTrajectoryKeyframes {
  position: Array<{ frame: number; position: Vec3 }>;
  pointOfInterest: Array<{ frame: number; pointOfInterest: Vec3 }>;
  zoom?: Array<{ frame: number; zoom: number }>;
}

export interface CameraLayerData {
  cameraId: string;      // Reference to the Camera3D object
  isActiveCamera: boolean;  // Is this the composition's active camera?

  // Camera3D object (inline storage)
  camera?: {
    type: 'one-node' | 'two-node';
    position: Vec3;
    pointOfInterest: Vec3;
    zoom: number;
    depthOfField: boolean;
    focusDistance: number;
    aperture: number;
    blurLevel: number;
    xRotation: number;
    yRotation: number;
    zRotation: number;
  };

  // Optional animated camera properties (for MotionEngine evaluation)
  animatedPosition?: AnimatableProperty<Vec3>;
  animatedTarget?: AnimatableProperty<Vec3>;
  animatedFov?: AnimatableProperty<number>;
  animatedFocalLength?: AnimatableProperty<number>;

  // Path following (camera moves along a spline) - legacy
  pathFollowing?: CameraPathFollowing;

  // Simplified path following (for AI tools)
  pathFollowingConfig?: CameraPathFollowingData;

  // Depth of field settings
  depthOfField?: CameraDepthOfField;
  animatedFocusDistance?: AnimatableProperty<number>;
  animatedAperture?: AnimatableProperty<number>;
  animatedBlurLevel?: AnimatableProperty<number>;

  // Camera shake effect
  shake?: CameraShakeData;

  // Rack focus effect
  rackFocus?: CameraRackFocusData;

  // Autofocus settings
  autoFocus?: CameraAutoFocusData;

  // Trajectory keyframes (generated from presets)
  trajectoryKeyframes?: CameraTrajectoryKeyframes;
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

// ============================================================
// LAYER TRANSFORM (2D/3D Hybrid)
// ============================================================

export interface LayerTransform {
  // Position can be {x,y} or {x,y,z} depending on threeD flag
  position: AnimatableProperty<{ x: number; y: number; z?: number }>;
  anchorPoint: AnimatableProperty<{ x: number; y: number; z?: number }>;
  scale: AnimatableProperty<{ x: number; y: number; z?: number }>;

  // 2D Rotation
  rotation: AnimatableProperty<number>;

  // 3D Rotations (Only active if threeD is true)
  orientation?: AnimatableProperty<{ x: number; y: number; z: number }>;
  rotationX?: AnimatableProperty<number>;
  rotationY?: AnimatableProperty<number>;
  rotationZ?: AnimatableProperty<number>;
}

// ============================================================
// ANIMATION TYPES
// ============================================================

export interface AnimatableProperty<T> {
  id: string;
  name: string;
  type: 'number' | 'position' | 'color' | 'enum' | 'vector3';
  value: T;             // Default/current value
  animated: boolean;
  keyframes: Keyframe<T>[];
  group?: string;       // Property group for timeline organization (e.g., "Transform", "Text", "More Options")

  // Expression system - applies post-interpolation modifications
  expression?: PropertyExpression;
}

/**
 * Expression attached to a property
 * Evaluated after keyframe interpolation to add dynamic behavior
 */
export interface PropertyExpression {
  /** Whether the expression is active */
  enabled: boolean;
  /** Expression type: 'preset' for named expressions, 'custom' for user scripts */
  type: 'preset' | 'custom';
  /** Expression name (for presets: 'jitter', 'repeatAfter', 'inertia', etc.) */
  name: string;
  /** Expression parameters */
  params: Record<string, number | string | boolean>;
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

// Control mode for bezier handles (industry standard)
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

  // Stroke properties
  stroke: string;              // Stroke color hex
  strokeWidth: number;         // Stroke width in pixels
  strokeOpacity?: number;      // Stroke opacity 0-100 (default 100)
  strokeLineCap?: 'butt' | 'round' | 'square';  // Line cap style
  strokeLineJoin?: 'miter' | 'round' | 'bevel'; // Line join style
  strokeMiterLimit?: number;   // Miter limit (default 4)

  // Animated Dash properties
  strokeDashArray?: number[] | AnimatableProperty<number[]>;  // Dash pattern [dash, gap, ...]
  strokeDashOffset?: number | AnimatableProperty<number>;     // Animated dash offset

  // Fill properties
  fill: string;                // Fill color hex (empty = no fill)
  fillOpacity?: number;        // Fill opacity 0-100 (default 100)

  // Animated Trim Paths (for draw-on effects)
  trimStart?: number | AnimatableProperty<number>;    // Trim start 0-100%
  trimEnd?: number | AnimatableProperty<number>;      // Trim end 0-100%
  trimOffset?: number | AnimatableProperty<number>;   // Trim offset in degrees

  // Path Effects (applied in order before trim)
  pathEffects?: SplinePathEffect[];

  // Animated spline support (Phase 1)
  animatedControlPoints?: AnimatableControlPoint[];
  animated?: boolean;   // True if using animatedControlPoints

  // Level of Detail (for complex vectors)
  lod?: SplineLODSettings;

  // Mesh Warp deformation pins (primary property)
  warpPins?: import('./meshWarp').WarpPin[];

  /** @deprecated Use warpPins instead */
  puppetPins?: import('./meshWarp').WarpPin[];
}

/**
 * Path effect base interface
 */
export interface SplinePathEffect {
  id: string;
  type: SplinePathEffectType;
  enabled: boolean;
  order: number;  // Execution order (lower = first)
}

export type SplinePathEffectType =
  | 'offsetPath'
  | 'roughen'
  | 'wiggle'
  | 'zigzag'
  | 'wave';

/**
 * Offset Path Effect - grow/shrink paths
 */
export interface OffsetPathEffect extends SplinePathEffect {
  type: 'offsetPath';
  amount: AnimatableProperty<number>;       // Positive = expand, negative = contract
  lineJoin: 'miter' | 'round' | 'bevel';
  miterLimit: AnimatableProperty<number>;
}

/**
 * Roughen Effect - organic hand-drawn look
 */
export interface RoughenEffect extends SplinePathEffect {
  type: 'roughen';
  size: AnimatableProperty<number>;         // Roughness magnitude
  detail: AnimatableProperty<number>;       // Points per segment
  seed: number;                             // Deterministic randomness
}

/**
 * Wiggle Path Effect - animated jitter
 */
export interface WigglePathEffect extends SplinePathEffect {
  type: 'wiggle';
  size: AnimatableProperty<number>;
  detail: AnimatableProperty<number>;
  temporalPhase: AnimatableProperty<number>;  // Animated offset for motion
  spatialPhase: AnimatableProperty<number>;
  correlation: AnimatableProperty<number>;    // 0-100%
  seed: number;
}

/**
 * ZigZag Effect - decorative zigzag pattern
 */
export interface ZigZagEffect extends SplinePathEffect {
  type: 'zigzag';
  size: AnimatableProperty<number>;
  ridgesPerSegment: AnimatableProperty<number>;
  pointType: 'corner' | 'smooth';
}

/**
 * Wave Effect - sine/triangle/square wave distortion
 */
export interface WaveEffect extends SplinePathEffect {
  type: 'wave';
  amplitude: AnimatableProperty<number>;
  frequency: AnimatableProperty<number>;
  phase: AnimatableProperty<number>;        // Animated phase for wave motion
  waveType: 'sine' | 'triangle' | 'square';
}

/**
 * Union type for all path effects
 */
export type SplinePathEffectInstance =
  | OffsetPathEffect
  | RoughenEffect
  | WigglePathEffect
  | ZigZagEffect
  | WaveEffect;

/**
 * Level of Detail settings for complex vectors
 */
export interface SplineLODSettings {
  enabled: boolean;
  mode: 'zoom' | 'playback' | 'both';
  levels: LODLevel[];
  maxPointsForPreview: number;
  simplificationTolerance: number;
  cullingEnabled: boolean;
  cullMargin: number;
}

/**
 * Single LOD level with pre-simplified points
 */
export interface LODLevel {
  tolerance: number;
  controlPoints: ControlPoint[];
  pointCount: number;
  /** Quality index (0 = highest, higher = more simplified) */
  quality?: number;
  /** Complexity metric for this level */
  complexity?: number;
}

/**
 * Static control point - for non-animated splines (legacy/default)
 */
export interface ControlPoint {
  id: string;
  x: number;
  y: number;
  depth?: number;       // Sampled from depth map
  handleIn: { x: number; y: number } | null;
  handleOut: { x: number; y: number } | null;
  type: 'corner' | 'smooth' | 'symmetric';
  group?: string;       // Group ID for grouped animations (e.g., "head", "arm_left")
}

/**
 * Animated control point - for keyframe-animated splines
 * x and y are AnimatableProperty<number> enabling per-frame interpolation
 */
export interface AnimatableControlPoint {
  id: string;
  x: AnimatableProperty<number>;
  y: AnimatableProperty<number>;
  depth?: AnimatableProperty<number>;  // Can also be animated in Phase 2
  handleIn: AnimatableHandle | null;   // Handles can be animated too
  handleOut: AnimatableHandle | null;
  type: 'corner' | 'smooth' | 'symmetric';
  group?: string;       // Group ID for grouped animations
}

/**
 * Animated bezier handle - for advanced handle animation
 */
export interface AnimatableHandle {
  x: AnimatableProperty<number>;
  y: AnimatableProperty<number>;
}

/**
 * Evaluated control point at a specific frame
 * Result of interpolating an AnimatableControlPoint
 */
export interface EvaluatedControlPoint {
  id: string;
  x: number;
  y: number;
  depth: number;
  handleIn: { x: number; y: number } | null;
  handleOut: { x: number; y: number } | null;
  type: 'corner' | 'smooth' | 'symmetric';
  group?: string;       // Group ID for grouped animations
}

/**
 * Convert a static ControlPoint to an AnimatableControlPoint
 * Used for migration and enabling animation on existing splines
 */
export function controlPointToAnimatable(cp: ControlPoint): AnimatableControlPoint {
  return {
    id: cp.id,
    x: createAnimatableProperty('x', cp.x, 'number'),
    y: createAnimatableProperty('y', cp.y, 'number'),
    depth: cp.depth !== undefined
      ? createAnimatableProperty('depth', cp.depth, 'number')
      : undefined,
    handleIn: cp.handleIn ? {
      x: createAnimatableProperty('handleIn.x', cp.handleIn.x, 'number'),
      y: createAnimatableProperty('handleIn.y', cp.handleIn.y, 'number'),
    } : null,
    handleOut: cp.handleOut ? {
      x: createAnimatableProperty('handleOut.x', cp.handleOut.x, 'number'),
      y: createAnimatableProperty('handleOut.y', cp.handleOut.y, 'number'),
    } : null,
    type: cp.type,
    group: cp.group,
  };
}

/**
 * Convert an AnimatableControlPoint back to a static ControlPoint
 * Uses current/default values (not frame-evaluated)
 */
export function animatableToControlPoint(acp: AnimatableControlPoint): ControlPoint {
  return {
    id: acp.id,
    x: acp.x.value,
    y: acp.y.value,
    depth: acp.depth?.value,
    handleIn: acp.handleIn ? {
      x: acp.handleIn.x.value,
      y: acp.handleIn.y.value,
    } : null,
    handleOut: acp.handleOut ? {
      x: acp.handleOut.x.value,
      y: acp.handleOut.y.value,
    } : null,
    type: acp.type,
    group: acp.group,
  };
}

// ============================================================
// TEXT DATA (Professional Feature Set)
// ============================================================

export interface TextData {
  // Source Text
  text: string;
  fontFamily: string;
  fontSize: number;
  fontWeight: string;
  fontStyle: 'normal' | 'italic';
  fill: string;         // Color hex
  stroke: string;       // Color hex
  strokeWidth: number;

  // Character Properties (from Context Menu / Animators)
  tracking: number;           // Tracking (spacing)
  lineSpacing: number;        // Leading
  lineAnchor: number;         // 0% to 100%
  characterOffset: number;    // Integer shift
  characterValue: number;     // Unicode shift
  blur: { x: number; y: number }; // Per-character blur

  // Paragraph (legacy aliases)
  letterSpacing: number;      // Alias for tracking
  lineHeight: number;         // Alias for lineSpacing
  textAlign: 'left' | 'center' | 'right';

  // Path Options (Professional Feature Set)
  pathLayerId: string | null;
  pathReversed: boolean;          // Reverse Path direction
  pathPerpendicularToPath: boolean; // Characters perpendicular to path tangent
  pathForceAlignment: boolean;    // Force alignment to path
  pathFirstMargin: number;        // First Margin (pixels from path start)
  pathLastMargin: number;         // Last Margin (pixels from path end)
  pathOffset: number;             // 0-100%, animatable - shifts all characters along path
  pathAlign: 'left' | 'center' | 'right';  // Baseline alignment

  // More Options (Advanced)
  anchorPointGrouping: 'character' | 'word' | 'line' | 'all';
  groupingAlignment: { x: number; y: number }; // Percentages
  fillAndStroke: 'fill-over-stroke' | 'stroke-over-fill';
  interCharacterBlending: 'normal' | 'multiply' | 'screen' | 'overlay';

  // 3D Text
  perCharacter3D: boolean;

  // Text Animators (After Effects-style per-character animation)
  animators?: TextAnimator[];
}

// ============================================================
// TEXT ANIMATOR (Per-character animation like AE)
// ============================================================

export interface TextAnimator {
  id: string;
  name: string;
  enabled: boolean;

  // Range Selector
  rangeSelector: TextRangeSelector;

  // Animatable Properties
  properties: TextAnimatorProperties;
}

export interface TextRangeSelector {
  // Selection mode
  mode: 'percent' | 'index';

  // Selection range (0-100 for percent, integers for index)
  start: AnimatableProperty<number>;
  end: AnimatableProperty<number>;
  offset: AnimatableProperty<number>;

  // Selection unit
  basedOn: 'characters' | 'characters_excluding_spaces' | 'words' | 'lines';

  // Shape and randomness
  shape: 'square' | 'ramp_up' | 'ramp_down' | 'triangle' | 'round' | 'smooth';
  randomizeOrder: boolean;
  randomSeed: number;

  // Easing
  ease: { high: number; low: number }; // 0-100
}

export interface TextAnimatorProperties {
  // Transform properties
  position?: AnimatableProperty<{ x: number; y: number }>;
  anchorPoint?: AnimatableProperty<{ x: number; y: number }>;
  scale?: AnimatableProperty<{ x: number; y: number }>;
  rotation?: AnimatableProperty<number>;
  skew?: AnimatableProperty<number>;
  skewAxis?: AnimatableProperty<number>;

  // Style properties
  opacity?: AnimatableProperty<number>;
  fillColor?: AnimatableProperty<string>;
  fillBrightness?: AnimatableProperty<number>;
  fillSaturation?: AnimatableProperty<number>;
  fillHue?: AnimatableProperty<number>;
  strokeColor?: AnimatableProperty<string>;
  strokeWidth?: AnimatableProperty<number>;

  // Character properties
  tracking?: AnimatableProperty<number>;
  lineAnchor?: AnimatableProperty<number>;
  lineSpacing?: AnimatableProperty<number>;
  characterOffset?: AnimatableProperty<number>;
  blur?: AnimatableProperty<{ x: number; y: number }>;
}

// Text Animator Presets
export type TextAnimatorPresetType =
  | 'typewriter'
  | 'fade_in_by_character'
  | 'fade_in_by_word'
  | 'bounce_in'
  | 'wave'
  | 'scale_in'
  | 'rotate_in'
  | 'slide_in_left'
  | 'slide_in_right'
  | 'blur_in'
  | 'random_fade';

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
  type: 'number' | 'position' | 'color' | 'enum' | 'vector3' = 'number',
  group?: string
): AnimatableProperty<T> {
  return {
    id: `prop_${name}_${Date.now()}_${Math.random().toString(36).substr(2, 5)}`,
    name,
    type,
    value,
    animated: false,
    keyframes: [],
    group
  };
}

/**
 * Create default layer transform
 */
export function createDefaultTransform(): LayerTransform {
  return {
    position: createAnimatableProperty('position', { x: 0, y: 0, z: 0 }, 'vector3'),
    anchorPoint: createAnimatableProperty('anchorPoint', { x: 0, y: 0, z: 0 }, 'vector3'),
    scale: createAnimatableProperty('scale', { x: 100, y: 100, z: 100 }, 'vector3'),
    rotation: createAnimatableProperty('rotation', 0, 'number'),
    // 3D rotation properties (always present for consistent structure)
    orientation: createAnimatableProperty('orientation', { x: 0, y: 0, z: 0 }, 'vector3'),
    rotationX: createAnimatableProperty('rotationX', 0, 'number'),
    rotationY: createAnimatableProperty('rotationY', 0, 'number'),
    rotationZ: createAnimatableProperty('rotationZ', 0, 'number')
  };
}

/**
 * Create a new empty project
 */
export function createEmptyProject(width: number, height: number): WeylProject {
  const mainCompId = 'main';
  const compositionSettings: CompositionSettings = {
    width,
    height,
    frameCount: 81,
    fps: 16,
    duration: 81 / 16,
    backgroundColor: '#000000',
    autoResizeToContent: true
  };

  return {
    version: "1.0.0",
    meta: {
      name: "Untitled",
      created: new Date().toISOString(),
      modified: new Date().toISOString()
    },
    // Multi-composition support
    compositions: {
      [mainCompId]: {
        id: mainCompId,
        name: "Main Comp",
        settings: compositionSettings,
        layers: [],
        currentFrame: 0,
        isNestedComp: false
      }
    },
    mainCompositionId: mainCompId,
    // Legacy alias
    composition: compositionSettings,
    assets: {},
    layers: [],
    currentFrame: 0
  };
}
