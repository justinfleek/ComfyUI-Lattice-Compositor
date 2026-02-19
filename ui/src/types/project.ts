// ============================================================
// LATTICE PROJECT SCHEMA - Complete Type Definitions
// ============================================================
//
// Architecture Overview:
// - Projects contain multiple Compositions
// - One composition is the "main" composition for export
// - Layers can reference other compositions (nested compositions)
// - Video assets store duration metadata for auto-sizing
// - ComfyUI sub-graph mapping via workflowId references
// ============================================================

// Import types needed for local use in this file
import type { AnimatableProperty } from "./animation";
import { createAnimatableProperty } from "./animation";
import type { EffectInstance } from "./effects";
import type { GlobalLightSettings, LayerStyles } from "./layerStyles";
import type { LayerMask, MatteType } from "./masks";
// BlendMode re-exported from blendModes.ts (not imported here to avoid conflict with local BlendMode type)
import type { ParticleData, ParticleLayerData } from "./particles";
import type { ShapeLayerData } from "./shapes";
import type { PathLayerData, SplineData } from "./spline";
import type { TemplateConfig } from "./templateBuilder";
import type { TextData } from "./text";
import type { LayerTransform, Vec2, Vec3 } from "./transform";
import type { JSONValue } from "./dataAsset";

// Animation types (extracted to animation.ts)
export type {
  AnimatableProperty,
  BaseInterpolationType,
  BezierHandle,
  ClipboardKeyframe,
  ControlMode,
  EasingType,
  InterpolationType,
  Keyframe,
  PropertyExpression,
  PropertyValue,
} from "./animation";
export { createAnimatableProperty, createKeyframe } from "./animation";
// Re-export types from modular files for backwards compatibility
// (Files importing from '@/types/project' directly need these)
export type { EffectInstance } from "./effects";
export type { GlobalLightSettings, LayerStyles } from "./layerStyles";
// Mask types (extracted to masks.ts)
export type {
  LayerMask,
  MaskMode,
  MaskPath,
  MaskVertex,
  MatteType,
  TrackMatteType,
} from "./masks";
export { createDefaultMask, createEllipseMask } from "./masks";
// Particle types (extracted to particles.ts)
export type {
  AudioBindingConfig,
  AudioCurveType,
  AudioFeatureName,
  AudioParticleMapping,
  AudioTargetType,
  CollisionConfig,
  ConnectionRenderConfig,
  DepthMapEmission,
  EmitterShape,
  FlockingConfig,
  GravityWellConfig,
  MaskEmission,
  ParticleData,
  ParticleEmitter,
  ParticleEmitterConfig,
  ParticleLayerData,
  ParticleModulationConfig,
  ParticlePhysics,
  ParticleRendering,
  ParticleRenderOptions,
  ParticleSystemLayerConfig,
  ParticleTexture,
  ParticleVisualizationConfig,
  SplinePathEmission,
  SpriteConfig,
  SubEmitterConfig,
  TurbulenceFieldConfig,
  VortexConfig,
} from "./particles";
export type { ShapeLayerData } from "./shapes";
// Spline types (extracted to spline.ts)
export type {
  AnimatableControlPoint,
  AnimatableHandle,
  ControlPoint,
  EvaluatedControlPoint,
  LODLevel,
  OffsetPathEffect,
  PathLayerData,
  RoughenEffect,
  SplineData,
  SplineLODSettings,
  SplinePathEffect,
  SplinePathEffectInstance,
  SplinePathEffectType,
  WaveEffect,
  WigglePathEffect,
  ZigZagEffect,
} from "./spline";
export {
  animatableToControlPoint,
  controlPointToAnimatable,
  createDefaultPathLayerData,
  createDefaultSplineData,
} from "./spline";
export type { TemplateConfig } from "./templateBuilder";
// Text types (extracted to text.ts)
export type {
  TextAnimator,
  TextAnimatorPresetType,
  TextAnimatorProperties,
  TextData,
  TextExpressionSelector,
  TextRangeSelector,
  TextWigglySelector,
} from "./text";
export { createDefaultTextData } from "./text";
// Transform types (extracted to transform.ts)
export type {
  LayerTransform,
  Vec2,
  Vec3,
} from "./transform";
export {
  createDefaultTransform,
  createFollowPathConstraint,
  normalizeLayerTransform,
} from "./transform";

// Layer data types are defined locally in this file (canonical source)
// Note: layerData.ts contains older/different definitions - do not import from there

export interface LatticeProject {
  version: "1.0.0";
  schemaVersion?: number; // Schema version for migrations (default: 1)
  meta: ProjectMeta;

  // Multi-composition support (professional workflow)
  compositions: Record<string, Composition>;
  mainCompositionId: string; // Which comp to export

  // Legacy single-comp alias (for backwards compatibility)
  composition: CompositionSettings;

  assets: Record<string, AssetReference>;

  // Data assets for data-driven animation (JSON, CSV, TSV)
  // Access in expressions via: footage("filename.json").sourceData
  dataAssets?: Record<string, DataAssetReference>;

  layers: Layer[]; // Layers for main composition (legacy)
  currentFrame: number;

  // Timeline snapping configuration (user preference)
  snapConfig?: import("@/services/timelineSnap").SnapConfig;

  // Export settings (user preferences for export)
  exportSettings?: {
    format: string; // Export format (e.g., 'mp4', 'png', 'webm')
    codec?: string; // Video codec (e.g., 'h264', 'vp9')
    quality?: string; // Quality preset (e.g., 'low', 'medium', 'high')
    resolution?: { width: number; height: number }; // Export resolution
    frameRate?: number; // Export frame rate
  };
}

/**
 * Reference to a data asset (JSON, CSV, TSV) for expressions
 * Used for data-driven animation - chart data, CSV tables, JSON configs
 */
export interface DataAssetReference {
  id: string;
  name: string; // Original filename
  type: "json" | "csv" | "tsv" | "mgjson";
  rawContent: string; // Original file content
  lastModified: number; // Timestamp

  // For JSON: the parsed data
  // System F/Omega proof: Use JSONValue for JSON-serializable data
  // Type proof: sourceData must be JSON-serializable for storage/transmission
  sourceData?: JSONValue;

  // For CSV/TSV: tabular structure
  headers?: string[];
  rows?: string[][];
  numRows?: number;
  numColumns?: number;
}

export interface ProjectMeta {
  name: string;
  created: string; // ISO 8601 date
  modified: string; // ISO 8601 date
  author?: string;
}

// ============================================================
// COMPOSITION - Independent timeline with its own layers
// ============================================================

/**
 * Timeline Marker
 * Visual indicator on the timeline for navigation, beat sync, and annotation
 */
export interface Marker {
  id: string;
  frame: number;
  label: string;
  color: string;
  duration?: number; // Optional marker duration (for range markers)
  comment?: string; // Optional comment/note
}

// ============================================================

export interface Composition {
  id: string;
  name: string;
  settings: CompositionSettings;
  layers: Layer[];
  currentFrame: number;

  // Nested composition metadata
  isNestedComp: boolean;
  parentCompositionId?: string; // If this is used as a nested comp

  // ComfyUI sub-graph mapping
  workflowId?: string; // Maps to ComfyUI sub-graph ID
  workflowInputs?: WorkflowInput[];
  workflowOutputs?: WorkflowOutput[];

  // Template Builder configuration
  // When set, this composition can be exported as a Lattice Template (.lattice.json)
  templateConfig?: TemplateConfig;

  // Global Light settings for Layer Styles
  // Styles with useGlobalLight=true share this angle/altitude
  globalLight?: GlobalLightSettings;

  // Timeline markers for navigation and annotation
  markers?: Marker[];
}

export type ColorSpace =
  | "sRGB"
  | "linear-sRGB"
  | "Wide-Gamut-RGB"
  | "Display-P3"
  | "ProPhoto-RGB"
  | "ACEScg"
  | "Rec709"
  | "Rec2020";

export type ViewTransform =
  | "sRGB"
  | "Display-P3"
  | "Rec709"
  | "ACES-sRGB"
  | "Filmic";

export interface ColorSettings {
  /** Working color space for compositing */
  workingColorSpace: ColorSpace;
  /** View transform for preview */
  viewTransform: ViewTransform;
  /** Export color space */
  exportColorSpace: ColorSpace | "source";
  /** Enable linear RGB compositing */
  linearCompositing: boolean;
}

export interface CompositionSettings {
  width: number; // Must be divisible by 8
  height: number; // Must be divisible by 8
  frameCount: number; // 81 default, auto-adjusted for video
  fps: number; // 16 for Phase 1
  duration: number; // Calculated: frameCount / fps
  backgroundColor: string;

  // Auto-adjustment behavior
  autoResizeToContent: boolean; // Resize when video imported

  // Frame blending for time-remapped layers (Tutorial 04)
  // When enabled, layers with timeStretch or speedMap interpolate between frames
  frameBlendingEnabled: boolean;

  // Color management (Phase 6)
  colorSettings?: ColorSettings;

  // Composition-level motion blur settings (applies to all layers unless overridden)
  motionBlur?: boolean; // Enable motion blur globally
  shutterAngle?: number; // Shutter angle in degrees (0-720, 180 = standard film)
  motionBlurSamples?: number; // Samples per frame (2-64, higher = smoother but slower)
}

// ============================================================
// COMFYUI WORKFLOW MAPPING
// ============================================================

export interface WorkflowInput {
  name: string;
  type: "image" | "video" | "latent" | "mask" | "number" | "string";
  nodeId: string;
  inputName: string;
}

export interface WorkflowOutput {
  name: string;
  type: "image" | "video" | "latent";
  nodeId: string;
  outputName: string;
}

// ============================================================
// ASSET REFERENCES
// ============================================================

/** Asset types supported by the compositor */
export type AssetType =
  | "depth_map" // Depth map image
  | "image" // Standard image (PNG, JPG, WebP)
  | "video" // Video file (MP4, WebM)
  | "audio" // Audio file (MP3, WAV, OGG)
  | "model" // 3D model (GLTF, OBJ, FBX, USD)
  | "pointcloud" // Point cloud (PLY, PCD, LAS)
  | "texture" // PBR texture map
  | "material" // Material definition (with texture refs)
  | "hdri" // Environment map (HDR, EXR)
  | "svg" // Vector graphic (for extrusion)
  | "sprite" // Single image for particles (no grid)
  | "spritesheet" // Sprite sheet for particles (grid of frames)
  | "lut"; // Color lookup table

/** PBR texture map types */
export type TextureMapType =
  | "albedo" // Base color / diffuse
  | "normal" // Normal map
  | "roughness" // Roughness map
  | "metalness" // Metalness map
  | "ao" // Ambient occlusion
  | "emissive" // Emissive map
  | "height" // Height/displacement map
  | "opacity" // Alpha/opacity map
  | "specular"; // Specular map (for non-PBR workflows)

export interface AssetReference {
  id: string;
  type: AssetType;
  source: "comfyui_node" | "file" | "generated" | "url";
  nodeId?: string;
  width: number;
  height: number;
  data: string; // Base64 or URL - always required for valid assets
  filename?: string; // Original filename

  // Video/Audio specific metadata
  frameCount?: number; // Total frames in video
  duration?: number; // Duration in seconds
  fps?: number; // Source FPS (for video)
  hasAudio?: boolean; // Video has audio track
  audioChannels?: number; // 1=mono, 2=stereo
  sampleRate?: number; // Audio sample rate

  // 3D Model metadata
  modelFormat?: ModelFormat;
  modelBoundingBox?: ModelBoundingBox;
  modelAnimations?: string[]; // Animation clip names
  modelMeshCount?: number;
  modelVertexCount?: number;

  // Point cloud metadata
  pointCloudFormat?: PointCloudFormat;
  pointCount?: number;

  // Texture metadata
  textureMapType?: TextureMapType;
  textureColorSpace?: "srgb" | "linear";

  // Material definition (references other texture assets)
  materialMaps?: {
    albedo?: string; // Asset ID for albedo texture
    normal?: string; // Asset ID for normal map
    roughness?: string; // Asset ID for roughness map
    metalness?: string; // Asset ID for metalness map
    ao?: string; // Asset ID for AO map
    emissive?: string; // Asset ID for emissive map
    height?: string; // Asset ID for height map
    opacity?: string; // Asset ID for opacity map
  };

  // HDRI metadata
  hdriExposure?: number;
  hdriRotation?: number;

  // SVG metadata (for extrusion)
  svgPaths?: number; // Number of paths in SVG
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

/**
 * Auto-Orient Mode - How a layer orients itself in 3D space
 *
 * - 'off': No auto-orientation, use manual rotation
 * - 'toCamera': Always face the camera (billboard), only X/Y position moves
 * - 'alongPath': Orient along motion path tangent
 * - 'toPointOfInterest': Orient toward a point of interest (for cameras/lights)
 */
export type AutoOrientMode =
  | "off"
  | "toCamera"
  | "alongPath"
  | "toPointOfInterest";

/**
 * Follow Path Constraint - Position a layer along a path/spline layer
 *
 * Uses arc-length parameterization for smooth, uniform motion along the path.
 * Works with both 'spline' and 'path' layer types.
 */
export interface FollowPathConstraint {
  /** Enable/disable the constraint */
  enabled: boolean;

  /** ID of the path or spline layer to follow (empty string if no target) */
  pathLayerId: string;

  /** Progress along the path (0 = start, 1 = end) - ANIMATABLE */
  progress: AnimatableProperty<number>;

  /** Perpendicular offset from the path (pixels) - positive = right of tangent */
  offset: AnimatableProperty<number>;

  /** Offset distance along the path (0-1 normalized) */
  tangentOffset: number;

  /** Auto-orient layer rotation to path tangent */
  autoOrient: boolean;

  /** Additional rotation offset when auto-orienting (degrees) */
  rotationOffset: AnimatableProperty<number>;

  /** Banking/tilt on curves (like a car on a racetrack) */
  banking: AnimatableProperty<number>;

  /** Loop behavior when progress goes beyond 0-1 */
  loopMode: "clamp" | "loop" | "pingpong";
}

// createFollowPathConstraint is now in transform.ts

/**
 * Audio Path Animation - Animate layer position along SVG path based on audio
 *
 * Uses AudioPathAnimator service for deterministic evaluation.
 * Position along path is driven by audio amplitude or accumulated movement.
 */
export interface AudioPathAnimation {
  /** Enable/disable the audio path animation */
  enabled: boolean;

  /** SVG path data string (M, L, C, Q, Z commands) */
  pathData: string;

  /** Movement mode: 'amplitude' (direct mapping) or 'accumulate' (travel forward) */
  movementMode: "amplitude" | "accumulate";

  /** Sensitivity/speed multiplier */
  sensitivity: number;

  /** Smoothing factor (0-1) - for amplitude mode release envelope */
  smoothing: number;

  /** Release envelope (0-1) - how fast position returns after peak (amplitude mode) */
  release: number;

  /** Power curve for amplitude (1=linear, >1=noise gate effect) */
  amplitudeCurve: number;

  /** Reverse direction on beat detection (accumulate mode) */
  flipOnBeat: boolean;

  /** Beat detection threshold (0.02=sensitive, 0.1=only kicks) */
  beatThreshold: number;

  /** Auto-orient layer rotation to path tangent */
  autoOrient: boolean;

  /** Additional rotation offset when auto-orienting (degrees) */
  rotationOffset: number;
}

export interface Layer {
  id: string;
  name: string;
  type: LayerType;
  visible: boolean;
  locked: boolean;
  isolate: boolean; // Isolate layer (show only this layer)
  minimized?: boolean; // Minimized layer (hide when minimized mode enabled)
  threeD: boolean; // 3D Layer Switch
  autoOrient?: AutoOrientMode; // Auto-orient behavior (billboard to camera, along path, etc.)
  followPath?: FollowPathConstraint; // Constrain layer position to follow a path layer
  audioPathAnimation?: AudioPathAnimation; // Animate position along SVG path based on audio
  motionBlur: boolean; // Motion Blur Switch
  motionBlurSettings?: LayerMotionBlurSettings; // Detailed motion blur configuration
  flattenTransform?: boolean; // Flatten Transform / Continuously Rasterize
  quality?: "draft" | "best"; // Quality switch
  effectsEnabled?: boolean; // Enable/disable all effects
  frameBlending?: boolean; // Frame blending for time-remapped footage
  effectLayer?: boolean; // Effects apply to layers below
  /** @deprecated Use effectLayer instead */
  adjustmentLayer?: boolean; // Effects apply to layers below (legacy)
  audioEnabled?: boolean; // Enable/disable audio for this layer
  labelColor?: string; // Layer label color (hex)

  // 3D Material Options (for 3D layers)
  materialOptions?: LayerMaterialOptions;

  // Timing (primary properties)
  startFrame: number; // First visible frame (0-based)
  endFrame: number; // Last visible frame (0-based)
  /** @deprecated Use 'startFrame' instead. Kept for backwards compatibility. */
  inPoint?: number;
  /** @deprecated Use 'endFrame' instead. Kept for backwards compatibility. */
  outPoint?: number;

  // Time Stretch (percentage-based speed control)
  // 100 = normal, 200 = half speed (2x duration), 50 = double speed (0.5x duration)
  // Negative values = reversed playback (-100 = normal reversed)
  timeStretch?: number;

  // Anchor point for time stretch operations
  // 'startFrame' = layer start stays fixed, end moves
  // 'endFrame' = layer end stays fixed, start moves
  // 'currentFrame' = stretch around current playhead position
  stretchAnchor?: "startFrame" | "endFrame" | "currentFrame";

  parentId: string | null;
  blendMode: BlendMode;
  opacity: AnimatableProperty<number>;
  transform: LayerTransform;

  // Video/Audio specific properties
  audio?: {
    level: AnimatableProperty<number>; // Audio Levels in dB
  };

  // Masking system
  masks?: LayerMask[]; // Mask paths applied to this layer
  matteType?: MatteType; // Matte source mode (uses layer above)
  matteLayerId?: string; // ID of layer used as matte source
  matteCompositionId?: string; // Optional: ID of composition containing matte layer (for cross-comp mattes)
  preserveTransparency?: boolean; // Only paint on existing pixels

  // Deprecated aliases for backwards compatibility
  /** @deprecated Use matteType instead */
  trackMatteType?: MatteType;
  /** @deprecated Use matteLayerId instead */
  trackMatteLayerId?: string;
  /** @deprecated Use matteCompositionId instead */
  trackMatteCompositionId?: string;

  properties: AnimatableProperty<any>[];
  effects: EffectInstance[]; // Effect stack - processed top to bottom

  // Layer Styles (Photoshop-style effects: drop shadow, bevel, stroke, etc.)
  // Renders BEFORE effects in fixed order: shadow → glow → bevel → overlay → stroke
  layerStyles?: LayerStyles;

  // All layer data types - must include every type from LayerDataMap
  data:
    | SplineData
    | PathLayerData
    | TextData
    | LegacyParticleLayerData // Was ParticleData - CODE IS TRUTH
    | ParticleLayerData
    | DepthflowLayerData
    | GeneratedMapData
    | CameraLayerData
    | ImageLayerData
    | VideoData
    | NestedCompData
    | MatteLayerData // Was ProceduralMatteData - CODE IS TRUTH
    | ShapeLayerData
    | ModelLayerData
    | PointCloudLayerData
    | DepthLayerData
    | NormalLayerData
    | AudioLayerData
    | ControlLayerData
    | PoseLayerData
    | LightLayerData
    | SolidLayerData
    | NullLayerData
    | GroupLayerData
    | EffectLayerData
    | GeneratedLayerData
    | ProceduralMatteData // Keep for procedural pattern mattes
    | ParticleData // Keep for advanced particle configs
    | null;
}

export type LayerType =
  | "depth" // Depth map visualization
  | "normal" // Normal map visualization
  | "spline" // Bezier path (visible shape with stroke/fill)
  | "path" // Motion path (invisible guide for text/camera/particles)
  | "text" // Animated text
  | "shape" // Vector shapes
  | "particle" // Particle emitter (legacy)
  | "particles" // New particle system layer
  | "depthflow" // Depthflow parallax layer
  | "image" // Static/animated image
  | "video" // Video layer
  | "audio" // Audio-only layer
  | "generated" // AI-generated map (depth, normal, edge, etc.)
  | "camera" // 2.5D/3D camera layer
  | "light" // 3D Light layer
  | "solid" // Solid color plane
  | "control" // Control layer (transform-only)
  | "null" // @deprecated Use 'control' instead
  | "group" // Layer group
  | "nestedComp" // Nested composition
  | "matte" // Procedural matte (animated patterns for track mattes)
  | "model" // 3D model (GLTF, OBJ, FBX, USD)
  | "pointcloud" // Point cloud (PLY, PCD, LAS)
  | "pose" // OpenPose skeleton (ControlNet pose conditioning)
  | "effectLayer" // Effect layer (effects apply to layers below)
  | "adjustment"; // @deprecated Use 'effectLayer' instead

// ============================================================
// MOTION BLUR SETTINGS
// ============================================================

export type MotionBlurType =
  | "standard" // Standard shutter-based blur
  | "pixel" // Pixel motion blur (analyzes frame differences)
  | "directional" // Directional blur (fixed direction)
  | "radial" // Radial blur (spin/zoom from center)
  | "vector" // Vector-based (uses velocity data)
  | "adaptive"; // Auto-selects based on motion

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
  radialMode?: "spin" | "zoom";
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
  castsShadows: "off" | "on" | "only";
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
  path: PathLayerData;
  text: TextData;
  particle: LegacyParticleLayerData; // Was ParticleData - CODE IS TRUTH
  particles: ParticleLayerData;
  depthflow: DepthflowLayerData;
  generated: GeneratedMapData;
  camera: CameraLayerData;
  video: VideoData;
  nestedComp: NestedCompData;
  matte: MatteLayerData; // Was ProceduralMatteData - CODE IS TRUTH
  shape: ShapeLayerData;
  model: ModelLayerData;
  pointcloud: PointCloudLayerData;
  // Layers with specialized data defined above
  image: ImageLayerData;
  depth: DepthLayerData;
  normal: NormalLayerData;
  audio: AudioLayerData;
  control: ControlLayerData;
  pose: PoseLayerData;
  // Layers with specialized data (previously null)
  light: LightLayerData;
  solid: SolidLayerData;
  null: NullLayerData;
  group: GroupLayerData;
  effectLayer: EffectLayerData;
  adjustment: EffectLayerData; // @deprecated - use effectLayer
};

/**
 * Union type of all possible layer data types.
 * Use for generic layer data operations where the specific layer type is unknown.
 */
export type AnyLayerData = LayerDataMap[keyof LayerDataMap];

/**
 * Alias for AnyLayerData - Union of all possible layer data types.
 * @deprecated Use AnyLayerData instead
 */
export type LayerDataUnion = AnyLayerData;

/**
 * Type guard to check if a layer has specific data type
 */
export function isLayerOfType<T extends keyof LayerDataMap>(
  layer: Layer,
  type: T,
): layer is Layer & { type: T; data: LayerDataMap[T] } {
  return layer.type === type;
}

/**
 * Get typed data from a layer
 * @throws Error if layer type doesn't match
 */
export function getLayerData<T extends keyof LayerDataMap>(
  layer: Layer,
  type: T,
): LayerDataMap[T] {
  if (layer.type === type) {
    return layer.data as LayerDataMap[T];
  }
  throw new Error(`[ProjectTypes] Layer type mismatch: expected "${type}", got "${layer.type}"`);
}

/**
 * Blend Modes - Industry standard compatibility
 * Organized by category matching professional animation software groupings
 */
export type BlendMode =
  // Normal
  | "normal"
  | "dissolve"
  // Darken
  | "darken"
  | "multiply"
  | "color-burn"
  | "linear-burn"
  | "darker-color"
  // Lighten
  | "lighten"
  | "screen"
  | "color-dodge"
  | "linear-dodge"
  | "lighter-color"
  | "add"
  // Contrast
  | "overlay"
  | "soft-light"
  | "hard-light"
  | "vivid-light"
  | "linear-light"
  | "pin-light"
  | "hard-mix"
  // Inversion
  | "difference"
  | "exclusion"
  | "subtract"
  | "divide"
  // Component (HSL)
  | "hue"
  | "saturation"
  | "color"
  | "luminosity"
  // Utility/Advanced modes
  | "stencil-alpha"
  | "stencil-luma"
  | "silhouette-alpha"
  | "silhouette-luma"
  | "alpha-add"
  | "luminescent-premul"
  // Classic blend modes (legacy compatibility)
  | "classic-color-burn"
  | "classic-color-dodge";

/**
 * Blend mode categories for UI organization
 */
export const BLEND_MODE_CATEGORIES = {
  normal: ["normal", "dissolve"],
  darken: ["darken", "multiply", "color-burn", "linear-burn", "darker-color"],
  lighten: [
    "lighten",
    "screen",
    "color-dodge",
    "linear-dodge",
    "lighter-color",
    "add",
  ],
  contrast: [
    "overlay",
    "soft-light",
    "hard-light",
    "vivid-light",
    "linear-light",
    "pin-light",
    "hard-mix",
  ],
  inversion: ["difference", "exclusion", "subtract", "divide"],
  component: ["hue", "saturation", "color", "luminosity"],
  utility: [
    "stencil-alpha",
    "stencil-luma",
    "silhouette-alpha",
    "silhouette-luma",
    "alpha-add",
    "luminescent-premul",
  ],
} as const;

// ============================================================
// IMAGE LAYER DATA - Static image display
// ============================================================

export interface ImageLayerData {
  // Asset reference - empty string if using inline source
  assetId: string;

  // Inline data URL - empty string if using assetId
  // Used for temporary/generated images before asset creation
  source: string;

  // Display options
  fit: "none" | "contain" | "cover" | "fill";

  // Cropping (for segmented regions)
  cropEnabled: boolean;
  cropRect: {
    x: number;
    y: number;
    width: number;
    height: number;
  };

  // Source info (for regeneration/editing)
  sourceType: "file" | "generated" | "segmented" | "inline";
  segmentationMaskId: string; // Empty string if not from segmentation
}

// ============================================================
// DEPTH LAYER DATA - Depth map visualization for AI workflows
// ============================================================

export interface DepthLayerData {
  /** Source asset ID (depth map image) */
  assetId: string | null;

  /** Visualization mode */
  visualizationMode: "grayscale" | "colormap" | "contour" | "3d-mesh";

  /** Color map preset for visualization */
  colorMap: "turbo" | "viridis" | "plasma" | "inferno" | "magma" | "grayscale";

  /** Invert depth values (near <-> far) */
  invert: boolean;

  /** Depth range normalization */
  minDepth: number;
  maxDepth: number;
  autoNormalize: boolean;

  /** Contour settings (when visualizationMode = 'contour') */
  contourLevels: number;
  contourColor: string;
  contourWidth: number;

  /** 3D mesh settings (when visualizationMode = '3d-mesh') */
  meshDisplacement: AnimatableProperty<number>;
  meshResolution: number;
  wireframe: boolean;
}

// ============================================================
// NORMAL LAYER DATA - Normal map visualization for AI workflows
// ============================================================

export interface NormalLayerData {
  /** Source asset ID (normal map image) */
  assetId: string | null;

  /** Visualization mode */
  visualizationMode: "rgb" | "hemisphere" | "arrows" | "lit";

  /** Normal map format */
  format: "opengl" | "directx";

  /** Flip channels */
  flipX: boolean;
  flipY: boolean;
  flipZ: boolean;

  /** Arrow visualization settings */
  arrowDensity: number;
  arrowScale: number;
  arrowColor: string;

  /** Lit visualization settings (fake lighting preview) */
  lightDirection: { x: number; y: number; z: number };
  lightIntensity: number;
  ambientIntensity: number;
}

// ============================================================
// AUDIO LAYER DATA - Audio-only layer (no visual)
// ============================================================

export interface AudioLayerData {
  /** Source asset ID (audio file) */
  assetId: string | null;

  /** Audio level (dB, 0 = unity) */
  level: AnimatableProperty<number>;

  /** Mute toggle */
  muted: boolean;

  /** Solo this audio track */
  solo: boolean;

  /** Panning (-1 = left, 0 = center, 1 = right) */
  pan: AnimatableProperty<number>;

  /** Playback settings */
  startTime: number;
  loop: boolean;
  speed: number;

  /** Waveform visualization in timeline */
  showWaveform: boolean;
  waveformColor: string;

  /** Audio reactivity - expose audio features for linking */
  exposeFeatures: boolean;

  /** Waveform data (sample amplitudes) */
  waveform?: number[];

  /** Detected beat frames */
  beats?: number[];

  /** Detected tempo (BPM) */
  tempo?: number;

  /** Per-frame amplitude data */
  amplitudeData?: number[];

  /** Layer-specific markers (for audio cue points) */
  markers?: Array<{ frame: number; label: string }>;
}

// ============================================================
// GENERATED LAYER DATA - AI-generated content
// ============================================================

export interface GeneratedLayerData {
  /** Generated content type */
  generationType:
    | "depth"
    | "normal"
    | "edge"
    | "segment"
    | "inpaint"
    | "custom";

  /** Source layer ID (input to generation) */
  sourceLayerId: string | null;

  /** Model used for generation */
  model: string;

  /** Generation parameters (model-specific) */
  parameters: Record<string, JSONValue>;

  /** Generated asset ID (output) */
  generatedAssetId: string | null;

  /** Generation status */
  status: "pending" | "generating" | "complete" | "error";
  errorMessage?: string;

  /** Auto-regenerate when source changes */
  autoRegenerate: boolean;

  /** Last generation timestamp */
  lastGenerated?: string;
}

// ============================================================
// GROUP LAYER DATA - Layer folder/group
// ============================================================

export interface GroupLayerData {
  /** Collapsed state in timeline */
  collapsed: boolean;

  /** Group color label */
  color: string | null;

  /** Pass-through mode (group doesn't create intermediate composite) */
  passThrough: boolean;

  /** Isolate group (only show group contents when selected) */
  isolate: boolean;
}

// ============================================================
// CONTROL LAYER DATA - Null object / transform controller
// ============================================================

export interface ControlLayerData {
  /** Visual size of control icon in editor */
  size: number;

  /** Show XYZ axis indicators */
  showAxes: boolean;

  /** Show control layer icon/gizmo */
  showIcon: boolean;

  /** Icon shape */
  iconShape: "crosshair" | "diamond" | "circle" | "square";

  /** Icon color */
  iconColor: string;
}

// ============================================================
// EFFECT LAYER DATA - Effects apply to layers below
// (Previously called Adjustment Layer - renamed for trade dress)
// ============================================================

export interface EffectLayerData {
  /** Effect layer flag (always true for effect layers) */
  effectLayer: boolean;

  /** @deprecated Use effectLayer - backwards compatibility */
  adjustmentLayer: boolean;

  /** Layer label color for organization */
  color: string;
}

/**
 * Create default effect layer data
 */
export function createDefaultEffectLayerData(): EffectLayerData {
  return {
    effectLayer: true,
    adjustmentLayer: true, // Backwards compatibility
    color: "#FF6B6B", // Default red color for effect layers
  };
}

// ============================================================
// LIGHT LAYER DATA - Point, spot, directional, ambient lights
// ============================================================

export interface LightLayerData {
  /** Light type */
  lightType: "point" | "spot" | "directional" | "ambient";

  /** Light color */
  color: string;

  /** Light intensity (0-100+) */
  intensity: number;

  /** Light radius (for point/spot lights) */
  radius: number;

  /** Falloff type */
  falloff: "none" | "linear" | "quadratic" | "smooth";

  /** Falloff distance */
  falloffDistance: number;

  /** Cast shadows */
  castShadows: boolean;

  /** Shadow darkness (0-100) */
  shadowDarkness: number;

  /** Shadow diffusion/softness */
  shadowDiffusion: number;

  // Spot light specific
  /** Cone angle for spot lights (degrees) */
  coneAngle?: number;

  /** Cone feather for spot light soft edge (0-100) - CODE IS TRUTH (was penumbra) */
  coneFeather?: number;

  /** Target position for spot/directional lights */
  target?: { x: number; y: number; z: number };
}

/**
 * Create default light layer data
 */
export function createDefaultLightLayerData(): LightLayerData {
  return {
    lightType: "point",
    color: "#ffffff",
    intensity: 100,
    radius: 500,
    falloff: "none",
    falloffDistance: 500,
    castShadows: false,
    shadowDarkness: 100,
    shadowDiffusion: 0,
  };
}

// ============================================================
// SOLID LAYER DATA - Solid color rectangle
// ============================================================

/** Motion path configuration for layer position animation */
export interface MotionPathConfig {
  enabled: boolean;
  path: Array<{ x: number; y: number }>; // Inline path points
  orientToPath?: boolean; // Auto-orient rotation to path tangent
  keyframes?: Array<{ frame: number; progress: number }>; // Progress keyframes (0-100)
  speedGraph?: Array<{ frame: number; speed: number }>; // Speed keyframes for variable speed along path
}

export interface SolidLayerData {
  /** Fill color */
  color: string;

  /** Width (defaults to composition width) */
  width: number;

  /** Height (defaults to composition height) */
  height: number;

  /** Shadow catcher mode - renders only shadows, not the solid color */
  shadowCatcher?: boolean;

  /** Shadow opacity (0-100) when in shadow catcher mode */
  shadowOpacity?: number;

  /** Shadow color (defaults to black) */
  shadowColor?: string;

  /** Receive shadows from lights */
  receiveShadow?: boolean;

  /** Motion path for position animation along inline path points */
  motionPath?: MotionPathConfig;
}

/**
 * Create default solid layer data
 */
export function createDefaultSolidLayerData(
  width = 1920,
  height = 1080,
): SolidLayerData {
  return {
    color: "#808080",
    width,
    height,
  };
}

// ============================================================
// NULL LAYER DATA - Invisible transform controller
// ============================================================

export interface NullLayerData {
  /** Visual size of null icon in editor */
  size: number;
}

/**
 * Create default null layer data
 */
export function createDefaultNullLayerData(): NullLayerData {
  return {
    size: 40,
  };
}

// ============================================================
// POSE LAYER DATA
// OpenPose skeleton for ControlNet conditioning
// ============================================================

export type PoseFormat = "coco18" | "body25" | "custom";

export interface PoseKeypoint {
  /** X position (0-1 normalized) */
  x: number;
  /** Y position (0-1 normalized) */
  y: number;
  /** Confidence/visibility (0-1, 0 = invisible) */
  confidence: number;
}

export interface Pose {
  /** Unique ID for this pose */
  id: string;
  /** Array of keypoints (length depends on format) */
  keypoints: PoseKeypoint[];
  /** Pose format */
  format: PoseFormat;
}

export interface PoseLayerData {
  /** All poses in this layer */
  poses: Pose[];
  /** Pose format */
  format: PoseFormat;
  /** Whether keypoints are normalized (0-1) */
  normalized: boolean;
  /** Bone line width */
  boneWidth: number;
  /** Keypoint circle radius */
  keypointRadius: number;
  /** Show keypoint circles */
  showKeypoints: boolean;
  /** Show bone connections */
  showBones: boolean;
  /** Show keypoint labels */
  showLabels: boolean;
  /** Use OpenPose standard colors */
  useDefaultColors: boolean;
  /** Custom bone color (when not using defaults) */
  customBoneColor: string;
  /** Custom keypoint color (when not using defaults) */
  customKeypointColor: string;
  /** Selected keypoint index for editing (-1 = none) */
  selectedKeypoint: number;
  /** Selected pose index for editing (-1 = none) */
  selectedPose: number;
  /** Animation - keypoints can be animated */
  animatedKeypoints?: Record<string, AnimatableProperty<Vec2>>;
}

/**
 * Create default pose layer data with T-pose
 */
export function createDefaultPoseLayerData(): PoseLayerData {
  return {
    poses: [
      {
        id: "pose-1",
        format: "coco18",
        keypoints: createDefaultTPose(),
      },
    ],
    format: "coco18",
    normalized: true,
    boneWidth: 4,
    keypointRadius: 4,
    showKeypoints: true,
    showBones: true,
    showLabels: false,
    useDefaultColors: true,
    customBoneColor: "#FFFFFF",
    customKeypointColor: "#FF0000",
    selectedKeypoint: -1,
    selectedPose: 0,
  };
}

/**
 * Create default T-pose keypoints (COCO 18-point format, normalized 0-1)
 */
function createDefaultTPose(): PoseKeypoint[] {
  return [
    { x: 0.5, y: 0.1, confidence: 1 }, // 0: nose
    { x: 0.5, y: 0.2, confidence: 1 }, // 1: neck
    { x: 0.35, y: 0.2, confidence: 1 }, // 2: right_shoulder
    { x: 0.2, y: 0.2, confidence: 1 }, // 3: right_elbow
    { x: 0.1, y: 0.2, confidence: 1 }, // 4: right_wrist
    { x: 0.65, y: 0.2, confidence: 1 }, // 5: left_shoulder
    { x: 0.8, y: 0.2, confidence: 1 }, // 6: left_elbow
    { x: 0.9, y: 0.2, confidence: 1 }, // 7: left_wrist
    { x: 0.4, y: 0.45, confidence: 1 }, // 8: right_hip
    { x: 0.4, y: 0.65, confidence: 1 }, // 9: right_knee
    { x: 0.4, y: 0.85, confidence: 1 }, // 10: right_ankle
    { x: 0.6, y: 0.45, confidence: 1 }, // 11: left_hip
    { x: 0.6, y: 0.65, confidence: 1 }, // 12: left_knee
    { x: 0.6, y: 0.85, confidence: 1 }, // 13: left_ankle
    { x: 0.45, y: 0.08, confidence: 1 }, // 14: right_eye
    { x: 0.55, y: 0.08, confidence: 1 }, // 15: left_eye
    { x: 0.4, y: 0.1, confidence: 1 }, // 16: right_ear
    { x: 0.6, y: 0.1, confidence: 1 }, // 17: left_ear
  ];
}

// ============================================================
// MATTE LAYER DATA - Procedural matte/mask generation
// ============================================================

export interface MatteLayerData {
  /** Matte extraction method */
  matteType:
    | "luminance"
    | "alpha"
    | "red"
    | "green"
    | "blue"
    | "hue"
    | "saturation";

  /** Invert the matte */
  invert: boolean;

  /** Threshold for matte cutoff */
  threshold: number;

  /** Feather/blur amount */
  feather: number;

  /** Expand/contract matte edges */
  expansion: number;

  /** Source layer ID (if extracting matte from another layer) */
  sourceLayerId: string | null;

  /** Preview mode */
  previewMode: "matte" | "composite" | "overlay";
}

// ============================================================
// LEGACY PARTICLE LAYER DATA (for backwards compatibility)
// ============================================================

export interface LegacyParticleLayerData {
  /** @deprecated Use ParticleLayerData with 'particles' type instead */
  emitterType: "point" | "line" | "circle" | "box";
  particleCount: number;
  lifetime: number;
  speed: number;
  spread: number;
  gravity: number;
  color: string;
  size: number;
}

// ============================================================
// VIDEO DATA - Full video playback control
// ============================================================

export interface VideoData {
  assetId: string | null;

  // Playback control
  loop: boolean; // Loop when reaching end
  pingPong?: boolean; // CODE IS TRUTH - not in defaults, code uses fallback
  startTime: number; // Start offset in source video (seconds)
  endTime?: number; // End time in source (undefined = full duration)
  speed: number; // Playback speed (1 = normal, 2 = 2x, 0.5 = half)

  // Speed mapping (professional feature for time manipulation)
  speedMapEnabled?: boolean; // CODE IS TRUTH - not in defaults
  speedMap?: AnimatableProperty<number>; // Maps comp time to video time
  /** @deprecated Use 'speedMapEnabled' instead */
  timeRemapEnabled?: boolean;
  /** @deprecated Use 'speedMap' instead */
  timeRemap?: AnimatableProperty<number>;

  // Timewarp - animatable speed with integration for smooth ramps
  // Unlike speedMap (which keyframes source time), Timewarp keyframes SPEED
  // and integrates the speed curve to calculate source frame
  timewarpEnabled?: boolean;
  timewarpSpeed?: AnimatableProperty<number>; // Speed % (100 = normal, 200 = 2x, 50 = 0.5x)
  timewarpMethod?: "whole-frames" | "frame-mix" | "pixel-motion";

  // Frame blending for speed changes
  frameBlending?: "none" | "frame-mix" | "pixel-motion"; // CODE IS TRUTH - not in defaults

  // Audio
  audioEnabled?: boolean; // CODE IS TRUTH - not in defaults
  audioLevel?: number; // 0-100 - CODE IS TRUTH - not in defaults

  // Poster frame (for thumbnails)
  posterFrame: number; // Frame to show when paused at start
}

// ============================================================
// NESTED COMP DATA - Nested composition reference
// ============================================================

export interface NestedCompData {
  compositionId: string | null; // Reference to composition in project.compositions - CODE IS TRUTH (defaults create null)

  // Speed mapping (time manipulation)
  speedMapEnabled?: boolean; // CODE IS TRUTH - not in defaults
  speedMap?: AnimatableProperty<number>; // Maps parent time to nested comp time
  /** @deprecated Use 'speedMapEnabled' instead */
  timeRemapEnabled?: boolean;
  /** @deprecated Use 'speedMap' instead */
  timeRemap?: AnimatableProperty<number>;

  // Timewarp - animatable speed with integration for smooth ramps
  timewarpEnabled?: boolean;
  timewarpSpeed?: AnimatableProperty<number>; // Speed % (100 = normal, 200 = 2x, 50 = 0.5x)
  timewarpMethod?: "whole-frames" | "frame-mix" | "pixel-motion";

  // Flatten transform (render nested layers in parent's 3D space)
  flattenTransform?: boolean; // CODE IS TRUTH - not in defaults

  // Override nested comp settings
  overrideFrameRate?: boolean; // CODE IS TRUTH - not in defaults
  frameRate?: number;
}

// ============================================================
// GENERATED MAP DATA (AI-powered layer generation)
// ============================================================

export interface GeneratedMapData {
  sourceLayerId: string; // Which layer to generate from
  mapType: GeneratedMapType;
  modelId: string; // Which model to use
  parameters: Record<string, JSONValue>;
  cachedResult?: string; // Base64 cached output
  lastGenerated?: string; // ISO timestamp
}

export type GeneratedMapType =
  | "depth" // DepthAnything V3
  | "normal" // NormalCrafter
  | "edge" // Canny/HED
  | "pose" // DWPose/OpenPose
  | "segment" // SAM2/MatSeg
  | "lineart" // Lineart extraction
  | "softedge"; // Soft edge detection

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
    direction: AnimatableProperty<number>; // Degrees
  };

  /** Invert the output (swap black/white) */
  inverted: boolean;

  /** Output levels (min/max black/white) */
  levels: {
    inputBlack: AnimatableProperty<number>; // 0-255
    inputWhite: AnimatableProperty<number>; // 0-255
    gamma: AnimatableProperty<number>; // 0.1-10
    outputBlack: AnimatableProperty<number>; // 0-255
    outputWhite: AnimatableProperty<number>; // 0-255
  };
}

/**
 * Available procedural pattern types
 */
export type ProceduralMatteType =
  | "linear_gradient" // Linear gradient (supports animated direction)
  | "radial_gradient" // Radial gradient (center point animatable)
  | "angular_gradient" // Conical/angular gradient
  | "ramp" // Animated wipe/reveal
  | "noise" // Fractal noise (Perlin/Simplex)
  | "checkerboard" // Animated checkerboard
  | "circle" // Animated circle (grow/shrink)
  | "rectangle" // Animated rectangle
  | "grid" // Grid pattern
  | "wave" // Wave pattern (sine/triangle)
  | "venetian_blinds" // Venetian blinds transition
  | "iris" // Iris wipe (circular reveal)
  | "radial_wipe" // Clock wipe
  | "dissolve"; // Random dissolve

/**
 * Pattern-specific parameters (varies by pattern type)
 */
export interface ProceduralMatteParams {
  // Linear/Angular gradient
  angle?: AnimatableProperty<number>; // Direction in degrees
  blend?: AnimatableProperty<number>; // Blend width (0-1)

  // Radial gradient
  centerX?: AnimatableProperty<number>; // Center X (0-1)
  centerY?: AnimatableProperty<number>; // Center Y (0-1)
  radius?: AnimatableProperty<number>; // Radius (0-2)

  // Ramp/Wipe
  progress?: AnimatableProperty<number>; // Wipe progress (0-1)
  softness?: AnimatableProperty<number>; // Edge softness

  // Noise
  scale?: AnimatableProperty<number>; // Noise scale
  octaves?: number; // Fractal octaves (1-8)
  persistence?: number; // Fractal persistence
  lacunarity?: number; // Fractal lacunarity
  seed?: number; // Random seed

  // Checkerboard/Grid
  tilesX?: AnimatableProperty<number>; // Horizontal tiles
  tilesY?: AnimatableProperty<number>; // Vertical tiles
  rotation?: AnimatableProperty<number>; // Pattern rotation

  // Circle/Rectangle
  width?: AnimatableProperty<number>; // Shape width
  height?: AnimatableProperty<number>; // Shape height
  cornerRadius?: AnimatableProperty<number>; // Corner radius

  // Wave
  frequency?: AnimatableProperty<number>; // Wave frequency
  amplitude?: AnimatableProperty<number>; // Wave amplitude
  waveType?: "sine" | "triangle" | "square" | "sawtooth";

  // Venetian blinds
  slats?: AnimatableProperty<number>; // Number of slats

  // Iris
  feather?: AnimatableProperty<number>; // Edge feather

  // Dissolve
  randomness?: AnimatableProperty<number>; // Dissolve randomness
  blockSize?: AnimatableProperty<number>; // Dissolve block size
}

/**
 * Create default procedural matte data
 */
export function createDefaultProceduralMatteData(
  patternType: ProceduralMatteType = "linear_gradient",
): ProceduralMatteData {
  return {
    patternType,
    parameters: {
      angle: createAnimatableProperty("Angle", 0, "number"),
      blend: createAnimatableProperty("Blend", 0.5, "number"),
      progress: createAnimatableProperty("Progress", 0.5, "number"),
      centerX: createAnimatableProperty("Center X", 0.5, "number"),
      centerY: createAnimatableProperty("Center Y", 0.5, "number"),
      radius: createAnimatableProperty("Radius", 1, "number"),
    },
    animation: {
      enabled: false,
      speed: createAnimatableProperty("Speed", 1, "number"),
      phase: createAnimatableProperty("Phase", 0, "number"),
      direction: createAnimatableProperty("Direction", 0, "number"),
    },
    inverted: false,
    levels: {
      inputBlack: createAnimatableProperty("Input Black", 0, "number"),
      inputWhite: createAnimatableProperty("Input White", 255, "number"),
      gamma: createAnimatableProperty("Gamma", 1, "number"),
      outputBlack: createAnimatableProperty("Output Black", 0, "number"),
      outputWhite: createAnimatableProperty("Output White", 255, "number"),
    },
  };
}

// Particle types moved to ./particles.ts
// Re-exported above for backwards compatibility

// ============================================================
// DEPTHFLOW PARALLAX LAYER DATA (matching akatz-ai)
// ============================================================

export type DepthflowPreset =
  | "static"
  | "zoom_in"
  | "zoom_out"
  | "dolly_zoom_in"
  | "dolly_zoom_out"
  | "pan_left"
  | "pan_right"
  | "pan_up"
  | "pan_down"
  | "circle_cw"
  | "circle_ccw"
  | "horizontal_swing"
  | "vertical_swing"
  | "custom";

export interface DepthflowLayerData {
  sourceLayerId: string | null; // CODE IS TRUTH - defaults create null
  depthLayerId: string | null; // CODE IS TRUTH - defaults create null
  config: DepthflowConfig;
  animatedZoom?: AnimatableProperty<number>;
  animatedOffsetX?: AnimatableProperty<number>;
  animatedOffsetY?: AnimatableProperty<number>;
  animatedRotation?: AnimatableProperty<number>;
  animatedDepthScale?: AnimatableProperty<number>;

  // Camera sync - drives depthflow from 3D camera motion
  cameraSyncEnabled?: boolean;
  cameraSyncLayerId?: string; // ID of the camera layer to sync from
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
export type ModelFormat =
  | "gltf"
  | "glb"
  | "obj"
  | "fbx"
  | "usd"
  | "usda"
  | "usdc"
  | "usdz"
  | "dae";

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
  duration: number; // In seconds
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
  scale:
    | AnimatableProperty<number>
    | {
        x: AnimatableProperty<number>;
        y: AnimatableProperty<number>;
        z: AnimatableProperty<number>;
      };

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
export type PointCloudFormat = "ply" | "pcd" | "las" | "laz" | "xyz" | "pts";

/** Point cloud coloring mode */
export type PointCloudColorMode =
  | "rgb" // Use embedded RGB colors
  | "intensity" // Color by intensity value
  | "height" // Color by Z position (height map)
  | "depth" // Color by distance from camera
  | "normal" // Color by surface normal
  | "classification" // Color by point classification (LAS)
  | "uniform"; // Single uniform color

/** Point cloud rendering mode */
export type PointCloudRenderMode =
  | "points" // Standard GL_POINTS
  | "circles" // Screen-space circles (anti-aliased)
  | "squares" // Screen-space squares
  | "splats"; // Gaussian splats (3DGS-style)

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

// Camera path following configuration
export interface CameraPathFollowing {
  enabled: boolean;
  pathLayerId: string; // ID of SplineLayer to follow
  parameter: AnimatableProperty<number>; // 0-1 position along path (can be keyframed)
  lookAhead: number; // Distance ahead to look (0-1 path units)
  bankingStrength: number; // How much to bank on turns (0-1)
  offsetY: number; // Height offset from path
  alignToPath: boolean; // Auto-orient camera along path tangent
  autoAdvance: boolean; // Automatically advance along path each frame
  autoAdvanceSpeed: number; // Speed of auto-advance (path units per frame)
}

// Camera shake configuration
export interface CameraShakeData {
  enabled: boolean;
  type: "handheld" | "impact" | "earthquake" | "subtle" | "custom";
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
  easing: "linear" | "ease-in" | "ease-out" | "ease-in-out" | "snap";
  holdStart: number;
  holdEnd: number;
}

// Autofocus configuration
export interface CameraAutoFocusData {
  enabled: boolean;
  mode: "center" | "point" | "nearest" | "farthest";
  focusPoint: { x: number; y: number };
  smoothing: number;
  threshold: number;
  sampleRadius: number;
}

// Path following configuration (simplified for AI tools)
export interface CameraPathFollowingData {
  enabled: boolean;
  splineLayerId: string | null;
  lookMode: "tangent" | "target" | "fixed";
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
  cameraId: string | null; // Reference to the Camera3D object - CODE IS TRUTH (defaults create null)
  isActiveCamera: boolean; // Is this the composition's active camera?

  // Camera3D object (inline storage)
  camera?: {
    type: "one-node" | "two-node";
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

// AudioParticleMapping is imported and re-exported from './particles'

// ============================================================
// EXTRACTED TEXTURE DATA (from MatSeg)
// ============================================================

export interface ExtractedTexture {
  id: string;
  sourceAssetId: string;
  region: BoundingBox;

  // The extracted tileable texture
  albedo: string; // Base64 PNG

  // Generated PBR maps
  pbr: {
    roughness: string;
    metallic: string;
    normal: string;
    height: string;
    ao: string;
  };

  // Metadata
  extractionMethod: "matseg" | "manual" | "sdxl";
  seamless: boolean;
  resolution: { width: number; height: number };
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
  format: "png_sequence";
  matteMode: "exclude_text" | "include_all";
  resolution: { width: number; height: number };
}

// ============================================================
// HELPER FUNCTIONS (unique to project.ts - others in modular files)
// ============================================================

/**
 * Normalize a layer's timing to use the new 'startFrame'/'endFrame' properties.
 * Handles migration from 'inPoint'/'outPoint' to 'startFrame'/'endFrame'.
 */
export function normalizeLayerTiming(layer: Layer): Layer {
  // If startFrame is missing but inPoint exists, use inPoint as startFrame
  if (layer.startFrame === undefined && layer.inPoint !== undefined) {
    layer.startFrame = layer.inPoint;
  }
  // If endFrame is missing but outPoint exists, use outPoint as endFrame
  if (layer.endFrame === undefined && layer.outPoint !== undefined) {
    layer.endFrame = layer.outPoint;
  }
  // Ensure both naming conventions exist for backwards compatibility
  if (layer.startFrame !== undefined && layer.inPoint === undefined) {
    layer.inPoint = layer.startFrame;
  }
  if (layer.endFrame !== undefined && layer.outPoint === undefined) {
    layer.outPoint = layer.endFrame;
  }
  return layer;
}

/**
 * Create a new empty project
 * @param width - Must be divisible by 8
 * @param height - Must be divisible by 8
 * @throws Error if dimensions are not divisible by 8
 */
export function createEmptyProject(
  width: number,
  height: number,
): LatticeProject {
  // Enforce divisibility by 8 constraint (required for AI video models)
  if (width % 8 !== 0 || height % 8 !== 0) {
    throw new Error(
      `Dimensions must be divisible by 8. Got ${width}x${height}. ` +
      `Use ${Math.round(width / 8) * 8}x${Math.round(height / 8) * 8} instead.`
    );
  }
  
  const mainCompId = "main";
  const compositionSettings: CompositionSettings = {
    width,
    height,
    frameCount: 81,
    fps: 16,
    duration: 81 / 16,
    backgroundColor: "#2d2d2d",
    autoResizeToContent: true,
    frameBlendingEnabled: false,
  };

  return {
    version: "1.0.0",
    schemaVersion: 2, // Current schema version - prevents migration on import
    meta: {
      name: "Untitled",
      created: new Date().toISOString(),
      modified: new Date().toISOString(),
    },
    // Multi-composition support
    compositions: {
      [mainCompId]: {
        id: mainCompId,
        name: "Main Comp",
        settings: compositionSettings,
        layers: [],
        currentFrame: 0,
        isNestedComp: false,
      },
    },
    mainCompositionId: mainCompId,
    // Legacy alias
    composition: compositionSettings,
    assets: {},
    layers: [],
    currentFrame: 0,
  };
}
