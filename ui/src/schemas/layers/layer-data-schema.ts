/**
 * Layer Data Schemas
 *
 * Zod schemas for all layer data types.
 * All numeric values use .finite() to reject NaN/Infinity.
 */

import { z } from "zod";
import {
  finiteNumber,
  positiveFinite,
  nonNegativeFinite,
  normalized01,
  positiveInt,
  nonNegativeInt,
  frameNumber,
  EntityIdSchema,
  NullableEntityIdSchema,
  Vec2Schema,
  Vec3Schema,
  HexColorSchema,
  RectSchema,
} from "./primitives-schema";
import { AnimatableNumberSchema, AnimatablePositionSchema, AnimatableVec3Schema } from "./animation-schema";

// ============================================================================
// Image Layer Data
// ============================================================================

export const ImageFitModeSchema = z.enum(["none", "contain", "cover", "fill"]);

export const ImageLayerDataSchema = z.object({
  assetId: NullableEntityIdSchema,
  fit: ImageFitModeSchema,
  cropEnabled: z.boolean().optional(),
  cropRect: RectSchema.optional(),
  sourceType: z.enum(["file", "generated", "segmented"]).optional(),
  segmentationMaskId: EntityIdSchema.optional(),
});

export type ImageLayerData = z.infer<typeof ImageLayerDataSchema>;

// ============================================================================
// Video Layer Data
// ============================================================================

export const TimewarpMethodSchema = z.enum(["whole-frames", "frame-mix", "pixel-motion"]);
export const FrameBlendingSchema = z.enum(["none", "frame-mix", "pixel-motion"]);

export const VideoDataSchema = z.object({
  assetId: NullableEntityIdSchema,
  loop: z.boolean(),
  pingPong: z.boolean().optional(),
  startTime: nonNegativeFinite,
  endTime: nonNegativeFinite.optional(),
  speed: positiveFinite,
  speedMapEnabled: z.boolean().optional(),
  speedMap: AnimatableNumberSchema.optional(),
  timeRemapEnabled: z.boolean().optional(),
  timeRemap: AnimatableNumberSchema.optional(),
  timewarpEnabled: z.boolean().optional(),
  timewarpSpeed: AnimatableNumberSchema.optional(),
  timewarpMethod: TimewarpMethodSchema.optional(),
  frameBlending: FrameBlendingSchema.optional(),
  audioEnabled: z.boolean().optional(),
  audioLevel: nonNegativeFinite.optional(),
  posterFrame: frameNumber,
});

export type VideoData = z.infer<typeof VideoDataSchema>;

// ============================================================================
// Depth Layer Data
// ============================================================================

export const DepthVisualizationModeSchema = z.enum([
  "grayscale",
  "colormap",
  "contour",
  "3d-mesh",
]);

export const DepthColorMapSchema = z.enum([
  "turbo",
  "viridis",
  "plasma",
  "inferno",
  "magma",
  "grayscale",
]);

export const DepthLayerDataSchema = z.object({
  assetId: NullableEntityIdSchema,
  visualizationMode: DepthVisualizationModeSchema,
  colorMap: DepthColorMapSchema,
  invert: z.boolean(),
  minDepth: finiteNumber,
  maxDepth: finiteNumber,
  autoNormalize: z.boolean(),
  contourLevels: positiveInt,
  contourColor: HexColorSchema,
  contourWidth: positiveFinite,
  meshDisplacement: AnimatableNumberSchema,
  meshResolution: positiveInt,
  wireframe: z.boolean(),
});

export type DepthLayerData = z.infer<typeof DepthLayerDataSchema>;

// ============================================================================
// Normal Layer Data
// ============================================================================

export const NormalVisualizationModeSchema = z.enum([
  "rgb",
  "hemisphere",
  "arrows",
  "lit",
]);

export const NormalLayerDataSchema = z.object({
  assetId: NullableEntityIdSchema,
  visualizationMode: NormalVisualizationModeSchema,
  format: z.enum(["opengl", "directx"]),
  flipX: z.boolean(),
  flipY: z.boolean(),
  flipZ: z.boolean(),
  arrowDensity: positiveFinite,
  arrowScale: positiveFinite,
  arrowColor: HexColorSchema,
  lightDirection: Vec3Schema,
  lightIntensity: nonNegativeFinite,
  ambientIntensity: nonNegativeFinite,
});

export type NormalLayerData = z.infer<typeof NormalLayerDataSchema>;

// ============================================================================
// Audio Layer Data
// ============================================================================

export const AudioMarkerSchema = z.object({
  frame: frameNumber,
  label: z.string(),
});

export const AudioLayerDataSchema = z.object({
  assetId: NullableEntityIdSchema,
  level: AnimatableNumberSchema,
  muted: z.boolean(),
  solo: z.boolean(),
  pan: AnimatableNumberSchema,
  startTime: nonNegativeFinite,
  loop: z.boolean(),
  speed: positiveFinite,
  showWaveform: z.boolean(),
  waveformColor: HexColorSchema,
  exposeFeatures: z.boolean(),
  waveform: z.array(finiteNumber).optional(),
  beats: z.array(frameNumber).optional(),
  tempo: positiveFinite.optional(),
  amplitudeData: z.array(finiteNumber).optional(),
  markers: z.array(AudioMarkerSchema).optional(),
});

export type AudioLayerData = z.infer<typeof AudioLayerDataSchema>;

// ============================================================================
// Generated Layer Data
// ============================================================================

export const GenerationTypeSchema = z.enum([
  "depth",
  "normal",
  "edge",
  "segment",
  "inpaint",
  "custom",
]);

export const GenerationStatusSchema = z.enum(["pending", "generating", "complete", "error"]);

export const GeneratedLayerDataSchema = z.object({
  generationType: GenerationTypeSchema,
  sourceLayerId: NullableEntityIdSchema,
  model: z.string(),
  parameters: z.record(z.unknown()), // Record<string, unknown>
  generatedAssetId: z.string().nullable(),
  status: GenerationStatusSchema,
  errorMessage: z.string().optional(),
  autoRegenerate: z.boolean(),
  lastGenerated: z.string().optional(),
});

export type GeneratedLayerData = z.infer<typeof GeneratedLayerDataSchema>;

// ============================================================================
// Solid Layer Data
// ============================================================================

export const SolidLayerDataSchema = z.object({
  color: HexColorSchema,
  width: positiveInt,
  height: positiveInt,
  shadowCatcher: z.boolean().optional(),
  shadowOpacity: z.number().finite().min(0).max(100).optional(),
  shadowColor: HexColorSchema.optional(),
  receiveShadow: z.boolean().optional(),
});

export type SolidLayerData = z.infer<typeof SolidLayerDataSchema>;

// ============================================================================
// Control Layer Data (Null replacement)
// ============================================================================

export const ControlLayerDataSchema = z.object({
  size: positiveFinite,
  showAxes: z.boolean(),
  showIcon: z.boolean(),
  iconShape: z.enum(["crosshair", "diamond", "circle", "square"]),
  iconColor: HexColorSchema,
});

export type ControlLayerData = z.infer<typeof ControlLayerDataSchema>;

// ============================================================================
// Null Layer Data (Deprecated)
// ============================================================================

export const NullLayerDataSchema = z.object({
  size: positiveFinite,
});

export type NullLayerData = z.infer<typeof NullLayerDataSchema>;

// ============================================================================
// Group Layer Data
// ============================================================================

export const GroupLayerDataSchema = z.object({
  collapsed: z.boolean(),
  color: z.string().nullable(),
  passThrough: z.boolean(),
  isolate: z.boolean(),
});

export type GroupLayerData = z.infer<typeof GroupLayerDataSchema>;

// ============================================================================
// Effect Layer Data (Adjustment Layer)
// ============================================================================

export const EffectLayerDataSchema = z.object({
  effectLayer: z.boolean(),
  /** @deprecated Use effectLayer instead */
  adjustmentLayer: z.boolean().optional(),
  color: HexColorSchema,
});

export type EffectLayerData = z.infer<typeof EffectLayerDataSchema>;

// ============================================================================
// Nested Comp Data
// ============================================================================

export const NestedCompDataSchema = z.object({
  compositionId: z.string().nullable(),
  speedMapEnabled: z.boolean().optional(),
  speedMap: AnimatableNumberSchema.optional(),
  timeRemapEnabled: z.boolean().optional(),
  timeRemap: AnimatableNumberSchema.optional(),
  timewarpEnabled: z.boolean().optional(),
  timewarpSpeed: AnimatableNumberSchema.optional(),
  timewarpMethod: TimewarpMethodSchema.optional(),
  flattenTransform: z.boolean().optional(),
  overrideFrameRate: z.boolean().optional(),
  frameRate: positiveFinite.optional(),
});

export type NestedCompData = z.infer<typeof NestedCompDataSchema>;

// ============================================================================
// Camera Layer Data
// ============================================================================

export const CameraTypeSchema = z.enum(["one-node", "two-node"]);

// Inline camera object storage
export const CameraObjectSchema = z.object({
  type: CameraTypeSchema,
  position: Vec3Schema,
  pointOfInterest: Vec3Schema,
  zoom: finiteNumber,
  depthOfField: z.boolean(),
  focusDistance: nonNegativeFinite,
  aperture: nonNegativeFinite,
  blurLevel: nonNegativeFinite,
  xRotation: finiteNumber,
  yRotation: finiteNumber,
  zRotation: finiteNumber,
});

export const DepthOfFieldSchema = z.object({
  enabled: z.boolean(),
  focusDistance: nonNegativeFinite,
  aperture: nonNegativeFinite,
  blurLevel: nonNegativeFinite,
});

export const IrisSchema = z.object({
  shape: z.number().finite().min(0).max(10),
  rotation: finiteNumber,
  roundness: normalized01,
  aspectRatio: z.number().finite().min(0.5).max(2),
  diffractionFringe: normalized01,
});

export const HighlightSchema = z.object({
  gain: normalized01,
  threshold: normalized01,
  saturation: normalized01,
});

// Camera path following (legacy)
export const CameraPathFollowingSchema = z.object({
  enabled: z.boolean(),
  pathLayerId: z.string(),
  parameter: AnimatableNumberSchema,
  lookAhead: finiteNumber,
  bankingStrength: finiteNumber,
  offsetY: finiteNumber,
  alignToPath: z.boolean(),
  autoAdvance: z.boolean(),
  autoAdvanceSpeed: finiteNumber,
});

// Simplified path following (for AI tools)
export const CameraPathFollowingConfigSchema = z.object({
  enabled: z.boolean(),
  splineLayerId: z.string().nullable(),
  lookMode: z.enum(["tangent", "target", "fixed"]),
  lookTarget: Vec3Schema.nullable(),
  startOffset: finiteNumber,
  speed: finiteNumber,
  bankAmount: finiteNumber,
  smoothing: finiteNumber,
});

// Camera shake effect
export const CameraShakeDataSchema = z.object({
  enabled: z.boolean(),
  type: z.enum(["handheld", "impact", "earthquake", "subtle", "custom"]),
  intensity: nonNegativeFinite,
  frequency: positiveFinite,
  rotationEnabled: z.boolean(),
  rotationScale: finiteNumber,
  seed: z.number().int(),
  decay: nonNegativeFinite,
  startFrame: frameNumber,
  duration: positiveFinite,
});

// Rack focus effect
export const CameraRackFocusDataSchema = z.object({
  enabled: z.boolean(),
  startDistance: nonNegativeFinite,
  endDistance: nonNegativeFinite,
  duration: positiveFinite,
  startFrame: frameNumber,
  easing: z.enum(["linear", "ease-in", "ease-out", "ease-in-out", "snap"]),
  holdStart: nonNegativeFinite,
  holdEnd: nonNegativeFinite,
});

// Autofocus settings
export const CameraAutoFocusDataSchema = z.object({
  enabled: z.boolean(),
  mode: z.enum(["center", "point", "nearest", "farthest"]),
  focusPoint: Vec2Schema,
  smoothing: normalized01,
  threshold: nonNegativeFinite,
  sampleRadius: positiveFinite,
});

// Trajectory keyframes storage
export const CameraTrajectoryKeyframesSchema = z.object({
  position: z.array(z.object({
    frame: frameNumber,
    position: Vec3Schema,
  })),
  pointOfInterest: z.array(z.object({
    frame: frameNumber,
    pointOfInterest: Vec3Schema,
  })),
  zoom: z.array(z.object({
    frame: frameNumber,
    zoom: finiteNumber,
  })).optional(),
});

export const CameraLayerDataSchema = z.object({
  cameraId: z.string().nullable(),
  isActiveCamera: z.boolean(),
  camera: CameraObjectSchema.optional(),
  animatedPosition: AnimatableVec3Schema.optional(),
  animatedTarget: AnimatableVec3Schema.optional(),
  animatedFov: AnimatableNumberSchema.optional(),
  animatedFocalLength: AnimatableNumberSchema.optional(),
  pathFollowing: CameraPathFollowingSchema.optional(),
  pathFollowingConfig: CameraPathFollowingConfigSchema.optional(),
  depthOfField: DepthOfFieldSchema.optional(),
  animatedFocusDistance: AnimatableNumberSchema.optional(),
  animatedAperture: AnimatableNumberSchema.optional(),
  animatedBlurLevel: AnimatableNumberSchema.optional(),
  shake: CameraShakeDataSchema.optional(),
  rackFocus: CameraRackFocusDataSchema.optional(),
  autoFocus: CameraAutoFocusDataSchema.optional(),
  trajectoryKeyframes: CameraTrajectoryKeyframesSchema.optional(),
});

export type CameraLayerData = z.infer<typeof CameraLayerDataSchema>;

// ============================================================================
// Light Layer Data
// ============================================================================

export const LightTypeSchema = z.enum([
  "point",
  "spot",
  "directional",
  "ambient",
]);

export const LightLayerDataSchema = z.object({
  lightType: LightTypeSchema,
  color: HexColorSchema,
  intensity: nonNegativeFinite,
  radius: positiveFinite,
  falloff: z.enum(["none", "linear", "quadratic", "smooth"]),
  falloffDistance: positiveFinite,
  castShadows: z.boolean(),
  shadowDarkness: z.number().finite().min(0).max(100),
  shadowDiffusion: nonNegativeFinite,
  // Spot light specific
  coneAngle: finiteNumber.optional(),
  coneFeather: z.number().finite().min(0).max(100).optional(),
  target: Vec3Schema.optional(),
});

export type LightLayerData = z.infer<typeof LightLayerDataSchema>;

// ============================================================================
// Pose Layer Data (OpenPose)
// ============================================================================

// Keypoint in a pose
export const PoseKeypointSchema = z.object({
  x: finiteNumber,
  y: finiteNumber,
  confidence: normalized01,
  visible: z.boolean(),
});

// Single pose (person)
export const PoseSchema = z.object({
  id: EntityIdSchema,
  keypoints: z.record(PoseKeypointSchema), // keypoint name -> position
  format: z.enum(["coco18", "body25", "custom"]),
});

export const PoseLayerDataSchema = z.object({
  poses: z.array(PoseSchema),
  format: z.enum(["coco18", "body25", "custom"]),
  normalized: z.boolean(),
  boneWidth: positiveFinite,
  keypointRadius: positiveFinite,
  showKeypoints: z.boolean(),
  showBones: z.boolean(),
  showLabels: z.boolean(),
  useDefaultColors: z.boolean(),
  customBoneColor: HexColorSchema,
  customKeypointColor: HexColorSchema,
  selectedKeypoint: z.number().int(),
  selectedPose: z.number().int(),
});

export type PoseLayerData = z.infer<typeof PoseLayerDataSchema>;

// ============================================================================
// Model Layer Data (3D models)
// ============================================================================

export const ModelLayerDataSchema = z.object({
  assetId: NullableEntityIdSchema,
  modelType: z.enum(["gltf", "obj", "fbx", "usd"]).optional(),
  scale: positiveFinite,
  autoCenter: z.boolean().optional(),
  autoNormalize: z.boolean().optional(),
  wireframe: z.boolean().optional(),
  doubleSided: z.boolean().optional(),
  materialOverride: z.string().optional(),
  animations: z.array(z.object({
    name: z.string(),
    duration: nonNegativeFinite,
    loop: z.boolean(),
  })).optional(),
  currentAnimation: z.string().optional(),
  animationSpeed: positiveFinite.optional(),
  animationTime: AnimatableNumberSchema.optional(),
});

export type ModelLayerData = z.infer<typeof ModelLayerDataSchema>;

// ============================================================================
// Point Cloud Layer Data
// ============================================================================

export const PointCloudLayerDataSchema = z.object({
  assetId: NullableEntityIdSchema,
  format: z.enum(["ply", "pcd", "las", "xyz"]).optional(),
  pointSize: positiveFinite,
  colorMode: z.enum(["rgb", "height", "intensity", "classification"]),
  colorMap: z.string().optional(),
  minHeight: finiteNumber.optional(),
  maxHeight: finiteNumber.optional(),
  decimation: z.number().finite().min(0).max(1).optional(),
  showBoundingBox: z.boolean().optional(),
});

export type PointCloudLayerData = z.infer<typeof PointCloudLayerDataSchema>;

// ============================================================================
// Matte Layer Data
// ============================================================================

export const MatteTypeEnumSchema = z.enum([
  "luminance",
  "alpha",
  "red",
  "green",
  "blue",
  "hue",
  "saturation",
]);

export const MatteLayerDataSchema = z.object({
  matteType: MatteTypeEnumSchema,
  invert: z.boolean(),
  threshold: finiteNumber,
  feather: nonNegativeFinite,
  expansion: finiteNumber,
  sourceLayerId: z.string().nullable(),
  previewMode: z.enum(["matte", "composite", "overlay"]),
});

export type MatteLayerData = z.infer<typeof MatteLayerDataSchema>;

// ============================================================================
// Procedural Matte Data (animated patterns for track mattes)
// ============================================================================

export const ProceduralMatteTypeSchema = z.enum([
  "linear_gradient",
  "radial_gradient",
  "angular_gradient",
  "ramp",
  "noise",
  "checkerboard",
  "circle",
  "rectangle",
  "grid",
  "wave",
  "venetian_blinds",
  "iris",
  "radial_wipe",
  "dissolve",
]);

export const ProceduralMatteParamsSchema = z.object({
  angle: AnimatableNumberSchema.optional(),
  blend: AnimatableNumberSchema.optional(),
  centerX: AnimatableNumberSchema.optional(),
  centerY: AnimatableNumberSchema.optional(),
  radius: AnimatableNumberSchema.optional(),
  progress: AnimatableNumberSchema.optional(),
  softness: AnimatableNumberSchema.optional(),
  scale: AnimatableNumberSchema.optional(),
  octaves: positiveInt.optional(),
  persistence: normalized01.optional(),
  lacunarity: positiveFinite.optional(),
  seed: z.number().int().optional(),
  tilesX: AnimatableNumberSchema.optional(),
  tilesY: AnimatableNumberSchema.optional(),
  rotation: AnimatableNumberSchema.optional(),
  width: AnimatableNumberSchema.optional(),
  height: AnimatableNumberSchema.optional(),
  cornerRadius: AnimatableNumberSchema.optional(),
  frequency: AnimatableNumberSchema.optional(),
  amplitude: AnimatableNumberSchema.optional(),
  waveType: z.enum(["sine", "triangle", "square", "sawtooth"]).optional(),
  slats: AnimatableNumberSchema.optional(),
  feather: AnimatableNumberSchema.optional(),
  randomness: AnimatableNumberSchema.optional(),
  blockSize: AnimatableNumberSchema.optional(),
});

export const ProceduralMatteDataSchema = z.object({
  patternType: ProceduralMatteTypeSchema,
  parameters: ProceduralMatteParamsSchema,
  animation: z.object({
    enabled: z.boolean(),
    speed: AnimatableNumberSchema,
    phase: AnimatableNumberSchema,
    direction: AnimatableNumberSchema,
  }),
  inverted: z.boolean(),
  levels: z.object({
    inputBlack: AnimatableNumberSchema,
    inputWhite: AnimatableNumberSchema,
    gamma: AnimatableNumberSchema,
    outputBlack: AnimatableNumberSchema,
    outputWhite: AnimatableNumberSchema,
  }),
});

export type ProceduralMatteData = z.infer<typeof ProceduralMatteDataSchema>;

// ============================================================================
// Depthflow Layer Data
// ============================================================================

export const DepthflowPresetSchema = z.enum([
  "static",
  "zoom_in",
  "zoom_out",
  "dolly_zoom_in",
  "dolly_zoom_out",
  "pan_left",
  "pan_right",
  "pan_up",
  "pan_down",
  "circle_cw",
  "circle_ccw",
  "horizontal_swing",
  "vertical_swing",
  "custom",
]);

export const DepthflowConfigSchema = z.object({
  preset: DepthflowPresetSchema,
  zoom: finiteNumber,
  offsetX: finiteNumber,
  offsetY: finiteNumber,
  rotation: finiteNumber,
  depthScale: finiteNumber,
  focusDepth: finiteNumber,
  dollyZoom: finiteNumber,
  orbitRadius: finiteNumber,
  orbitSpeed: finiteNumber,
  swingAmplitude: finiteNumber,
  swingFrequency: finiteNumber,
  edgeDilation: finiteNumber,
  inpaintEdges: z.boolean(),
});

export const CameraToDepthflowConfigSchema = z.object({
  sensitivityX: finiteNumber,
  sensitivityY: finiteNumber,
  sensitivityZ: finiteNumber,
  sensitivityRotation: finiteNumber,
  baseZoom: finiteNumber,
  invertX: z.boolean(),
  invertY: z.boolean(),
  zoomClamp: z.object({ min: finiteNumber, max: finiteNumber }),
  offsetClamp: z.object({ min: finiteNumber, max: finiteNumber }),
});

export const DepthflowLayerDataSchema = z.object({
  sourceLayerId: z.string().nullable(),
  depthLayerId: z.string().nullable(),
  config: DepthflowConfigSchema,
  animatedZoom: AnimatableNumberSchema.optional(),
  animatedOffsetX: AnimatableNumberSchema.optional(),
  animatedOffsetY: AnimatableNumberSchema.optional(),
  animatedRotation: AnimatableNumberSchema.optional(),
  animatedDepthScale: AnimatableNumberSchema.optional(),
  cameraSyncEnabled: z.boolean().optional(),
  cameraSyncLayerId: z.string().optional(),
  cameraSyncConfig: CameraToDepthflowConfigSchema.optional(),
});

export type DepthflowLayerData = z.infer<typeof DepthflowLayerDataSchema>;

// ============================================================================
// Generated Map Data (AI preprocessors)
// ============================================================================

export const GeneratedMapDataSchema = z.object({
  mapType: z.enum(["depth", "normal", "edge", "segment", "pose", "flow"]),
  sourceLayerId: NullableEntityIdSchema,
  preprocessor: z.string(),
  params: z.record(z.union([finiteNumber, z.string(), z.boolean()])).optional(),
  cachedFrames: z.record(EntityIdSchema).optional(),
  autoUpdate: z.boolean().optional(),
});

export type GeneratedMapData = z.infer<typeof GeneratedMapDataSchema>;

// ============================================================================
// Spline/Path Common Types
// ============================================================================

export const ControlPointTypeSchema = z.enum(["corner", "smooth", "symmetric"]);

export const HandleSchema = z.object({
  x: finiteNumber,
  y: finiteNumber,
}).nullable();

export const ControlPointSchema = z.object({
  id: EntityIdSchema,
  x: finiteNumber,
  y: finiteNumber,
  depth: finiteNumber.optional(),
  handleIn: HandleSchema,
  handleOut: HandleSchema,
  type: ControlPointTypeSchema,
  group: z.string().optional(),
});

export type ControlPoint = z.infer<typeof ControlPointSchema>;

// ============================================================================
// Spline Layer Data (visible bezier paths)
// ============================================================================

export const RGBAColorObjectSchema = z.object({
  r: normalized01,
  g: normalized01,
  b: normalized01,
  a: normalized01,
});

export const GradientStopSchema = z.object({
  position: normalized01,
  color: RGBAColorObjectSchema,
});

export const StrokeGradientSchema = z.object({
  type: z.enum(["linear", "radial"]),
  stops: z.array(GradientStopSchema),
  followPath: z.boolean().optional(),
  spread: z.number().finite().min(0).max(100).optional(),
  offsetKeyframes: z.array(z.object({
    frame: frameNumber,
    value: finiteNumber,
  })).optional(),
});

// AnimatableHandle for animated bezier handles
export const AnimatableHandleSchema = z.object({
  x: AnimatableNumberSchema,
  y: AnimatableNumberSchema,
});

// AnimatableControlPoint for keyframe-animated splines
export const AnimatableControlPointSchema = z.object({
  id: EntityIdSchema,
  x: AnimatableNumberSchema,
  y: AnimatableNumberSchema,
  depth: AnimatableNumberSchema.optional(),
  handleIn: AnimatableHandleSchema.nullable(),
  handleOut: AnimatableHandleSchema.nullable(),
  type: ControlPointTypeSchema,
  group: z.string().optional(),
});

// Path Effect Types
export const SplinePathEffectTypeSchema = z.enum([
  "offsetPath",
  "roughen",
  "wiggle",
  "zigzag",
  "wave",
]);

// Base path effect
export const SplinePathEffectBaseSchema = z.object({
  id: EntityIdSchema,
  type: SplinePathEffectTypeSchema,
  enabled: z.boolean(),
  order: nonNegativeInt,
});

// Offset Path Effect
export const OffsetPathEffectSchema = SplinePathEffectBaseSchema.extend({
  type: z.literal("offsetPath"),
  amount: AnimatableNumberSchema,
  lineJoin: z.enum(["miter", "round", "bevel"]),
  miterLimit: AnimatableNumberSchema,
});

// Roughen Effect
export const RoughenEffectSchema = SplinePathEffectBaseSchema.extend({
  type: z.literal("roughen"),
  size: AnimatableNumberSchema,
  detail: AnimatableNumberSchema,
  seed: z.number().int(),
});

// Wiggle Path Effect
export const WigglePathEffectSchema = SplinePathEffectBaseSchema.extend({
  type: z.literal("wiggle"),
  size: AnimatableNumberSchema,
  detail: AnimatableNumberSchema,
  temporalPhase: AnimatableNumberSchema,
  spatialPhase: AnimatableNumberSchema,
  correlation: AnimatableNumberSchema,
  seed: z.number().int(),
});

// ZigZag Effect
export const ZigZagEffectSchema = SplinePathEffectBaseSchema.extend({
  type: z.literal("zigzag"),
  size: AnimatableNumberSchema,
  ridgesPerSegment: AnimatableNumberSchema,
  pointType: z.enum(["corner", "smooth"]),
});

// Wave Effect
export const WaveEffectSchema = SplinePathEffectBaseSchema.extend({
  type: z.literal("wave"),
  amplitude: AnimatableNumberSchema,
  frequency: AnimatableNumberSchema,
  phase: AnimatableNumberSchema,
  waveType: z.enum(["sine", "triangle", "square"]),
});

// Union of all path effects
export const SplinePathEffectSchema = z.union([
  OffsetPathEffectSchema,
  RoughenEffectSchema,
  WigglePathEffectSchema,
  ZigZagEffectSchema,
  WaveEffectSchema,
]);

// LOD Level
export const LODLevelSchema = z.object({
  tolerance: positiveFinite,
  controlPoints: z.array(ControlPointSchema),
  pointCount: positiveInt,
  quality: nonNegativeInt.optional(),
  complexity: nonNegativeFinite.optional(),
});

// Spline LOD Settings
export const SplineLODSettingsSchema = z.object({
  enabled: z.boolean(),
  mode: z.enum(["zoom", "playback", "both"]),
  levels: z.array(LODLevelSchema),
  maxPointsForPreview: positiveInt,
  simplificationTolerance: positiveFinite,
  cullingEnabled: z.boolean(),
  cullMargin: nonNegativeFinite,
});

// Warp Pin (for mesh warp deformation)
export const WarpPinSchema = z.object({
  id: EntityIdSchema,
  position: Vec2Schema,
  originalPosition: Vec2Schema,
  offset: Vec2Schema,
  stiffness: normalized01,
  depth: finiteNumber.optional(),
  rotation: finiteNumber.optional(),
  scale: positiveFinite.optional(),
  selected: z.boolean().optional(),
});

// Audio Reactive config
export const SplineAudioReactiveSchema = z.object({
  enabled: z.boolean(),
  sourceLayerId: z.string(),
  property: z.string(),
  multiplier: finiteNumber,
  smoothing: nonNegativeFinite,
});

// Helper: union of static value or AnimatableProperty
const NumberOrAnimatableSchema = z.union([finiteNumber, AnimatableNumberSchema]);
const NumberArrayOrAnimatableSchema = z.union([
  z.array(nonNegativeFinite),
  z.any(), // AnimatableProperty<number[]> - complex type
]);

export const SplineDataSchema = z.object({
  pathData: z.string(),
  controlPoints: z.array(ControlPointSchema),
  closed: z.boolean(),
  strokeType: z.enum(["solid", "gradient"]).optional(),
  stroke: HexColorSchema,
  strokeGradient: StrokeGradientSchema.optional(),
  strokeWidth: nonNegativeFinite,
  strokeOpacity: z.number().finite().min(0).max(100).optional(),
  lineCap: z.enum(["butt", "round", "square"]).optional(),
  lineJoin: z.enum(["miter", "round", "bevel"]).optional(),
  strokeMiterLimit: positiveFinite.optional(),

  // Can be static or AnimatableProperty
  dashArray: NumberArrayOrAnimatableSchema.optional(),
  dashOffset: NumberOrAnimatableSchema.optional(),

  fill: HexColorSchema.optional(),
  fillOpacity: z.number().finite().min(0).max(100).optional(),

  // Trim paths - can be static or AnimatableProperty
  trimStart: NumberOrAnimatableSchema.optional(),
  trimEnd: NumberOrAnimatableSchema.optional(),
  trimOffset: NumberOrAnimatableSchema.optional(),

  // Path effects
  pathEffects: z.array(SplinePathEffectSchema).optional(),

  // Animated spline support
  animatedControlPoints: z.array(AnimatableControlPointSchema).optional(),
  animated: z.boolean().optional(),

  // Level of Detail
  lod: SplineLODSettingsSchema.optional(),

  // Mesh Warp deformation pins
  warpPins: z.array(WarpPinSchema).optional(),
  /** @deprecated Use warpPins instead */
  puppetPins: z.array(WarpPinSchema).optional(),

  // Audio-reactive animation
  audioReactive: SplineAudioReactiveSchema.optional(),
});

export type SplineData = z.infer<typeof SplineDataSchema>;

// ============================================================================
// Path Layer Data (invisible motion paths)
// ============================================================================

export const PathLayerDataSchema = z.object({
  pathData: z.string(),
  controlPoints: z.array(ControlPointSchema),
  closed: z.boolean(),
  showGuide: z.boolean(),
  guideColor: HexColorSchema,
  guideDashPattern: z.tuple([nonNegativeFinite, nonNegativeFinite]),
  animated: z.boolean().optional(),
});

export type PathLayerData = z.infer<typeof PathLayerDataSchema>;

// ============================================================================
// Text Layer Data
// ============================================================================

export const TextAlignSchema = z.enum(["left", "center", "right"]);
export const TextBaselineSchema = z.enum(["top", "middle", "bottom"]);
export const TextDirectionSchema = z.enum(["ltr", "rtl"]);

// Text Range Selector
export const TextRangeSelectorSchema = z.object({
  mode: z.enum(["percent", "index"]),
  start: AnimatableNumberSchema,
  end: AnimatableNumberSchema,
  offset: AnimatableNumberSchema,
  basedOn: z.enum(["characters", "characters_excluding_spaces", "words", "lines"]),
  shape: z.enum(["square", "ramp_up", "ramp_down", "triangle", "round", "smooth"]),
  selectorMode: z.enum(["add", "subtract", "intersect", "min", "max", "difference"]).optional(),
  amount: z.number().finite().min(0).max(100).optional(),
  smoothness: z.number().finite().min(0).max(100).optional(),
  randomizeOrder: z.boolean(),
  randomSeed: z.number().int(),
  ease: z.object({
    high: z.number().finite().min(0).max(100),
    low: z.number().finite().min(0).max(100),
  }),
});

// Wiggly Selector
export const TextWigglySelectorSchema = z.object({
  enabled: z.boolean(),
  mode: z.enum(["add", "subtract", "intersect", "min", "max", "difference"]),
  maxAmount: z.number().finite().min(0).max(100),
  minAmount: z.number().finite().min(0).max(100),
  wigglesPerSecond: positiveFinite,
  correlation: z.number().finite().min(0).max(100),
  lockDimensions: z.boolean(),
  basedOn: z.enum(["characters", "characters_excluding_spaces", "words", "lines"]),
  randomSeed: z.number().int(),
});

// Expression Selector
export const TextExpressionSelectorSchema = z.object({
  enabled: z.boolean(),
  mode: z.enum(["add", "subtract", "intersect", "min", "max", "difference"]),
  amountExpression: z.string(),
  basedOn: z.enum(["characters", "characters_excluding_spaces", "words", "lines"]),
});

// Text Animator Properties
export const TextAnimatorPropertiesSchema = z.object({
  position: AnimatablePositionSchema.optional(),
  anchorPoint: AnimatablePositionSchema.optional(),
  scale: AnimatablePositionSchema.optional(),
  rotation: AnimatableNumberSchema.optional(),
  skew: AnimatableNumberSchema.optional(),
  skewAxis: AnimatableNumberSchema.optional(),
  opacity: AnimatableNumberSchema.optional(),
  fillColor: z.any().optional(), // AnimatableProperty<string>
  fillBrightness: AnimatableNumberSchema.optional(),
  fillSaturation: AnimatableNumberSchema.optional(),
  fillHue: AnimatableNumberSchema.optional(),
  strokeColor: z.any().optional(), // AnimatableProperty<string>
  strokeWidth: AnimatableNumberSchema.optional(),
  tracking: AnimatableNumberSchema.optional(),
  lineAnchor: AnimatableNumberSchema.optional(),
  lineSpacing: AnimatableNumberSchema.optional(),
  characterOffset: AnimatableNumberSchema.optional(),
  blur: AnimatablePositionSchema.optional(),
}).passthrough(); // Allow additional properties

// Text Animator
export const TextAnimatorSchema = z.object({
  id: EntityIdSchema,
  name: z.string(),
  enabled: z.boolean(),
  rangeSelector: TextRangeSelectorSchema,
  wigglySelector: TextWigglySelectorSchema.optional(),
  expressionSelector: TextExpressionSelectorSchema.optional(),
  properties: TextAnimatorPropertiesSchema,
});

// Main TextData schema
export const TextDataSchema = z.object({
  // Source Text
  text: z.string(),
  fontFamily: z.string(),
  fontSize: positiveFinite,
  fontWeight: z.string(),
  fontStyle: z.enum(["normal", "italic"]),
  fill: HexColorSchema,
  stroke: HexColorSchema,
  strokeWidth: nonNegativeFinite,

  // Character Properties
  tracking: finiteNumber,
  lineSpacing: positiveFinite,
  lineAnchor: z.number().finite().min(0).max(100),
  characterOffset: z.number().int(),
  characterValue: z.number().int(),
  blur: Vec2Schema,

  // Paragraph (legacy aliases)
  letterSpacing: finiteNumber,
  lineHeight: positiveFinite,
  textAlign: TextAlignSchema,

  // Path Options
  pathLayerId: z.string().nullable(),
  pathReversed: z.boolean(),
  pathPerpendicularToPath: z.boolean(),
  pathForceAlignment: z.boolean(),
  pathFirstMargin: finiteNumber,
  pathLastMargin: finiteNumber,
  pathOffset: z.number().finite().min(0).max(100),
  pathAlign: z.enum(["left", "center", "right"]),

  // More Options (optional)
  anchorPointGrouping: z.enum(["character", "word", "line", "all"]).optional(),
  groupingAlignment: Vec2Schema.optional(),
  fillAndStroke: z.enum(["fill-over-stroke", "stroke-over-fill"]).optional(),
  interCharacterBlending: z.enum(["normal", "multiply", "screen", "overlay"]).optional(),

  // 3D Text
  perCharacter3D: z.boolean().optional(),

  // Advanced Character Properties
  baselineShift: finiteNumber.optional(),
  textCase: z.enum(["normal", "uppercase", "lowercase", "smallCaps"]).optional(),
  verticalAlign: z.enum(["normal", "superscript", "subscript"]).optional(),

  // OpenType Features
  kerning: z.boolean().optional(),
  ligatures: z.boolean().optional(),
  discretionaryLigatures: z.boolean().optional(),
  smallCapsFeature: z.boolean().optional(),
  stylisticSet: z.number().int().min(0).max(20).optional(),

  // Advanced Paragraph Properties
  firstLineIndent: finiteNumber.optional(),
  spaceBefore: finiteNumber.optional(),
  spaceAfter: finiteNumber.optional(),

  // Text Animators
  animators: z.array(TextAnimatorSchema).optional(),
});

export type TextData = z.infer<typeof TextDataSchema>;

// ============================================================================
// Shape Layer Data
// ============================================================================

// Import the correct ShapeLayerData schema from shapes-schema.ts
import { ShapeLayerDataSchema } from "./shapes-schema";

export { ShapeLayerDataSchema };
export type ShapeLayerData = z.infer<typeof ShapeLayerDataSchema>;

// ============================================================================
// Particle Layer Data (Legacy)
// ============================================================================

export const EmitterShapeSchema = z.enum([
  "point",
  "line",
  "circle",
  "box",
  "sphere",
  "ring",
  "spline",
  "depth-map",
  "mask",
  "cone",
  "image",
  "depthEdge",
]);

export const LegacyParticleLayerDataSchema = z.object({
  emitterType: z.enum(["point", "line", "circle", "box"]),
  particleCount: positiveInt,
  lifetime: positiveFinite,
  speed: nonNegativeFinite,
  spread: finiteNumber,
  gravity: finiteNumber,
  color: HexColorSchema,
  size: positiveFinite,
});

export type LegacyParticleLayerData = z.infer<typeof LegacyParticleLayerDataSchema>;

// ============================================================================
// Particle Layer Data (New system - matching RyanOnTheInside)
// ============================================================================

// Sprite configuration
export const SpriteConfigSchema = z.object({
  enabled: z.boolean(),
  imageUrl: z.string().nullable(),
  imageData: z.any().nullable(), // ImageBitmap | HTMLImageElement
  isSheet: z.boolean(),
  columns: positiveInt,
  rows: positiveInt,
  totalFrames: positiveInt,
  frameRate: positiveFinite,
  playMode: z.enum(["loop", "once", "pingpong", "random"]),
  billboard: z.boolean(),
  rotationEnabled: z.boolean(),
  rotationSpeed: finiteNumber,
  rotationSpeedVariance: nonNegativeFinite,
  alignToVelocity: z.boolean(),
});

// Spline path emission
export const SplinePathEmissionSchema = z.object({
  layerId: z.string(),
  emitMode: z.enum(["uniform", "random", "start", "end", "sequential"]),
  parameter: finiteNumber,
  alignToPath: z.boolean(),
  offset: finiteNumber,
  bidirectional: z.boolean(),
});

// Depth map emission
export const DepthMapEmissionSchema = z.object({
  sourceLayerId: z.string(),
  depthMin: normalized01,
  depthMax: normalized01,
  density: positiveFinite,
  velocityByDepth: z.boolean(),
  sizeByDepth: z.boolean(),
  depthMode: z.enum(["near-white", "near-black"]),
});

// Mask emission
export const MaskEmissionSchema = z.object({
  sourceLayerId: z.string(),
  threshold: normalized01,
  density: positiveFinite,
  channel: z.enum(["luminance", "alpha", "red", "green", "blue"]),
  invert: z.boolean(),
  sampleRate: positiveInt,
});

// Particle emitter config
export const ParticleEmitterConfigSchema = z.object({
  id: z.string(),
  name: z.string(),
  x: finiteNumber,
  y: finiteNumber,
  z: finiteNumber.optional(),
  direction: finiteNumber,
  spread: finiteNumber,
  speed: nonNegativeFinite,
  speedVariance: nonNegativeFinite,
  size: positiveFinite,
  sizeVariance: nonNegativeFinite,
  color: z.tuple([finiteNumber, finiteNumber, finiteNumber]), // RGB 0-1
  emissionRate: positiveFinite,
  initialBurst: nonNegativeInt,
  particleLifetime: positiveFinite,
  lifetimeVariance: nonNegativeFinite,
  enabled: z.boolean(),
  burstOnBeat: z.boolean(),
  burstCount: positiveInt,
  shape: EmitterShapeSchema,
  shapeRadius: nonNegativeFinite,
  shapeWidth: nonNegativeFinite,
  shapeHeight: nonNegativeFinite,
  shapeDepth: nonNegativeFinite,
  shapeInnerRadius: nonNegativeFinite,
  emitFromEdge: z.boolean(),
  emitFromVolume: z.boolean(),
  splinePath: SplinePathEmissionSchema.nullable(),
  depthMapEmission: DepthMapEmissionSchema.optional(),
  maskEmission: MaskEmissionSchema.optional(),
  sprite: SpriteConfigSchema,
  // Cone shape
  coneAngle: finiteNumber.optional(),
  coneRadius: nonNegativeFinite.optional(),
  coneLength: nonNegativeFinite.optional(),
  // Image shape
  imageSourceLayerId: z.string().optional(),
  emissionThreshold: normalized01.optional(),
  emitFromMaskEdge: z.boolean().optional(),
  // Depth edge
  depthSourceLayerId: z.string().optional(),
  depthEdgeThreshold: nonNegativeFinite.optional(),
  depthScale: finiteNumber.optional(),
  // Alternative names
  lifespan: positiveFinite.optional(),
  startSize: positiveFinite.optional(),
  endSize: positiveFinite.optional(),
  startColor: HexColorSchema.optional(),
  endColor: HexColorSchema.optional(),
  startOpacity: normalized01.optional(),
  endOpacity: normalized01.optional(),
  velocitySpread: nonNegativeFinite.optional(),
});

// Gravity well config
export const GravityWellConfigSchema = z.object({
  id: z.string(),
  name: z.string(),
  x: finiteNumber,
  y: finiteNumber,
  strength: finiteNumber,
  radius: positiveFinite,
  falloff: z.enum(["linear", "quadratic", "constant"]),
  enabled: z.boolean(),
});

// Vortex config
export const VortexConfigSchema = z.object({
  id: z.string(),
  name: z.string(),
  x: finiteNumber,
  y: finiteNumber,
  strength: finiteNumber,
  radius: positiveFinite,
  rotationSpeed: finiteNumber,
  inwardPull: finiteNumber,
  enabled: z.boolean(),
});

// Modulation config
export const ParticleModulationConfigSchema = z.object({
  id: z.string(),
  emitterId: z.string(),
  property: z.enum(["size", "speed", "opacity", "colorR", "colorG", "colorB"]),
  startValue: finiteNumber,
  endValue: finiteNumber,
  easing: z.string(),
});

// Turbulence field
export const TurbulenceFieldConfigSchema = z.object({
  id: z.string(),
  enabled: z.boolean(),
  scale: positiveFinite,
  strength: nonNegativeFinite,
  evolutionSpeed: nonNegativeFinite,
  octaves: positiveInt.optional(),
  persistence: normalized01.optional(),
  animationSpeed: nonNegativeFinite.optional(),
});

// Sub-emitter
export const SubEmitterConfigSchema = z.object({
  id: z.string(),
  parentEmitterId: z.string(),
  trigger: z.literal("death"),
  spawnCount: positiveInt,
  inheritVelocity: normalized01,
  size: positiveFinite,
  sizeVariance: nonNegativeFinite,
  lifetime: positiveFinite,
  speed: nonNegativeFinite,
  spread: finiteNumber,
  color: z.tuple([finiteNumber, finiteNumber, finiteNumber]),
  enabled: z.boolean(),
});

// Flocking config
export const FlockingConfigSchema = z.object({
  enabled: z.boolean(),
  separationWeight: z.number().finite().min(0).max(100),
  separationRadius: positiveFinite,
  alignmentWeight: z.number().finite().min(0).max(100),
  alignmentRadius: positiveFinite,
  cohesionWeight: z.number().finite().min(0).max(100),
  cohesionRadius: positiveFinite,
  maxSpeed: positiveFinite,
  maxForce: positiveFinite,
  perceptionAngle: finiteNumber,
});

// Collision plane
export const CollisionPlaneConfigSchema = z.object({
  id: z.string(),
  name: z.string().optional(),
  enabled: z.boolean(),
  point: Vec3Schema,
  normal: Vec3Schema,
  bounciness: normalized01,
  friction: normalized01,
});

// Collision config
export const CollisionConfigSchema = z.object({
  enabled: z.boolean(),
  particleCollision: z.boolean(),
  particleRadius: positiveFinite,
  bounciness: normalized01,
  friction: normalized01,
  boundaryEnabled: z.boolean(),
  boundaryBehavior: z.enum(["none", "kill", "bounce", "wrap", "stick"]),
  boundaryPadding: nonNegativeFinite,
  floorEnabled: z.boolean().optional(),
  floorY: normalized01.optional(),
  floorBehavior: z.enum(["none", "bounce", "stick", "kill"]).optional(),
  floorFriction: normalized01.optional(),
  ceilingEnabled: z.boolean().optional(),
  ceilingY: normalized01.optional(),
  planes: z.array(CollisionPlaneConfigSchema).optional(),
});

// Connection render config
export const ConnectionRenderConfigSchema = z.object({
  enabled: z.boolean(),
  maxDistance: positiveFinite,
  maxConnections: z.number().int().min(1).max(5),
  lineWidth: z.number().finite().min(0.5).max(3),
  lineOpacity: normalized01,
  fadeByDistance: z.boolean(),
  color: z.tuple([finiteNumber, finiteNumber, finiteNumber]).optional(),
});

// Audio binding
export const AudioBindingConfigSchema = z.object({
  id: z.string(),
  enabled: z.boolean(),
  feature: z.enum(["amplitude", "bass", "mid", "high", "beat", "spectralCentroid"]),
  smoothing: normalized01,
  min: finiteNumber,
  max: finiteNumber,
  target: z.enum(["emitter", "system", "forceField"]),
  targetId: z.string(),
  parameter: z.string(),
  outputMin: finiteNumber,
  outputMax: finiteNumber,
  curve: z.enum(["linear", "exponential", "logarithmic", "step"]),
  stepCount: positiveInt.optional(),
  triggerMode: z.enum(["continuous", "onThreshold", "onBeat"]).optional(),
  threshold: normalized01.optional(),
});

// Audio particle mapping
export const AudioParticleMappingSchema = z.object({
  feature: z.enum(["amplitude", "rms", "bass", "mid", "high", "onsets"]),
  parameter: z.enum(["emissionRate", "speed", "size", "gravity", "windStrength"]),
  emitterId: z.string().optional(),
  sensitivity: positiveFinite,
  smoothing: normalized01,
});

// Render options
export const ParticleRenderOptionsSchema = z.object({
  blendMode: z.enum(["normal", "additive", "multiply", "screen"]),
  renderTrails: z.boolean(),
  trailLength: positiveInt,
  trailOpacityFalloff: normalized01,
  particleShape: z.enum(["circle", "square", "triangle", "star"]),
  glowEnabled: z.boolean(),
  glowRadius: nonNegativeFinite,
  glowIntensity: nonNegativeFinite,
  motionBlur: z.boolean(),
  motionBlurStrength: normalized01,
  motionBlurSamples: z.number().int().min(1).max(16),
  connections: ConnectionRenderConfigSchema,
  spriteEnabled: z.boolean().optional(),
  spriteImageUrl: z.string().optional(),
  spriteColumns: positiveInt.optional(),
  spriteRows: positiveInt.optional(),
  spriteAnimate: z.boolean().optional(),
  spriteFrameRate: positiveFinite.optional(),
  spriteRandomStart: z.boolean().optional(),
  lodEnabled: z.boolean().optional(),
  lodDistances: z.array(finiteNumber).optional(),
  lodSizeMultipliers: z.array(finiteNumber).optional(),
  dofEnabled: z.boolean().optional(),
  dofFocusDistance: nonNegativeFinite.optional(),
  dofFocusRange: positiveFinite.optional(),
  dofMaxBlur: normalized01.optional(),
  shadowsEnabled: z.boolean().optional(),
  castShadows: z.boolean().optional(),
  receiveShadows: z.boolean().optional(),
  shadowSoftness: nonNegativeFinite.optional(),
  meshMode: z.enum(["billboard", "mesh"]).optional(),
  meshGeometry: z.enum(["cube", "sphere", "cylinder", "cone", "torus", "custom"]).optional(),
});

// System config
export const ParticleSystemLayerConfigSchema = z.object({
  maxParticles: positiveInt,
  gravity: finiteNumber,
  windStrength: finiteNumber,
  windDirection: finiteNumber,
  warmupPeriod: nonNegativeInt,
  respectMaskBoundary: z.boolean(),
  boundaryBehavior: z.enum(["bounce", "kill", "wrap"]),
  friction: normalized01,
  turbulenceFields: z.array(TurbulenceFieldConfigSchema).optional(),
  subEmitters: z.array(SubEmitterConfigSchema).optional(),
  useGPU: z.boolean().optional(),
});

// Visualization config
export const ParticleVisualizationConfigSchema = z.object({
  showHorizon: z.boolean(),
  showGrid: z.boolean(),
  showAxis: z.boolean(),
  gridSize: positiveFinite,
  gridDepth: positiveFinite,
});

// Particle group config
export const ParticleGroupConfigSchema = z.object({
  id: z.string(),
  name: z.string(),
  enabled: z.boolean(),
  color: z.tuple([finiteNumber, finiteNumber, finiteNumber, finiteNumber]),
  collisionMask: nonNegativeInt,
  connectionMask: nonNegativeInt,
});

// Spring structure
export const SpringStructureSchema = z.object({
  id: z.string(),
  type: z.enum(["cloth", "rope", "softbody", "custom"]),
  width: positiveInt.optional(),
  height: positiveInt.optional(),
  length: positiveInt.optional(),
  startParticle: nonNegativeInt,
  pinnedParticles: z.array(nonNegativeInt),
  stiffness: positiveFinite,
  damping: nonNegativeFinite,
  breakThreshold: nonNegativeFinite,
});

// Spring system config
export const SpringSystemConfigSchema = z.object({
  enabled: z.boolean(),
  useVerlet: z.boolean(),
  solverIterations: z.number().int().min(1).max(16),
  globalStiffness: positiveFinite,
  globalDamping: nonNegativeFinite,
  enableBreaking: z.boolean(),
  gravity: Vec3Schema,
  structures: z.array(SpringStructureSchema).optional(),
});

// SPH fluid config
export const SPHFluidConfigSchema = z.object({
  enabled: z.boolean(),
  preset: z.enum(["water", "honey", "lava", "gas", "custom"]),
  smoothingRadius: positiveFinite,
  restDensity: positiveFinite,
  gasConstant: positiveFinite,
  viscosity: nonNegativeFinite,
  surfaceTension: nonNegativeFinite,
  gravity: Vec3Schema,
  boundaryDamping: normalized01,
});

// LOD config
export const ParticleLODConfigSchema = z.object({
  enabled: z.boolean(),
  distances: z.array(finiteNumber),
  sizeMultipliers: z.array(finiteNumber),
});

// DOF config
export const ParticleDOFConfigSchema = z.object({
  enabled: z.boolean(),
  focusDistance: nonNegativeFinite,
  focusRange: positiveFinite,
  blurAmount: normalized01,
});

// Main ParticleLayerData schema
export const ParticleLayerDataSchema = z.object({
  systemConfig: ParticleSystemLayerConfigSchema,
  emitters: z.array(ParticleEmitterConfigSchema),
  gravityWells: z.array(GravityWellConfigSchema),
  vortices: z.array(VortexConfigSchema),
  modulations: z.array(ParticleModulationConfigSchema).optional(),
  renderOptions: ParticleRenderOptionsSchema,
  turbulenceFields: z.array(TurbulenceFieldConfigSchema).optional(),
  subEmitters: z.array(SubEmitterConfigSchema).optional(),
  flocking: FlockingConfigSchema.optional(),
  collision: CollisionConfigSchema.optional(),
  audioBindings: z.array(AudioBindingConfigSchema).optional(),
  audioMappings: z.array(AudioParticleMappingSchema).optional(),
  exportEnabled: z.boolean().optional(),
  exportFormat: z.string().optional(),
  speedMapEnabled: z.boolean().optional(),
  speedMap: AnimatableNumberSchema.optional(),
  visualization: ParticleVisualizationConfigSchema.optional(),
  groups: z.array(ParticleGroupConfigSchema).optional(),
  springConfig: SpringSystemConfigSchema.optional(),
  sphConfig: SPHFluidConfigSchema.optional(),
  lodConfig: ParticleLODConfigSchema.optional(),
  dofConfig: ParticleDOFConfigSchema.optional(),
  collisionPlanes: z.array(CollisionPlaneConfigSchema).optional(),
  particleGroups: z.array(ParticleGroupConfigSchema).optional(),
});

export type ParticleLayerData = z.infer<typeof ParticleLayerDataSchema>;

// ============================================================================
// Union of all layer data types
// ============================================================================

export const LayerDataSchema = z.union([
  ImageLayerDataSchema,
  VideoDataSchema,
  DepthLayerDataSchema,
  NormalLayerDataSchema,
  AudioLayerDataSchema,
  GeneratedLayerDataSchema,
  SolidLayerDataSchema,
  ControlLayerDataSchema,
  NullLayerDataSchema,
  GroupLayerDataSchema,
  EffectLayerDataSchema,
  NestedCompDataSchema,
  CameraLayerDataSchema,
  LightLayerDataSchema,
  PoseLayerDataSchema,
  ModelLayerDataSchema,
  PointCloudLayerDataSchema,
  MatteLayerDataSchema,
  ProceduralMatteDataSchema,
  DepthflowLayerDataSchema,
  GeneratedMapDataSchema,
  SplineDataSchema,
  PathLayerDataSchema,
  TextDataSchema,
  ShapeLayerDataSchema,
  LegacyParticleLayerDataSchema,
  ParticleLayerDataSchema,
  z.null(),
]);

export type LayerData = z.infer<typeof LayerDataSchema>;
