/**
 * Layer Data Schemas
 *
 * Zod schemas for all layer data types.
 * All numeric values use .finite() to reject NaN/Infinity.
 * Includes comprehensive validation constraints for security and data integrity.
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
import { AnimatableNumberSchema, AnimatablePositionSchema, AnimatableVec3Schema, PropertyValueSchema, createAnimatablePropertySchema } from "./animation-schema";
import {
  entityId,
  boundedArray,
  iso8601DateTime,
  MAX_NAME_LENGTH,
  MAX_STRING_LENGTH,
  MAX_ARRAY_LENGTH,
  MAX_ANIMATION_NAME_LENGTH,
  MAX_PATH_LENGTH,
  MAX_FONT_FAMILY_LENGTH,
  MAX_URL_LENGTH,
} from "../shared-validation";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Image Layer Data
// ════════════════════════════════════════════════════════════════════════════

export const ImageFitModeSchema = z.enum(["none", "contain", "cover", "fill"]);

export const ImageLayerDataSchema = z.object({
  assetId: NullableEntityIdSchema,
  fit: ImageFitModeSchema,
  cropEnabled: z.boolean().optional(),
  cropRect: RectSchema.optional(),
  sourceType: z.enum(["file", "generated", "segmented"]).optional(),
  segmentationMaskId: EntityIdSchema.optional(),
}).strict();

export type ImageLayerData = z.infer<typeof ImageLayerDataSchema>;

// ════════════════════════════════════════════════════════════════════════════
// Video Layer Data
// ════════════════════════════════════════════════════════════════════════════

export const TimewarpMethodSchema = z.enum(["whole-frames", "frame-mix", "pixel-motion"]);
export const FrameBlendingSchema = z.enum(["none", "frame-mix", "pixel-motion"]);

export const VideoDataSchema = z.object({
  assetId: NullableEntityIdSchema,
  loop: z.boolean(),
  pingPong: z.boolean().optional(),
  startTime: nonNegativeFinite,
  endTime: nonNegativeFinite.optional(),
  speed: positiveFinite.max(100), // Max 100x speed
  speedMapEnabled: z.boolean().optional(),
  speedMap: AnimatableNumberSchema.optional(),
  timeRemapEnabled: z.boolean().optional(),
  timeRemap: AnimatableNumberSchema.optional(),
  timewarpEnabled: z.boolean().optional(),
  timewarpSpeed: AnimatableNumberSchema.optional(),
  timewarpMethod: TimewarpMethodSchema.optional(),
  frameBlending: FrameBlendingSchema.optional(),
  audioEnabled: z.boolean().optional(),
  audioLevel: nonNegativeFinite.max(200).optional(), // Max 200% audio level
  posterFrame: frameNumber,
}).strict().refine(
  (data) => {
    // endTime should be >= startTime if both present
    if (data.endTime !== undefined && data.endTime < data.startTime) {
      return false;
    }
    return true;
  },
  { message: "endTime must be >= startTime", path: ["endTime"] }
);

export type VideoData = z.infer<typeof VideoDataSchema>;

// ════════════════════════════════════════════════════════════════════════════
// Depth Layer Data
// ════════════════════════════════════════════════════════════════════════════

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
  contourLevels: positiveInt.max(1000), // Max 1000 contour levels
  contourColor: HexColorSchema,
  contourWidth: positiveFinite.max(100), // Max 100px contour width
  meshDisplacement: AnimatableNumberSchema,
  meshResolution: positiveInt.max(1000), // Max 1000x1000 mesh resolution
  wireframe: z.boolean(),
}).strict().refine(
  (data) => {
    // maxDepth should be > minDepth
    return data.maxDepth > data.minDepth;
  },
  { message: "maxDepth must be greater than minDepth", path: ["maxDepth"] }
);

export type DepthLayerData = z.infer<typeof DepthLayerDataSchema>;

// ════════════════════════════════════════════════════════════════════════════
// Normal Layer Data
// ════════════════════════════════════════════════════════════════════════════

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
  arrowDensity: positiveFinite.max(1000), // Max 1000 arrows per unit
  arrowScale: positiveFinite.max(100), // Max 100x arrow scale
  arrowColor: HexColorSchema,
  lightDirection: Vec3Schema,
  lightIntensity: nonNegativeFinite.max(1000), // Max 1000% intensity
  ambientIntensity: nonNegativeFinite.max(1000), // Max 1000% intensity
}).strict();

export type NormalLayerData = z.infer<typeof NormalLayerDataSchema>;

// ════════════════════════════════════════════════════════════════════════════
// Audio Layer Data
// ════════════════════════════════════════════════════════════════════════════

export const AudioMarkerSchema = z.object({
  frame: frameNumber,
  label: z.string().min(1).max(MAX_NAME_LENGTH).trim(),
}).strict();

export const AudioLayerDataSchema = z.object({
  assetId: NullableEntityIdSchema,
  level: AnimatableNumberSchema,
  muted: z.boolean(),
  solo: z.boolean(),
  pan: AnimatableNumberSchema,
  startTime: nonNegativeFinite,
  loop: z.boolean(),
  speed: positiveFinite.max(100), // Max 100x speed
  showWaveform: z.boolean(),
  waveformColor: HexColorSchema,
  exposeFeatures: z.boolean(),
  waveform: boundedArray(finiteNumber, 1000000).optional(), // Max 1M waveform samples
  beats: boundedArray(frameNumber, 100000).optional(), // Max 100k beats
  tempo: positiveFinite.max(1000).optional(), // Max 1000 BPM
  amplitudeData: boundedArray(finiteNumber, 1000000).optional(), // Max 1M amplitude samples
  markers: boundedArray(AudioMarkerSchema, 10000).optional(), // Max 10k markers
}).strict();

export type AudioLayerData = z.infer<typeof AudioLayerDataSchema>;

// ════════════════════════════════════════════════════════════════════════════
// Generated Layer Data
// ════════════════════════════════════════════════════════════════════════════

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
  model: z.string().min(1).max(MAX_NAME_LENGTH).trim(),
  parameters: z.record(z.string().max(200), PropertyValueSchema).refine(
    (params) => Object.keys(params).length <= 1000,
    { message: "Maximum 1000 parameters allowed" }
  ),
  generatedAssetId: z.string().nullable(),
  status: GenerationStatusSchema,
  errorMessage: z.string().max(MAX_STRING_LENGTH).trim().optional(),
  autoRegenerate: z.boolean(),
  lastGenerated: iso8601DateTime.optional(),
}).strict();

export type GeneratedLayerData = z.infer<typeof GeneratedLayerDataSchema>;

// ════════════════════════════════════════════════════════════════════════════
// Solid Layer Data
// ════════════════════════════════════════════════════════════════════════════

export const SolidLayerDataSchema = z.object({
  color: HexColorSchema,
  width: positiveInt.max(16384), // Max reasonable dimension
  height: positiveInt.max(16384), // Max reasonable dimension
  shadowCatcher: z.boolean().optional(),
  shadowOpacity: z.number().finite().min(0).max(100).optional(),
  shadowColor: HexColorSchema.optional(),
  receiveShadow: z.boolean().optional(),
}).strict();

export type SolidLayerData = z.infer<typeof SolidLayerDataSchema>;

// ════════════════════════════════════════════════════════════════════════════
// Control Layer Data (Null replacement)
// ════════════════════════════════════════════════════════════════════════════

export const ControlLayerDataSchema = z.object({
  size: positiveFinite.max(10000), // Max 10k units
  showAxes: z.boolean(),
  showIcon: z.boolean(),
  iconShape: z.enum(["crosshair", "diamond", "circle", "square"]),
  iconColor: HexColorSchema,
}).strict();

export type ControlLayerData = z.infer<typeof ControlLayerDataSchema>;

// ════════════════════════════════════════════════════════════════════════════
// Null Layer Data (Deprecated)
// ════════════════════════════════════════════════════════════════════════════

export const NullLayerDataSchema = z.object({
  size: positiveFinite.max(10000), // Max 10k units
}).strict();

export type NullLayerData = z.infer<typeof NullLayerDataSchema>;

// ════════════════════════════════════════════════════════════════════════════
// Group Layer Data
// ════════════════════════════════════════════════════════════════════════════

export const GroupLayerDataSchema = z.object({
  collapsed: z.boolean(),
  color: z.string().max(50).nullable(), // Color string (hex or name)
  passThrough: z.boolean(),
  isolate: z.boolean(),
}).strict();

export type GroupLayerData = z.infer<typeof GroupLayerDataSchema>;

// ════════════════════════════════════════════════════════════════════════════
// Effect Layer Data (Adjustment Layer)
// ════════════════════════════════════════════════════════════════════════════

export const EffectLayerDataSchema = z.object({
  effectLayer: z.boolean(),
  /** @deprecated Use effectLayer instead */
  adjustmentLayer: z.boolean().optional(),
  color: HexColorSchema,
}).strict();

export type EffectLayerData = z.infer<typeof EffectLayerDataSchema>;

// ════════════════════════════════════════════════════════════════════════════
// Nested Comp Data
// ════════════════════════════════════════════════════════════════════════════

export const NestedCompDataSchema = z.object({
  compositionId: entityId.nullable(),
  speedMapEnabled: z.boolean().optional(),
  speedMap: AnimatableNumberSchema.optional(),
  timeRemapEnabled: z.boolean().optional(),
  timeRemap: AnimatableNumberSchema.optional(),
  timewarpEnabled: z.boolean().optional(),
  timewarpSpeed: AnimatableNumberSchema.optional(),
  timewarpMethod: TimewarpMethodSchema.optional(),
  flattenTransform: z.boolean().optional(),
  overrideFrameRate: z.boolean().optional(),
  frameRate: positiveFinite.max(120).optional(), // Max 120 FPS
}).strict();

export type NestedCompData = z.infer<typeof NestedCompDataSchema>;

// ════════════════════════════════════════════════════════════════════════════
// Camera Layer Data
// ════════════════════════════════════════════════════════════════════════════

export const CameraTypeSchema = z.enum(["one-node", "two-node"]);

// Inline camera object storage
export const CameraObjectSchema = z.object({
  type: CameraTypeSchema,
  position: Vec3Schema,
  pointOfInterest: Vec3Schema,
  zoom: finiteNumber.min(0.1).max(1000), // Reasonable zoom range
  depthOfField: z.boolean(),
  focusDistance: nonNegativeFinite.max(100000), // Max 100k units
  aperture: nonNegativeFinite.max(100), // Max f/100
  blurLevel: nonNegativeFinite.max(100), // Max 100% blur
  xRotation: finiteNumber,
  yRotation: finiteNumber,
  zRotation: finiteNumber,
}).strict();

export const DepthOfFieldSchema = z.object({
  enabled: z.boolean(),
  focusDistance: nonNegativeFinite.max(100000), // Max 100k units
  aperture: nonNegativeFinite.max(100), // Max f/100
  blurLevel: nonNegativeFinite.max(100), // Max 100% blur
}).strict();

export const IrisSchema = z.object({
  shape: z.number().finite().min(0).max(10),
  rotation: finiteNumber,
  roundness: normalized01,
  aspectRatio: z.number().finite().min(0.5).max(2),
  diffractionFringe: normalized01,
}).strict();

export const HighlightSchema = z.object({
  gain: normalized01,
  threshold: normalized01,
  saturation: normalized01,
}).strict();

// Camera path following (legacy)
export const CameraPathFollowingSchema = z.object({
  enabled: z.boolean(),
  pathLayerId: entityId,
  parameter: AnimatableNumberSchema,
  lookAhead: finiteNumber,
  bankingStrength: finiteNumber,
  offsetY: finiteNumber,
  alignToPath: z.boolean(),
  autoAdvance: z.boolean(),
  autoAdvanceSpeed: finiteNumber.max(100), // Max 100x speed
}).strict();

// Simplified path following (for AI tools)
export const CameraPathFollowingConfigSchema = z.object({
  enabled: z.boolean(),
  splineLayerId: entityId.nullable(),
  lookMode: z.enum(["tangent", "target", "fixed"]),
  lookTarget: Vec3Schema.nullable(),
  startOffset: finiteNumber,
  speed: finiteNumber.max(100), // Max 100x speed
  bankAmount: finiteNumber.max(90), // Max 90 degrees banking
  smoothing: normalized01,
}).strict();

// Camera shake effect
export const CameraShakeDataSchema = z.object({
  enabled: z.boolean(),
  type: z.enum(["handheld", "impact", "earthquake", "subtle", "custom"]),
  intensity: nonNegativeFinite.max(1000), // Max 1000% intensity
  frequency: positiveFinite.max(1000), // Max 1000 Hz
  rotationEnabled: z.boolean(),
  rotationScale: finiteNumber.max(100), // Max 100x rotation scale
  seed: z.number().int(),
  decay: nonNegativeFinite.max(100), // Max 100% decay
  startFrame: frameNumber,
  duration: positiveFinite.max(100000), // Max 100k frames duration
}).strict();

// Rack focus effect
export const CameraRackFocusDataSchema = z.object({
  enabled: z.boolean(),
  startDistance: nonNegativeFinite.max(100000), // Max 100k units
  endDistance: nonNegativeFinite.max(100000), // Max 100k units
  duration: positiveFinite.max(100000), // Max 100k frames
  startFrame: frameNumber,
  easing: z.enum(["linear", "ease-in", "ease-out", "ease-in-out", "snap"]),
  holdStart: nonNegativeFinite.max(100000), // Max 100k frames
  holdEnd: nonNegativeFinite.max(100000), // Max 100k frames
}).strict().refine(
  (data) => {
    // endDistance should be >= startDistance for consistency
    return data.endDistance >= data.startDistance;
  },
  { message: "endDistance should be >= startDistance", path: ["endDistance"] }
);

// Autofocus settings
export const CameraAutoFocusDataSchema = z.object({
  enabled: z.boolean(),
  mode: z.enum(["center", "point", "nearest", "farthest"]),
  focusPoint: Vec2Schema,
  smoothing: normalized01,
  threshold: nonNegativeFinite.max(1000), // Max threshold
  sampleRadius: positiveFinite.max(1000), // Max 1000px sample radius
}).strict();

// Trajectory keyframes storage
export const CameraTrajectoryKeyframesSchema = z.object({
  position: boundedArray(z.object({
    frame: frameNumber,
    position: Vec3Schema,
  }).strict(), 100000), // Max 100k position keyframes
  pointOfInterest: boundedArray(z.object({
    frame: frameNumber,
    pointOfInterest: Vec3Schema,
  }).strict(), 100000), // Max 100k POI keyframes
  zoom: boundedArray(z.object({
    frame: frameNumber,
    zoom: finiteNumber,
  }).strict(), 100000).optional(), // Max 100k zoom keyframes
}).strict();

export const CameraLayerDataSchema = z.object({
  cameraId: entityId.nullable(),
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
}).strict();

export type CameraLayerData = z.infer<typeof CameraLayerDataSchema>;

// ════════════════════════════════════════════════════════════════════════════
// Light Layer Data
// ════════════════════════════════════════════════════════════════════════════

export const LightTypeSchema = z.enum([
  "point",
  "spot",
  "directional",
  "ambient",
]);

export const LightLayerDataSchema = z.object({
  lightType: LightTypeSchema,
  color: HexColorSchema,
  intensity: nonNegativeFinite.max(10000), // Max 10000% intensity
  radius: positiveFinite.max(10000), // Max 10k units radius
  falloff: z.enum(["none", "linear", "quadratic", "smooth"]),
  falloffDistance: positiveFinite.max(100000), // Max 100k units
  castShadows: z.boolean(),
  shadowDarkness: z.number().finite().min(0).max(100),
  shadowDiffusion: nonNegativeFinite.max(1000), // Max 1000px diffusion
  // Spot light specific
  coneAngle: finiteNumber.min(0).max(180).optional(), // Max 180 degrees
  coneFeather: z.number().finite().min(0).max(100).optional(),
  target: Vec3Schema.optional(),
}).strict();

export type LightLayerData = z.infer<typeof LightLayerDataSchema>;

// ════════════════════════════════════════════════════════════════════════════
// Pose Layer Data (OpenPose)
// ════════════════════════════════════════════════════════════════════════════

// Keypoint in a pose
export const PoseKeypointSchema = z.object({
  x: finiteNumber,
  y: finiteNumber,
  confidence: normalized01,
  visible: z.boolean(),
}).strict();

// Single pose (person)
export const PoseSchema = z.object({
  id: EntityIdSchema,
  keypoints: z.record(z.string().max(100), PoseKeypointSchema).refine(
    (keypoints) => Object.keys(keypoints).length <= 100, // Max 100 keypoints per pose
    { message: "Maximum 100 keypoints per pose" }
  ),
  format: z.enum(["coco18", "body25", "custom"]),
}).strict();

export const PoseLayerDataSchema = z.object({
  poses: boundedArray(PoseSchema, 1000), // Max 1000 poses per layer
  format: z.enum(["coco18", "body25", "custom"]),
  normalized: z.boolean(),
  boneWidth: positiveFinite.max(100), // Max 100px bone width
  keypointRadius: positiveFinite.max(100), // Max 100px keypoint radius
  showKeypoints: z.boolean(),
  showBones: z.boolean(),
  showLabels: z.boolean(),
  useDefaultColors: z.boolean(),
  customBoneColor: HexColorSchema,
  customKeypointColor: HexColorSchema,
  selectedKeypoint: z.number().int().min(-1), // -1 = none selected
  selectedPose: z.number().int().min(-1), // -1 = none selected
}).strict();

export type PoseLayerData = z.infer<typeof PoseLayerDataSchema>;

// ════════════════════════════════════════════════════════════════════════════
// Model Layer Data (3D models)
// ════════════════════════════════════════════════════════════════════════════

export const ModelLayerDataSchema = z.object({
  assetId: NullableEntityIdSchema,
  modelType: z.enum(["gltf", "obj", "fbx", "usd"]).optional(),
  scale: positiveFinite.max(1000), // Max 1000x scale
  autoCenter: z.boolean().optional(),
  autoNormalize: z.boolean().optional(),
  wireframe: z.boolean().optional(),
  doubleSided: z.boolean().optional(),
  materialOverride: z.string().max(MAX_NAME_LENGTH).trim().optional(),
  animations: boundedArray(z.object({
    name: z.string().min(1).max(MAX_ANIMATION_NAME_LENGTH).trim(),
    duration: nonNegativeFinite.max(86400), // Max 24 hours
    loop: z.boolean(),
  }).strict(), 1000).optional(), // Max 1000 animations
  currentAnimation: z.string().max(MAX_ANIMATION_NAME_LENGTH).trim().optional(),
  animationSpeed: positiveFinite.max(100).optional(), // Max 100x speed
  animationTime: AnimatableNumberSchema.optional(),
}).strict();

export type ModelLayerData = z.infer<typeof ModelLayerDataSchema>;

// ════════════════════════════════════════════════════════════════════════════
// Point Cloud Layer Data
// ════════════════════════════════════════════════════════════════════════════

export const PointCloudLayerDataSchema = z.object({
  assetId: NullableEntityIdSchema,
  format: z.enum(["ply", "pcd", "las", "xyz"]).optional(),
  pointSize: positiveFinite.max(100), // Max 100px point size
  colorMode: z.enum(["rgb", "height", "intensity", "classification"]),
  colorMap: z.string().max(MAX_NAME_LENGTH).trim().optional(),
  minHeight: finiteNumber.optional(),
  maxHeight: finiteNumber.optional(),
  decimation: z.number().finite().min(0).max(1).optional(),
  showBoundingBox: z.boolean().optional(),
}).strict().refine(
  (data) => {
    // maxHeight should be > minHeight if both present
    if (data.maxHeight !== undefined && data.minHeight !== undefined && data.maxHeight <= data.minHeight) {
      return false;
    }
    return true;
  },
  { message: "maxHeight must be greater than minHeight", path: ["maxHeight"] }
);

export type PointCloudLayerData = z.infer<typeof PointCloudLayerDataSchema>;

// ════════════════════════════════════════════════════════════════════════════
// Matte Layer Data
// ════════════════════════════════════════════════════════════════════════════

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
  threshold: finiteNumber.min(0).max(255), // 0-255 range
  feather: nonNegativeFinite.max(1000), // Max 1000px feather
  expansion: finiteNumber.max(1000), // Max 1000px expansion
  sourceLayerId: entityId.nullable(),
  previewMode: z.enum(["matte", "composite", "overlay"]),
}).strict();

export type MatteLayerData = z.infer<typeof MatteLayerDataSchema>;

// ════════════════════════════════════════════════════════════════════════════
// Procedural Matte Data (animated patterns for track mattes)
// ════════════════════════════════════════════════════════════════════════════

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
  octaves: positiveInt.max(10).optional(), // Max 10 octaves
  persistence: normalized01.optional(),
  lacunarity: positiveFinite.max(10).optional(), // Max 10x lacunarity
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
}).strict();

export const ProceduralMatteDataSchema = z.object({
  patternType: ProceduralMatteTypeSchema,
  parameters: ProceduralMatteParamsSchema,
  animation: z.object({
    enabled: z.boolean(),
    speed: AnimatableNumberSchema,
    phase: AnimatableNumberSchema,
    direction: AnimatableNumberSchema,
  }).strict(),
  inverted: z.boolean(),
  levels: z.object({
    inputBlack: AnimatableNumberSchema,
    inputWhite: AnimatableNumberSchema,
    gamma: AnimatableNumberSchema,
    outputBlack: AnimatableNumberSchema,
    outputWhite: AnimatableNumberSchema,
  }).strict().refine(
    (levels) => {
      // inputWhite should be > inputBlack
      return levels.inputWhite > levels.inputBlack;
    },
    { message: "inputWhite must be greater than inputBlack", path: ["inputWhite"] }
  ).refine(
    (levels) => {
      // outputWhite should be > outputBlack
      return levels.outputWhite > levels.outputBlack;
    },
    { message: "outputWhite must be greater than outputBlack", path: ["outputWhite"] }
  ),
}).strict();

export type ProceduralMatteData = z.infer<typeof ProceduralMatteDataSchema>;

// ════════════════════════════════════════════════════════════════════════════
// Depthflow Layer Data
// ════════════════════════════════════════════════════════════════════════════

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
  zoom: finiteNumber.min(0.1).max(100), // Reasonable zoom range
  offsetX: finiteNumber.max(10000), // Max 10k px offset
  offsetY: finiteNumber.max(10000), // Max 10k px offset
  rotation: finiteNumber,
  depthScale: finiteNumber.max(100), // Max 100x depth scale
  focusDepth: finiteNumber.max(100000), // Max 100k units
  dollyZoom: finiteNumber.max(100), // Max 100x dolly zoom
  orbitRadius: finiteNumber.max(100000), // Max 100k units
  orbitSpeed: finiteNumber.max(100), // Max 100x speed
  swingAmplitude: finiteNumber.max(10000), // Max 10k px amplitude
  swingFrequency: finiteNumber.max(100), // Max 100 Hz
  edgeDilation: finiteNumber.max(1000), // Max 1000px dilation
  inpaintEdges: z.boolean(),
}).strict();

export const CameraToDepthflowConfigSchema = z.object({
  sensitivityX: finiteNumber.max(100), // Max 100x sensitivity
  sensitivityY: finiteNumber.max(100), // Max 100x sensitivity
  sensitivityZ: finiteNumber.max(100), // Max 100x sensitivity
  sensitivityRotation: finiteNumber.max(100), // Max 100x sensitivity
  baseZoom: finiteNumber.min(0.1).max(100), // Reasonable zoom range
  invertX: z.boolean(),
  invertY: z.boolean(),
  zoomClamp: z.object({ min: finiteNumber, max: finiteNumber }).strict().refine(
    (clamp) => clamp.max > clamp.min,
    { message: "zoomClamp max must be greater than min" }
  ),
  offsetClamp: z.object({ min: finiteNumber, max: finiteNumber }).strict().refine(
    (clamp) => clamp.max > clamp.min,
    { message: "offsetClamp max must be greater than min" }
  ),
}).strict();

export const DepthflowLayerDataSchema = z.object({
  sourceLayerId: entityId.nullable(),
  depthLayerId: entityId.nullable(),
  config: DepthflowConfigSchema,
  animatedZoom: AnimatableNumberSchema.optional(),
  animatedOffsetX: AnimatableNumberSchema.optional(),
  animatedOffsetY: AnimatableNumberSchema.optional(),
  animatedRotation: AnimatableNumberSchema.optional(),
  animatedDepthScale: AnimatableNumberSchema.optional(),
  cameraSyncEnabled: z.boolean().optional(),
  cameraSyncLayerId: entityId.optional(),
  cameraSyncConfig: CameraToDepthflowConfigSchema.optional(),
}).strict();

export type DepthflowLayerData = z.infer<typeof DepthflowLayerDataSchema>;

// ════════════════════════════════════════════════════════════════════════════
// Generated Map Data (AI preprocessors)
// ════════════════════════════════════════════════════════════════════════════

export const GeneratedMapDataSchema = z.object({
  mapType: z.enum(["depth", "normal", "edge", "segment", "pose", "flow"]),
  sourceLayerId: NullableEntityIdSchema,
  preprocessor: z.string().min(1).max(MAX_NAME_LENGTH).trim(),
  params: z.record(z.string().max(200), z.union([finiteNumber, z.string().max(MAX_STRING_LENGTH), z.boolean()])).refine(
    (params) => Object.keys(params).length <= 1000,
    { message: "Maximum 1000 parameters allowed" }
  ).optional(),
  cachedFrames: z.record(z.string().max(200), EntityIdSchema).refine(
    (frames) => Object.keys(frames).length <= 100000,
    { message: "Maximum 100k cached frames allowed" }
  ).optional(),
  autoUpdate: z.boolean().optional(),
}).strict();

export type GeneratedMapData = z.infer<typeof GeneratedMapDataSchema>;

// ════════════════════════════════════════════════════════════════════════════
// Spline/Path Common Types
// ════════════════════════════════════════════════════════════════════════════

export const ControlPointTypeSchema = z.enum(["corner", "smooth", "symmetric"]);

export const HandleSchema = z.object({
  x: finiteNumber,
  y: finiteNumber,
}).strict().nullable();

export const ControlPointSchema = z.object({
  id: EntityIdSchema,
  x: finiteNumber,
  y: finiteNumber,
  depth: finiteNumber.optional(),
  handleIn: HandleSchema,
  handleOut: HandleSchema,
  type: ControlPointTypeSchema,
  group: z.string().max(MAX_NAME_LENGTH).trim().optional(),
}).strict();

export type ControlPoint = z.infer<typeof ControlPointSchema>;

// ════════════════════════════════════════════════════════════════════════════
// Spline Layer Data (visible bezier paths)
// ════════════════════════════════════════════════════════════════════════════

export const RGBAColorObjectSchema = z.object({
  r: normalized01,
  g: normalized01,
  b: normalized01,
  a: normalized01,
}).strict();

export const GradientStopSchema = z.object({
  position: normalized01,
  color: RGBAColorObjectSchema,
}).strict();

export const StrokeGradientSchema = z.object({
  type: z.enum(["linear", "radial"]),
  stops: boundedArray(GradientStopSchema, 100), // Max 100 stops
  followPath: z.boolean().optional(),
  spread: z.number().finite().min(0).max(100).optional(),
  offsetKeyframes: boundedArray(z.object({
    frame: frameNumber,
    value: finiteNumber,
  }).strict(), 10000).optional(), // Max 10k offset keyframes
}).strict().refine(
  (data) => {
    // Must have at least 2 stops
    if (data.stops.length < 2) {
      return false;
    }
    // Stops should be sorted by position
    for (let i = 1; i < data.stops.length; i++) {
      if (data.stops[i].position < data.stops[i - 1].position) {
        return false;
      }
    }
    return true;
  },
  { message: "Gradient must have at least 2 stops, and stops must be sorted by position", path: ["stops"] }
);

// AnimatableHandle for animated bezier handles
export const AnimatableHandleSchema = z.object({
  x: AnimatableNumberSchema,
  y: AnimatableNumberSchema,
}).strict();

// AnimatableControlPoint for keyframe-animated splines
export const AnimatableControlPointSchema = z.object({
  id: EntityIdSchema,
  x: AnimatableNumberSchema,
  y: AnimatableNumberSchema,
  depth: AnimatableNumberSchema.optional(),
  handleIn: AnimatableHandleSchema.nullable(),
  handleOut: AnimatableHandleSchema.nullable(),
  type: ControlPointTypeSchema,
  group: z.string().max(MAX_NAME_LENGTH).trim().optional(),
}).strict();

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
  order: nonNegativeInt.max(1000), // Max 1000 effects per spline
}).strict();

// Offset Path Effect
export const OffsetPathEffectSchema = SplinePathEffectBaseSchema.extend({
  type: z.literal("offsetPath"),
  amount: AnimatableNumberSchema,
  lineJoin: z.enum(["miter", "round", "bevel"]),
  miterLimit: AnimatableNumberSchema, // Miter limit (no max on animatable)
}).strict();

// Roughen Effect
export const RoughenEffectSchema = SplinePathEffectBaseSchema.extend({
  type: z.literal("roughen"),
  size: AnimatableNumberSchema,
  detail: AnimatableNumberSchema, // Detail level (no max on animatable)
  seed: z.number().int(),
}).strict();

// Wiggle Path Effect
export const WigglePathEffectSchema = SplinePathEffectBaseSchema.extend({
  type: z.literal("wiggle"),
  size: AnimatableNumberSchema,
  detail: AnimatableNumberSchema, // Detail level (no max on animatable)
  temporalPhase: AnimatableNumberSchema,
  spatialPhase: AnimatableNumberSchema,
  correlation: AnimatableNumberSchema,
  seed: z.number().int(),
}).strict();

// ZigZag Effect
export const ZigZagEffectSchema = SplinePathEffectBaseSchema.extend({
  type: z.literal("zigzag"),
  size: AnimatableNumberSchema,
  ridgesPerSegment: AnimatableNumberSchema, // Ridges per segment (no max on animatable)
  pointType: z.enum(["corner", "smooth"]),
}).strict();

// Wave Effect
export const WaveEffectSchema = SplinePathEffectBaseSchema.extend({
  type: z.literal("wave"),
  amplitude: AnimatableNumberSchema,
  frequency: AnimatableNumberSchema, // Frequency (no max on animatable)
  phase: AnimatableNumberSchema,
  waveType: z.enum(["sine", "triangle", "square"]),
}).strict();

// Union of all path effects
export const SplinePathEffectSchema = z.union([
  OffsetPathEffectSchema,
  RoughenEffectSchema,
  WigglePathEffectSchema,
  ZigZagEffectSchema,
  WaveEffectSchema,
]);

//                                                                  // lod // l
export const LODLevelSchema = z.object({
  tolerance: positiveFinite.max(1000), // Max 1000px tolerance
  controlPoints: boundedArray(ControlPointSchema, 100000), // Max 100k control points per LOD level
  pointCount: positiveInt.max(1000000), // Max 1M points
  quality: nonNegativeInt.max(100).optional(), // Max 100 quality level
  complexity: nonNegativeFinite.max(1000).optional(), // Max complexity score
}).strict();

// Spline LOD Settings
export const SplineLODSettingsSchema = z.object({
  enabled: z.boolean(),
  mode: z.enum(["zoom", "playback", "both"]),
  levels: boundedArray(LODLevelSchema, 100), // Max 100 LOD levels
  maxPointsForPreview: positiveInt.max(1000000), // Max 1M points for preview
  simplificationTolerance: positiveFinite.max(1000), // Max 1000px tolerance
  cullingEnabled: z.boolean(),
  cullMargin: nonNegativeFinite.max(10000), // Max 10k px margin
}).strict();

// Warp Pin (for mesh warp deformation)
export const WarpPinSchema = z.object({
  id: EntityIdSchema,
  position: Vec2Schema,
  originalPosition: Vec2Schema,
  offset: Vec2Schema,
  stiffness: normalized01,
  depth: finiteNumber.optional(),
  rotation: finiteNumber.optional(),
  scale: positiveFinite.max(100).optional(), // Max 100x scale
  selected: z.boolean().optional(),
}).strict();

// Audio Reactive config
export const SplineAudioReactiveSchema = z.object({
  enabled: z.boolean(),
  sourceLayerId: entityId,
  property: z.string().max(MAX_PATH_LENGTH).trim(),
  multiplier: finiteNumber.max(1000), // Max 1000x multiplier
  smoothing: normalized01,
}).strict();

// Helper: union of static value or AnimatableProperty
const NumberOrAnimatableSchema = z.union([finiteNumber, AnimatableNumberSchema]);
const NumberArrayOrAnimatableSchema = z.union([
  z.array(nonNegativeFinite),
  createAnimatablePropertySchema(z.array(nonNegativeFinite).max(MAX_ARRAY_LENGTH)), // AnimatableProperty<number[]>
]);

export const SplineDataSchema = z.object({
  pathData: z.string().max(MAX_STRING_LENGTH), // Max path data length
  controlPoints: boundedArray(ControlPointSchema, 100000), // Max 100k control points
  closed: z.boolean(),
  strokeType: z.enum(["solid", "gradient"]).optional(),
  stroke: HexColorSchema,
  strokeGradient: StrokeGradientSchema.optional(),
  strokeWidth: nonNegativeFinite.max(1000), // Max 1000px stroke width
  strokeOpacity: z.number().finite().min(0).max(100).optional(),
  lineCap: z.enum(["butt", "round", "square"]).optional(),
  lineJoin: z.enum(["miter", "round", "bevel"]).optional(),
  strokeMiterLimit: positiveFinite.max(100).optional(), // Max reasonable miter limit

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
  pathEffects: boundedArray(SplinePathEffectSchema, 100).optional(), // Max 100 path effects

  // Animated spline support
  animatedControlPoints: boundedArray(AnimatableControlPointSchema, 100000).optional(), // Max 100k animated points
  animated: z.boolean().optional(),

  // Level of Detail
  lod: SplineLODSettingsSchema.optional(),

  // Mesh Warp deformation pins
  warpPins: boundedArray(WarpPinSchema, 10000).optional(), // Max 10k warp pins
  /** @deprecated Use warpPins instead */
  puppetPins: boundedArray(WarpPinSchema, 10000).optional(), // Max 10k puppet pins

  // Audio-reactive animation
  audioReactive: SplineAudioReactiveSchema.optional(),
}).strict().refine(
  (data) => {
    // Closed paths should have at least 3 control points
    if (data.closed && data.controlPoints.length < 3) {
      return false;
    }
    return true;
  },
  { message: "Closed splines must have at least 3 control points", path: ["controlPoints"] }
);

export type SplineData = z.infer<typeof SplineDataSchema>;

// ════════════════════════════════════════════════════════════════════════════
// Path Layer Data (invisible motion paths)
// ════════════════════════════════════════════════════════════════════════════

export const PathLayerDataSchema = z.object({
  pathData: z.string().max(MAX_STRING_LENGTH), // Max path data length
  controlPoints: boundedArray(ControlPointSchema, 100000), // Max 100k control points
  closed: z.boolean(),
  showGuide: z.boolean(),
  guideColor: HexColorSchema,
  guideDashPattern: z.tuple([nonNegativeFinite.max(1000), nonNegativeFinite.max(1000)]), // Max 1000px dash/gap
  animated: z.boolean().optional(),
}).strict().refine(
  (data) => {
    // Closed paths should have at least 3 control points
    if (data.closed && data.controlPoints.length < 3) {
      return false;
    }
    return true;
  },
  { message: "Closed paths must have at least 3 control points", path: ["controlPoints"] }
);

export type PathLayerData = z.infer<typeof PathLayerDataSchema>;

// ════════════════════════════════════════════════════════════════════════════
// Text Layer Data
// ════════════════════════════════════════════════════════════════════════════

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
  }).strict(),
}).strict();

// Wiggly Selector
export const TextWigglySelectorSchema = z.object({
  enabled: z.boolean(),
  mode: z.enum(["add", "subtract", "intersect", "min", "max", "difference"]),
  maxAmount: z.number().finite().min(0).max(100),
  minAmount: z.number().finite().min(0).max(100),
  wigglesPerSecond: positiveFinite.max(1000), // Max 1000 wiggles per second
  correlation: z.number().finite().min(0).max(100),
  lockDimensions: z.boolean(),
  basedOn: z.enum(["characters", "characters_excluding_spaces", "words", "lines"]),
  randomSeed: z.number().int(),
}).strict().refine(
  (data) => {
    // maxAmount should be >= minAmount
    return data.maxAmount >= data.minAmount;
  },
  { message: "maxAmount must be >= minAmount", path: ["maxAmount"] }
);

// Expression Selector
export const TextExpressionSelectorSchema = z.object({
  enabled: z.boolean(),
  mode: z.enum(["add", "subtract", "intersect", "min", "max", "difference"]),
  amountExpression: z.string().max(MAX_STRING_LENGTH).trim(),
  basedOn: z.enum(["characters", "characters_excluding_spaces", "words", "lines"]),
}).strict();

// Text Animator Properties
export const TextAnimatorPropertiesSchema = z.object({
  position: AnimatablePositionSchema.optional(),
  anchorPoint: AnimatablePositionSchema.optional(),
  scale: AnimatablePositionSchema.optional(),
  rotation: AnimatableNumberSchema.optional(),
  skew: AnimatableNumberSchema.optional(),
  skewAxis: AnimatableNumberSchema.optional(),
  opacity: AnimatableNumberSchema.optional(),
  fillColor: createAnimatablePropertySchema(z.string().max(MAX_STRING_LENGTH)).optional(), // AnimatableProperty<string>
  fillBrightness: AnimatableNumberSchema.optional(),
  fillSaturation: AnimatableNumberSchema.optional(),
  fillHue: AnimatableNumberSchema.optional(),
  strokeColor: createAnimatablePropertySchema(z.string().max(MAX_STRING_LENGTH)).optional(), // AnimatableProperty<string>
  strokeWidth: AnimatableNumberSchema.optional(),
  tracking: AnimatableNumberSchema.optional(),
  lineAnchor: AnimatableNumberSchema.optional(),
  lineSpacing: AnimatableNumberSchema.optional(),
  characterOffset: AnimatableNumberSchema.optional(),
  blur: AnimatablePositionSchema.optional(),
}).strict(); // Changed from passthrough to strict for validation

// Text Animator
export const TextAnimatorSchema = z.object({
  id: EntityIdSchema,
  name: z.string().min(1).max(MAX_NAME_LENGTH).trim(),
  enabled: z.boolean(),
  rangeSelector: TextRangeSelectorSchema,
  wigglySelector: TextWigglySelectorSchema.optional(),
  expressionSelector: TextExpressionSelectorSchema.optional(),
  properties: TextAnimatorPropertiesSchema,
}).strict();

// Main TextData schema
export const TextDataSchema = z.object({
  // Source Text
  text: z.string().max(MAX_STRING_LENGTH), // Max text length
  fontFamily: z.string().max(MAX_FONT_FAMILY_LENGTH).trim(),
  fontSize: positiveFinite.max(10000), // Max 10k px font size
  fontWeight: z.string().max(50).trim(), // Font weight string
  fontStyle: z.enum(["normal", "italic"]),
  fill: HexColorSchema,
  stroke: HexColorSchema,
  strokeWidth: nonNegativeFinite.max(1000), // Max 1000px stroke width

  // Character Properties
  tracking: finiteNumber.max(1000), // Max 1000px tracking
  lineSpacing: positiveFinite.max(1000), // Max 1000px line spacing
  lineAnchor: z.number().finite().min(0).max(100),
  characterOffset: z.number().int(),
  characterValue: z.number().int(),
  blur: Vec2Schema,

  // Paragraph (legacy aliases)
  letterSpacing: finiteNumber.max(1000), // Max 1000px letter spacing
  lineHeight: positiveFinite.max(1000), // Max 1000px line height
  textAlign: TextAlignSchema,

  // Path Options
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy null
  // Pattern match: pathLayerId ∈ string (empty string = no path, never null)
  pathLayerId: z.string(),
  pathReversed: z.boolean(),
  pathPerpendicularToPath: z.boolean(),
  pathForceAlignment: z.boolean(),
  pathFirstMargin: finiteNumber.max(10000), // Max 10k px margin
  pathLastMargin: finiteNumber.max(10000), // Max 10k px margin
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
  baselineShift: finiteNumber.max(10000).optional(), // Max 10k px baseline shift
  textCase: z.enum(["normal", "uppercase", "lowercase", "smallCaps"]).optional(),
  verticalAlign: z.enum(["normal", "superscript", "subscript"]).optional(),

  // OpenType Features
  kerning: z.boolean().optional(),
  ligatures: z.boolean().optional(),
  discretionaryLigatures: z.boolean().optional(),
  smallCapsFeature: z.boolean().optional(),
  stylisticSet: z.number().int().min(0).max(20).optional(),

  // Advanced Paragraph Properties
  firstLineIndent: finiteNumber.max(10000).optional(), // Max 10k px indent
  spaceBefore: finiteNumber.max(10000).optional(), // Max 10k px space
  spaceAfter: finiteNumber.max(10000).optional(), // Max 10k px space

  // Text Animators
  animators: boundedArray(TextAnimatorSchema, 100).optional(), // Max 100 animators
}).strict();

export type TextData = z.infer<typeof TextDataSchema>;

// ════════════════════════════════════════════════════════════════════════════
// Shape Layer Data
// ════════════════════════════════════════════════════════════════════════════

// Import the correct ShapeLayerData schema from shapes-schema.ts
import { ShapeLayerDataSchema } from "./shapes-schema";

export { ShapeLayerDataSchema };
export type ShapeLayerData = z.infer<typeof ShapeLayerDataSchema>;

// ════════════════════════════════════════════════════════════════════════════
// Particle Layer Data (Legacy)
// ════════════════════════════════════════════════════════════════════════════

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
  particleCount: positiveInt.max(10000000), // Max 10M particles
  lifetime: positiveFinite.max(86400), // Max 24 hours lifetime
  speed: nonNegativeFinite.max(10000), // Max 10k units/sec speed
  spread: finiteNumber.max(360), // Max 360 degrees spread
  gravity: finiteNumber.max(10000), // Max 10k units/sec^2 gravity
  color: HexColorSchema,
  size: positiveFinite.max(10000), // Max 10k px particle size
}).strict();

export type LegacyParticleLayerData = z.infer<typeof LegacyParticleLayerDataSchema>;

// ════════════════════════════════════════════════════════════════════════════
// Particle Layer Data (New system - matching RyanOnTheInside)
// ════════════════════════════════════════════════════════════════════════════

// Sprite configuration
export const SpriteConfigSchema = z.object({
  enabled: z.boolean(),
  imageUrl: z.string().max(MAX_URL_LENGTH).nullable(),
  imageData: z.custom<ImageBitmap | HTMLImageElement | null>(
    (val) => val === null || val instanceof ImageBitmap || val instanceof HTMLImageElement
  ).nullable(), // ImageBitmap | HTMLImageElement
  isSheet: z.boolean(),
  columns: positiveInt.max(1000), // Max 1000 columns
  rows: positiveInt.max(1000), // Max 1000 rows
  totalFrames: positiveInt.max(1000000), // Max 1M frames
  frameRate: positiveFinite.max(1000), // Max 1000 FPS
  playMode: z.enum(["loop", "once", "pingpong", "random"]),
  billboard: z.boolean(),
  rotationEnabled: z.boolean(),
  rotationSpeed: finiteNumber.max(1000), // Max 1000 deg/sec rotation
  rotationSpeedVariance: nonNegativeFinite.max(1000), // Max 1000 deg/sec variance
  alignToVelocity: z.boolean(),
}).strict().refine(
  (data) => {
    // If isSheet, columns * rows should match totalFrames approximately
    if (data.isSheet && data.columns * data.rows !== data.totalFrames) {
      return false;
    }
    return true;
  },
  { message: "columns * rows must equal totalFrames for sprite sheets", path: ["totalFrames"] }
);

// Spline path emission
export const SplinePathEmissionSchema = z.object({
  layerId: entityId,
  emitMode: z.enum(["uniform", "random", "start", "end", "sequential"]),
  parameter: normalized01,
  alignToPath: z.boolean(),
  offset: finiteNumber.max(10000), // Max 10k px offset
  bidirectional: z.boolean(),
}).strict();

// Depth map emission
export const DepthMapEmissionSchema = z.object({
  sourceLayerId: entityId,
  depthMin: normalized01,
  depthMax: normalized01,
  density: positiveFinite.max(1000000), // Max 1M particles per unit
  velocityByDepth: z.boolean(),
  sizeByDepth: z.boolean(),
  depthMode: z.enum(["near-white", "near-black"]),
}).strict().refine(
  (data) => {
    // depthMax should be >= depthMin
    return data.depthMax >= data.depthMin;
  },
  { message: "depthMax must be >= depthMin", path: ["depthMax"] }
);

// Mask emission
export const MaskEmissionSchema = z.object({
  sourceLayerId: entityId,
  threshold: normalized01,
  density: positiveFinite.max(1000000), // Max 1M particles per unit
  channel: z.enum(["luminance", "alpha", "red", "green", "blue"]),
  invert: z.boolean(),
  sampleRate: positiveInt.max(1000), // Max 1000x sample rate
}).strict();

// Particle emitter config
export const ParticleEmitterConfigSchema = z.object({
  id: entityId,
  name: z.string().min(1).max(MAX_NAME_LENGTH).trim(),
  x: finiteNumber,
  y: finiteNumber,
  z: finiteNumber.optional(),
  direction: finiteNumber,
  spread: finiteNumber.max(360), // Max 360 degrees spread
  speed: nonNegativeFinite.max(100000), // Max 100k units/sec speed
  speedVariance: nonNegativeFinite.max(100000), // Max 100k units/sec variance
  size: positiveFinite.max(100000), // Max 100k px size
  sizeVariance: nonNegativeFinite.max(100000), // Max 100k px variance
  color: z.tuple([normalized01, normalized01, normalized01]), // RGB 0-1
  emissionRate: positiveFinite.max(1000000), // Max 1M particles/sec
  initialBurst: nonNegativeInt.max(10000000), // Max 10M initial burst
  particleLifetime: positiveFinite.max(86400), // Max 24 hours lifetime
  lifetimeVariance: nonNegativeFinite.max(86400), // Max 24 hours variance
  enabled: z.boolean(),
  burstOnBeat: z.boolean(),
  burstCount: positiveInt.max(1000000), // Max 1M burst count
  shape: EmitterShapeSchema,
  shapeRadius: nonNegativeFinite.max(100000), // Max 100k units radius
  shapeWidth: nonNegativeFinite.max(100000), // Max 100k units width
  shapeHeight: nonNegativeFinite.max(100000), // Max 100k units height
  shapeDepth: nonNegativeFinite.max(100000), // Max 100k units depth
  shapeInnerRadius: nonNegativeFinite.max(100000), // Max 100k units inner radius
  emitFromEdge: z.boolean(),
  emitFromVolume: z.boolean(),
  splinePath: SplinePathEmissionSchema.nullable(),
  depthMapEmission: DepthMapEmissionSchema.optional(),
  maskEmission: MaskEmissionSchema.optional(),
  sprite: SpriteConfigSchema,
  // Cone shape
  coneAngle: finiteNumber.min(0).max(180).optional(), // Max 180 degrees
  coneRadius: nonNegativeFinite.max(100000).optional(), // Max 100k units
  coneLength: nonNegativeFinite.max(100000).optional(), // Max 100k units
  // Image shape
  imageSourceLayerId: entityId.optional(),
  emissionThreshold: normalized01.optional(),
  emitFromMaskEdge: z.boolean().optional(),
  // Depth edge
  depthSourceLayerId: entityId.optional(),
  depthEdgeThreshold: nonNegativeFinite.max(1000).optional(), // Max threshold
  depthScale: finiteNumber.max(1000).optional(), // Max 1000x scale
  // Alternative names
  lifespan: positiveFinite.max(86400).optional(), // Max 24 hours
  startSize: positiveFinite.max(100000).optional(), // Max 100k px
  endSize: positiveFinite.max(100000).optional(), // Max 100k px
  startColor: HexColorSchema.optional(),
  endColor: HexColorSchema.optional(),
  startOpacity: normalized01.optional(),
  endOpacity: normalized01.optional(),
  velocitySpread: nonNegativeFinite.max(100000).optional(), // Max 100k units/sec
}).strict();

// Gravity well config
export const GravityWellConfigSchema = z.object({
  id: entityId,
  name: z.string().min(1).max(MAX_NAME_LENGTH).trim(),
  x: finiteNumber,
  y: finiteNumber,
  strength: finiteNumber.max(100000), // Max 100k units/sec^2 strength
  radius: positiveFinite.max(100000), // Max 100k units radius
  falloff: z.enum(["linear", "quadratic", "constant"]),
  enabled: z.boolean(),
}).strict();

// Vortex config
export const VortexConfigSchema = z.object({
  id: entityId,
  name: z.string().min(1).max(MAX_NAME_LENGTH).trim(),
  x: finiteNumber,
  y: finiteNumber,
  strength: finiteNumber.max(100000), // Max 100k units/sec^2 strength
  radius: positiveFinite.max(100000), // Max 100k units radius
  rotationSpeed: finiteNumber.max(10000), // Max 10k deg/sec rotation
  inwardPull: finiteNumber.max(100000), // Max 100k units/sec^2 pull
  enabled: z.boolean(),
}).strict();

// Modulation config
export const ParticleModulationConfigSchema = z.object({
  id: entityId,
  emitterId: entityId,
  property: z.enum(["size", "speed", "opacity", "colorR", "colorG", "colorB"]),
  startValue: finiteNumber,
  endValue: finiteNumber,
  easing: z.string().max(MAX_NAME_LENGTH).trim(),
}).strict();

// Turbulence field
export const TurbulenceFieldConfigSchema = z.object({
  id: entityId,
  enabled: z.boolean(),
  scale: positiveFinite.max(10000), // Max 10k scale
  strength: nonNegativeFinite.max(100000), // Max 100k strength
  evolutionSpeed: nonNegativeFinite.max(1000), // Max 1000 evolution speed
  octaves: positiveInt.max(10).optional(), // Max 10 octaves
  persistence: normalized01.optional(),
  animationSpeed: nonNegativeFinite.max(1000).optional(), // Max 1000 animation speed
}).strict();

// Sub-emitter
export const SubEmitterConfigSchema = z.object({
  id: entityId,
  parentEmitterId: entityId,
  trigger: z.literal("death"),
  spawnCount: positiveInt.max(1000000), // Max 1M spawn count
  inheritVelocity: normalized01,
  size: positiveFinite.max(100000), // Max 100k px size
  sizeVariance: nonNegativeFinite.max(100000), // Max 100k px variance
  lifetime: positiveFinite.max(86400), // Max 24 hours lifetime
  speed: nonNegativeFinite.max(100000), // Max 100k units/sec speed
  spread: finiteNumber.max(360), // Max 360 degrees spread
  color: z.tuple([normalized01, normalized01, normalized01]), // RGB 0-1
  enabled: z.boolean(),
}).strict();

// Flocking config
export const FlockingConfigSchema = z.object({
  enabled: z.boolean(),
  separationWeight: z.number().finite().min(0).max(100),
  separationRadius: positiveFinite.max(100000), // Max 100k units radius
  alignmentWeight: z.number().finite().min(0).max(100),
  alignmentRadius: positiveFinite.max(100000), // Max 100k units radius
  cohesionWeight: z.number().finite().min(0).max(100),
  cohesionRadius: positiveFinite.max(100000), // Max 100k units radius
  maxSpeed: positiveFinite.max(100000), // Max 100k units/sec speed
  maxForce: positiveFinite.max(100000), // Max 100k units/sec^2 force
  perceptionAngle: finiteNumber.max(360), // Max 360 degrees
}).strict();

// Collision plane
export const CollisionPlaneConfigSchema = z.object({
  id: entityId,
  name: z.string().max(MAX_NAME_LENGTH).trim().optional(),
  enabled: z.boolean(),
  point: Vec3Schema,
  normal: Vec3Schema,
  bounciness: normalized01,
  friction: normalized01,
}).strict();

// Collision config
export const CollisionConfigSchema = z.object({
  enabled: z.boolean(),
  particleCollision: z.boolean(),
  particleRadius: positiveFinite.max(10000), // Max 10k px radius
  bounciness: normalized01,
  friction: normalized01,
  boundaryEnabled: z.boolean(),
  boundaryBehavior: z.enum(["none", "kill", "bounce", "wrap", "stick"]),
  boundaryPadding: nonNegativeFinite.max(100000), // Max 100k px padding
  floorEnabled: z.boolean().optional(),
  floorY: normalized01.optional(),
  floorBehavior: z.enum(["none", "bounce", "stick", "kill"]).optional(),
  floorFriction: normalized01.optional(),
  ceilingEnabled: z.boolean().optional(),
  ceilingY: normalized01.optional(),
  planes: boundedArray(CollisionPlaneConfigSchema, 1000).optional(), // Max 1000 collision planes
}).strict();

// Connection render config
export const ConnectionRenderConfigSchema = z.object({
  enabled: z.boolean(),
  maxDistance: positiveFinite.max(100000), // Max 100k units distance
  maxConnections: z.number().int().min(1).max(5),
  lineWidth: z.number().finite().min(0.5).max(3),
  lineOpacity: normalized01,
  fadeByDistance: z.boolean(),
  color: z.tuple([normalized01, normalized01, normalized01]).optional(), // RGB 0-1
}).strict();

// Audio binding
export const AudioBindingConfigSchema = z.object({
  id: entityId,
  enabled: z.boolean(),
  feature: z.enum(["amplitude", "bass", "mid", "high", "beat", "spectralCentroid"]),
  smoothing: normalized01,
  min: finiteNumber,
  max: finiteNumber,
  target: z.enum(["emitter", "system", "forceField"]),
  targetId: entityId,
  parameter: z.string().max(MAX_PATH_LENGTH).trim(),
  outputMin: finiteNumber,
  outputMax: finiteNumber,
  curve: z.enum(["linear", "exponential", "logarithmic", "step"]),
  stepCount: positiveInt.max(1000).optional(), // Max 1000 steps
  triggerMode: z.enum(["continuous", "onThreshold", "onBeat"]).optional(),
  threshold: normalized01.optional(),
}).strict().refine(
  (data) => {
    // max should be >= min
    return data.max >= data.min;
  },
  { message: "max must be >= min", path: ["max"] }
).refine(
  (data) => {
    // outputMax should be >= outputMin
    return data.outputMax >= data.outputMin;
  },
  { message: "outputMax must be >= outputMin", path: ["outputMax"] }
);

// Audio particle mapping
export const AudioParticleMappingSchema = z.object({
  feature: z.enum(["amplitude", "rms", "bass", "mid", "high", "onsets"]),
  parameter: z.enum(["emissionRate", "speed", "size", "gravity", "windStrength"]),
  emitterId: entityId.optional(),
  sensitivity: positiveFinite.max(1000), // Max 1000x sensitivity
  smoothing: normalized01,
}).strict();

// Render options
export const ParticleRenderOptionsSchema = z.object({
  blendMode: z.enum(["normal", "additive", "multiply", "screen"]),
  renderTrails: z.boolean(),
  trailLength: positiveInt.max(10000), // Max 10k frames trail length
  trailOpacityFalloff: normalized01,
  particleShape: z.enum(["circle", "square", "triangle", "star"]),
  glowEnabled: z.boolean(),
  glowRadius: nonNegativeFinite.max(1000), // Max 1000px glow radius
  glowIntensity: nonNegativeFinite.max(1000), // Max 1000% glow intensity
  motionBlur: z.boolean(),
  motionBlurStrength: normalized01,
  motionBlurSamples: z.number().int().min(1).max(16),
  connections: ConnectionRenderConfigSchema,
  spriteEnabled: z.boolean().optional(),
  spriteImageUrl: z.string().max(MAX_URL_LENGTH).optional(),
  spriteColumns: positiveInt.max(1000).optional(), // Max 1000 columns
  spriteRows: positiveInt.max(1000).optional(), // Max 1000 rows
  spriteAnimate: z.boolean().optional(),
  spriteFrameRate: positiveFinite.max(1000).optional(), // Max 1000 FPS
  spriteRandomStart: z.boolean().optional(),
  lodEnabled: z.boolean().optional(),
  lodDistances: boundedArray(finiteNumber.max(100000), 100).optional(), // Max 100 LOD distances
  lodSizeMultipliers: boundedArray(finiteNumber.max(100), 100).optional(), // Max 100 multipliers
  dofEnabled: z.boolean().optional(),
  dofFocusDistance: nonNegativeFinite.max(100000).optional(), // Max 100k units
  dofFocusRange: positiveFinite.max(100000).optional(), // Max 100k units
  dofMaxBlur: normalized01.optional(),
  shadowsEnabled: z.boolean().optional(),
  castShadows: z.boolean().optional(),
  receiveShadows: z.boolean().optional(),
  shadowSoftness: nonNegativeFinite.max(1000).optional(), // Max 1000px softness
  meshMode: z.enum(["billboard", "mesh"]).optional(),
  meshGeometry: z.enum(["cube", "sphere", "cylinder", "cone", "torus", "custom"]).optional(),
}).strict();

// System config
export const ParticleSystemLayerConfigSchema = z.object({
  maxParticles: positiveInt.max(10000000), // Max 10M particles
  gravity: finiteNumber.max(100000), // Max 100k units/sec^2 gravity
  windStrength: finiteNumber.max(100000), // Max 100k units/sec^2 wind
  windDirection: finiteNumber.max(360), // Max 360 degrees
  warmupPeriod: nonNegativeInt.max(100000), // Max 100k frames warmup
  respectMaskBoundary: z.boolean(),
  boundaryBehavior: z.enum(["bounce", "kill", "wrap"]),
  friction: normalized01,
  turbulenceFields: boundedArray(TurbulenceFieldConfigSchema, 100).optional(), // Max 100 turbulence fields
  subEmitters: boundedArray(SubEmitterConfigSchema, 1000).optional(), // Max 1000 sub-emitters
  useGPU: z.boolean().optional(),
}).strict();

// Visualization config
export const ParticleVisualizationConfigSchema = z.object({
  showHorizon: z.boolean(),
  showGrid: z.boolean(),
  showAxis: z.boolean(),
  gridSize: positiveFinite.max(100000), // Max 100k units grid size
  gridDepth: positiveFinite.max(100000), // Max 100k units grid depth
}).strict();

// Particle group config
export const ParticleGroupConfigSchema = z.object({
  id: entityId,
  name: z.string().min(1).max(MAX_NAME_LENGTH).trim(),
  enabled: z.boolean(),
  color: z.tuple([normalized01, normalized01, normalized01, normalized01]), // RGBA 0-1
  collisionMask: nonNegativeInt.max(4294967295), // Max 32-bit mask
  connectionMask: nonNegativeInt.max(4294967295), // Max 32-bit mask
}).strict();

// Spring structure
export const SpringStructureSchema = z.object({
  id: entityId,
  type: z.enum(["cloth", "rope", "softbody", "custom"]),
  width: positiveInt.max(10000).optional(), // Max 10k width
  height: positiveInt.max(10000).optional(), // Max 10k height
  length: positiveInt.max(100000).optional(), // Max 100k length
  startParticle: nonNegativeInt.max(10000000), // Max 10M particle index
  pinnedParticles: boundedArray(nonNegativeInt.max(10000000), 10000).optional(), // Max 10k pinned particles
  stiffness: positiveFinite.max(1000000), // Max 1M stiffness
  damping: nonNegativeFinite.max(1000000), // Max 1M damping
  breakThreshold: nonNegativeFinite.max(1000000), // Max 1M break threshold
}).strict();

// Spring system config
export const SpringSystemConfigSchema = z.object({
  enabled: z.boolean(),
  useVerlet: z.boolean(),
  solverIterations: z.number().int().min(1).max(16),
  globalStiffness: positiveFinite.max(1000000), // Max 1M stiffness
  globalDamping: nonNegativeFinite.max(1000000), // Max 1M damping
  enableBreaking: z.boolean(),
  gravity: Vec3Schema,
  structures: boundedArray(SpringStructureSchema, 1000).optional(), // Max 1000 structures
}).strict();

//                                                                       // sph
export const SPHFluidConfigSchema = z.object({
  enabled: z.boolean(),
  preset: z.enum(["water", "honey", "lava", "gas", "custom"]),
  smoothingRadius: positiveFinite.max(100000), // Max 100k units radius
  restDensity: positiveFinite.max(1000000), // Max 1M density
  gasConstant: positiveFinite.max(1000000), // Max 1M gas constant
  viscosity: nonNegativeFinite.max(1000000), // Max 1M viscosity
  surfaceTension: nonNegativeFinite.max(1000000), // Max 1M surface tension
  gravity: Vec3Schema,
  boundaryDamping: normalized01,
}).strict();

//                                                                       // lod
export const ParticleLODConfigSchema = z.object({
  enabled: z.boolean(),
  distances: boundedArray(finiteNumber.max(100000), 100), // Max 100 LOD distances
  sizeMultipliers: boundedArray(finiteNumber.max(100), 100), // Max 100 multipliers
}).strict().refine(
  (data) => {
    // distances and sizeMultipliers should have same length
    return data.distances.length === data.sizeMultipliers.length;
  },
  { message: "distances and sizeMultipliers must have same length", path: ["sizeMultipliers"] }
);

//                                                                       // dof
export const ParticleDOFConfigSchema = z.object({
  enabled: z.boolean(),
  focusDistance: nonNegativeFinite.max(100000), // Max 100k units
  focusRange: positiveFinite.max(100000), // Max 100k units
  blurAmount: normalized01,
}).strict();

// Main ParticleLayerData schema
export const ParticleLayerDataSchema = z.object({
  systemConfig: ParticleSystemLayerConfigSchema,
  emitters: boundedArray(ParticleEmitterConfigSchema, 1000), // Max 1000 emitters
  gravityWells: boundedArray(GravityWellConfigSchema, 1000), // Max 1000 gravity wells
  vortices: boundedArray(VortexConfigSchema, 1000), // Max 1000 vortices
  modulations: boundedArray(ParticleModulationConfigSchema, 10000).optional(), // Max 10k modulations
  renderOptions: ParticleRenderOptionsSchema,
  turbulenceFields: boundedArray(TurbulenceFieldConfigSchema, 100).optional(), // Max 100 turbulence fields
  subEmitters: boundedArray(SubEmitterConfigSchema, 1000).optional(), // Max 1000 sub-emitters
  flocking: FlockingConfigSchema.optional(),
  collision: CollisionConfigSchema.optional(),
  audioBindings: boundedArray(AudioBindingConfigSchema, 1000).optional(), // Max 1000 audio bindings
  audioMappings: boundedArray(AudioParticleMappingSchema, 1000).optional(), // Max 1000 audio mappings
  exportEnabled: z.boolean().optional(),
  exportFormat: z.string().max(50).trim().optional(),
  speedMapEnabled: z.boolean().optional(),
  speedMap: AnimatableNumberSchema.optional(),
  visualization: ParticleVisualizationConfigSchema.optional(),
  groups: boundedArray(ParticleGroupConfigSchema, 1000).optional(), // Max 1000 groups
  springConfig: SpringSystemConfigSchema.optional(),
  sphConfig: SPHFluidConfigSchema.optional(),
  lodConfig: ParticleLODConfigSchema.optional(),
  dofConfig: ParticleDOFConfigSchema.optional(),
  collisionPlanes: boundedArray(CollisionPlaneConfigSchema, 1000).optional(), // Max 1000 collision planes
  particleGroups: boundedArray(ParticleGroupConfigSchema, 1000).optional(), // Max 1000 particle groups
}).strict();

export type ParticleLayerData = z.infer<typeof ParticleLayerDataSchema>;

// ════════════════════════════════════════════════════════════════════════════
// Union of all layer data types
// ════════════════════════════════════════════════════════════════════════════

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
