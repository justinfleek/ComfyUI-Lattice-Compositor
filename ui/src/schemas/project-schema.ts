/**
 * Project Schema
 *
 * Zod schemas for validating LatticeProject files.
 * All numeric values use .finite() to reject NaN/Infinity.
 */

import { z } from "zod";
import {
  EntityIdSchema,
  HexColorSchema,
  positiveInt,
  positiveFinite,
  nonNegativeFinite,
  finiteNumber,
  frameNumber,
} from "./layers/primitives-schema";
import { LayerSchema } from "./layers/layer-schema";

// ============================================================================
// Constants
// ============================================================================

export const PROJECT_VERSION = "1.0.0" as const;
export const MAX_DIMENSION = 16384;
export const MAX_FPS = 120;
export const MAX_FRAME_COUNT = 100000;

// ============================================================================
// Color Settings
// ============================================================================

export const ColorSpaceSchema = z.enum([
  "sRGB",
  "linear-sRGB",
  "Adobe-RGB",
  "Display-P3",
  "ProPhoto-RGB",
  "ACEScg",
  "Rec709",
  "Rec2020",
]);

export type ColorSpace = z.infer<typeof ColorSpaceSchema>;

export const ViewTransformSchema = z.enum([
  "sRGB",
  "Display-P3",
  "Rec709",
  "ACES-sRGB",
  "Filmic",
]);

export type ViewTransform = z.infer<typeof ViewTransformSchema>;

export const ColorSettingsSchema = z.object({
  workingColorSpace: ColorSpaceSchema,
  viewTransform: ViewTransformSchema,
  exportColorSpace: z.union([ColorSpaceSchema, z.literal("source")]),
  linearCompositing: z.boolean(),
});

export type ColorSettings = z.infer<typeof ColorSettingsSchema>;

// ============================================================================
// Composition Settings
// ============================================================================

export const CompositionSettingsSchema = z.object({
  width: z.number().int().positive().max(MAX_DIMENSION).refine(
    (n) => n % 8 === 0,
    { message: "Width must be divisible by 8" }
  ),
  height: z.number().int().positive().max(MAX_DIMENSION).refine(
    (n) => n % 8 === 0,
    { message: "Height must be divisible by 8" }
  ),
  frameCount: z.number().int().positive().max(MAX_FRAME_COUNT),
  fps: positiveFinite.max(MAX_FPS),
  duration: positiveFinite,
  backgroundColor: HexColorSchema,
  autoResizeToContent: z.boolean(),
  frameBlendingEnabled: z.boolean(),
  colorSettings: ColorSettingsSchema.optional(),
  motionBlur: z.boolean().optional(),
  shutterAngle: z.number().finite().min(0).max(720).optional(),
  motionBlurSamples: z.number().int().min(2).max(64).optional(),
});

export type CompositionSettings = z.infer<typeof CompositionSettingsSchema>;

// ============================================================================
// Workflow Mapping
// ============================================================================

export const WorkflowInputTypeSchema = z.enum([
  "image",
  "video",
  "latent",
  "mask",
  "number",
  "string",
]);

export const WorkflowInputSchema = z.object({
  name: z.string(),
  type: WorkflowInputTypeSchema,
  nodeId: z.string(),
  inputName: z.string(),
});

export type WorkflowInput = z.infer<typeof WorkflowInputSchema>;

export const WorkflowOutputTypeSchema = z.enum(["image", "video", "latent"]);

export const WorkflowOutputSchema = z.object({
  name: z.string(),
  type: WorkflowOutputTypeSchema,
  nodeId: z.string(),
  outputName: z.string(),
});

export type WorkflowOutput = z.infer<typeof WorkflowOutputSchema>;

// ============================================================================
// Global Light Settings
// ============================================================================

export const GlobalLightSettingsSchema = z.object({
  angle: finiteNumber,
  altitude: finiteNumber,
});

export type GlobalLightSettings = z.infer<typeof GlobalLightSettingsSchema>;

// ============================================================================
// Marker
// ============================================================================

export const MarkerSchema = z.object({
  id: EntityIdSchema,
  frame: frameNumber,
  label: z.string(),
  color: HexColorSchema,
  duration: positiveInt.optional(),
  comment: z.string().optional(),
});

export type Marker = z.infer<typeof MarkerSchema>;

// ============================================================================
// Composition
// ============================================================================

export const CompositionSchema = z.object({
  id: EntityIdSchema,
  name: z.string(),
  settings: CompositionSettingsSchema,
  layers: z.array(LayerSchema),
  currentFrame: frameNumber,
  isNestedComp: z.boolean(),
  parentCompositionId: EntityIdSchema.optional(),
  workflowId: z.string().optional(),
  workflowInputs: z.array(WorkflowInputSchema).optional(),
  workflowOutputs: z.array(WorkflowOutputSchema).optional(),
  globalLight: GlobalLightSettingsSchema.optional(),
  markers: z.array(MarkerSchema).optional(),
});

export type Composition = z.infer<typeof CompositionSchema>;

// ============================================================================
// Asset Types
// ============================================================================

export const AssetTypeSchema = z.enum([
  "depth_map",
  "image",
  "video",
  "audio",
  "model",
  "pointcloud",
  "texture",
  "material",
  "hdri",
  "svg",
  "sprite",
  "spritesheet",
  "lut",
]);

export type AssetType = z.infer<typeof AssetTypeSchema>;

export const AssetSourceSchema = z.enum([
  "comfyui_node",
  "file",
  "generated",
  "url",
]);

export type AssetSource = z.infer<typeof AssetSourceSchema>;

export const TextureMapTypeSchema = z.enum([
  "albedo",
  "normal",
  "roughness",
  "metalness",
  "ao",
  "emissive",
  "height",
  "opacity",
  "specular",
]);

export type TextureMapType = z.infer<typeof TextureMapTypeSchema>;

export const ModelFormatSchema = z.enum(["gltf", "glb", "obj", "fbx", "usd"]);
export type ModelFormat = z.infer<typeof ModelFormatSchema>;

export const PointCloudFormatSchema = z.enum(["ply", "pcd", "las", "xyz"]);
export type PointCloudFormat = z.infer<typeof PointCloudFormatSchema>;

export const ModelBoundingBoxSchema = z.object({
  min: z.object({ x: finiteNumber, y: finiteNumber, z: finiteNumber }),
  max: z.object({ x: finiteNumber, y: finiteNumber, z: finiteNumber }),
});

export type ModelBoundingBox = z.infer<typeof ModelBoundingBoxSchema>;

export const SVGViewBoxSchema = z.object({
  x: finiteNumber,
  y: finiteNumber,
  width: positiveFinite,
  height: positiveFinite,
});

export type SVGViewBox = z.infer<typeof SVGViewBoxSchema>;

export const MaterialMapsSchema = z.object({
  albedo: EntityIdSchema.optional(),
  normal: EntityIdSchema.optional(),
  roughness: EntityIdSchema.optional(),
  metalness: EntityIdSchema.optional(),
  ao: EntityIdSchema.optional(),
  emissive: EntityIdSchema.optional(),
  height: EntityIdSchema.optional(),
  opacity: EntityIdSchema.optional(),
});

export type MaterialMaps = z.infer<typeof MaterialMapsSchema>;

export const AssetReferenceSchema = z.object({
  id: EntityIdSchema,
  type: AssetTypeSchema,
  source: AssetSourceSchema,
  nodeId: z.string().optional(),
  width: positiveInt,
  height: positiveInt,
  data: z.string().min(1),
  filename: z.string().optional(),

  // Video/Audio metadata
  frameCount: positiveInt.optional(),
  duration: positiveFinite.optional(),
  fps: positiveFinite.optional(),
  hasAudio: z.boolean().optional(),
  audioChannels: z.number().int().min(1).max(8).optional(),
  sampleRate: positiveInt.optional(),

  // 3D Model metadata
  modelFormat: ModelFormatSchema.optional(),
  modelBoundingBox: ModelBoundingBoxSchema.optional(),
  modelAnimations: z.array(z.string()).optional(),
  modelMeshCount: positiveInt.optional(),
  modelVertexCount: positiveInt.optional(),

  // Point cloud metadata
  pointCloudFormat: PointCloudFormatSchema.optional(),
  pointCount: positiveInt.optional(),

  // Texture metadata
  textureMapType: TextureMapTypeSchema.optional(),
  textureColorSpace: z.enum(["srgb", "linear"]).optional(),

  // Material definition
  materialMaps: MaterialMapsSchema.optional(),

  // HDRI metadata
  hdriExposure: finiteNumber.optional(),
  hdriRotation: finiteNumber.optional(),

  // SVG metadata
  svgPaths: positiveInt.optional(),
  svgViewBox: SVGViewBoxSchema.optional(),

  // Sprite sheet metadata
  spriteColumns: positiveInt.optional(),
  spriteRows: positiveInt.optional(),
  spriteCount: positiveInt.optional(),
  spriteFrameRate: positiveFinite.optional(),
});

export type AssetReference = z.infer<typeof AssetReferenceSchema>;

// ============================================================================
// Data Asset
// ============================================================================

export const DataAssetTypeSchema = z.enum(["json", "csv", "tsv", "mgjson"]);

export type DataAssetType = z.infer<typeof DataAssetTypeSchema>;

export const DataAssetReferenceSchema = z.object({
  id: EntityIdSchema,
  name: z.string(),
  type: DataAssetTypeSchema,
  rawContent: z.string(),
  lastModified: z.number().int().nonnegative(),
  sourceData: z.unknown().optional(),
  headers: z.array(z.string()).optional(),
  rows: z.array(z.array(z.string())).optional(),
  numRows: positiveInt.optional(),
  numColumns: positiveInt.optional(),
});

export type DataAssetReference = z.infer<typeof DataAssetReferenceSchema>;

// ============================================================================
// Project Meta
// ============================================================================

export const ProjectMetaSchema = z.object({
  name: z.string(),
  created: z.string(), // ISO 8601
  modified: z.string(), // ISO 8601
  author: z.string().optional(),
});

export type ProjectMeta = z.infer<typeof ProjectMetaSchema>;

// ============================================================================
// Export Settings
// ============================================================================

export const ExportSettingsSchema = z.object({
  format: z.string(),
  codec: z.string().optional(),
  quality: z.string().optional(),
  resolution: z.object({
    width: positiveInt,
    height: positiveInt,
  }).optional(),
  frameRate: positiveFinite.optional(),
});

export type ExportSettings = z.infer<typeof ExportSettingsSchema>;

// ============================================================================
// Main Project Schema
// ============================================================================

export const LatticeProjectSchema = z.object({
  version: z.literal(PROJECT_VERSION),
  schemaVersion: positiveInt.optional(),
  meta: ProjectMetaSchema,
  compositions: z.record(CompositionSchema),
  mainCompositionId: EntityIdSchema,
  composition: CompositionSettingsSchema, // Legacy alias
  assets: z.record(AssetReferenceSchema),
  dataAssets: z.record(DataAssetReferenceSchema).optional(),
  layers: z.array(LayerSchema), // Legacy for main composition
  currentFrame: frameNumber,
  exportSettings: ExportSettingsSchema.optional(),
});

export type LatticeProject = z.infer<typeof LatticeProjectSchema>;

// ============================================================================
// Validation Helpers
// ============================================================================

/**
 * Validate a project file.
 */
export function validateProject(data: unknown): LatticeProject {
  return LatticeProjectSchema.parse(data);
}

/**
 * Safely validate a project file (returns success/error).
 */
export function safeValidateProject(data: unknown) {
  return LatticeProjectSchema.safeParse(data);
}

/**
 * Validate a composition.
 */
export function validateComposition(data: unknown): Composition {
  return CompositionSchema.parse(data);
}

/**
 * Safely validate a composition (returns success/error).
 */
export function safeValidateComposition(data: unknown) {
  return CompositionSchema.safeParse(data);
}
