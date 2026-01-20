/**
 * Project Schema
 *
 * Zod schemas for validating LatticeProject files.
 * All numeric values use .finite() to reject NaN/Infinity.
 * Includes comprehensive validation constraints for security and data integrity.
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
import {
  entityId,
  boundedArray,
  iso8601DateTime,
  filename,
  url,
  base64OrDataUrl,
  jsonSerializable,
  MAX_NAME_LENGTH,
  MAX_DESCRIPTION_LENGTH,
  MAX_COMMENT_LENGTH,
  MAX_STRING_LENGTH,
  MAX_ARRAY_LENGTH,
  MAX_ANIMATION_NAME_LENGTH,
} from "./shared-validation";

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
}).strict();

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
  duration: positiveFinite.max(86400), // Max 24 hours duration
  backgroundColor: HexColorSchema,
  autoResizeToContent: z.boolean(),
  frameBlendingEnabled: z.boolean(),
  colorSettings: ColorSettingsSchema.optional(),
  motionBlur: z.boolean().optional(),
  shutterAngle: z.number().finite().min(0).max(720).optional(),
  motionBlurSamples: z.number().int().min(2).max(64).optional(),
}).strict().refine(
  (data) => {
    // duration should match frameCount / fps approximately
    const expectedDuration = data.frameCount / data.fps;
    const tolerance = 0.01;
    return Math.abs(data.duration - expectedDuration) < tolerance;
  },
  { message: "duration should match frameCount / fps", path: ["duration"] }
);

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
  name: z.string().min(1).max(MAX_NAME_LENGTH).trim(),
  type: WorkflowInputTypeSchema,
  nodeId: entityId,
  inputName: z.string().min(1).max(MAX_NAME_LENGTH).trim(),
}).strict();

export type WorkflowInput = z.infer<typeof WorkflowInputSchema>;

export const WorkflowOutputTypeSchema = z.enum(["image", "video", "latent"]);

export const WorkflowOutputSchema = z.object({
  name: z.string().min(1).max(MAX_NAME_LENGTH).trim(),
  type: WorkflowOutputTypeSchema,
  nodeId: entityId,
  outputName: z.string().min(1).max(MAX_NAME_LENGTH).trim(),
}).strict();

export type WorkflowOutput = z.infer<typeof WorkflowOutputSchema>;

// ============================================================================
// Global Light Settings
// ============================================================================

export const GlobalLightSettingsSchema = z.object({
  angle: finiteNumber.max(360), // Max 360 degrees
  altitude: finiteNumber.min(-90).max(90), // -90 to 90 degrees
}).strict();

export type GlobalLightSettings = z.infer<typeof GlobalLightSettingsSchema>;

// ============================================================================
// Marker
// ============================================================================

export const MarkerSchema = z.object({
  id: EntityIdSchema,
  frame: frameNumber,
  label: z.string().min(1).max(MAX_NAME_LENGTH).trim(),
  color: HexColorSchema,
  duration: positiveInt.max(100000).optional(), // Max 100k frames duration
  comment: z.string().max(MAX_COMMENT_LENGTH).trim().optional(),
}).strict();

export type Marker = z.infer<typeof MarkerSchema>;

// ============================================================================
// Composition
// ============================================================================

export const CompositionSchema = z.object({
  id: EntityIdSchema,
  name: z.string().min(1).max(MAX_NAME_LENGTH).trim(),
  settings: CompositionSettingsSchema,
  layers: boundedArray(LayerSchema, 10000), // Max 10k layers per composition
  currentFrame: frameNumber,
  isNestedComp: z.boolean(),
  parentCompositionId: EntityIdSchema.optional(),
  workflowId: entityId.optional(),
  workflowInputs: boundedArray(WorkflowInputSchema, 1000).optional(), // Max 1000 workflow inputs
  workflowOutputs: boundedArray(WorkflowOutputSchema, 1000).optional(), // Max 1000 workflow outputs
  globalLight: GlobalLightSettingsSchema.optional(),
  markers: boundedArray(MarkerSchema, 10000).optional(), // Max 10k markers
}).strict().refine(
  (data) => {
    // currentFrame should be within composition bounds
    return data.currentFrame >= 0 && data.currentFrame < data.settings.frameCount;
  },
  { message: "currentFrame must be within composition frame range", path: ["currentFrame"] }
);

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
  min: z.object({ x: finiteNumber, y: finiteNumber, z: finiteNumber }).strict(),
  max: z.object({ x: finiteNumber, y: finiteNumber, z: finiteNumber }).strict(),
}).strict().refine(
  (data) => {
    // min < max for each component
    return (
      data.min.x < data.max.x &&
      data.min.y < data.max.y &&
      data.min.z < data.max.z
    );
  },
  { message: "min must be less than max for all components", path: ["min"] }
);

export type ModelBoundingBox = z.infer<typeof ModelBoundingBoxSchema>;

export const SVGViewBoxSchema = z.object({
  x: finiteNumber,
  y: finiteNumber,
  width: positiveFinite.max(100000), // Max 100k units width
  height: positiveFinite.max(100000), // Max 100k units height
}).strict();

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
}).strict();

export type MaterialMaps = z.infer<typeof MaterialMapsSchema>;

export const AssetReferenceSchema = z.object({
  id: EntityIdSchema,
  type: AssetTypeSchema,
  source: AssetSourceSchema,
  nodeId: entityId.optional(),
  width: positiveInt.max(16384), // Max reasonable dimension
  height: positiveInt.max(16384), // Max reasonable dimension
  data: z.union([base64OrDataUrl, url, z.string().max(MAX_STRING_LENGTH)]), // Base64/data URL, URL, or string
  filename: filename.optional(),

  // Video/Audio metadata
  frameCount: positiveInt.max(100000).optional(), // Max 100k frames
  duration: positiveFinite.max(86400).optional(), // Max 24 hours
  fps: positiveFinite.max(120).optional(), // Max 120 FPS
  hasAudio: z.boolean().optional(),
  audioChannels: z.number().int().min(1).max(8).optional(),
  sampleRate: positiveInt.max(192000).optional(), // Max 192kHz sample rate

  // 3D Model metadata
  modelFormat: ModelFormatSchema.optional(),
  modelBoundingBox: ModelBoundingBoxSchema.optional(),
  modelAnimations: boundedArray(z.string().max(MAX_ANIMATION_NAME_LENGTH).trim(), 1000).optional(), // Max 1000 animations
  modelMeshCount: positiveInt.max(100000).optional(), // Max 100k meshes
  modelVertexCount: positiveInt.max(10000000).optional(), // Max 10M vertices

  // Point cloud metadata
  pointCloudFormat: PointCloudFormatSchema.optional(),
  pointCount: positiveInt.max(100000000).optional(), // Max 100M points

  // Texture metadata
  textureMapType: TextureMapTypeSchema.optional(),
  textureColorSpace: z.enum(["srgb", "linear"]).optional(),

  // Material definition
  materialMaps: MaterialMapsSchema.optional(),

  // HDRI metadata
  hdriExposure: finiteNumber.min(-10).max(10).optional(), // Reasonable exposure range
  hdriRotation: finiteNumber.max(360).optional(), // Max 360 degrees rotation

  // SVG metadata
  svgPaths: positiveInt.max(100000).optional(), // Max 100k SVG paths
  svgViewBox: SVGViewBoxSchema.optional(),

  // Sprite sheet metadata
  spriteColumns: positiveInt.max(1000).optional(), // Max 1000 columns
  spriteRows: positiveInt.max(1000).optional(), // Max 1000 rows
  spriteCount: positiveInt.max(1000000).optional(), // Max 1M sprites
  spriteFrameRate: positiveFinite.max(120).optional(), // Max 120 FPS
}).strict().refine(
  (data) => {
    // If type is "model", modelFormat should be present
    if (data.type === "model" && !data.modelFormat) {
      return false;
    }
    return true;
  },
  { message: "modelFormat is required when type is 'model'", path: ["modelFormat"] }
).refine(
  (data) => {
    // If type is "pointcloud", pointCloudFormat should be present
    if (data.type === "pointcloud" && !data.pointCloudFormat) {
      return false;
    }
    return true;
  },
  { message: "pointCloudFormat is required when type is 'pointcloud'", path: ["pointCloudFormat"] }
).refine(
  (data) => {
    // If source is "url", data should be a URL
    if (data.source === "url" && typeof data.data === "string" && !data.data.startsWith("http")) {
      return false;
    }
    return true;
  },
  { message: "data must be a URL when source is 'url'", path: ["data"] }
).refine(
  (data) => {
    // Sprite sheet validation
    if (data.type === "spritesheet") {
      if (data.spriteColumns === undefined || data.spriteRows === undefined) {
        return false;
      }
      if (data.spriteCount !== undefined) {
        const expectedCount = data.spriteColumns * data.spriteRows;
        if (Math.abs(data.spriteCount - expectedCount) > 0.5) {
          return false;
        }
      }
    }
    return true;
  },
  { message: "spriteColumns and spriteRows are required for spritesheet, and spriteCount should match columns * rows", path: ["spriteColumns"] }
);

export type AssetReference = z.infer<typeof AssetReferenceSchema>;

// ============================================================================
// Data Asset
// ============================================================================

export const DataAssetTypeSchema = z.enum(["json", "csv", "tsv", "mgjson"]);

export type DataAssetType = z.infer<typeof DataAssetTypeSchema>;

export const DataAssetReferenceSchema = z.object({
  id: EntityIdSchema,
  name: z.string().min(1).max(MAX_NAME_LENGTH).trim(),
  type: DataAssetTypeSchema,
  rawContent: z.string().max(MAX_ARRAY_LENGTH), // Max content size
  lastModified: z.number().int().nonnegative(),
  sourceData: jsonSerializable.optional(),
  headers: boundedArray(z.string().max(200).trim(), 10000).optional(), // Max 10k headers
  rows: boundedArray(boundedArray(z.string().max(MAX_STRING_LENGTH), 10000), MAX_ARRAY_LENGTH).optional(), // Max rows and columns
  numRows: positiveInt.max(MAX_ARRAY_LENGTH).optional(),
  numColumns: positiveInt.max(10000).optional(),
}).strict().refine(
  (data) => {
    // If headers/rows are present, numRows/numColumns should match
    if (data.headers && data.numColumns !== undefined) {
      if (data.headers.length !== data.numColumns) {
        return false;
      }
    }
    if (data.rows && data.numRows !== undefined) {
      if (data.rows.length !== data.numRows) {
        return false;
      }
    }
    if (data.rows && data.headers) {
      // All rows should have same length as headers
      const headerCount = data.headers.length;
      if (!data.rows.every((row) => row.length === headerCount)) {
        return false;
      }
    }
    return true;
  },
  { message: "numRows/numColumns must match actual array lengths, and all rows must have same length as headers", path: ["numRows"] }
);

export type DataAssetReference = z.infer<typeof DataAssetReferenceSchema>;

// ============================================================================
// Project Meta
// ============================================================================

export const ProjectMetaSchema = z.object({
  name: z.string().min(1).max(MAX_NAME_LENGTH).trim(),
  created: iso8601DateTime,
  modified: iso8601DateTime,
  author: z.string().max(MAX_NAME_LENGTH).trim().optional(),
}).strict().refine(
  (data) => {
    // modified should be >= created
    const createdDate = new Date(data.created);
    const modifiedDate = new Date(data.modified);
    return modifiedDate >= createdDate;
  },
  { message: "modified must be >= created", path: ["modified"] }
);

export type ProjectMeta = z.infer<typeof ProjectMetaSchema>;

// ============================================================================
// Export Settings
// ============================================================================

export const ExportSettingsSchema = z.object({
  format: z.string().min(1).max(50).trim(), // Format name
  codec: z.string().max(50).trim().optional(), // Codec name
  quality: z.string().max(50).trim().optional(), // Quality setting
  resolution: z.object({
    width: positiveInt.max(16384), // Max reasonable dimension
    height: positiveInt.max(16384), // Max reasonable dimension
  }).strict().optional(),
  frameRate: positiveFinite.max(120).optional(), // Max 120 FPS
}).strict();

export type ExportSettings = z.infer<typeof ExportSettingsSchema>;

// ============================================================================
// Main Project Schema
// ============================================================================

export const LatticeProjectSchema = z.object({
  version: z.literal(PROJECT_VERSION),
  schemaVersion: positiveInt.max(1000).optional(), // Max schema version
  meta: ProjectMetaSchema,
  compositions: z.record(z.string().max(200), CompositionSchema).refine(
    (compositions) => Object.keys(compositions).length <= 1000,
    { message: "Maximum 1000 compositions allowed" }
  ),
  mainCompositionId: EntityIdSchema,
  composition: CompositionSettingsSchema, // Legacy alias
  assets: z.record(z.string().max(200), AssetReferenceSchema).refine(
    (assets) => Object.keys(assets).length <= 100000,
    { message: "Maximum 100k assets allowed" }
  ),
  dataAssets: z.record(z.string().max(200), DataAssetReferenceSchema).refine(
    (dataAssets) => Object.keys(dataAssets).length <= 10000,
    { message: "Maximum 10k data assets allowed" }
  ).optional(),
  layers: boundedArray(LayerSchema, 10000).optional(), // Max 10k layers (legacy)
  currentFrame: frameNumber,
  exportSettings: ExportSettingsSchema.optional(),
}).strict().refine(
  (data) => {
    // mainCompositionId should exist in compositions
    return data.mainCompositionId in data.compositions;
  },
  { message: "mainCompositionId must exist in compositions", path: ["mainCompositionId"] }
);

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
