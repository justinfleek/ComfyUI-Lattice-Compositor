/**
 * Asset Schemas
 *
 * Zod schemas for asset references and metadata.
 * All numeric values use .finite() to reject NaN/Infinity.
 * Includes comprehensive validation constraints for security and data integrity.
 */

import { z } from "zod";
import { finiteNumber, nonNegativeFinite, positiveFinite, normalized01 } from "../layers/primitives-schema";
import {
  entityId,
  filename,
  url,
  base64OrDataUrl,
  mimeType,
  boundedArray,
  nonEmptyArray,
  jsonSerializable,
  MAX_NAME_LENGTH,
  MAX_ANIMATION_NAME_LENGTH,
  MAX_WARNING_LENGTH,
  MAX_ARRAY_LENGTH,
  MAX_STRING_LENGTH,
} from "../shared-validation";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Asset Type Enums
// ════════════════════════════════════════════════════════════════════════════

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

export const ModelFormatSchema = z.enum([
  "gltf",
  "glb",
  "obj",
  "fbx",
  "usd",
  "usda",
  "usdc",
  "usdz",
]);

export type ModelFormat = z.infer<typeof ModelFormatSchema>;

export const PointCloudFormatSchema = z.enum([
  "ply",
  "pcd",
  "las",
  "laz",
  "xyz",
  "pts",
]);

export type PointCloudFormat = z.infer<typeof PointCloudFormatSchema>;

export const AssetSourceSchema = z.enum([
  "comfyui_node",
  "file",
  "generated",
  "url",
]);

export type AssetSource = z.infer<typeof AssetSourceSchema>;

// ════════════════════════════════════════════════════════════════════════════
// Model Bounding Box
// ════════════════════════════════════════════════════════════════════════════

const Vec3Schema = z.object({
  x: finiteNumber,
  y: finiteNumber,
  z: finiteNumber,
}).strict();

export const ModelBoundingBoxSchema = z.object({
  min: Vec3Schema,
  max: Vec3Schema,
  center: Vec3Schema,
  size: Vec3Schema,
}).strict().refine(
  (data) => {
    // Validate min < max for each component
    return (
      data.min.x < data.max.x &&
      data.min.y < data.max.y &&
      data.min.z < data.max.z
    );
  },
  { message: "min must be less than max for all components", path: ["min"] }
).refine(
  (data) => {
    // Validate size matches max - min
    const expectedSize = {
      x: data.max.x - data.min.x,
      y: data.max.y - data.min.y,
      z: data.max.z - data.min.z,
    };
    const tolerance = 0.0001;
    return (
      Math.abs(data.size.x - expectedSize.x) < tolerance &&
      Math.abs(data.size.y - expectedSize.y) < tolerance &&
      Math.abs(data.size.z - expectedSize.z) < tolerance
    );
  },
  { message: "size must match max - min", path: ["size"] }
).refine(
  (data) => {
    // Validate center is between min and max
    return (
      data.min.x <= data.center.x && data.center.x <= data.max.x &&
      data.min.y <= data.center.y && data.center.y <= data.max.y &&
      data.min.z <= data.center.z && data.center.z <= data.max.z
    );
  },
  { message: "center must be between min and max", path: ["center"] }
);

export type ModelBoundingBox = z.infer<typeof ModelBoundingBoxSchema>;

// ════════════════════════════════════════════════════════════════════════════
// Material Maps
// ════════════════════════════════════════════════════════════════════════════

export const MaterialMapsSchema = z.object({
  albedo: entityId.optional(),
  normal: entityId.optional(),
  roughness: entityId.optional(),
  metalness: entityId.optional(),
  ao: entityId.optional(),
  emissive: entityId.optional(),
  height: entityId.optional(),
  opacity: entityId.optional(),
}).strict();

export type MaterialMaps = z.infer<typeof MaterialMapsSchema>;

// ════════════════════════════════════════════════════════════════════════════
//                                                                  // svg // v
// ════════════════════════════════════════════════════════════════════════════

export const SVGViewBoxSchema = z.object({
  x: finiteNumber,
  y: finiteNumber,
  width: positiveFinite,
  height: positiveFinite,
}).strict();

export type SVGViewBox = z.infer<typeof SVGViewBoxSchema>;

// ════════════════════════════════════════════════════════════════════════════
// Sprite Validation
// ════════════════════════════════════════════════════════════════════════════

export const SpriteValidationSchema = z.object({
  isPowerOfTwo: z.boolean(),
  hasAlpha: z.boolean(),
  originalFormat: z.string().max(50),
  warnings: boundedArray(z.string().max(MAX_WARNING_LENGTH), 100).optional(),
}).strict();

export type SpriteValidation = z.infer<typeof SpriteValidationSchema>;

// ════════════════════════════════════════════════════════════════════════════
// Asset Reference
// ════════════════════════════════════════════════════════════════════════════

export const AssetReferenceSchema = z.object({
  id: entityId,
  type: AssetTypeSchema,
  source: AssetSourceSchema,
  nodeId: entityId.optional(),
  width: positiveFinite.max(16384), // Max reasonable dimension
  height: positiveFinite.max(16384),
  data: z.union([base64OrDataUrl, url]), // Base64/data URL or URL
  filename: filename.optional(),

  // Video/Audio specific metadata
  frameCount: positiveFinite.max(100000).optional(), // Max reasonable frame count
  duration: nonNegativeFinite.max(86400).optional(), // Max 24 hours
  fps: positiveFinite.max(120).optional(), // Max reasonable FPS
  hasAudio: z.boolean().optional(),
  audioChannels: z.union([z.literal(1), z.literal(2)]).optional(),
  sampleRate: positiveFinite.max(192000).optional(), // Max reasonable sample rate

  // 3D Model metadata
  modelFormat: ModelFormatSchema.optional(),
  modelBoundingBox: ModelBoundingBoxSchema.optional(),
  modelAnimations: boundedArray(z.string().max(MAX_ANIMATION_NAME_LENGTH), 1000).optional(),
  modelMeshCount: nonNegativeFinite.max(100000).optional(),
  modelVertexCount: nonNegativeFinite.max(10000000).optional(), // 10M vertices max

  // Point cloud metadata
  pointCloudFormat: PointCloudFormatSchema.optional(),
  pointCount: nonNegativeFinite.max(100000000).optional(), // 100M points max

  // Texture metadata
  textureMapType: TextureMapTypeSchema.optional(),
  textureColorSpace: z.enum(["srgb", "linear"]).optional(),

  // Material definition
  materialMaps: MaterialMapsSchema.optional(),

  //                                                                      // hdri
  hdriExposure: finiteNumber.min(-10).max(10).optional(), // Reasonable exposure range
  hdriRotation: finiteNumber.optional(), // Rotation in degrees

  //                                                                       // svg
  svgPaths: nonNegativeFinite.max(100000).optional(),
  svgViewBox: SVGViewBoxSchema.optional(),

  // Sprite sheet metadata
  spriteColumns: positiveFinite.max(1000).optional(),
  spriteRows: positiveFinite.max(1000).optional(),
  spriteCount: nonNegativeFinite.max(1000000).optional(), // 1M sprites max
  spriteFrameRate: positiveFinite.max(120).optional(),

  // Sprite validation metadata
  spriteValidation: SpriteValidationSchema.optional(),
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
    if (data.source === "url" && !data.data.startsWith("http")) {
      return false;
    }
    return true;
  },
  { message: "data must be a URL when source is 'url'", path: ["data"] }
).refine(
  (data) => {
    // If type is "video" or "audio", duration should be present
    if ((data.type === "video" || data.type === "audio") && data.duration === undefined) {
      return false;
    }
    return true;
  },
  { message: "duration is required for video and audio assets", path: ["duration"] }
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

// ════════════════════════════════════════════════════════════════════════════
// Data Asset Reference
// ════════════════════════════════════════════════════════════════════════════

export const DataAssetTypeSchema = z.enum([
  "json",
  "csv",
  "tsv",
  "mgjson",
]);

export type DataAssetType = z.infer<typeof DataAssetTypeSchema>;

export const DataAssetReferenceSchema = z.object({
  id: entityId,
  name: z.string().min(1).max(MAX_NAME_LENGTH).trim(),
  type: DataAssetTypeSchema,
  rawContent: z.string().max(MAX_ARRAY_LENGTH), // Max content size
  lastModified: nonNegativeFinite,
  sourceData: jsonSerializable.optional(),
  headers: boundedArray(z.string().max(200), 10000).optional(), // Max 10k headers
  rows: boundedArray(boundedArray(z.string().max(MAX_STRING_LENGTH), 10000), MAX_ARRAY_LENGTH).optional(),
  numRows: nonNegativeFinite.max(MAX_ARRAY_LENGTH).optional(),
  numColumns: nonNegativeFinite.max(10000).optional(),
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
