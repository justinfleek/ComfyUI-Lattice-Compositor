/**
 * Preset Schemas
 *
 * Zod schemas for preset system (particles, effects, animations, etc.).
 * All numeric values use .finite() to reject NaN/Infinity.
 * Includes comprehensive validation constraints for security and data integrity.
 */

import { z } from "zod";
import { finiteNumber, normalized01, positiveFinite, nonNegativeFinite, Vec3Schema } from "../layers/primitives-schema";
import { KeyframeSchema } from "../layers/animation-schema";
import { SplinePathEffectSchema } from "../layers/layer-data-schema";
import { PropertyValueSchema } from "../layers/animation-schema";
import {
  entityId,
  boundedArray,
  iso8601DateTime,
  base64OrDataUrl,
  MAX_NAME_LENGTH,
  MAX_DESCRIPTION_LENGTH,
  MAX_TAG_LENGTH,
  MAX_TAGS_COUNT,
} from "../shared-validation";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Preset Category
// ═══════════════════════════════════════════════════════════════════════════

export const PresetCategorySchema = z.enum([
  "particle",
  "effect",
  "animation",
  "camera-shake",
  "camera-trajectory",
  "path-effect",
  "text-style",
  "color-palette",
]);

export type PresetCategory = z.infer<typeof PresetCategorySchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Preset Metadata
// ═══════════════════════════════════════════════════════════════════════════

// Base schema without refinements (for extend)
const PresetMetadataBaseSchema = z.object({
  id: entityId,
  name: z.string().min(1).max(MAX_NAME_LENGTH).trim(),
  category: PresetCategorySchema,
  description: z.string().max(MAX_DESCRIPTION_LENGTH).trim().optional(),
  tags: boundedArray(z.string().max(MAX_TAG_LENGTH).min(1).trim(), MAX_TAGS_COUNT).optional(),
  author: z.string().max(MAX_NAME_LENGTH).trim().optional(),
  createdAt: iso8601DateTime,
  updatedAt: iso8601DateTime,
  thumbnail: base64OrDataUrl.optional(),
  isBuiltIn: z.boolean().optional(),
  version: z.number().int().positive().max(1000).optional(), // Max version 1000
});

export const PresetMetadataSchema = PresetMetadataBaseSchema.strict().refine(
  (data) => data.updatedAt >= data.createdAt,
  { message: "updatedAt must be >= createdAt", path: ["updatedAt"] }
);

export type PresetMetadata = z.infer<typeof PresetMetadataSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Particle Preset Config
// ═══════════════════════════════════════════════════════════════════════════

export const ParticlePresetConfigSchema = z.object({
  maxParticles: positiveFinite.max(10000000).optional(), // Max 10M particles
  gravity: finiteNumber.min(-1000).max(1000).optional(), // Reasonable gravity range
  turbulenceStrength: normalized01.optional(),
  emissionRate: positiveFinite.max(100000).optional(), // Max 100k particles/sec
  lifespan: positiveFinite.max(3600).optional(), // Max 1 hour lifespan
  startSize: positiveFinite.max(10000).optional(),
  endSize: positiveFinite.max(10000).optional(),
  startColor: z.string().regex(/^#[0-9A-Fa-f]{6,8}$/).optional(), // Hex color
  endColor: z.string().regex(/^#[0-9A-Fa-f]{6,8}$/).optional(),
  velocitySpread: normalized01.optional(),
}).strict().refine(
  (data) => {
    // endSize should be >= 0 if both present
    if (data.startSize !== undefined && data.endSize !== undefined && data.endSize < 0) {
      return false;
    }
    return true;
  },
  { message: "endSize must be >= 0", path: ["endSize"] }
);

export type ParticlePresetConfig = z.infer<typeof ParticlePresetConfigSchema>;

export const ParticlePresetSchema = PresetMetadataBaseSchema.extend({
  category: z.literal("particle"),
  config: ParticlePresetConfigSchema,
}).strict().refine(
  (data) => data.updatedAt >= data.createdAt,
  { message: "updatedAt must be >= createdAt", path: ["updatedAt"] }
);

export type ParticlePreset = z.infer<typeof ParticlePresetSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Effect Preset
// ═══════════════════════════════════════════════════════════════════════════

export const EffectPresetSchema = PresetMetadataBaseSchema.extend({
  category: z.literal("effect"),
  effects: boundedArray(
    z.object({
      type: z.string().min(1).max(200).trim(),
      params: z.record(z.string().max(200), PropertyValueSchema).refine(
        (params) => Object.keys(params).length <= 1000,
        { message: "Maximum 1000 parameters per effect" }
      ),
    }).strict(),
    1000 // Max 1000 effects per preset
  ).min(1), // At least 1 effect
}).strict().refine(
  (data) => data.updatedAt >= data.createdAt,
  { message: "updatedAt must be >= createdAt", path: ["updatedAt"] }
);

export type EffectPreset = z.infer<typeof EffectPresetSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Path Effect Preset
// ═══════════════════════════════════════════════════════════════════════════

export const PathEffectPresetSchema = PresetMetadataBaseSchema.extend({
  category: z.literal("path-effect"),
  effects: boundedArray(SplinePathEffectSchema, 1000).min(1),
}).strict().refine(
  (data) => data.updatedAt >= data.createdAt,
  { message: "updatedAt must be >= createdAt", path: ["updatedAt"] }
);

export type PathEffectPreset = z.infer<typeof PathEffectPresetSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Camera Shake Config Schema
// ═══════════════════════════════════════════════════════════════════════════

export const CameraShakeConfigSchema = z.object({
  enabled: z.boolean(),
  type: z.enum(["handheld", "impact", "earthquake", "subtle", "custom"]),
  intensity: normalized01,
  frequency: positiveFinite.max(100), // Max 100 Hz
  rotationEnabled: z.boolean(),
  rotationScale: normalized01,
  seed: z.number().int().nonnegative().max(2147483647), // Max 32-bit int
  decay: normalized01,
  startFrame: z.number().int().nonnegative().max(100000), // Max 100k frames
  duration: positiveFinite.max(100000), // Max 100k frames duration
}).strict();

export type CameraShakeConfig = z.infer<typeof CameraShakeConfigSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Camera Trajectory Config Schema
// ═══════════════════════════════════════════════════════════════════════════

export const CameraTrajectoryConfigSchema = z.object({
  position: boundedArray(
    z.object({
      frame: z.number().int().nonnegative().max(100000),
      position: Vec3Schema,
    }).strict(),
    100000 // Max 100k keyframes
  ),
  pointOfInterest: boundedArray(
    z.object({
      frame: z.number().int().nonnegative().max(100000),
      pointOfInterest: Vec3Schema,
    }).strict(),
    100000 // Max 100k keyframes
  ),
  zoom: boundedArray(
    z.object({
      frame: z.number().int().nonnegative().max(100000),
      zoom: positiveFinite.max(1000), // Max 1000x zoom
    }).strict(),
    100000 // Max 100k keyframes
  ).optional(),
}).strict();

export type CameraTrajectoryConfig = z.infer<typeof CameraTrajectoryConfigSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Camera Shake Preset
// ═══════════════════════════════════════════════════════════════════════════

export const CameraShakePresetSchema = PresetMetadataBaseSchema.extend({
  category: z.literal("camera-shake"),
  config: CameraShakeConfigSchema,
}).strict().refine(
  (data) => data.updatedAt >= data.createdAt,
  { message: "updatedAt must be >= createdAt", path: ["updatedAt"] }
);

export type CameraShakePreset = z.infer<typeof CameraShakePresetSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Camera Trajectory Preset
// ═══════════════════════════════════════════════════════════════════════════

export const CameraTrajectoryPresetSchema = PresetMetadataBaseSchema.extend({
  category: z.literal("camera-trajectory"),
  config: CameraTrajectoryConfigSchema,
}).strict().refine(
  (data) => data.updatedAt >= data.createdAt,
  { message: "updatedAt must be >= createdAt", path: ["updatedAt"] }
);

export type CameraTrajectoryPreset = z.infer<typeof CameraTrajectoryPresetSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Text Style Preset
// ═══════════════════════════════════════════════════════════════════════════

export const TextStylePresetSchema = PresetMetadataBaseSchema.extend({
  category: z.literal("text-style"),
  style: z.object({
    fontFamily: z.string().max(200).trim().optional(),
    fontSize: positiveFinite.max(1000).optional(), // Max 1000pt font size
    fontWeight: z.union([
      z.string().max(50).trim(),
      z.number().int().min(100).max(900),
    ]).optional(),
    fill: z.string().regex(/^#[0-9A-Fa-f]{6,8}$/).optional(),
    stroke: z.string().regex(/^#[0-9A-Fa-f]{6,8}$/).optional(),
    strokeWidth: positiveFinite.max(1000).optional(),
    letterSpacing: finiteNumber.min(-100).max(100).optional(), // Reasonable letter spacing
    lineHeight: positiveFinite.max(100).optional(), // Max 100x line height
    textAlign: z.enum(["left", "center", "right", "justify"]).optional(),
  }).strict(),
}).strict().refine(
  (data) => data.updatedAt >= data.createdAt,
  { message: "updatedAt must be >= createdAt", path: ["updatedAt"] }
);

export type TextStylePreset = z.infer<typeof TextStylePresetSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Color Palette Preset
// ═══════════════════════════════════════════════════════════════════════════

export const ColorPalettePresetSchema = PresetMetadataBaseSchema.extend({
  category: z.literal("color-palette"),
  colors: boundedArray(
    z.string().regex(/^#[0-9A-Fa-f]{6,8}$/), // Hex colors
    1000 // Max 1000 colors
  ).min(1), // At least 1 color
}).strict().refine(
  (data) => data.updatedAt >= data.createdAt,
  { message: "updatedAt must be >= createdAt", path: ["updatedAt"] }
);

export type ColorPalettePreset = z.infer<typeof ColorPalettePresetSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Animation Preset
// ═══════════════════════════════════════════════════════════════════════════

export const AnimationPresetSchema = PresetMetadataBaseSchema.extend({
  category: z.literal("animation"),
  keyframes: boundedArray(KeyframeSchema, 100000).min(1), // Max 100k keyframes
}).strict().refine(
  (data) => data.updatedAt >= data.createdAt,
  { message: "updatedAt must be >= createdAt", path: ["updatedAt"] }
);

export type AnimationPreset = z.infer<typeof AnimationPresetSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Union Preset Type
// ═══════════════════════════════════════════════════════════════════════════

// Base schemas without refinements for discriminated union
const ParticlePresetBaseSchema = PresetMetadataBaseSchema.extend({
  category: z.literal("particle"),
  config: ParticlePresetConfigSchema,
}).strict();

const EffectPresetBaseSchema = PresetMetadataBaseSchema.extend({
  category: z.literal("effect"),
  effects: boundedArray(
    z.object({
      type: z.string().min(1).max(200).trim(),
      params: z.record(z.string().max(200), PropertyValueSchema).refine(
        (params) => Object.keys(params).length <= 1000,
        { message: "Maximum 1000 parameters per effect" }
      ),
    }).strict(),
    1000
  ).min(1),
}).strict();

const PathEffectPresetBaseSchema = PresetMetadataBaseSchema.extend({
  category: z.literal("path-effect"),
  effects: boundedArray(SplinePathEffectSchema, 1000).min(1),
}).strict();

const CameraShakePresetBaseSchema = PresetMetadataBaseSchema.extend({
  category: z.literal("camera-shake"),
  config: CameraShakeConfigSchema,
}).strict();

const CameraTrajectoryPresetBaseSchema = PresetMetadataBaseSchema.extend({
  category: z.literal("camera-trajectory"),
  config: CameraTrajectoryConfigSchema,
}).strict();

const TextStylePresetBaseSchema = PresetMetadataBaseSchema.extend({
  category: z.literal("text-style"),
  style: z.object({
    fontFamily: z.string().max(200).trim().optional(),
    fontSize: positiveFinite.max(1000).optional(),
    fontWeight: z.union([
      z.string().max(50).trim(),
      z.number().int().min(100).max(900),
    ]).optional(),
    fill: z.string().regex(/^#[0-9A-Fa-f]{6,8}$/).optional(),
    stroke: z.string().regex(/^#[0-9A-Fa-f]{6,8}$/).optional(),
    strokeWidth: positiveFinite.max(1000).optional(),
    letterSpacing: finiteNumber.min(-100).max(100).optional(),
    lineHeight: positiveFinite.max(100).optional(),
    textAlign: z.enum(["left", "center", "right", "justify"]).optional(),
  }).strict(),
}).strict();

const ColorPalettePresetBaseSchema = PresetMetadataBaseSchema.extend({
  category: z.literal("color-palette"),
  colors: boundedArray(
    z.string().regex(/^#[0-9A-Fa-f]{6,8}$/),
    1000
  ).min(1),
}).strict();

const AnimationPresetBaseSchema = PresetMetadataBaseSchema.extend({
  category: z.literal("animation"),
  keyframes: boundedArray(KeyframeSchema, 100000).min(1),
}).strict();

export const PresetSchema = z.discriminatedUnion("category", [
  ParticlePresetBaseSchema,
  EffectPresetBaseSchema,
  PathEffectPresetBaseSchema,
  CameraShakePresetBaseSchema,
  CameraTrajectoryPresetBaseSchema,
  TextStylePresetBaseSchema,
  ColorPalettePresetBaseSchema,
  AnimationPresetBaseSchema,
]).refine(
  (data) => data.updatedAt >= data.createdAt,
  { message: "updatedAt must be >= createdAt", path: ["updatedAt"] }
);

export type Preset = z.infer<typeof PresetSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Preset Collection Schema
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Preset Collection
 * Used for preset import/export and localStorage storage
 */
export const PresetCollectionSchema = z.object({
  version: z.number().int().positive().max(1000), // Max version 1000
  presets: boundedArray(PresetSchema, 10000), // Max 10k presets
  exportedAt: z.number().int().nonnegative().max(2147483647000), // Max timestamp (year 2038)
}).strict();

export type PresetCollection = z.infer<typeof PresetCollectionSchema>;
