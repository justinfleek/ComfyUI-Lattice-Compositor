/**
 * Main Layer Schema
 *
 * Zod schema for validating Layer objects.
 * All numeric values use .finite() to reject NaN/Infinity.
 * Includes comprehensive validation constraints for security and data integrity.
 */

import { z } from "zod";
import {
  finiteNumber,
  nonNegativeFinite,
  frameNumber,
  EntityIdSchema,
  NullableEntityIdSchema,
  BlendModeSchema,
  QualityModeSchema,
  HexColorSchema,
} from "./primitives-schema";
import {
  AnimatableNumberSchema,
  AnimatablePropertySchema,
} from "./animation-schema";
import {
  LayerTransformSchema,
  LayerMotionBlurSettingsSchema,
  LayerMaterialOptionsSchema,
  AutoOrientModeSchema,
  FollowPathConstraintSchema,
  AudioPathAnimationSchema,
} from "./transform-schema";
import { LayerDataSchema } from "./layer-data-schema";
import {
  boundedArray,
  MAX_NAME_LENGTH,
} from "../shared-validation";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Layer Type
// ════════════════════════════════════════════════════════════════════════════

/**
 * All layer types supported by the compositor.
 */
export const LayerTypeSchema = z.enum([
  "depth",
  "normal",
  "spline",
  "path",
  "text",
  "shape",
  "particle",
  "particles",
  "depthflow",
  "image",
  "video",
  "audio",
  "generated",
  "camera",
  "light",
  "solid",
  "control",
  "null", // @deprecated
  "group",
  "nestedComp",
  "matte",
  "model",
  "pointcloud",
  "pose",
  "effectLayer",
  "adjustment", // @deprecated
]);

export type LayerType = z.infer<typeof LayerTypeSchema>;

// ════════════════════════════════════════════════════════════════════════════
// Matte Types
// ════════════════════════════════════════════════════════════════════════════

import { MatteTypeSchema as MatteTypeSchemaFull } from "../masks/masks-schema";
export { MatteTypeSchemaFull as MatteTypeSchema };
export type { MatteType } from "../masks/masks-schema";

// ════════════════════════════════════════════════════════════════════════════
// Effect Instance
// ════════════════════════════════════════════════════════════════════════════

import { EffectInstanceSchema as EffectInstanceSchemaFull } from "../effects/effects-schema";
export { EffectInstanceSchemaFull as EffectInstanceSchema };
export type { EffectInstance } from "../effects/effects-schema";

// ════════════════════════════════════════════════════════════════════════════
// Layer Mask
// ════════════════════════════════════════════════════════════════════════════

import { LayerMaskSchema as LayerMaskSchemaFull, MaskModeSchema as MaskModeSchemaFull } from "../masks/masks-schema";
export { LayerMaskSchemaFull as LayerMaskSchema, MaskModeSchemaFull as MaskModeSchema };
export type { LayerMask, MaskMode } from "../masks/masks-schema";

// ════════════════════════════════════════════════════════════════════════════
// Layer Styles
// ════════════════════════════════════════════════════════════════════════════

import { LayerStylesSchema as LayerStylesSchemaFull } from "../layerStyles/layerStyles-schema";
export { LayerStylesSchemaFull as LayerStylesSchema };
export type { LayerStyles } from "../layerStyles/layerStyles-schema";

// ════════════════════════════════════════════════════════════════════════════
// Audio Settings
// ════════════════════════════════════════════════════════════════════════════

export const LayerAudioSchema = z.object({
  level: AnimatableNumberSchema,
}).strict();

export type LayerAudio = z.infer<typeof LayerAudioSchema>;

// ════════════════════════════════════════════════════════════════════════════
// Main Layer Schema
// ════════════════════════════════════════════════════════════════════════════

/**
 * Complete Layer schema for validation.
 */
export const LayerSchema = z.object({
  id: EntityIdSchema,
  name: z.string().min(1).max(MAX_NAME_LENGTH).trim(),
  type: LayerTypeSchema,
  visible: z.boolean(),
  locked: z.boolean(),
  isolate: z.boolean(),
  minimized: z.boolean().optional(),
  threeD: z.boolean(),
  autoOrient: AutoOrientModeSchema.optional(),
  followPath: FollowPathConstraintSchema.optional(),
  audioPathAnimation: AudioPathAnimationSchema.optional(),
  motionBlur: z.boolean(),
  motionBlurSettings: LayerMotionBlurSettingsSchema.optional(),
  flattenTransform: z.boolean().optional(),
  quality: QualityModeSchema.optional(),
  effectsEnabled: z.boolean().optional(),
  frameBlending: z.boolean().optional(),
  effectLayer: z.boolean().optional(),
  /** @deprecated Use effectLayer instead */
  adjustmentLayer: z.boolean().optional(),
  audioEnabled: z.boolean().optional(),
  labelColor: HexColorSchema.optional(),

  // 3D Material Options
  materialOptions: LayerMaterialOptionsSchema.optional(),

  // Timing
  startFrame: frameNumber,
  endFrame: frameNumber,
  /** @deprecated Use startFrame instead */
  inPoint: frameNumber.optional(),
  /** @deprecated Use endFrame instead */
  outPoint: frameNumber.optional(),

  // Time Stretch
  timeStretch: finiteNumber.min(0.01).max(100).optional(), // Max 100x stretch
  stretchAnchor: z.enum(["startFrame", "endFrame", "currentFrame"]).optional(),

  // Hierarchy
  parentId: NullableEntityIdSchema,
  blendMode: BlendModeSchema,
  opacity: AnimatableNumberSchema,
  transform: LayerTransformSchema,

  // Audio
  audio: LayerAudioSchema.optional(),

  // Masking
  masks: boundedArray(LayerMaskSchemaFull, 100).optional(), // Max 100 masks per layer
  matteType: MatteTypeSchemaFull.optional(),
  matteLayerId: EntityIdSchema.optional(),
  matteCompositionId: EntityIdSchema.optional(),
  preserveTransparency: z.boolean().optional(),

  // Deprecated aliases
  /** @deprecated Use matteType instead */
  trackMatteType: MatteTypeSchemaFull.optional(),
  /** @deprecated Use matteLayerId instead */
  trackMatteLayerId: EntityIdSchema.optional(),
  /** @deprecated Use matteCompositionId instead */
  trackMatteCompositionId: EntityIdSchema.optional(),

  // Properties and effects
  properties: boundedArray(AnimatablePropertySchema, 10000), // Max 10k properties per layer
  effects: boundedArray(EffectInstanceSchemaFull, 1000), // Max 1000 effects per layer

  // Layer styles
  layerStyles: LayerStylesSchemaFull,

  // Layer-specific data
  data: LayerDataSchema,
}).strict().refine(
  (data) => {
    // endFrame should be >= startFrame
    return data.endFrame >= data.startFrame;
  },
  { message: "endFrame must be >= startFrame", path: ["endFrame"] }
);

export type Layer = z.infer<typeof LayerSchema>;

// ════════════════════════════════════════════════════════════════════════════
// Validation Helpers
// ════════════════════════════════════════════════════════════════════════════

/**
 * Validate a layer object.
 */
export function validateLayer(data: unknown): Layer {
  return LayerSchema.parse(data);
}

/**
 * Safely validate a layer object (returns success/error).
 */
export function safeValidateLayer(data: unknown) {
  return LayerSchema.safeParse(data);
}
