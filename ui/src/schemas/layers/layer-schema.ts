/**
 * Main Layer Schema
 *
 * Zod schema for validating Layer objects.
 * All numeric values use .finite() to reject NaN/Infinity.
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

// ============================================================================
// Layer Type
// ============================================================================

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

// ============================================================================
// Matte Types
// ============================================================================

export const MatteTypeSchema = z.enum([
  "none",
  "alpha",
  "alpha-inverted",
  "luma",
  "luma-inverted",
]);

export type MatteType = z.infer<typeof MatteTypeSchema>;

// ============================================================================
// Effect Instance (simplified)
// ============================================================================

export const EffectInstanceSchema = z.object({
  id: EntityIdSchema,
  type: z.string(),
  name: z.string(),
  enabled: z.boolean(),
  expanded: z.boolean().optional(),
  params: z.record(z.union([
    finiteNumber,
    z.string(),
    z.boolean(),
    z.array(finiteNumber),
    z.object({ x: finiteNumber, y: finiteNumber }),
    z.object({ r: finiteNumber, g: finiteNumber, b: finiteNumber, a: finiteNumber }),
  ])).optional(),
});

export type EffectInstance = z.infer<typeof EffectInstanceSchema>;

// ============================================================================
// Layer Mask (simplified)
// ============================================================================

export const MaskModeSchema = z.enum([
  "add",
  "subtract",
  "intersect",
  "difference",
  "none",
]);

export const LayerMaskSchema = z.object({
  id: EntityIdSchema,
  name: z.string(),
  mode: MaskModeSchema,
  inverted: z.boolean(),
  opacity: AnimatableNumberSchema.optional(),
  feather: nonNegativeFinite.optional(),
  expansion: finiteNumber.optional(),
  locked: z.boolean().optional(),
  visible: z.boolean().optional(),
});

export type LayerMask = z.infer<typeof LayerMaskSchema>;

// ============================================================================
// Layer Styles (simplified)
// ============================================================================

export const LayerStylesSchema = z.object({
  dropShadow: z.object({
    enabled: z.boolean(),
    color: HexColorSchema.optional(),
    opacity: z.number().finite().min(0).max(100).optional(),
    angle: finiteNumber.optional(),
    distance: nonNegativeFinite.optional(),
    spread: nonNegativeFinite.optional(),
    size: nonNegativeFinite.optional(),
  }).optional(),
  innerShadow: z.object({
    enabled: z.boolean(),
    color: HexColorSchema.optional(),
    opacity: z.number().finite().min(0).max(100).optional(),
    angle: finiteNumber.optional(),
    distance: nonNegativeFinite.optional(),
    choke: nonNegativeFinite.optional(),
    size: nonNegativeFinite.optional(),
  }).optional(),
  outerGlow: z.object({
    enabled: z.boolean(),
    color: HexColorSchema.optional(),
    opacity: z.number().finite().min(0).max(100).optional(),
    spread: nonNegativeFinite.optional(),
    size: nonNegativeFinite.optional(),
  }).optional(),
  innerGlow: z.object({
    enabled: z.boolean(),
    color: HexColorSchema.optional(),
    opacity: z.number().finite().min(0).max(100).optional(),
    choke: nonNegativeFinite.optional(),
    size: nonNegativeFinite.optional(),
    source: z.enum(["center", "edge"]).optional(),
  }).optional(),
  bevelEmboss: z.object({
    enabled: z.boolean(),
    style: z.enum(["outer-bevel", "inner-bevel", "emboss", "pillow-emboss"]).optional(),
    depth: nonNegativeFinite.optional(),
    direction: z.enum(["up", "down"]).optional(),
    size: nonNegativeFinite.optional(),
    soften: nonNegativeFinite.optional(),
    angle: finiteNumber.optional(),
    altitude: finiteNumber.optional(),
    highlightColor: HexColorSchema.optional(),
    highlightOpacity: z.number().finite().min(0).max(100).optional(),
    shadowColor: HexColorSchema.optional(),
    shadowOpacity: z.number().finite().min(0).max(100).optional(),
  }).optional(),
  stroke: z.object({
    enabled: z.boolean(),
    color: HexColorSchema.optional(),
    size: nonNegativeFinite.optional(),
    position: z.enum(["outside", "inside", "center"]).optional(),
    opacity: z.number().finite().min(0).max(100).optional(),
  }).optional(),
}).optional();

export type LayerStyles = z.infer<typeof LayerStylesSchema>;

// ============================================================================
// Audio Settings
// ============================================================================

export const LayerAudioSchema = z.object({
  level: AnimatableNumberSchema,
});

export type LayerAudio = z.infer<typeof LayerAudioSchema>;

// ============================================================================
// Main Layer Schema
// ============================================================================

/**
 * Complete Layer schema for validation.
 */
export const LayerSchema = z.object({
  id: EntityIdSchema,
  name: z.string(),
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
  timeStretch: finiteNumber.optional(),
  stretchAnchor: z.enum(["startFrame", "endFrame", "currentFrame"]).optional(),

  // Hierarchy
  parentId: NullableEntityIdSchema,
  blendMode: BlendModeSchema,
  opacity: AnimatableNumberSchema,
  transform: LayerTransformSchema,

  // Audio
  audio: LayerAudioSchema.optional(),

  // Masking
  masks: z.array(LayerMaskSchema).optional(),
  matteType: MatteTypeSchema.optional(),
  matteLayerId: EntityIdSchema.optional(),
  matteCompositionId: EntityIdSchema.optional(),
  preserveTransparency: z.boolean().optional(),

  // Deprecated aliases
  /** @deprecated Use matteType instead */
  trackMatteType: MatteTypeSchema.optional(),
  /** @deprecated Use matteLayerId instead */
  trackMatteLayerId: EntityIdSchema.optional(),
  /** @deprecated Use matteCompositionId instead */
  trackMatteCompositionId: EntityIdSchema.optional(),

  // Properties and effects
  properties: z.array(AnimatablePropertySchema),
  effects: z.array(EffectInstanceSchema),

  // Layer styles
  layerStyles: LayerStylesSchema,

  // Layer-specific data
  data: LayerDataSchema,
});

export type Layer = z.infer<typeof LayerSchema>;

// ============================================================================
// Validation Helpers
// ============================================================================

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
