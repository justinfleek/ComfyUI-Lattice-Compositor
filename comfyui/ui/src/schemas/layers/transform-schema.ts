/**
 * Transform Schemas
 *
 * Zod schemas for layer transforms and related types.
 * All numeric values use .finite() to reject NaN/Infinity.
 * Includes comprehensive validation constraints for security and data integrity.
 */

import { z } from "zod";
import {
  finiteNumber,
  normalized01,
  positiveInt,
  EntityIdSchema,
} from "./primitives-schema";
import {
  AnimatableNumberSchema,
  AnimatablePositionSchema,
  AnimatableVec3Schema,
} from "./animation-schema";
import {
  entityId,
  MAX_NAME_LENGTH,
} from "../shared-validation";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Separate Dimensions
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Flags for using separate X/Y/Z properties.
 */
export const SeparateDimensionsSchema = z.object({
  position: z.boolean(),
  scale: z.boolean(),
}).strict();

export type SeparateDimensions = z.infer<typeof SeparateDimensionsSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Layer Transform
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Full layer transform schema.
 */
export const LayerTransformSchema = z.object({
  position: AnimatablePositionSchema,
  positionX: AnimatableNumberSchema.optional(),
  positionY: AnimatableNumberSchema.optional(),
  positionZ: AnimatableNumberSchema.optional(),

  origin: AnimatablePositionSchema,
  /** @deprecated Use 'origin' instead */
  anchorPoint: AnimatablePositionSchema.optional(),

  scale: AnimatablePositionSchema,
  scaleX: AnimatableNumberSchema.optional(),
  scaleY: AnimatableNumberSchema.optional(),
  scaleZ: AnimatableNumberSchema.optional(),

  rotation: AnimatableNumberSchema,

  orientation: AnimatableVec3Schema.optional(),
  rotationX: AnimatableNumberSchema.optional(),
  rotationY: AnimatableNumberSchema.optional(),
  rotationZ: AnimatableNumberSchema.optional(),

  separateDimensions: SeparateDimensionsSchema.optional(),
}).strict();

export type LayerTransform = z.infer<typeof LayerTransformSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Motion Blur
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Motion blur type.
 */
export const MotionBlurTypeSchema = z.enum([
  "standard",
  "pixel",
  "directional",
  "radial",
  "vector",
  "adaptive",
]);

export type MotionBlurType = z.infer<typeof MotionBlurTypeSchema>;

/**
 * Layer motion blur settings.
 */
export const LayerMotionBlurSettingsSchema = z.object({
  type: MotionBlurTypeSchema,
  shutterAngle: z.number().finite().min(0).max(720),
  shutterPhase: z.number().finite().min(-180).max(180),
  samplesPerFrame: z.number().int().min(2).max(64),
  direction: finiteNumber.optional(),
  blurLength: finiteNumber.min(0).max(1000).optional(), // Max reasonable blur length
  radialMode: z.enum(["spin", "zoom"]).optional(),
  radialCenterX: normalized01.optional(),
  radialCenterY: normalized01.optional(),
  radialAmount: z.number().finite().min(0).max(100).optional(),
}).strict();

export type LayerMotionBlurSettings = z.infer<typeof LayerMotionBlurSettingsSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Material Options
// ═══════════════════════════════════════════════════════════════════════════

/**
 * 3D material options for layers.
 */
export const LayerMaterialOptionsSchema = z.object({
  castsShadows: z.enum(["off", "on", "only"]),
  lightTransmission: z.number().finite().min(0).max(100),
  acceptsShadows: z.boolean(),
  acceptsLights: z.boolean(),
  ambient: z.number().finite().min(0).max(100),
  diffuse: z.number().finite().min(0).max(100),
  specularIntensity: z.number().finite().min(0).max(100),
  specularShininess: z.number().finite().min(0).max(100),
  metal: z.number().finite().min(0).max(100),
}).strict();

export type LayerMaterialOptions = z.infer<typeof LayerMaterialOptionsSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Auto-Orient
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Auto-orient mode.
 */
export const AutoOrientModeSchema = z.enum([
  "off",
  "toCamera",
  "alongPath",
  "toPointOfInterest",
]);

export type AutoOrientMode = z.infer<typeof AutoOrientModeSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Follow Path Constraint
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Follow path constraint for positioning along a path.
 */
export const FollowPathConstraintSchema = z.object({
  enabled: z.boolean(),
  pathLayerId: entityId,
  progress: AnimatableNumberSchema,
  offset: AnimatablePositionSchema.optional(),
  autoOrient: z.boolean().optional(),
  orientOffset: AnimatableNumberSchema.optional(),
  loop: z.boolean().optional(),
  pingPong: z.boolean().optional(),
}).strict();

export type FollowPathConstraint = z.infer<typeof FollowPathConstraintSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Audio Path Animation
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Audio-driven path animation.
 */
export const AudioPathAnimationSchema = z.object({
  enabled: z.boolean(),
  pathLayerId: entityId,
  audioLayerId: entityId,
  feature: z.enum(["amplitude", "bass", "mid", "treble", "spectral"]),
  sensitivity: z.number().finite().min(0).max(2),
  smoothing: z.number().finite().min(0).max(1),
  offset: finiteNumber,
  loop: z.boolean(),
}).strict();

export type AudioPathAnimation = z.infer<typeof AudioPathAnimationSchema>;
