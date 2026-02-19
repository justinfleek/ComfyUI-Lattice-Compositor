/**
 * Effect Schemas
 *
 * Zod schemas for effects, effect parameters, and effect instances.
 * All numeric values use .finite() to reject NaN/Infinity.
 * Includes comprehensive validation constraints for security and data integrity.
 */

import { z } from "zod";
import { finiteNumber, normalized01, positiveFinite } from "../layers/primitives-schema";
import { AnimatablePropertySchema, PropertyValueSchema } from "../layers/animation-schema";
import { WarpPinSchema, WarpMeshSchema } from "../meshWarp/meshWarp-schema";
import {
  entityId,
  boundedArray,
  nonEmptyArray,
  shaderCode,
  MAX_NAME_LENGTH,
  MAX_DESCRIPTION_LENGTH,
} from "../shared-validation";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Effect Category
// ═══════════════════════════════════════════════════════════════════════════

export const EffectCategorySchema = z.enum([
  "blur-sharpen",
  "color-correction",
  "distort",
  "generate",
  "keying",
  "matte",
  "noise-grain",
  "perspective",
  "stylize",
  "time",
  "transition",
  "utility",
]);

export type EffectCategory = z.infer<typeof EffectCategorySchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Effect Parameter Type
// ═══════════════════════════════════════════════════════════════════════════

export const EffectParameterTypeSchema = z.enum([
  "number",
  "color",
  "point",
  "point3D",
  "angle",
  "checkbox",
  "dropdown",
  "layer",
  "string",
  "curve",
  "data",
]);

export type EffectParameterType = z.infer<typeof EffectParameterTypeSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Effect Parameter Option
// ═══════════════════════════════════════════════════════════════════════════

export const EffectParameterOptionSchema = z.object({
  label: z.string().min(1).max(200).trim(),
  value: z.union([z.string().max(500), finiteNumber]),
}).strict();

export type EffectParameterOption = z.infer<typeof EffectParameterOptionSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Effect Parameter
// ═══════════════════════════════════════════════════════════════════════════

export const EffectParameterSchema = z.object({
  id: entityId,
  name: z.string().min(1).max(MAX_NAME_LENGTH).trim(),
  type: EffectParameterTypeSchema,
  value: PropertyValueSchema,
  defaultValue: PropertyValueSchema,
  min: finiteNumber.optional(),
  max: finiteNumber.optional(),
  step: positiveFinite.optional(),
  options: nonEmptyArray(EffectParameterOptionSchema).optional(),
  animatable: z.boolean(),
  group: z.string().max(MAX_NAME_LENGTH).optional(),
}).strict().refine(
  (data) => {
    // If type is "dropdown", options must be present
    if (data.type === "dropdown" && (!data.options || data.options.length === 0)) {
      return false;
    }
    return true;
  },
  { message: "options array is required for dropdown type", path: ["options"] }
).refine(
  (data) => {
    // min <= max when both present
    if (data.min !== undefined && data.max !== undefined && data.min > data.max) {
      return false;
    }
    return true;
  },
  { message: "min must be <= max when both are present", path: ["min"] }
).refine(
  (data) => {
    // step must be positive when present
    if (data.step !== undefined && data.step <= 0) {
      return false;
    }
    return true;
  },
  { message: "step must be positive", path: ["step"] }
);

export type EffectParameter = z.infer<typeof EffectParameterSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Effect Definition
// ═══════════════════════════════════════════════════════════════════════════

// Base schema for EffectParameter without refinements (for omit/extend)
const EffectParameterBaseSchema = z.object({
  id: entityId,
  name: z.string().min(1).max(MAX_NAME_LENGTH).trim(),
  type: EffectParameterTypeSchema,
  value: PropertyValueSchema,
  defaultValue: PropertyValueSchema,
  min: finiteNumber.optional(),
  max: finiteNumber.optional(),
  step: positiveFinite.optional(),
  options: nonEmptyArray(EffectParameterOptionSchema).optional(),
  animatable: z.boolean(),
  group: z.string().max(MAX_NAME_LENGTH).optional(),
});

export const EffectDefinitionSchema = z.object({
  name: z.string().min(1).max(MAX_NAME_LENGTH).trim(),
  category: EffectCategorySchema,
  description: z.string().max(MAX_DESCRIPTION_LENGTH).trim(),
  parameters: boundedArray(
    EffectParameterBaseSchema.omit({ id: true, value: true }),
    1000 // Max 1000 parameters per effect
  ),
  fragmentShader: shaderCode.optional(),
}).strict();

export type EffectDefinition = z.infer<typeof EffectDefinitionSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Effect
// ═══════════════════════════════════════════════════════════════════════════

export const EffectSchema = z.object({
  id: entityId,
  name: z.string().min(1).max(MAX_NAME_LENGTH).trim(),
  category: EffectCategorySchema,
  enabled: z.boolean(),
  expanded: z.boolean(),
  parameters: boundedArray(EffectParameterSchema, 1000),
  fragmentShader: shaderCode.optional(),
}).strict();

export type Effect = z.infer<typeof EffectSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Effect Instance
// ═══════════════════════════════════════════════════════════════════════════

export const EffectInstanceSchema = z.object({
  id: entityId,
  effectKey: z.string().min(1).max(200).trim(), // Key into EFFECT_DEFINITIONS
  name: z.string().min(1).max(MAX_NAME_LENGTH).trim(),
  category: EffectCategorySchema,
  enabled: z.boolean(),
  expanded: z.boolean(),
  parameters: z.record(z.string().max(200), AnimatablePropertySchema).refine(
    (params) => Object.keys(params).length <= 1000,
    { message: "Maximum 1000 parameters allowed" }
  ),
}).strict();

export type EffectInstance = z.infer<typeof EffectInstanceSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Mesh Deform Effect Instance
// ═══════════════════════════════════════════════════════════════════════════

export const MeshDeformEffectInstanceSchema = EffectInstanceSchema.extend({
  effectKey: z.literal("mesh-deform"),
  pins: boundedArray(WarpPinSchema, 10000), // Max 10k pins
  cachedMesh: WarpMeshSchema.optional(),
  meshDirty: z.boolean(),
}).strict();

export type MeshDeformEffectInstance = z.infer<typeof MeshDeformEffectInstanceSchema>;
