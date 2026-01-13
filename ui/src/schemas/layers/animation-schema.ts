/**
 * Animation Schemas
 *
 * Zod schemas for keyframes, animatable properties, and expressions.
 * All numeric values use .finite() to reject NaN/Infinity.
 */

import { z } from "zod";
import {
  finiteNumber,
  frameNumber,
  EntityIdSchema,
  Vec3Schema,
  Position2DOr3DSchema,
  RGBAColorSchema,
} from "./primitives-schema";

// ============================================================================
// Interpolation Types
// ============================================================================

/**
 * Base interpolation types.
 */
export const BaseInterpolationTypeSchema = z.enum(["linear", "bezier", "hold"]);

export type BaseInterpolationType = z.infer<typeof BaseInterpolationTypeSchema>;

/**
 * All easing function names.
 */
export const EasingTypeSchema = z.enum([
  "easeInSine",
  "easeOutSine",
  "easeInOutSine",
  "easeInQuad",
  "easeOutQuad",
  "easeInOutQuad",
  "easeInCubic",
  "easeOutCubic",
  "easeInOutCubic",
  "easeInQuart",
  "easeOutQuart",
  "easeInOutQuart",
  "easeInQuint",
  "easeOutQuint",
  "easeInOutQuint",
  "easeInExpo",
  "easeOutExpo",
  "easeInOutExpo",
  "easeInCirc",
  "easeOutCirc",
  "easeInOutCirc",
  "easeInBack",
  "easeOutBack",
  "easeInOutBack",
  "easeInElastic",
  "easeOutElastic",
  "easeInOutElastic",
  "easeInBounce",
  "easeOutBounce",
  "easeInOutBounce",
]);

export type EasingType = z.infer<typeof EasingTypeSchema>;

/**
 * Combined interpolation type (base + easing).
 */
export const InterpolationTypeSchema = z.union([
  BaseInterpolationTypeSchema,
  EasingTypeSchema,
]);

export type InterpolationType = z.infer<typeof InterpolationTypeSchema>;

// ============================================================================
// Bezier Handle
// ============================================================================

/**
 * Bezier handle for keyframe curves.
 */
export const BezierHandleSchema = z.object({
  frame: finiteNumber,
  value: finiteNumber,
  enabled: z.boolean(),
});

export type BezierHandle = z.infer<typeof BezierHandleSchema>;

/**
 * Control mode for bezier handles.
 */
export const ControlModeSchema = z.enum(["symmetric", "smooth", "corner"]);

export type ControlMode = z.infer<typeof ControlModeSchema>;

// ============================================================================
// Property Value Types
// ============================================================================

/**
 * All possible values that can be stored in keyframes.
 */
export const PropertyValueSchema = z.union([
  finiteNumber,
  z.string(),
  z.object({ x: finiteNumber, y: finiteNumber }),
  z.object({ x: finiteNumber, y: finiteNumber, z: finiteNumber.optional() }),
  RGBAColorSchema,
]);

export type PropertyValue = z.infer<typeof PropertyValueSchema>;

// ============================================================================
// Keyframe Schema
// ============================================================================

/**
 * Generic keyframe with bezier handles.
 */
export const KeyframeSchema = z.object({
  id: EntityIdSchema,
  frame: frameNumber,
  value: PropertyValueSchema,
  interpolation: InterpolationTypeSchema,
  inHandle: BezierHandleSchema,
  outHandle: BezierHandleSchema,
  controlMode: ControlModeSchema,
  spatialInTangent: Vec3Schema.optional(),
  spatialOutTangent: Vec3Schema.optional(),
});

export type Keyframe = z.infer<typeof KeyframeSchema>;

/**
 * Keyframe with number value.
 */
export const NumberKeyframeSchema = KeyframeSchema.extend({
  value: finiteNumber,
});

export type NumberKeyframe = z.infer<typeof NumberKeyframeSchema>;

/**
 * Keyframe with position value.
 */
export const PositionKeyframeSchema = KeyframeSchema.extend({
  value: Position2DOr3DSchema,
});

export type PositionKeyframe = z.infer<typeof PositionKeyframeSchema>;

/**
 * Keyframe with color value.
 */
export const ColorKeyframeSchema = KeyframeSchema.extend({
  value: RGBAColorSchema,
});

export type ColorKeyframe = z.infer<typeof ColorKeyframeSchema>;

// ============================================================================
// Property Expression
// ============================================================================

/**
 * Expression attached to a property.
 */
export const PropertyExpressionSchema = z.object({
  enabled: z.boolean(),
  type: z.enum(["preset", "custom"]),
  name: z.string(),
  params: z.record(z.union([finiteNumber, z.string(), z.boolean()])),
});

export type PropertyExpression = z.infer<typeof PropertyExpressionSchema>;

// ============================================================================
// Animatable Property
// ============================================================================

/**
 * Property type enum.
 */
export const PropertyTypeSchema = z.enum([
  "number",
  "position",
  "color",
  "enum",
  "vector3",
]);

export type PropertyType = z.infer<typeof PropertyTypeSchema>;

/**
 * Generic animatable property schema factory.
 * Creates a schema for an animatable property with a specific value type.
 */
export function createAnimatablePropertySchema<T extends z.ZodTypeAny>(
  valueSchema: T
) {
  return z.object({
    id: EntityIdSchema,
    name: z.string(),
    type: PropertyTypeSchema,
    value: valueSchema,
    animated: z.boolean(),
    keyframes: z.array(KeyframeSchema),
    group: z.string().optional(),
    expression: PropertyExpressionSchema.optional(),
  });
}

/**
 * Animatable number property.
 */
export const AnimatableNumberSchema = createAnimatablePropertySchema(finiteNumber);

export type AnimatableNumber = z.infer<typeof AnimatableNumberSchema>;

/**
 * Animatable position property (2D or 3D).
 */
export const AnimatablePositionSchema = createAnimatablePropertySchema(Position2DOr3DSchema);

export type AnimatablePosition = z.infer<typeof AnimatablePositionSchema>;

/**
 * Animatable Vec3 property.
 */
export const AnimatableVec3Schema = createAnimatablePropertySchema(Vec3Schema);

export type AnimatableVec3 = z.infer<typeof AnimatableVec3Schema>;

/**
 * Animatable color property.
 */
export const AnimatableColorSchema = createAnimatablePropertySchema(RGBAColorSchema);

export type AnimatableColor = z.infer<typeof AnimatableColorSchema>;

/**
 * Animatable enum property (string value).
 */
export const AnimatableEnumSchema = createAnimatablePropertySchema(z.string());

export type AnimatableEnum = z.infer<typeof AnimatableEnumSchema>;

/**
 * Generic animatable property (any value type).
 */
export const AnimatablePropertySchema = z.object({
  id: EntityIdSchema,
  name: z.string(),
  type: PropertyTypeSchema,
  value: PropertyValueSchema,
  animated: z.boolean(),
  keyframes: z.array(KeyframeSchema),
  group: z.string().optional(),
  expression: PropertyExpressionSchema.optional(),
});

export type AnimatableProperty = z.infer<typeof AnimatablePropertySchema>;

// ============================================================================
// Clipboard Keyframe
// ============================================================================

/**
 * Clipboard keyframe entry with property path context.
 */
export const ClipboardKeyframeSchema = z.object({
  layerId: EntityIdSchema,
  propertyPath: z.string(),
  keyframes: z.array(KeyframeSchema),
});

export type ClipboardKeyframe = z.infer<typeof ClipboardKeyframeSchema>;
