/**
 * Layer Primitive Schemas
 *
 * Foundational Zod schemas for layer data types.
 * All numeric values use .finite() to reject NaN/Infinity.
 */

import { z } from "zod";

// ============================================================================
// Finite Number Primitives
// ============================================================================

/** Finite number that rejects NaN and Infinity */
export const finiteNumber = z.number().finite();

/** Positive finite number */
export const positiveFinite = z.number().finite().positive();

/** Non-negative finite number */
export const nonNegativeFinite = z.number().finite().nonnegative();

/** Normalized value 0-1 */
export const normalized01 = z.number().finite().min(0).max(1);

/** Normalized value -1 to 1 */
export const normalizedNeg1To1 = z.number().finite().min(-1).max(1);

/** Positive integer */
export const positiveInt = z.number().int().positive();

/** Non-negative integer */
export const nonNegativeInt = z.number().int().nonnegative();

/** Frame number (non-negative integer) */
export const frameNumber = z.number().int().nonnegative();

// ============================================================================
// Vector Schemas
// ============================================================================

/**
 * 2D vector with x and y components.
 */
export const Vec2Schema = z.object({
  x: finiteNumber,
  y: finiteNumber,
});

export type Vec2 = z.infer<typeof Vec2Schema>;

/**
 * 3D vector with x, y, and z components.
 */
export const Vec3Schema = z.object({
  x: finiteNumber,
  y: finiteNumber,
  z: finiteNumber,
});

export type Vec3 = z.infer<typeof Vec3Schema>;

/**
 * 2D or 3D position with optional z component.
 */
export const Position2DOr3DSchema = z.object({
  x: finiteNumber,
  y: finiteNumber,
  z: finiteNumber.optional(),
});

export type Position2DOr3D = z.infer<typeof Position2DOr3DSchema>;

// ============================================================================
// Color Schemas
// ============================================================================

/**
 * RGBA color with values 0-1.
 */
export const RGBAColorSchema = z.object({
  r: normalized01,
  g: normalized01,
  b: normalized01,
  a: normalized01,
});

export type RGBAColor = z.infer<typeof RGBAColorSchema>;

/**
 * RGBA color with values 0-255 integers.
 */
export const RGBA255ColorSchema = z.object({
  r: z.number().int().min(0).max(255),
  g: z.number().int().min(0).max(255),
  b: z.number().int().min(0).max(255),
  a: z.number().int().min(0).max(255),
});

export type RGBA255Color = z.infer<typeof RGBA255ColorSchema>;

/**
 * Hex color string (with or without #).
 */
export const HexColorSchema = z.string().regex(/^#?[0-9a-fA-F]{3,8}$/, {
  message: "Invalid hex color format",
});

export type HexColor = z.infer<typeof HexColorSchema>;

/**
 * Color that can be hex string or RGBA object.
 */
export const ColorValueSchema = z.union([HexColorSchema, RGBAColorSchema]);

export type ColorValue = z.infer<typeof ColorValueSchema>;

// ============================================================================
// Rect Schemas
// ============================================================================

/**
 * Rectangle with x, y, width, height.
 */
export const RectSchema = z.object({
  x: finiteNumber,
  y: finiteNumber,
  width: nonNegativeFinite,
  height: nonNegativeFinite,
});

export type Rect = z.infer<typeof RectSchema>;

// ============================================================================
// ID Schemas
// ============================================================================

/**
 * Valid entity ID (non-empty string).
 */
export const EntityIdSchema = z.string().min(1);

export type EntityId = z.infer<typeof EntityIdSchema>;

/**
 * Nullable entity ID (null means no reference).
 */
export const NullableEntityIdSchema = z.string().min(1).nullable();

export type NullableEntityId = z.infer<typeof NullableEntityIdSchema>;

// ============================================================================
// Enum Schemas
// ============================================================================

/**
 * Blend modes.
 */
export const BlendModeSchema = z.enum([
  "normal",
  "multiply",
  "screen",
  "overlay",
  "darken",
  "lighten",
  "color-dodge",
  "color-burn",
  "hard-light",
  "soft-light",
  "difference",
  "exclusion",
  "hue",
  "saturation",
  "color",
  "luminosity",
  "add",
  "subtract",
  "divide",
  "classic-color-dodge",
  "classic-color-burn",
  "stencil-alpha",
  "stencil-luma",
  "silhouette-alpha",
  "silhouette-luma",
  "behind",
  "alpha-add",
  "dissolve",
]);

export type BlendMode = z.infer<typeof BlendModeSchema>;

/**
 * Quality modes.
 */
export const QualityModeSchema = z.enum(["draft", "best"]);

export type QualityMode = z.infer<typeof QualityModeSchema>;
