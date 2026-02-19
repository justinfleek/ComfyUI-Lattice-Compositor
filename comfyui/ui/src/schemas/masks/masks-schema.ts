/**
 * Mask Schemas
 *
 * Zod schemas for layer masks and track mattes.
 * All numeric values use .finite() to reject NaN/Infinity.
 * Includes comprehensive validation constraints for security and data integrity.
 */

import { z } from "zod";
import { finiteNumber, normalized01 } from "../layers/primitives-schema";
import { AnimatablePropertySchema } from "../layers/animation-schema";
import {
  entityId,
  hexColor,
  boundedArray,
  MAX_NAME_LENGTH,
} from "../shared-validation";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Matte Types
// ════════════════════════════════════════════════════════════════════════════

export const MatteTypeSchema = z.enum([
  "none",
  "alpha",
  "alpha_inverted",
  "luma",
  "luma_inverted",
]);

export type MatteType = z.infer<typeof MatteTypeSchema>;

// ════════════════════════════════════════════════════════════════════════════
// Mask Mode
// ════════════════════════════════════════════════════════════════════════════

export const MaskModeSchema = z.enum([
  "add",
  "subtract",
  "intersect",
  "lighten",
  "darken",
  "difference",
  "none",
]);

export type MaskMode = z.infer<typeof MaskModeSchema>;

// ════════════════════════════════════════════════════════════════════════════
// Mask Vertex
// ════════════════════════════════════════════════════════════════════════════

export const MaskVertexSchema = z.object({
  x: finiteNumber,
  y: finiteNumber,
  inTangentX: finiteNumber,
  inTangentY: finiteNumber,
  outTangentX: finiteNumber,
  outTangentY: finiteNumber,
}).strict();

export type MaskVertex = z.infer<typeof MaskVertexSchema>;

// ════════════════════════════════════════════════════════════════════════════
// Mask Path
// ════════════════════════════════════════════════════════════════════════════

export const MaskPathSchema = z.object({
  closed: z.boolean(),
  vertices: boundedArray(MaskVertexSchema, 10000).min(1), // Min 1 vertex, max 10k
}).strict().refine(
  (data) => {
    // Closed paths should have at least 3 vertices
    if (data.closed && data.vertices.length < 3) {
      return false;
    }
    return true;
  },
  { message: "Closed paths must have at least 3 vertices", path: ["vertices"] }
);

export type MaskPath = z.infer<typeof MaskPathSchema>;

// ════════════════════════════════════════════════════════════════════════════
// Layer Mask
// ════════════════════════════════════════════════════════════════════════════

export const LayerMaskSchema = z.object({
  id: entityId,
  name: z.string().min(1).max(MAX_NAME_LENGTH).trim(),
  enabled: z.boolean(),
  locked: z.boolean(),
  mode: MaskModeSchema,
  inverted: z.boolean(),
  path: AnimatablePropertySchema,
  opacity: AnimatablePropertySchema,
  feather: AnimatablePropertySchema,
  featherX: AnimatablePropertySchema.optional(),
  featherY: AnimatablePropertySchema.optional(),
  expansion: AnimatablePropertySchema,
  color: hexColor,
}).strict();

export type LayerMask = z.infer<typeof LayerMaskSchema>;
