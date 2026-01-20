/**
 * WorkflowParams Schemas
 *
 * Zod schemas for validating WorkflowParams.motionData and related structures.
 * These define the EXACT property names that workflow templates expect.
 *
 * CRITICAL: These schemas ensure property names match what ComfyUI nodes require.
 * If property names don't match, exports will fail silently.
 * Includes comprehensive validation constraints for security and data integrity.
 */

import { z } from "zod";
import {
  boundedArray,
} from "../shared-validation";

// ============================================================================
// Primitives
// ============================================================================

const finiteNumber = z.number().finite();
const positiveInt = z.number().int().positive();
const nonNegativeInt = z.number().int().nonnegative();
const positiveFinite = z.number().finite().positive();

// ============================================================================
// Track Point Schema (WanMove/ATI format)
// ============================================================================

/**
 * Track point format: {x, y} objects
 * Used by WanMove and ATI exports
 */
export const TrackPointSchema = z.object({
  x: finiteNumber.max(16384), // Max reasonable coordinate
  y: finiteNumber.max(16384), // Max reasonable coordinate
}).strict();

export type TrackPoint = z.infer<typeof TrackPointSchema>;

// ============================================================================
// WanMove MotionData Schema
// ============================================================================

/**
 * WanMove motionData structure.
 * Matches what generateWanMoveWorkflow() expects:
 * - tracks: Array<Array<{x, y}>> - Each inner array is one track with per-frame points
 * - Format matches exportWanMoveTrackCoordsJSON() output after JSON.parse()
 */
export const WanMoveMotionDataSchema = z.object({
  tracks: boundedArray(boundedArray(TrackPointSchema, 100000), 10000), // Max 10k tracks, 100k points per track
}).strict();

export type WanMoveMotionData = z.infer<typeof WanMoveMotionDataSchema>;

// ============================================================================
// ATI MotionData Schema
// ============================================================================

/**
 * ATI motionData structure.
 * Matches what generateATIWorkflow() expects:
 * - trajectories: Array<Array<{x, y}>> - Same format as WanMove tracks
 * - Format matches exportATITrackCoordsJSON() output after JSON.parse()
 */
export const ATIMotionDataSchema = z.object({
  trajectories: boundedArray(boundedArray(TrackPointSchema, 121), 10000), // Max 10k trajectories, exactly 121 points per trajectory (ATI format)
}).strict();

export type ATIMotionData = z.infer<typeof ATIMotionDataSchema>;

// ============================================================================
// Unified MotionData Schema (Discriminated Union)
// ============================================================================

/**
 * Unified motionData schema that validates based on export target.
 * This is what WorkflowParams.motionData should be.
 */
export const MotionDataSchema = z.union([
  WanMoveMotionDataSchema,
  ATIMotionDataSchema,
]);

export type MotionData = z.infer<typeof MotionDataSchema>;

// ============================================================================
// Validation Functions
// ============================================================================

/**
 * Validate WanMove motionData structure
 */
export function validateWanMoveMotionData(
  data: unknown,
): WanMoveMotionData {
  return WanMoveMotionDataSchema.parse(data);
}

/**
 * Safe validate WanMove motionData structure
 */
export function safeValidateWanMoveMotionData(
  data: unknown,
): { success: true; data: WanMoveMotionData } | { success: false; error: z.ZodError } {
  const result = WanMoveMotionDataSchema.safeParse(data);
  if (result.success) {
    return { success: true, data: result.data };
  }
  return { success: false, error: result.error };
}

/**
 * Validate ATI motionData structure
 */
export function validateATIMotionData(data: unknown): ATIMotionData {
  return ATIMotionDataSchema.parse(data);
}

/**
 * Safe validate ATI motionData structure
 */
export function safeValidateATIMotionData(
  data: unknown,
): { success: true; data: ATIMotionData } | { success: false; error: z.ZodError } {
  const result = ATIMotionDataSchema.safeParse(data);
  if (result.success) {
    return { success: true, data: result.data };
  }
  return { success: false, error: result.error };
}

/**
 * Validate motionData for a specific export target
 */
export function validateMotionDataForTarget(
  target: "wan-move" | "ati",
  data: unknown,
): WanMoveMotionData | ATIMotionData {
  switch (target) {
    case "wan-move":
      return validateWanMoveMotionData(data);
    case "ati":
      return validateATIMotionData(data);
    default:
      throw new Error(`Unknown export target for motionData: ${target}`);
  }
}
