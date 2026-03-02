/**
 * Motion Suggestion Schema
 *
 * Zod schemas for validating AI motion suggestion responses.
 * Used in visionAuthoring/MotionIntentResolver for parsing AI responses.
 * Includes comprehensive validation constraints for security and data integrity.
 */

import { z } from "zod";
import {
  entityId,
  boundedArray,
  MAX_DESCRIPTION_LENGTH,
} from "../shared-validation";
import { Vec3Schema } from "../layers/primitives-schema";
import { normalized01, finiteNumber, positiveFinite, nonNegativeFinite } from "../layers/primitives-schema";

// ============================================================================
// Primitives
// ============================================================================

const positiveInt = z.number().int().positive();

// ============================================================================
// Control Point Schema
// ============================================================================

/**
 * Bezier handle (2D, not 3D)
 */
const BezierHandleSchema = z.object({
  x: finiteNumber,
  y: finiteNumber,
}).strict();

/**
 * Control point for spline/path suggestions
 * Matches ControlPoint from types/spline.ts
 */
export const ControlPointSchema = z.object({
  id: z.string().min(1).max(200).trim(),
  x: finiteNumber,
  y: finiteNumber,
  depth: normalized01.optional(), // Normalized depth 0-1
  handleIn: BezierHandleSchema.nullable().optional(),
  handleOut: BezierHandleSchema.nullable().optional(),
  type: z.enum(["corner", "smooth", "symmetric"]).optional(),
  group: z.string().max(200).trim().optional(), // Group ID for grouped animations
}).strict();

export type ControlPoint = z.infer<typeof ControlPointSchema>;

// ============================================================================
// Camera Motion Type Schema
// ============================================================================

export const CameraMotionTypeSchema = z.enum([
  "dolly",
  "truck",
  "pedestal",
  "pan",
  "tilt",
  "roll",
  "orbit",
  "drift",
  "handheld",
  "crane",
  "zoom",
  "follow_path",
]);

export type CameraMotionType = z.infer<typeof CameraMotionTypeSchema>;

// ============================================================================
// Motion Intensity Schema
// ============================================================================

export const MotionIntensitySchema = z.enum([
  "very_subtle",
  "subtle",
  "medium",
  "strong",
  "dramatic",
]);

export type MotionIntensity = z.infer<typeof MotionIntensitySchema>;

// ============================================================================
// Easing Type Schema
// ============================================================================

export const EasingTypeSchema = z.enum([
  "linear",
  "easeIn",
  "easeOut",
  "easeInOut",
  "bounce",
  "elastic",
]);

export type EasingType = z.infer<typeof EasingTypeSchema>;

// ============================================================================
// Camera Motion Intent Schema
// ============================================================================

export const CameraMotionIntentSchema = z.object({
  type: CameraMotionTypeSchema,
  intensity: MotionIntensitySchema,
  axis: z.enum(["x", "y", "z", "all"]).optional(),
  durationFrames: positiveInt.max(100000).optional(), // Max 100k frames
  suggestedEasing: EasingTypeSchema.optional(),
  noiseAmount: normalized01.optional(), // For handheld
  orbitCenter: Vec3Schema.optional(), // For orbit
  suggestedPath: boundedArray(ControlPointSchema, 10000).optional(), // Max 10k points
}).strict();

export type CameraMotionIntent = z.infer<typeof CameraMotionIntentSchema>;

// ============================================================================
// Spline Usage Schema
// ============================================================================

export const SplineUsageSchema = z.enum([
  "camera_path",
  "emitter_path",
  "text_path",
  "layer_path",
]);

export type SplineUsage = z.infer<typeof SplineUsageSchema>;

// ============================================================================
// Spline Motion Intent Schema
// ============================================================================

export const SplineMotionIntentSchema = z.object({
  usage: SplineUsageSchema,
  smoothness: normalized01, // 0-1 curve smoothness
  complexity: positiveInt.max(10000).optional(), // Max 10k control points
  worldSpace: z.boolean(),
  suggestedPoints: boundedArray(ControlPointSchema, 10000), // Max 10k points
  closed: z.boolean(),
}).strict();

export type SplineMotionIntent = z.infer<typeof SplineMotionIntentSchema>;

// ============================================================================
// Particle Behavior Schema
// ============================================================================

export const ParticleBehaviorSchema = z.enum([
  "flow",
  "drift",
  "spray",
  "turbulence",
  "explosion",
  "vortex",
  "rain",
  "snow",
  "fireflies",
  "dust",
  "along_path",
]);

export type ParticleBehavior = z.infer<typeof ParticleBehaviorSchema>;

// ============================================================================
// Particle Motion Intent Schema
// ============================================================================

export const ParticleMotionIntentSchema = z.object({
  behavior: ParticleBehaviorSchema,
  direction: Vec3Schema.optional(),
  intensity: normalized01, // 0-1 intensity
  spread: normalized01.optional(), // 0-1 spread
  lifetime: positiveFinite.max(3600).optional(), // Max 1 hour lifetime
  colorScheme: z.enum(["warm", "cool", "neutral", "custom"]).optional(),
  suggestedEmitPath: boundedArray(ControlPointSchema, 10000).optional(), // Max 10k points
}).strict();

export type ParticleMotionIntent = z.infer<typeof ParticleMotionIntentSchema>;

// ============================================================================
// Layer Motion Type Schema
// ============================================================================

export const LayerMotionTypeSchema = z.enum([
  "parallax",
  "float",
  "sway",
  "breathe",
  "drift",
  "noise",
  "pulse",
  "rotate",
  "follow_path",
]);

export type LayerMotionType = z.infer<typeof LayerMotionTypeSchema>;

// ============================================================================
// Layer Motion Intent Schema
// ============================================================================

export const LayerMotionIntentSchema = z.object({
  targetLayerId: entityId.optional(),
  motionType: LayerMotionTypeSchema,
  amplitude: normalized01, // 0-1 amplitude
  frequency: positiveFinite.max(1000).optional(), // Max 1000 Hz
  phase: normalized01.optional(), // 0-1 phase offset
  axis: z.enum(["x", "y", "z", "scale", "rotation"]).optional(),
  suggestedPath: boundedArray(ControlPointSchema, 10000).optional(), // Max 10k points
}).strict();

export type LayerMotionIntent = z.infer<typeof LayerMotionIntentSchema>;

// ============================================================================
// Motion Intent Result Schema (Main Schema)
// ============================================================================

/**
 * Motion Intent Result
 * Full AI response structure for motion suggestions
 */
export const MotionIntentResultSchema = z.object({
  description: z.string().min(1).max(MAX_DESCRIPTION_LENGTH).trim(),
  confidence: normalized01, // 0-1 confidence
  cameraIntents: boundedArray(CameraMotionIntentSchema, 100).optional(), // Max 100 camera intents
  layerIntents: boundedArray(LayerMotionIntentSchema, 1000).optional(), // Max 1k layer intents
  particleIntents: boundedArray(ParticleMotionIntentSchema, 100).optional(), // Max 100 particle intents
  splineIntents: boundedArray(SplineMotionIntentSchema, 100).optional(), // Max 100 spline intents
  rawResponse: z.string().max(100000).trim().optional(), // Max 100k chars for debugging
}).strict();

export type MotionIntentResult = z.infer<typeof MotionIntentResultSchema>;

// ============================================================================
// Motion Suggestion Schema (Alias for AI Response)
// ============================================================================

/**
 * Motion Suggestion Schema
 * Alias for MotionIntentResultSchema - used for AI response validation
 */
export const MotionSuggestionSchema = MotionIntentResultSchema;

export type MotionSuggestion = z.infer<typeof MotionSuggestionSchema>;

// ============================================================================
// Validation Helpers
// ============================================================================

export function validateMotionIntentResult(data: unknown): MotionIntentResult {
  return MotionIntentResultSchema.parse(data);
}

export function safeValidateMotionIntentResult(data: unknown) {
  return MotionIntentResultSchema.safeParse(data);
}

export function validateMotionSuggestion(data: unknown): MotionSuggestion {
  return MotionSuggestionSchema.parse(data);
}

export function safeValidateMotionSuggestion(data: unknown) {
  return MotionSuggestionSchema.safeParse(data);
}
