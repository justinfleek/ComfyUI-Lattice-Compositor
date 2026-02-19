/**
 * Validation Limits Schema
 *
 * Zod schemas for validating validation limits stored in localStorage.
 * Includes comprehensive validation constraints for security and data integrity.
 */

import { z } from "zod";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Primitives
// ═══════════════════════════════════════════════════════════════════════════

const positiveFinite = z.number().finite().positive();
const nonNegativeFinite = z.number().finite().nonnegative();

// ═══════════════════════════════════════════════════════════════════════════
// Validation Limits Schema
// ═══════════════════════════════════════════════════════════════════════════

export const ValidationLimitsSchema = z.object({
  maxDimension: positiveFinite.max(16384).int(), // Max 16k dimension
  maxDimensionAbsolute: positiveFinite.max(16384).int(), // Absolute max (never configurable)
  maxFrameCount: positiveFinite.max(100000).int(), // Max 100k frames
  maxFrameCountAbsolute: positiveFinite.max(100000).int(), // Absolute max
  maxArrayLength: positiveFinite.max(1000000).int(), // Max 1M array elements
  maxArrayLengthAbsolute: positiveFinite.max(1000000).int(), // Absolute max
  maxParticles: positiveFinite.max(10000000).int(), // Max 10M particles
  maxParticlesAbsolute: positiveFinite.max(10000000).int(), // Absolute max
  maxLayers: positiveFinite.max(10000).int(), // Max 10k layers
  maxLayersAbsolute: positiveFinite.max(10000).int(), // Absolute max
  maxKeyframesPerProperty: positiveFinite.max(100000).int(), // Max 100k keyframes
  maxKeyframesPerPropertyAbsolute: positiveFinite.max(100000).int(), // Absolute max
  maxStringLength: positiveFinite.max(1000000).int(), // Max 1M chars
  maxStringLengthAbsolute: positiveFinite.max(1000000).int(), // Absolute max
  maxFPS: positiveFinite.max(120), // Max 120 FPS
  maxFPSAbsolute: positiveFinite.max(120), // Absolute max
}).strict().refine(
  (data) => {
    // Configurable limits must be <= absolute limits
    return (
      data.maxDimension <= data.maxDimensionAbsolute &&
      data.maxFrameCount <= data.maxFrameCountAbsolute &&
      data.maxArrayLength <= data.maxArrayLengthAbsolute &&
      data.maxParticles <= data.maxParticlesAbsolute &&
      data.maxLayers <= data.maxLayersAbsolute &&
      data.maxKeyframesPerProperty <= data.maxKeyframesPerPropertyAbsolute &&
      data.maxStringLength <= data.maxStringLengthAbsolute &&
      data.maxFPS <= data.maxFPSAbsolute
    );
  },
  { message: "Configurable limits must be <= absolute limits" }
);

export type ValidationLimits = z.infer<typeof ValidationLimitsSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Validation Helpers
// ═══════════════════════════════════════════════════════════════════════════

export function validateValidationLimits(data: unknown): ValidationLimits {
  return ValidationLimitsSchema.parse(data);
}

export function safeValidateValidationLimits(data: unknown) {
  return ValidationLimitsSchema.safeParse(data);
}
