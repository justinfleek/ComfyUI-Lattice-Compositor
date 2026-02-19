/**
 * Particle Preferences Schema
 *
 * Zod schemas for validating particle preferences stored in localStorage.
 * Includes comprehensive validation constraints for security and data integrity.
 */

import { z } from "zod";
import {
  MAX_NAME_LENGTH,
} from "../shared-validation";

// ============================================================================
// Primitives
// ============================================================================

const positiveFinite = z.number().finite().positive();
const nonNegativeFinite = z.number().finite().nonnegative();

// ============================================================================
// Rendering Backend Schema
// ============================================================================

export const RenderingBackendSchema = z.enum([
  "auto",
  "webgpu",
  "webgl2",
  "cpu",
]);

export type RenderingBackend = z.infer<typeof RenderingBackendSchema>;

// ============================================================================
// Simulation Mode Schema
// ============================================================================

export const SimulationModeSchema = z.enum([
  "realtime",
  "cached",
  "baked",
]);

export type SimulationMode = z.infer<typeof SimulationModeSchema>;

// ============================================================================
// Particle Preferences Schema
// ============================================================================

export const ParticlePreferencesSchema = z.object({
  renderingBackend: RenderingBackendSchema,
  simulationMode: SimulationModeSchema,
  cacheCheckpointInterval: positiveFinite.max(10000).int(), // Max 10k frames between checkpoints
  maxCacheMemoryMB: positiveFinite.max(100000).int(), // Max 100GB cache memory
  maxParticlesPerLayer: positiveFinite.max(100000000).int(), // Max 100M particles per layer
  enableGPUCompute: z.boolean(),
  targetFPS: z.number().int().min(1).max(120), // Max 120 FPS
  enableMotionBlur: z.boolean(),
  enableSoftParticles: z.boolean(),
  enableShadows: z.boolean(),
  lodEnabled: z.boolean(),
}).strict();

export type ParticlePreferences = z.infer<typeof ParticlePreferencesSchema>;

// ============================================================================
// Validation Helpers
// ============================================================================

export function validateParticlePreferences(data: unknown): ParticlePreferences {
  return ParticlePreferencesSchema.parse(data);
}

export function safeValidateParticlePreferences(data: unknown) {
  return ParticlePreferencesSchema.safeParse(data);
}
