/**
 * Particle Trajectory Export Schemas
 *
 * Zod schemas for validating particle trajectory export data.
 * Matches ParticleTrajectoryExport interface.
 */

import { z } from "zod";

// ============================================================================
// Primitives
// ============================================================================

const finiteNumber = z.number().finite();
const nonNegativeInt = z.number().int().nonnegative();
const positiveInt = z.number().int().positive();
const normalized01 = z.number().finite().min(0).max(1);

// ============================================================================
// Particle Position Schema
// ============================================================================

export const ParticlePositionSchema = z.object({
  frame: nonNegativeInt,
  x: finiteNumber,
  y: finiteNumber,
  z: finiteNumber.optional(),
});

export type ParticlePosition = z.infer<typeof ParticlePositionSchema>;

// ============================================================================
// Particle Velocity Schema
// ============================================================================

export const ParticleVelocitySchema = z.object({
  frame: nonNegativeInt,
  vx: finiteNumber,
  vy: finiteNumber,
  vz: finiteNumber,
});

export type ParticleVelocity = z.infer<typeof ParticleVelocitySchema>;

// ============================================================================
// Particle Color Schema
// ============================================================================

export const ParticleColorSchema = z.object({
  r: normalized01,
  g: normalized01,
  b: normalized01,
});

export type ParticleColor = z.infer<typeof ParticleColorSchema>;

// ============================================================================
// Particle Data Schema
// ============================================================================

export const ParticleDataSchema = z.object({
  id: z.number().int(), // Particle ID is a number
  birthFrame: nonNegativeInt,
  deathFrame: nonNegativeInt,
  positions: z.array(ParticlePositionSchema),
  velocities: z.array(ParticleVelocitySchema).optional(),
  size: z.array(finiteNumber).optional(), // Can be any number, not just 0-1
  opacity: z.array(normalized01).optional(),
  color: z.array(ParticleColorSchema).optional(),
});

export type ParticleData = z.infer<typeof ParticleDataSchema>;

// ============================================================================
// Emitter Config Schema
// ============================================================================

export const EmitterConfigSchema = z.object({
  type: z.string().min(1),
  position: z.object({
    x: finiteNumber,
    y: finiteNumber,
    z: finiteNumber,
  }),
  rate: positiveInt,
  lifetime: positiveInt,
});

export type EmitterConfig = z.infer<typeof EmitterConfigSchema>;

// ============================================================================
// Particle Trajectory Export Schema
// ============================================================================

/**
 * Particle trajectory export.
 * Matches ParticleTrajectoryExport interface exactly.
 */
export const ParticleTrajectoryExportSchema = z.object({
  particles: z.array(ParticleDataSchema),
  emitterConfig: EmitterConfigSchema,
  metadata: z.object({
    totalParticles: nonNegativeInt,
    frameCount: positiveInt,
    maxActiveParticles: nonNegativeInt,
  }),
});

export type ParticleTrajectoryExport = z.infer<
  typeof ParticleTrajectoryExportSchema
>;

// ============================================================================
// Validation Helpers
// ============================================================================

export function validateParticleTrajectoryExport(
  data: unknown,
): ParticleTrajectoryExport {
  return ParticleTrajectoryExportSchema.parse(data);
}

export function safeValidateParticleTrajectoryExport(data: unknown) {
  return ParticleTrajectoryExportSchema.safeParse(data);
}
