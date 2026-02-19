/**
 * Particle Trajectory Export Schemas
 *
 * Zod schemas for validating particle trajectory export data.
 * Matches ParticleTrajectoryExport interface.
 * Includes comprehensive validation constraints for security and data integrity.
 */

import { z } from "zod";
import {
  boundedArray,
  MAX_NAME_LENGTH,
  MAX_ARRAY_LENGTH,
} from "../shared-validation";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Primitives
// ════════════════════════════════════════════════════════════════════════════

const finiteNumber = z.number().finite();
const nonNegativeInt = z.number().int().nonnegative();
const positiveInt = z.number().int().positive();
const normalized01 = z.number().finite().min(0).max(1);

// ════════════════════════════════════════════════════════════════════════════
// Particle Position Schema
// ════════════════════════════════════════════════════════════════════════════

export const ParticlePositionSchema = z.object({
  frame: nonNegativeInt.max(100000), // Max 100k frames
  x: finiteNumber,
  y: finiteNumber,
  z: finiteNumber.optional(),
}).strict();

export type ParticlePosition = z.infer<typeof ParticlePositionSchema>;

// ════════════════════════════════════════════════════════════════════════════
// Particle Velocity Schema
// ════════════════════════════════════════════════════════════════════════════

export const ParticleVelocitySchema = z.object({
  frame: nonNegativeInt.max(100000), // Max 100k frames
  vx: finiteNumber.max(100000), // Max 100k units/sec velocity
  vy: finiteNumber.max(100000), // Max 100k units/sec velocity
  vz: finiteNumber.max(100000), // Max 100k units/sec velocity
}).strict();

export type ParticleVelocity = z.infer<typeof ParticleVelocitySchema>;

// ════════════════════════════════════════════════════════════════════════════
// Particle Color Schema
// ════════════════════════════════════════════════════════════════════════════

export const ParticleColorSchema = z.object({
  r: normalized01,
  g: normalized01,
  b: normalized01,
}).strict();

export type ParticleColor = z.infer<typeof ParticleColorSchema>;

// ════════════════════════════════════════════════════════════════════════════
// Particle Data Schema
// ════════════════════════════════════════════════════════════════════════════

export const ParticleDataSchema = z.object({
  id: z.number().int().max(10000000), // Max 10M particle ID
  birthFrame: nonNegativeInt.max(100000), // Max 100k frames
  deathFrame: nonNegativeInt.max(100000), // Max 100k frames
  positions: boundedArray(ParticlePositionSchema, 100000), // Max 100k positions per particle
  velocities: boundedArray(ParticleVelocitySchema, 100000).optional(), // Max 100k velocities
  size: boundedArray(finiteNumber.max(100000), 100000).optional(), // Max 100k size values, 100k px max
  opacity: boundedArray(normalized01, 100000).optional(), // Max 100k opacity values
  color: boundedArray(ParticleColorSchema, 100000).optional(), // Max 100k color values
}).strict().refine(
  (data) => {
    // deathFrame should be >= birthFrame
    return data.deathFrame >= data.birthFrame;
  },
  { message: "deathFrame must be >= birthFrame", path: ["deathFrame"] }
).refine(
  (data) => {
    // positions array length should match frame range
    const expectedLength = data.deathFrame - data.birthFrame + 1;
    return data.positions.length === expectedLength;
  },
  { message: "positions array length must match deathFrame - birthFrame + 1", path: ["positions"] }
);

export type ParticleData = z.infer<typeof ParticleDataSchema>;

// ════════════════════════════════════════════════════════════════════════════
// Emitter Config Schema
// ════════════════════════════════════════════════════════════════════════════

export const EmitterConfigSchema = z.object({
  type: z.string().min(1).max(MAX_NAME_LENGTH).trim(),
  position: z.object({
    x: finiteNumber,
    y: finiteNumber,
    z: finiteNumber,
  }).strict(),
  rate: positiveInt.max(1000000), // Max 1M particles/sec
  lifetime: positiveInt.max(100000), // Max 100k frames lifetime
}).strict();

export type EmitterConfig = z.infer<typeof EmitterConfigSchema>;

// ════════════════════════════════════════════════════════════════════════════
// Particle Trajectory Export Schema
// ════════════════════════════════════════════════════════════════════════════

/**
 * Particle trajectory export.
 * Matches ParticleTrajectoryExport interface exactly.
 */
export const ParticleTrajectoryExportSchema = z.object({
  particles: boundedArray(ParticleDataSchema, 10000000), // Max 10M particles
  emitterConfig: EmitterConfigSchema,
  metadata: z.object({
    totalParticles: nonNegativeInt.max(10000000), // Max 10M particles
    frameCount: positiveInt.max(100000), // Max 100k frames
    maxActiveParticles: nonNegativeInt.max(10000000), // Max 10M active particles
  }).strict(),
}).strict().refine(
  (data) => {
    // totalParticles should match particles array length
    return data.metadata.totalParticles === data.particles.length;
  },
  { message: "totalParticles must match particles array length", path: ["metadata", "totalParticles"] }
);

export type ParticleTrajectoryExport = z.infer<
  typeof ParticleTrajectoryExportSchema
>;

// ════════════════════════════════════════════════════════════════════════════
// Validation Helpers
// ════════════════════════════════════════════════════════════════════════════

export function validateParticleTrajectoryExport(
  data: unknown,
): ParticleTrajectoryExport {
  return ParticleTrajectoryExportSchema.parse(data);
}

export function safeValidateParticleTrajectoryExport(data: unknown) {
  return ParticleTrajectoryExportSchema.safeParse(data);
}
