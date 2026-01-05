/**
 * Particle Collision System
 *
 * Handles collision detection and response for particles.
 * Supports boundary collisions and particle-particle collisions.
 * Uses shared SpatialHashGrid for efficient O(n) neighbor queries.
 *
 * Extracted from GPUParticleSystem.ts for modularity.
 */

import type { SpatialHashGrid } from "./SpatialHashGrid";
import { PARTICLE_STRIDE } from "./types";

// ============================================================================
// TYPES
// ============================================================================

export type BoundsBehavior =
  | "none"
  | "kill"
  | "bounce"
  | "wrap"
  | "clamp"
  | "stick";

export interface CollisionConfig {
  enabled: boolean;
  particleCollision: boolean;
  particleRadius: number;
  bounciness: number;
  friction: number;
  bounds?: {
    min: { x: number; y: number; z: number };
    max: { x: number; y: number; z: number };
  };
  boundsBehavior: BoundsBehavior;
}

// ============================================================================
// PARTICLE COLLISION SYSTEM CLASS
// ============================================================================

export class ParticleCollisionSystem {
  private readonly maxParticles: number;
  private config: CollisionConfig;

  // Reference to shared spatial hash (set externally)
  private spatialHash: SpatialHashGrid | null = null;

  constructor(maxParticles: number, config: Partial<CollisionConfig> = {}) {
    this.maxParticles = maxParticles;
    this.config = {
      enabled: config.enabled ?? true,
      particleCollision: config.particleCollision ?? false,
      particleRadius: config.particleRadius ?? 5,
      bounciness: config.bounciness ?? 0.5,
      friction: config.friction ?? 0.1,
      bounds: config.bounds,
      boundsBehavior: config.boundsBehavior ?? "none",
    };
  }

  /**
   * Set the shared spatial hash grid reference
   * This should be called once during initialization
   */
  setSpatialHash(hash: SpatialHashGrid): void {
    this.spatialHash = hash;
  }

  // ============================================================================
  // UPDATE
  // ============================================================================

  /**
   * Apply collision detection and response
   * @param particleBuffer - The current particle data buffer (modified in place)
   */
  update(particleBuffer: Float32Array): void {
    if (!this.config.enabled) return;

    // Apply boundary collisions
    if (this.config.bounds && this.config.boundsBehavior !== "none") {
      this.applyBoundaryCollisions(particleBuffer);
    }

    // Apply particle-particle collisions (expensive, uses spatial hash)
    if (this.config.particleCollision) {
      this.applyParticleCollisions(particleBuffer);
    }
  }

  // ============================================================================
  // BOUNDARY COLLISIONS
  // ============================================================================

  /**
   * Apply boundary collision response
   */
  private applyBoundaryCollisions(buffer: Float32Array): void {
    if (!this.config.bounds) return;

    const { min, max } = this.config.bounds;
    const bounciness = this.config.bounciness;
    const behavior = this.config.boundsBehavior;

    for (let i = 0; i < this.maxParticles; i++) {
      const offset = i * PARTICLE_STRIDE;
      const lifetime = buffer[offset + 7];
      const age = buffer[offset + 6];

      if (lifetime <= 0 || age >= lifetime) continue;

      let px = buffer[offset + 0];
      let py = buffer[offset + 1];
      let pz = buffer[offset + 2];
      let vx = buffer[offset + 3];
      let vy = buffer[offset + 4];
      let vz = buffer[offset + 5];

      let collided = false;

      // X boundaries
      if (px < min.x) {
        if (behavior === "bounce") {
          px = min.x + (min.x - px);
          vx = -vx * bounciness;
        } else if (behavior === "wrap") {
          px = max.x - (min.x - px);
        } else if (behavior === "kill") {
          buffer[offset + 6] = buffer[offset + 7]; // Set age = lifetime (kill)
          continue;
        } else if (behavior === "clamp") {
          px = min.x;
          vx = 0; // Stop X velocity but keep other motion
        } else if (behavior === "stick") {
          px = min.x;
          vx = 0;
          vy = 0;
          vz = 0; // Stop all motion when stuck
        }
        collided = true;
      } else if (px > max.x) {
        if (behavior === "bounce") {
          px = max.x - (px - max.x);
          vx = -vx * bounciness;
        } else if (behavior === "wrap") {
          px = min.x + (px - max.x);
        } else if (behavior === "kill") {
          buffer[offset + 6] = buffer[offset + 7];
          continue;
        } else if (behavior === "clamp") {
          px = max.x;
          vx = 0; // Stop X velocity but keep other motion
        } else if (behavior === "stick") {
          px = max.x;
          vx = 0;
          vy = 0;
          vz = 0;
        }
        collided = true;
      }

      // Y boundaries (includes floor/ceiling)
      if (py < min.y) {
        if (behavior === "bounce") {
          py = min.y + (min.y - py);
          vy = -vy * bounciness;
        } else if (behavior === "wrap") {
          py = max.y - (min.y - py);
        } else if (behavior === "kill") {
          buffer[offset + 6] = buffer[offset + 7];
          continue;
        } else if (behavior === "clamp") {
          py = min.y;
          vy = 0; // Stop Y velocity but keep other motion
        } else if (behavior === "stick") {
          py = min.y;
          vx = 0;
          vy = 0;
          vz = 0;
        }
        collided = true;
      } else if (py > max.y) {
        if (behavior === "bounce") {
          py = max.y - (py - max.y);
          vy = -vy * bounciness;
        } else if (behavior === "wrap") {
          py = min.y + (py - max.y);
        } else if (behavior === "kill") {
          buffer[offset + 6] = buffer[offset + 7];
          continue;
        } else if (behavior === "clamp") {
          py = max.y;
          vy = 0; // Stop Y velocity but keep other motion
        } else if (behavior === "stick") {
          py = max.y;
          vx = 0;
          vy = 0;
          vz = 0;
        }
        collided = true;
      }

      // Z boundaries
      if (pz < min.z) {
        if (behavior === "bounce") {
          pz = min.z + (min.z - pz);
          vz = -vz * bounciness;
        } else if (behavior === "wrap") {
          pz = max.z - (min.z - pz);
        } else if (behavior === "kill") {
          buffer[offset + 6] = buffer[offset + 7];
          continue;
        } else if (behavior === "clamp") {
          pz = min.z;
          vz = 0; // Stop Z velocity but keep other motion
        } else if (behavior === "stick") {
          pz = min.z;
          vx = 0;
          vy = 0;
          vz = 0;
        }
        collided = true;
      } else if (pz > max.z) {
        if (behavior === "bounce") {
          pz = max.z - (pz - max.z);
          vz = -vz * bounciness;
        } else if (behavior === "wrap") {
          pz = min.z + (pz - max.z);
        } else if (behavior === "kill") {
          buffer[offset + 6] = buffer[offset + 7];
          continue;
        } else if (behavior === "clamp") {
          pz = max.z;
          vz = 0; // Stop Z velocity but keep other motion
        } else if (behavior === "stick") {
          pz = max.z;
          vx = 0;
          vy = 0;
          vz = 0;
        }
        collided = true;
      }

      if (collided) {
        buffer[offset + 0] = px;
        buffer[offset + 1] = py;
        buffer[offset + 2] = pz;
        buffer[offset + 3] = vx;
        buffer[offset + 4] = vy;
        buffer[offset + 5] = vz;
      }
    }
  }

  // ============================================================================
  // PARTICLE-PARTICLE COLLISIONS
  // ============================================================================

  /**
   * Apply particle-particle collision response
   * Uses shared spatial hash for efficiency
   */
  private applyParticleCollisions(buffer: Float32Array): void {
    if (!this.spatialHash) return;

    const radius = this.config.particleRadius;
    const radiusSq = radius * radius * 4; // 2*radius squared for collision detection
    const bounciness = this.config.bounciness;

    // Check collisions using shared spatial hash
    for (let i = 0; i < this.maxParticles; i++) {
      const offset = i * PARTICLE_STRIDE;
      const lifetime = buffer[offset + 7];
      const age = buffer[offset + 6];

      if (lifetime <= 0 || age >= lifetime) continue;

      const px = buffer[offset + 0];
      const py = buffer[offset + 1];
      const pz = buffer[offset + 2];
      let vx = buffer[offset + 3];
      let vy = buffer[offset + 4];
      let vz = buffer[offset + 5];
      const mass1 = buffer[offset + 8];

      // Use shared spatial hash for neighbor queries
      for (const j of this.spatialHash.getNeighbors(px, py, pz)) {
        if (j <= i) continue; // Avoid duplicate checks

        const jOffset = j * PARTICLE_STRIDE;
        const jx = buffer[jOffset + 0];
        const jy = buffer[jOffset + 1];
        const jz = buffer[jOffset + 2];

        const dx = jx - px;
        const dy = jy - py;
        const dz = jz - pz;
        const distSq = dx * dx + dy * dy + dz * dz;

        if (distSq < radiusSq && distSq > 0.001) {
          // Collision detected - simple elastic collision response
          const dist = Math.sqrt(distSq);
          const nx = dx / dist;
          const ny = dy / dist;
          const nz = dz / dist;

          let jvx = buffer[jOffset + 3];
          let jvy = buffer[jOffset + 4];
          let jvz = buffer[jOffset + 5];
          const mass2 = buffer[jOffset + 8];

          // Relative velocity
          const dvx = vx - jvx;
          const dvy = vy - jvy;
          const dvz = vz - jvz;
          const dvn = dvx * nx + dvy * ny + dvz * nz;

          // Only resolve if particles are approaching
          if (dvn > 0) continue;

          // Impulse magnitude
          const totalMass = mass1 + mass2;
          const impulse = (-(1 + bounciness) * dvn) / totalMass;

          // Apply impulse
          vx += impulse * mass2 * nx;
          vy += impulse * mass2 * ny;
          vz += impulse * mass2 * nz;

          jvx -= impulse * mass1 * nx;
          jvy -= impulse * mass1 * ny;
          jvz -= impulse * mass1 * nz;

          buffer[jOffset + 3] = jvx;
          buffer[jOffset + 4] = jvy;
          buffer[jOffset + 5] = jvz;

          // Separate particles to prevent overlap
          const overlap = (radius * 2 - dist) / 2;
          buffer[offset + 0] -= nx * overlap;
          buffer[offset + 1] -= ny * overlap;
          buffer[offset + 2] -= nz * overlap;
          buffer[jOffset + 0] += nx * overlap;
          buffer[jOffset + 1] += ny * overlap;
          buffer[jOffset + 2] += nz * overlap;
        }
      }

      buffer[offset + 3] = vx;
      buffer[offset + 4] = vy;
      buffer[offset + 5] = vz;
    }
  }

  // ============================================================================
  // ACCESSORS
  // ============================================================================

  /**
   * Check if collision system is enabled
   */
  isEnabled(): boolean {
    return this.config.enabled;
  }

  /**
   * Enable or disable collisions
   */
  setEnabled(enabled: boolean): void {
    this.config.enabled = enabled;
  }

  /**
   * Update collision configuration
   */
  updateConfig(config: Partial<CollisionConfig>): void {
    Object.assign(this.config, config);
  }

  /**
   * Get current configuration
   */
  getConfig(): CollisionConfig {
    return { ...this.config };
  }
}
