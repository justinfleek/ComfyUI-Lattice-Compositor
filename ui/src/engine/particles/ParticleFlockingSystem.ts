/**
 * Particle Flocking System
 *
 * Implements boid-like flocking behavior with:
 * - Separation (avoid crowding)
 * - Alignment (match velocity with neighbors)
 * - Cohesion (move toward center of group)
 *
 * Uses shared SpatialHashGrid for efficient O(n) neighbor queries.
 *
 * Extracted from GPUParticleSystem.ts for modularity.
 */

import * as THREE from "three";
import type { SpatialHashGrid } from "./SpatialHashGrid";
import { type FlockingConfig, PARTICLE_STRIDE } from "./types";

// ============================================================================
// PARTICLE FLOCKING SYSTEM CLASS
// ============================================================================

export class ParticleFlockingSystem {
  private readonly maxParticles: number;
  private config: FlockingConfig;

  // Reference to shared spatial hash (set externally)
  private spatialHash: SpatialHashGrid | null = null;

  constructor(maxParticles: number, config: FlockingConfig) {
    this.maxParticles = maxParticles;
    this.config = config;
  }

  // ============================================================================
  // SPATIAL HASH
  // ============================================================================

  /**
   * Set the shared spatial hash grid reference
   * This should be called once during initialization
   */
  setSpatialHash(hash: SpatialHashGrid): void {
    this.spatialHash = hash;
  }

  /**
   * Get the spatial hash (for backwards compatibility)
   * @deprecated Use setSpatialHash and rebuild from GPUParticleSystem instead
   */
  getSpatialHash(): Map<string, number[]> | null {
    return this.spatialHash?.getRawCells() ?? null;
  }

  /**
   * @deprecated Use shared SpatialHashGrid.rebuild() instead
   * Kept for backwards compatibility - now a no-op
   */
  updateSpatialHash(_particleBuffer: Float32Array): void {
    // No-op: spatial hash is now managed by GPUParticleSystem
    // and shared between flocking and collision systems
  }

  // ============================================================================
  // FLOCKING BEHAVIOR
  // ============================================================================

  /**
   * Apply flocking behaviors to all particles
   * @param particleBuffer - The current particle data buffer (modified in place)
   * @param dt - Delta time in seconds
   */
  applyFlocking(particleBuffer: Float32Array, dt: number): void {
    if (!this.config.enabled || !this.spatialHash) return;

    for (let i = 0; i < this.maxParticles; i++) {
      const offset = i * PARTICLE_STRIDE;
      const lifetime = particleBuffer[offset + 7];
      const age = particleBuffer[offset + 6];
      if (lifetime <= 0 || age >= lifetime) continue;

      const px = particleBuffer[offset + 0];
      const py = particleBuffer[offset + 1];
      const pz = particleBuffer[offset + 2];

      const separation = new THREE.Vector3();
      const alignment = new THREE.Vector3();
      const cohesion = new THREE.Vector3();
      let separationCount = 0;
      let alignmentCount = 0;
      let cohesionCount = 0;

      // Get particle velocity for perception angle check
      const vx = particleBuffer[offset + 3];
      const vy = particleBuffer[offset + 4];
      const vz = particleBuffer[offset + 5];
      const speed = Math.sqrt(vx * vx + vy * vy + vz * vz);

      // Precompute perception angle cosine threshold (360° means all neighbors visible)
      const perceptionCos =
        this.config.perceptionAngle >= 360
          ? -1.0 // -1 means all angles pass
          : Math.cos(((this.config.perceptionAngle / 2) * Math.PI) / 180);

      // Use shared spatial hash for neighbor queries
      for (const j of this.spatialHash.getNeighbors(px, py, pz)) {
        if (j === i) continue;

        const jOffset = j * PARTICLE_STRIDE;
        const jx = particleBuffer[jOffset + 0];
        const jy = particleBuffer[jOffset + 1];
        const jz = particleBuffer[jOffset + 2];

        const dx = px - jx;
        const dy = py - jy;
        const dz = pz - jz;
        const dist = Math.sqrt(dx * dx + dy * dy + dz * dz);

        // Check perception angle: is neighbor within field of view?
        // Skip if particle is stationary (can't determine facing direction)
        if (speed > 0.001 && perceptionCos > -1.0) {
          // Direction TO neighbor (opposite of dx, dy, dz which is FROM neighbor)
          const toNeighborX = -dx / dist;
          const toNeighborY = -dy / dist;
          const toNeighborZ = -dz / dist;

          // Dot product with normalized velocity (facing direction)
          const dot =
            (vx / speed) * toNeighborX +
            (vy / speed) * toNeighborY +
            (vz / speed) * toNeighborZ;

          // If dot < perceptionCos, neighbor is outside field of view
          if (dot < perceptionCos) continue;
        }

        // Separation - steer away from nearby neighbors
        if (dist < this.config.separationRadius && dist > 0) {
          separation.add(new THREE.Vector3(dx, dy, dz).divideScalar(dist));
          separationCount++;
        }

        // Alignment - match velocity with neighbors
        if (dist < this.config.alignmentRadius) {
          alignment.add(
            new THREE.Vector3(
              particleBuffer[jOffset + 3],
              particleBuffer[jOffset + 4],
              particleBuffer[jOffset + 5],
            ),
          );
          alignmentCount++;
        }

        // Cohesion - steer toward center of neighbors
        if (dist < this.config.cohesionRadius) {
          cohesion.add(new THREE.Vector3(jx, jy, jz));
          cohesionCount++;
        }
      }

      // Apply weighted forces
      if (separationCount > 0) {
        separation
          .divideScalar(separationCount)
          .normalize()
          .multiplyScalar(this.config.separationWeight);
      }
      if (alignmentCount > 0) {
        alignment
          .divideScalar(alignmentCount)
          .normalize()
          .multiplyScalar(this.config.alignmentWeight);
      }
      if (cohesionCount > 0) {
        cohesion.divideScalar(cohesionCount);
        cohesion
          .sub(new THREE.Vector3(px, py, pz))
          .normalize()
          .multiplyScalar(this.config.cohesionWeight);
      }

      // Combine steering forces
      const steering = separation.add(alignment).add(cohesion);
      if (steering.length() > this.config.maxForce) {
        steering.normalize().multiplyScalar(this.config.maxForce);
      }

      // Apply to velocity
      particleBuffer[offset + 3] += steering.x * dt;
      particleBuffer[offset + 4] += steering.y * dt;
      particleBuffer[offset + 5] += steering.z * dt;

      // Limit speed
      const newSpeed = Math.sqrt(
        particleBuffer[offset + 3] ** 2 +
          particleBuffer[offset + 4] ** 2 +
          particleBuffer[offset + 5] ** 2,
      );
      if (newSpeed > this.config.maxSpeed) {
        const scale = this.config.maxSpeed / newSpeed;
        particleBuffer[offset + 3] *= scale;
        particleBuffer[offset + 4] *= scale;
        particleBuffer[offset + 5] *= scale;
      }
    }
  }

  // ============================================================================
  // ACCESSORS
  // ============================================================================

  /**
   * Check if flocking is enabled
   */
  isEnabled(): boolean {
    return this.config.enabled;
  }

  /**
   * Enable or disable flocking
   */
  setEnabled(enabled: boolean): void {
    this.config.enabled = enabled;
  }

  /**
   * Update flocking configuration
   */
  updateConfig(config: Partial<FlockingConfig>): void {
    Object.assign(this.config, config);
  }

  /**
   * Get current configuration
   */
  getConfig(): FlockingConfig {
    return { ...this.config };
  }

  // ============================================================================
  // CLEANUP
  // ============================================================================

  /**
   * Reset flocking state
   * Note: Spatial hash is managed externally and cleared by GPUParticleSystem
   */
  reset(): void {
    // No local state to reset - spatial hash is shared
  }
}
