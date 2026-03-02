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
import type { ISpatialHash } from "./types";
import { type FlockingConfig, PARTICLE_STRIDE } from "./types";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                   // particle // flocking // system // class
// ════════════════════════════════════════════════════════════════════════════

export class ParticleFlockingSystem {
  private readonly maxParticles: number;
  private config: FlockingConfig;

  // Reference to shared spatial hash (set externally)
  private spatialHash: ISpatialHash | null = null;

  constructor(maxParticles: number, config: FlockingConfig) {
    // Validate maxParticles to prevent infinite loop
    this.maxParticles = Number.isFinite(maxParticles) && maxParticles > 0
      ? Math.min(Math.floor(maxParticles), 10_000_000)
      : 10000;
    this.config = config;
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                           // spatial // hash
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Set the shared spatial hash grid reference
   * This should be called once during initialization
   */
  /**
   * Set the spatial hash reference
   *
   * Type proof: hash ∈ ISpatialHash
   * Lean4: theorem setSpatialHash_valid : hash implements ISpatialHash
   */
  setSpatialHash(hash: ISpatialHash): void {
    this.spatialHash = hash;
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                      // flocking // behavior
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Apply flocking behaviors to all particles
   * @param particleBuffer - The current particle data buffer (modified in place)
   * @param dt - Delta time in seconds
   */
  applyFlocking(particleBuffer: Float32Array, dt: number): void {
    if (!this.config.enabled || !this.spatialHash) return;
    
    // Validate dt to prevent NaN propagation
    const safeDt = Number.isFinite(dt) && dt >= 0 ? Math.min(dt, 1.0) : 0.016;

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
      // Validate perceptionAngle to prevent NaN
      const safePerceptionAngle = Number.isFinite(this.config.perceptionAngle) 
        ? Math.max(0, this.config.perceptionAngle) 
        : 360;
      const perceptionCos =
        safePerceptionAngle >= 360
          ? -1.0 // -1 means all angles pass
          : Math.cos(((safePerceptionAngle / 2) * Math.PI) / 180);

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

        // Validate radius values
        const safeSepRadius = Number.isFinite(this.config.separationRadius) && this.config.separationRadius > 0
          ? this.config.separationRadius : 50;
        const safeAlignRadius = Number.isFinite(this.config.alignmentRadius) && this.config.alignmentRadius > 0
          ? this.config.alignmentRadius : 100;
        const safeCohRadius = Number.isFinite(this.config.cohesionRadius) && this.config.cohesionRadius > 0
          ? this.config.cohesionRadius : 150;

        // Separation - steer away from nearby neighbors
        if (dist < safeSepRadius && dist > 0) {
          separation.add(new THREE.Vector3(dx, dy, dz).divideScalar(dist));
          separationCount++;
        }

        // Alignment - match velocity with neighbors
        if (dist < safeAlignRadius) {
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
        if (dist < safeCohRadius) {
          cohesion.add(new THREE.Vector3(jx, jy, jz));
          cohesionCount++;
        }
      }

      // Validate weights and maxForce
      const safeSepWeight = Number.isFinite(this.config.separationWeight) ? this.config.separationWeight : 1.5;
      const safeAlignWeight = Number.isFinite(this.config.alignmentWeight) ? this.config.alignmentWeight : 1.0;
      const safeCohWeight = Number.isFinite(this.config.cohesionWeight) ? this.config.cohesionWeight : 1.0;
      const safeMaxForce = Number.isFinite(this.config.maxForce) && this.config.maxForce > 0
        ? this.config.maxForce : 10;

      // Apply weighted forces
      if (separationCount > 0) {
        separation
          .divideScalar(separationCount)
          .normalize()
          .multiplyScalar(safeSepWeight);
      }
      if (alignmentCount > 0) {
        alignment
          .divideScalar(alignmentCount)
          .normalize()
          .multiplyScalar(safeAlignWeight);
      }
      if (cohesionCount > 0) {
        cohesion.divideScalar(cohesionCount);
        cohesion
          .sub(new THREE.Vector3(px, py, pz))
          .normalize()
          .multiplyScalar(safeCohWeight);
      }

      // Combine steering forces
      const steering = separation.add(alignment).add(cohesion);
      if (steering.length() > safeMaxForce) {
        steering.normalize().multiplyScalar(safeMaxForce);
      }

      // Apply to velocity (using validated safeDt)
      particleBuffer[offset + 3] += steering.x * safeDt;
      particleBuffer[offset + 4] += steering.y * safeDt;
      particleBuffer[offset + 5] += steering.z * safeDt;

      // Limit speed (validate maxSpeed to prevent velocity reversal)
      const safeMaxSpeed = Number.isFinite(this.config.maxSpeed) && this.config.maxSpeed > 0
        ? this.config.maxSpeed
        : 100;  // Default max speed
      const newSpeed = Math.sqrt(
        particleBuffer[offset + 3] ** 2 +
          particleBuffer[offset + 4] ** 2 +
          particleBuffer[offset + 5] ** 2,
      );
      if (newSpeed > safeMaxSpeed) {
        const scale = safeMaxSpeed / newSpeed;
        particleBuffer[offset + 3] *= scale;
        particleBuffer[offset + 4] *= scale;
        particleBuffer[offset + 5] *= scale;
      }
    }
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                                 // accessors
  // ════════════════════════════════════════════════════════════════════════════

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

  // ════════════════════════════════════════════════════════════════════════════
  //                                                                   // cleanup
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Reset flocking state
   * Note: Spatial hash is managed externally and cleared by GPUParticleSystem
   */
  reset(): void {
    // No local state to reset - spatial hash is shared
  }
}
