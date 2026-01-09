/**
 * Particle Sub-Emitter System
 *
 * Handles spawning particles from sub-emitters when parent particles
 * die, collide, or meet other trigger conditions.
 *
 * Extracted from GPUParticleSystem.ts for modularity.
 */

import { PARTICLE_STRIDE, type SubEmitterConfig } from "./types";

// ============================================================================
// TYPES
// ============================================================================

export interface DeathEvent {
  index: number;
  emitterId?: string;
}

export type RNGFunction = () => number;
export type EmitCallback = (event: {
  index: number;
  emitterId: string;
  isSubEmitter: boolean;
}) => void;

// ============================================================================
// PARTICLE SUB-EMITTER SYSTEM CLASS
// ============================================================================

export class ParticleSubEmitter {
  private subEmitters: Map<string, SubEmitterConfig> = new Map();
  private rng: RNGFunction;
  private onEmit?: EmitCallback;
  private readonly maxParticles: number;

  // Queue for death events to process
  private pendingDeathEvents: DeathEvent[] = [];

  constructor(maxParticles: number, rng: RNGFunction) {
    // Validate maxParticles for bounds checking
    this.maxParticles = Number.isFinite(maxParticles) && maxParticles > 0
      ? Math.floor(maxParticles)
      : 10000;
    this.rng = rng;
  }

  // ============================================================================
  // SUB-EMITTER MANAGEMENT
  // ============================================================================

  /**
   * Add a sub-emitter configuration
   */
  addSubEmitter(config: SubEmitterConfig): void {
    this.subEmitters.set(config.id, config);
  }

  /**
   * Remove a sub-emitter
   */
  removeSubEmitter(id: string): void {
    this.subEmitters.delete(id);
  }

  /**
   * Get all sub-emitters
   */
  getSubEmitters(): Map<string, SubEmitterConfig> {
    return this.subEmitters;
  }

  /**
   * Set the emit callback
   */
  setEmitCallback(callback: EmitCallback): void {
    this.onEmit = callback;
  }

  // ============================================================================
  // DEATH EVENT HANDLING
  // ============================================================================

  /**
   * Queue a death event for processing
   */
  queueDeathEvent(event: DeathEvent): void {
    this.pendingDeathEvents.push(event);
  }

  /**
   * Process all queued death events and spawn sub-particles
   * @param particleBuffer - The particle data buffer (modified in place)
   * @param freeIndices - Array of free particle indices
   * @returns Number of particles spawned
   */
  processDeathEvents(
    particleBuffer: Float32Array,
    freeIndices: number[],
  ): number {
    if (this.subEmitters.size === 0) {
      this.pendingDeathEvents = [];
      return 0;
    }

    let spawnCount = 0;
    const deathQueue = this.pendingDeathEvents;
    this.pendingDeathEvents = [];

    for (const death of deathQueue) {
      // Find sub-emitters triggered by death
      for (const subEmitter of this.subEmitters.values()) {
        if (subEmitter.trigger !== "death") continue;
        if (!subEmitter.parentEmitterId) continue;

        // Check parent emitter filter
        // '*' means trigger on any emitter's particles
        // Specific ID means only trigger on that emitter's particles
        // Note: death.emitterId may be undefined if particle tracking not implemented
        if (
          subEmitter.parentEmitterId !== "*" &&
          death.emitterId !== undefined
        ) {
          if (death.emitterId !== subEmitter.parentEmitterId) continue;
        }

        // Check trigger probability
        if (this.rng() > subEmitter.triggerProbability) continue;

        // Validate death.index bounds
        if (!Number.isFinite(death.index) || death.index < 0 || death.index >= this.maxParticles) {
          continue;
        }

        // Get parent particle data
        const offset = death.index * PARTICLE_STRIDE;

        const parentPos = {
          x: particleBuffer[offset + 0],
          y: particleBuffer[offset + 1],
          z: particleBuffer[offset + 2],
        };
        const parentVel = {
          x: particleBuffer[offset + 3],
          y: particleBuffer[offset + 4],
          z: particleBuffer[offset + 5],
        };
        const parentSize = particleBuffer[offset + 9];
        const parentColor: [number, number, number, number] = [
          particleBuffer[offset + 12],
          particleBuffer[offset + 13],
          particleBuffer[offset + 14],
          particleBuffer[offset + 15],
        ];
        const parentRotation = particleBuffer[offset + 10];

        // Spawn sub-particles (validate count to prevent infinite loop)
        const rawCount =
          (Number.isFinite(subEmitter.emitCount) ? subEmitter.emitCount : 10) +
          Math.floor((this.rng() - 0.5) * 2 * (Number.isFinite(subEmitter.emitCountVariance) ? subEmitter.emitCountVariance : 0));
        const count = Math.max(0, Math.min(rawCount, 1000));  // Cap at 1000 sub-particles

        for (let i = 0; i < count; i++) {
          if (freeIndices.length === 0) break;

          const index = freeIndices.pop()!;
          const subOffset = index * PARTICLE_STRIDE;

          // Position inheritance
          particleBuffer[subOffset + 0] = parentPos.x;
          particleBuffer[subOffset + 1] = parentPos.y;
          particleBuffer[subOffset + 2] = parentPos.z;

          // Velocity - combination of inherited and new emission direction
          // Validate all config values
          const overrides = subEmitter.overrides;
          const rawSpeed = overrides.initialSpeed ?? 100;
          const speed = (Number.isFinite(rawSpeed) && rawSpeed >= 0) ? rawSpeed : 100;
          const rawSpread = overrides.emissionSpread ?? 180;
          const spread = Number.isFinite(rawSpread) ? Math.max(0, Math.min(360, rawSpread)) : 180;

          // Random direction within spread cone (spherical for death = explosion)
          const theta = this.rng() * Math.PI * 2;
          const phi = Math.acos(
            1 - this.rng() * (1 - Math.cos((spread * Math.PI) / 180)),
          );
          const newVelX = Math.sin(phi) * Math.cos(theta) * speed;
          const newVelY = Math.sin(phi) * Math.sin(theta) * speed;
          const newVelZ = Math.cos(phi) * speed;

          // Blend inherited velocity (validate inheritVelocity)
          const inheritVel = Number.isFinite(subEmitter.inheritVelocity) 
            ? subEmitter.inheritVelocity : 0;
          particleBuffer[subOffset + 3] = newVelX + parentVel.x * inheritVel;
          particleBuffer[subOffset + 4] = newVelY + parentVel.y * inheritVel;
          particleBuffer[subOffset + 5] = newVelZ + parentVel.z * inheritVel;

          // Life (validate lifetime)
          particleBuffer[subOffset + 6] = 0; // age
          const rawLifetime = overrides.lifetime ?? 30;
          const lifetime = (Number.isFinite(rawLifetime) && rawLifetime > 0) ? rawLifetime : 30;
          particleBuffer[subOffset + 7] = lifetime;

          // Physical - validate mass and size to prevent division by zero
          // Must check Number.isFinite before using - Math.max(NaN, x) = NaN
          const rawMass = overrides.initialMass ?? 1;
          const safeMass = (Number.isFinite(rawMass) && rawMass > 0) ? rawMass : 1;
          particleBuffer[subOffset + 8] = safeMass; // mass

          const rawInitialSize = overrides.initialSize ?? 5;
          const safeInitialSize = (Number.isFinite(rawInitialSize) && rawInitialSize > 0) ? rawInitialSize : 5;
          const rawInheritSize = subEmitter.inheritSize ?? 0;
          const safeInheritSize = Number.isFinite(rawInheritSize) ? rawInheritSize : 0;
          const rawSize = safeInitialSize * (safeInheritSize > 0 ? parentSize * safeInheritSize : 1);
          particleBuffer[subOffset + 9] = Number.isFinite(rawSize) ? Math.max(rawSize, 0.001) : 5; // size

          // Rotation (validate inheritRotation)
          const rawInheritRot = subEmitter.inheritRotation ?? 0;
          const inheritRot = Number.isFinite(rawInheritRot) ? rawInheritRot : 0;
          particleBuffer[subOffset + 10] =
            inheritRot > 0
              ? parentRotation * inheritRot
              : this.rng() * Math.PI * 2;
          const rawAngVel = overrides.initialAngularVelocity ?? 0;
          const angVel = Number.isFinite(rawAngVel) ? rawAngVel : 0;
          particleBuffer[subOffset + 11] = angVel;

          // Color inheritance (validate inheritColor and colorStart)
          const rawColorStart = overrides.colorStart ?? [1, 1, 1, 1];
          const colorStart: [number, number, number, number] = [
            Number.isFinite(rawColorStart[0]) ? rawColorStart[0] : 1,
            Number.isFinite(rawColorStart[1]) ? rawColorStart[1] : 1,
            Number.isFinite(rawColorStart[2]) ? rawColorStart[2] : 1,
            Number.isFinite(rawColorStart[3]) ? rawColorStart[3] : 1,
          ];
          const rawInheritCol = subEmitter.inheritColor ?? 0;
          const inheritCol = Number.isFinite(rawInheritCol) ? rawInheritCol : 0;
          if (inheritCol > 0) {
            particleBuffer[subOffset + 12] =
              parentColor[0] * inheritCol +
              colorStart[0] * (1 - inheritCol);
            particleBuffer[subOffset + 13] =
              parentColor[1] * inheritCol +
              colorStart[1] * (1 - inheritCol);
            particleBuffer[subOffset + 14] =
              parentColor[2] * inheritCol +
              colorStart[2] * (1 - inheritCol);
            particleBuffer[subOffset + 15] =
              parentColor[3] * inheritCol +
              colorStart[3] * (1 - inheritCol);
          } else {
            particleBuffer[subOffset + 12] = colorStart[0];
            particleBuffer[subOffset + 13] = colorStart[1];
            particleBuffer[subOffset + 14] = colorStart[2];
            particleBuffer[subOffset + 15] = colorStart[3];
          }

          spawnCount++;

          // Emit callback
          if (this.onEmit) {
            this.onEmit({
              index,
              emitterId: subEmitter.id,
              isSubEmitter: true,
            });
          }
        }
      }
    }

    return spawnCount;
  }

  // ============================================================================
  // ACCESSORS
  // ============================================================================

  /**
   * Check if any sub-emitters are configured
   */
  hasSubEmitters(): boolean {
    return this.subEmitters.size > 0;
  }

  /**
   * Get pending death event count
   */
  getPendingEventCount(): number {
    return this.pendingDeathEvents.length;
  }

  // ============================================================================
  // CLEANUP
  // ============================================================================

  /**
   * Reset sub-emitter state
   */
  reset(): void {
    this.pendingDeathEvents = [];
  }

  /**
   * Clear all sub-emitters
   */
  clear(): void {
    this.subEmitters.clear();
    this.pendingDeathEvents = [];
  }
}
