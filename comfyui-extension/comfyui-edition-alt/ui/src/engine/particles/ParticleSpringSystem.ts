/**
 * Particle Spring System
 *
 * Implements spring forces between particles for:
 * - Soft body simulation
 * - Cloth simulation
 * - Rope/chain effects
 * - Tension/compression forces
 *
 * Uses Hooke's Law: F = -k(x - rest) - damping * v
 * Supports Verlet integration for stability with stiff springs.
 */

import { PARTICLE_STRIDE } from "./types";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                                     // types
// ════════════════════════════════════════════════════════════════════════════

/**
 * A spring connecting two particles
 */
export interface Spring {
  /** Index of first particle */
  particleA: number;
  /** Index of second particle */
  particleB: number;
  /** Rest length (natural length when no force applied) */
  restLength: number;
  /** Spring stiffness (higher = stiffer, but can become unstable) */
  stiffness: number;
  /** Damping coefficient (reduces oscillation) */
  damping: number;
  /** Maximum stretch before breaking (0 = unbreakable) */
  breakThreshold: number;
  /** Whether this spring is currently active */
  active: boolean;
}

/**
 * Spring constraint for position-based dynamics
 */
export interface SpringConstraint {
  particleA: number;
  particleB: number;
  restLength: number;
  /** Compliance (inverse stiffness) for XPBD solver */
  compliance: number;
}

/**
 * Configuration for the spring system
 */
export interface SpringSystemConfig {
  /** Global stiffness multiplier */
  globalStiffness: number;
  /** Global damping multiplier */
  globalDamping: number;
  /** Number of constraint solver iterations (more = stiffer but slower) */
  solverIterations: number;
  /** Use Verlet integration (more stable for springs) */
  useVerlet: boolean;
  /** Enable spring breaking */
  enableBreaking: boolean;
  /** Gravity (for soft body integration) */
  gravity: { x: number; y: number; z: number };
}

// ════════════════════════════════════════════════════════════════════════════
//                                                 // spring // system // class
// ════════════════════════════════════════════════════════════════════════════

export class ParticleSpringSystem {
  private maxParticles: number;
  private springs: Spring[] = [];
  private constraints: SpringConstraint[] = [];
  private config: SpringSystemConfig;

  // Verlet integration requires previous positions
  private prevPositions: Float32Array | null = null;
  private initialized = false;

  constructor(maxParticles: number, config: Partial<SpringSystemConfig> = {}) {
    // Validate maxParticles
    this.maxParticles = Number.isFinite(maxParticles) && maxParticles > 0
      ? Math.min(Math.floor(maxParticles), 1_000_000)
      : 10000;

    // Validate and sanitize config values to prevent NaN propagation
    const safeFloat = (v: number | undefined, def: number, min: number, max: number) => {
      if (v === undefined || !Number.isFinite(v)) return def;
      return Math.max(min, Math.min(max, v));
    };

    const safeGravity = config.gravity;
    const gravity = safeGravity && 
      Number.isFinite(safeGravity.x) && 
      Number.isFinite(safeGravity.y) && 
      Number.isFinite(safeGravity.z)
        ? safeGravity
        : { x: 0, y: -980, z: 0 };

    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
    const solverIterations = (typeof config.solverIterations === "number" && Number.isFinite(config.solverIterations) && config.solverIterations >= 1) ? config.solverIterations : 4;
    const useVerlet = (typeof config.useVerlet === "boolean") ? config.useVerlet : true;
    const enableBreaking = (typeof config.enableBreaking === "boolean") ? config.enableBreaking : false;
    this.config = {
      globalStiffness: safeFloat(config.globalStiffness, 100, 0.001, 10000),
      globalDamping: safeFloat(config.globalDamping, 5, 0, 1000),
      solverIterations: Math.max(1, Math.min(64, Math.floor(solverIterations))),
      useVerlet,
      enableBreaking,
      gravity,
    };
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                            // initialization
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Initialize the system with particle buffer
   * Must be called before first update if using Verlet integration
   */
  initialize(particleBuffer: Float32Array): void {
    if (this.config.useVerlet) {
      // Store initial positions for Verlet integration
      this.prevPositions = new Float32Array(this.maxParticles * 3);
      for (let i = 0; i < this.maxParticles; i++) {
        const offset = i * PARTICLE_STRIDE;
        this.prevPositions[i * 3 + 0] = particleBuffer[offset + 0];
        this.prevPositions[i * 3 + 1] = particleBuffer[offset + 1];
        this.prevPositions[i * 3 + 2] = particleBuffer[offset + 2];
      }
    }
    this.initialized = true;
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                      // spring // management
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Add a spring between two particles
   */
  addSpring(
    particleA: number,
    particleB: number,
    restLength: number,
    stiffness?: number,
    damping?: number,
    breakThreshold?: number
  ): void {
    // Validate indices
    if (particleA < 0 || particleA >= this.maxParticles ||
        particleB < 0 || particleB >= this.maxParticles ||
        particleA === particleB) {
      return;
    }

    // Validate and sanitize spring parameters to prevent NaN
    const safeRestLength = Number.isFinite(restLength) && restLength > 0 
      ? restLength : 10;
    const safeStiffness = Number.isFinite(stiffness) && stiffness !== undefined
      ? Math.max(0.001, Math.min(10000, stiffness))
      : this.config.globalStiffness;
    const safeDamping = Number.isFinite(damping) && damping !== undefined
      ? Math.max(0, Math.min(1000, damping))
      : this.config.globalDamping;
    const safeBreakThreshold = Number.isFinite(breakThreshold) && breakThreshold !== undefined
      ? Math.max(0, breakThreshold)
      : 0;

    this.springs.push({
      particleA,
      particleB,
      restLength: safeRestLength,
      stiffness: safeStiffness,
      damping: safeDamping,
      breakThreshold: safeBreakThreshold,
      active: true,
    });
  }

  /**
   * Create a grid of springs for cloth simulation
   * @param startIndex - First particle index
   * @param width - Number of particles in X direction
   * @param height - Number of particles in Y direction
   * @param spacing - Distance between adjacent particles
   * @param stiffness - Spring stiffness
   */
  createClothGrid(
    startIndex: number,
    width: number,
    height: number,
    spacing: number,
    stiffness?: number
  ): void {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
    const k = (stiffness !== null && stiffness !== undefined && typeof stiffness === "number" && Number.isFinite(stiffness) && stiffness > 0) ? stiffness : this.config.globalStiffness;
    const diagLength = spacing * Math.SQRT2;

    for (let y = 0; y < height; y++) {
      for (let x = 0; x < width; x++) {
        const idx = startIndex + y * width + x;

        // Structural springs (horizontal)
        if (x < width - 1) {
          this.addSpring(idx, idx + 1, spacing, k);
        }

        // Structural springs (vertical)
        if (y < height - 1) {
          this.addSpring(idx, idx + width, spacing, k);
        }

        // Shear springs (diagonal)
        if (x < width - 1 && y < height - 1) {
          this.addSpring(idx, idx + width + 1, diagLength, k * 0.5);
          this.addSpring(idx + 1, idx + width, diagLength, k * 0.5);
        }

        // Bend springs (skip one particle for resistance to bending)
        if (x < width - 2) {
          this.addSpring(idx, idx + 2, spacing * 2, k * 0.25);
        }
        if (y < height - 2) {
          this.addSpring(idx, idx + width * 2, spacing * 2, k * 0.25);
        }
      }
    }
  }

  /**
   * Create a chain/rope of springs
   */
  createChain(
    particleIndices: number[],
    spacing: number,
    stiffness?: number
  ): void {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
    const k = (stiffness !== null && stiffness !== undefined && typeof stiffness === "number" && Number.isFinite(stiffness) && stiffness > 0) ? stiffness : this.config.globalStiffness;

    for (let i = 0; i < particleIndices.length - 1; i++) {
      this.addSpring(particleIndices[i], particleIndices[i + 1], spacing, k);
    }
  }

  /**
   * Create a soft body (3D lattice of springs)
   */
  createSoftBody(
    startIndex: number,
    width: number,
    height: number,
    depth: number,
    spacing: number,
    stiffness?: number
  ): void {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
    const k = (stiffness !== null && stiffness !== undefined && typeof stiffness === "number" && Number.isFinite(stiffness) && stiffness > 0) ? stiffness : this.config.globalStiffness;

    const getIdx = (x: number, y: number, z: number) =>
      startIndex + z * width * height + y * width + x;

    for (let z = 0; z < depth; z++) {
      for (let y = 0; y < height; y++) {
        for (let x = 0; x < width; x++) {
          const idx = getIdx(x, y, z);

          // Connect to neighbors in all 6 directions
          if (x < width - 1) this.addSpring(idx, getIdx(x + 1, y, z), spacing, k);
          if (y < height - 1) this.addSpring(idx, getIdx(x, y + 1, z), spacing, k);
          if (z < depth - 1) this.addSpring(idx, getIdx(x, y, z + 1), spacing, k);

          // Diagonal springs for structural integrity
          if (x < width - 1 && y < height - 1) {
            this.addSpring(idx, getIdx(x + 1, y + 1, z), spacing * Math.SQRT2, k * 0.5);
          }
          if (y < height - 1 && z < depth - 1) {
            this.addSpring(idx, getIdx(x, y + 1, z + 1), spacing * Math.SQRT2, k * 0.5);
          }
          if (x < width - 1 && z < depth - 1) {
            this.addSpring(idx, getIdx(x + 1, y, z + 1), spacing * Math.SQRT2, k * 0.5);
          }
        }
      }
    }
  }

  /**
   * Remove all springs
   */
  clearSprings(): void {
    this.springs = [];
    this.constraints = [];
  }

  /**
   * Remove springs connected to a specific particle
   */
  removeParticleSprings(particleIndex: number): void {
    this.springs = this.springs.filter(
      s => s.particleA !== particleIndex && s.particleB !== particleIndex
    );
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                         // physics // update
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Apply spring forces to particles
   * @param particleBuffer - The particle data buffer (modified in place)
   * @param dt - Delta time in seconds
   */
  update(particleBuffer: Float32Array, dt: number): void {
    if (!this.initialized && this.config.useVerlet) {
      this.initialize(particleBuffer);
    }

    // Validate dt
    const safeDt = Number.isFinite(dt) && dt > 0 ? Math.min(dt, 0.1) : 0.016;

    if (this.config.useVerlet) {
      this.updateVerlet(particleBuffer, safeDt);
    } else {
      this.updateEuler(particleBuffer, safeDt);
    }
  }

  /**
   * Euler integration with spring forces
   * Simpler but less stable for stiff springs
   */
  private updateEuler(buffer: Float32Array, dt: number): void {
    const brokenSprings: number[] = [];

    for (let s = 0; s < this.springs.length; s++) {
      const spring = this.springs[s];
      if (!spring.active) continue;

      const offsetA = spring.particleA * PARTICLE_STRIDE;
      const offsetB = spring.particleB * PARTICLE_STRIDE;

      // Skip dead particles
      const lifetimeA = buffer[offsetA + 7];
      const lifetimeB = buffer[offsetB + 7];
      if (lifetimeA <= 0 || lifetimeB <= 0) continue;

      // Get positions
      const ax = buffer[offsetA + 0];
      const ay = buffer[offsetA + 1];
      const az = buffer[offsetA + 2];
      const bx = buffer[offsetB + 0];
      const by = buffer[offsetB + 1];
      const bz = buffer[offsetB + 2];

      // Get velocities
      const avx = buffer[offsetA + 3];
      const avy = buffer[offsetA + 4];
      const avz = buffer[offsetA + 5];
      const bvx = buffer[offsetB + 3];
      const bvy = buffer[offsetB + 4];
      const bvz = buffer[offsetB + 5];

      // Calculate spring vector
      const dx = bx - ax;
      const dy = by - ay;
      const dz = bz - az;
      const dist = Math.sqrt(dx * dx + dy * dy + dz * dz);

      if (dist < 0.0001) continue;

      // Check for breaking
      if (this.config.enableBreaking && spring.breakThreshold > 0) {
        const stretch = Math.abs(dist - spring.restLength) / spring.restLength;
        if (stretch > spring.breakThreshold) {
          brokenSprings.push(s);
          continue;
        }
      }

      // Normalize direction
      const nx = dx / dist;
      const ny = dy / dist;
      const nz = dz / dist;

      // Hooke's Law: F = -k * (x - rest)
      const displacement = dist - spring.restLength;
      const springForce = spring.stiffness * this.config.globalStiffness * displacement;

      // Damping: F_damp = -c * v_relative_along_spring
      const relVelX = bvx - avx;
      const relVelY = bvy - avy;
      const relVelZ = bvz - avz;
      const relVelAlongSpring = relVelX * nx + relVelY * ny + relVelZ * nz;
      const dampingForce = spring.damping * this.config.globalDamping * relVelAlongSpring;

      // Total force magnitude - clamp to prevent numerical instability
      // Max force prevents runaway when damping is 0 and stiffness is high
      const MAX_FORCE = 10000;
      const rawForceMag = springForce + dampingForce;
      const forceMag = Math.max(-MAX_FORCE, Math.min(MAX_FORCE, rawForceMag));

      // Skip if force is not finite
      if (!Number.isFinite(forceMag)) continue;

      // Apply forces (equal and opposite to both particles)
      const forceX = forceMag * nx;
      const forceY = forceMag * ny;
      const forceZ = forceMag * nz;

      // Get masses for acceleration (F = ma -> a = F/m)
      const massA = Math.max(buffer[offsetA + 8], 0.1);
      const massB = Math.max(buffer[offsetB + 8], 0.1);

      // Calculate velocity deltas
      const dvAx = (forceX / massA) * dt;
      const dvAy = (forceY / massA) * dt;
      const dvAz = (forceZ / massA) * dt;
      const dvBx = (forceX / massB) * dt;
      const dvBy = (forceY / massB) * dt;
      const dvBz = (forceZ / massB) * dt;

      // Only apply if deltas are finite
      if (Number.isFinite(dvAx) && Number.isFinite(dvAy) && Number.isFinite(dvAz)) {
        buffer[offsetA + 3] += dvAx;
        buffer[offsetA + 4] += dvAy;
        buffer[offsetA + 5] += dvAz;
      }

      if (Number.isFinite(dvBx) && Number.isFinite(dvBy) && Number.isFinite(dvBz)) {
        buffer[offsetB + 3] -= dvBx;
        buffer[offsetB + 4] -= dvBy;
        buffer[offsetB + 5] -= dvBz;
      }
    }

    // Remove broken springs
    for (let i = brokenSprings.length - 1; i >= 0; i--) {
      this.springs[brokenSprings[i]].active = false;
    }

    // Integrate positions based on velocities
    // Clamp max velocity to prevent numerical instability
    const MAX_VELOCITY = 10000;
    
    for (let i = 0; i < this.maxParticles; i++) {
      const offset = i * PARTICLE_STRIDE;
      const lifetime = buffer[offset + 7];
      const age = buffer[offset + 6];

      if (lifetime <= 0 || age >= lifetime) continue;

      // Apply gravity to velocity
      buffer[offset + 3] += this.config.gravity.x * dt;
      buffer[offset + 4] += this.config.gravity.y * dt;
      buffer[offset + 5] += this.config.gravity.z * dt;

      // Clamp velocities to prevent runaway
      buffer[offset + 3] = Math.max(-MAX_VELOCITY, Math.min(MAX_VELOCITY, buffer[offset + 3]));
      buffer[offset + 4] = Math.max(-MAX_VELOCITY, Math.min(MAX_VELOCITY, buffer[offset + 4]));
      buffer[offset + 5] = Math.max(-MAX_VELOCITY, Math.min(MAX_VELOCITY, buffer[offset + 5]));

      // Skip if velocity is NaN
      if (!Number.isFinite(buffer[offset + 3])) buffer[offset + 3] = 0;
      if (!Number.isFinite(buffer[offset + 4])) buffer[offset + 4] = 0;
      if (!Number.isFinite(buffer[offset + 5])) buffer[offset + 5] = 0;

      // Update position
      const newX = buffer[offset + 0] + buffer[offset + 3] * dt;
      const newY = buffer[offset + 1] + buffer[offset + 4] * dt;
      const newZ = buffer[offset + 2] + buffer[offset + 5] * dt;

      // Only apply if positions are finite
      if (Number.isFinite(newX)) buffer[offset + 0] = newX;
      if (Number.isFinite(newY)) buffer[offset + 1] = newY;
      if (Number.isFinite(newZ)) buffer[offset + 2] = newZ;
    }
  }

  /**
   * Verlet integration with position-based constraints
   * More stable for stiff springs and cloth simulation
   */
  private updateVerlet(buffer: Float32Array, dt: number): void {
    if (!this.prevPositions) return;

    const gravity = this.config.gravity;
    const brokenSprings: number[] = [];

    // Step 1: Verlet integration (position update based on previous position)
    for (let i = 0; i < this.maxParticles; i++) {
      const offset = i * PARTICLE_STRIDE;
      const lifetime = buffer[offset + 7];
      const age = buffer[offset + 6];

      if (lifetime <= 0 || age >= lifetime) continue;

      const mass = Math.max(buffer[offset + 8], 0.1);

      // Current position
      const px = buffer[offset + 0];
      const py = buffer[offset + 1];
      const pz = buffer[offset + 2];

      // Previous position
      const prevX = this.prevPositions[i * 3 + 0];
      const prevY = this.prevPositions[i * 3 + 1];
      const prevZ = this.prevPositions[i * 3 + 2];

      // Verlet: new_pos = 2 * pos - prev_pos + acceleration * dt²
      // acceleration = gravity / mass (but gravity is already an acceleration)
      const accelX = gravity.x;
      const accelY = gravity.y;
      const accelZ = gravity.z;

      const newX = 2 * px - prevX + accelX * dt * dt;
      const newY = 2 * py - prevY + accelY * dt * dt;
      const newZ = 2 * pz - prevZ + accelZ * dt * dt;

      // Store current as previous
      this.prevPositions[i * 3 + 0] = px;
      this.prevPositions[i * 3 + 1] = py;
      this.prevPositions[i * 3 + 2] = pz;

      // Update position
      buffer[offset + 0] = newX;
      buffer[offset + 1] = newY;
      buffer[offset + 2] = newZ;

      // Derive velocity from position change (for other systems)
      buffer[offset + 3] = (newX - px) / dt;
      buffer[offset + 4] = (newY - py) / dt;
      buffer[offset + 5] = (newZ - pz) / dt;
    }

    // Step 2: Satisfy spring constraints (multiple iterations for stiffness)
    for (let iter = 0; iter < this.config.solverIterations; iter++) {
      for (let s = 0; s < this.springs.length; s++) {
        const spring = this.springs[s];
        if (!spring.active) continue;

        const offsetA = spring.particleA * PARTICLE_STRIDE;
        const offsetB = spring.particleB * PARTICLE_STRIDE;

        // Skip dead particles
        const lifetimeA = buffer[offsetA + 7];
        const lifetimeB = buffer[offsetB + 7];
        if (lifetimeA <= 0 || lifetimeB <= 0) continue;

        // Get positions
        const ax = buffer[offsetA + 0];
        const ay = buffer[offsetA + 1];
        const az = buffer[offsetA + 2];
        const bx = buffer[offsetB + 0];
        const by = buffer[offsetB + 1];
        const bz = buffer[offsetB + 2];

        // Calculate current length
        const dx = bx - ax;
        const dy = by - ay;
        const dz = bz - az;
        const dist = Math.sqrt(dx * dx + dy * dy + dz * dz);

        if (dist < 0.0001) continue;

        // Check for breaking
        if (this.config.enableBreaking && spring.breakThreshold > 0 && iter === 0) {
          const stretch = Math.abs(dist - spring.restLength) / spring.restLength;
          if (stretch > spring.breakThreshold) {
            brokenSprings.push(s);
            continue;
          }
        }

        // Calculate correction
        const diff = (dist - spring.restLength) / dist;

        // Get inverse masses for weighted correction
        const massA = Math.max(buffer[offsetA + 8], 0.1);
        const massB = Math.max(buffer[offsetB + 8], 0.1);
        const invMassA = 1 / massA;
        const invMassB = 1 / massB;
        const invMassSum = invMassA + invMassB;

        if (invMassSum < 0.0001) continue;

        // Position correction (mass-weighted)
        const correctionFactor = diff * 0.5; // Relaxation factor for stability
        const corrX = dx * correctionFactor;
        const corrY = dy * correctionFactor;
        const corrZ = dz * correctionFactor;

        const weightA = invMassA / invMassSum;
        const weightB = invMassB / invMassSum;

        // Apply corrections
        buffer[offsetA + 0] += corrX * weightA;
        buffer[offsetA + 1] += corrY * weightA;
        buffer[offsetA + 2] += corrZ * weightA;

        buffer[offsetB + 0] -= corrX * weightB;
        buffer[offsetB + 1] -= corrY * weightB;
        buffer[offsetB + 2] -= corrZ * weightB;
      }
    }

    // Remove broken springs
    for (let i = brokenSprings.length - 1; i >= 0; i--) {
      this.springs[brokenSprings[i]].active = false;
    }
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                                       // pin
  // ════════════════════════════════════════════════════════════════════════════

  /** Particles that are pinned (don't move) */
  private pinnedParticles: Set<number> = new Set();

  /**
   * Pin a particle in place (useful for cloth anchors)
   */
  pinParticle(particleIndex: number): void {
    this.pinnedParticles.add(particleIndex);
  }

  /**
   * Unpin a particle
   */
  unpinParticle(particleIndex: number): void {
    this.pinnedParticles.delete(particleIndex);
  }

  /**
   * Check if a particle is pinned
   */
  isPinned(particleIndex: number): boolean {
    return this.pinnedParticles.has(particleIndex);
  }

  /**
   * Apply pin constraints (call after spring update)
   */
  applyPins(buffer: Float32Array, pinPositions: Map<number, { x: number; y: number; z: number }>): void {
    for (const [idx, pos] of pinPositions) {
      if (idx < 0 || idx >= this.maxParticles) continue;

      const offset = idx * PARTICLE_STRIDE;
      buffer[offset + 0] = pos.x;
      buffer[offset + 1] = pos.y;
      buffer[offset + 2] = pos.z;
      buffer[offset + 3] = 0; // Zero velocity
      buffer[offset + 4] = 0;
      buffer[offset + 5] = 0;

      // Also update prevPositions for Verlet
      if (this.prevPositions) {
        this.prevPositions[idx * 3 + 0] = pos.x;
        this.prevPositions[idx * 3 + 1] = pos.y;
        this.prevPositions[idx * 3 + 2] = pos.z;
      }
    }
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                                 // accessors
  // ════════════════════════════════════════════════════════════════════════════

  getSpringCount(): number {
    return this.springs.filter(s => s.active).length;
  }

  getSprings(): readonly Spring[] {
    return this.springs;
  }

  updateConfig(config: Partial<SpringSystemConfig>): void {
    Object.assign(this.config, config);
  }

  getConfig(): SpringSystemConfig {
    return { ...this.config };
  }
}
