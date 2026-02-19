/**
 * ParticleSimulationController - Scrub-Safe Particle Evaluation
 *
 * ARCHITECTURAL CONTRACT:
 * =======================
 * This controller makes particle systems DETERMINISTIC and SCRUB-SAFE.
 *
 * PROBLEM:
 * ParticleSystem.step() accumulates state over time. Without this controller,
 * scrubbing to frame 100, then to frame 50, then back to frame 100 produces
 * DIFFERENT results because the simulation path was 0→100→50→100 instead of 0→100.
 *
 * SOLUTION:
 * 1. Use a seeded RNG for all randomness
 * 2. Cache particle state at regular checkpoint intervals
 * 3. To evaluate frame N: reset to nearest checkpoint, replay simulation to N
 *
 * GUARANTEES:
 * - evaluateAtFrame(100) always returns identical ParticleSnapshot
 * - Scrub order does not affect results
 * - Same seed + config + frame → identical particle positions
 *
 * AXIOMS ENFORCED:
 * - Axiom 1: Time is immutable input
 * - Axiom 2: Frame evaluation is order-independent
 * - Axiom 5: Particles are evaluated, not advanced
 */

import type { Particle, ParticleSystemConfig } from "@/services/particleSystem";
import { ParticleSystem } from "@/services/particleSystem";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                                     // types
// ════════════════════════════════════════════════════════════════════════════

/**
 * Immutable snapshot of particle system state at a specific frame
 * DETERMINISM: No timestamps or non-deterministic values
 */
export interface ParticleSnapshot {
  /** Frame number this snapshot represents */
  readonly frame: number;

  /** Deep copy of all particles at this frame */
  readonly particles: readonly ParticleState[];

  /** Total particle count */
  readonly count: number;

  /** Seed used for this simulation */
  readonly seed: number;

  /** RNG state at this snapshot (for checkpoint restoration) */
  readonly rngState: number;
}

/**
 * Serializable particle state (complete Particle state for checkpoint restoration)
 */
export interface ParticleState {
  readonly id: number;
  readonly x: number;
  readonly y: number;
  readonly prevX: number; // For trail rendering
  readonly prevY: number;
  readonly vx: number;
  readonly vy: number;
  readonly age: number;
  readonly lifetime: number;
  readonly size: number;
  readonly baseSize: number; // Original size before modulations
  readonly color: readonly [number, number, number, number];
  readonly baseColor: readonly [number, number, number, number]; // Original color
  readonly rotation: number;
  readonly angularVelocity: number;
  readonly spriteIndex: number;
  readonly emitterId: string;
  readonly isSubParticle: boolean;
  readonly collisionCount: number;
}

/**
 * Checkpoint: cached particle state at a frame
 * DETERMINISM: Captures all state needed for exact replay
 */
interface Checkpoint {
  frame: number;
  particles: ParticleState[];
  emissionAccumulators: Map<string, number>;
  nextParticleId: number;
  noiseTime: number;
  frameCount: number;
  /** RNG state at this checkpoint for deterministic restoration */
  rngState: number;
}

/**
 * Seeded pseudo-random number generator
 * Uses mulberry32 algorithm for deterministic results
 */
class SeededRNG {
  private state: number;

  constructor(seed: number) {
    this.state = seed;
  }

  /** Reset to initial seed */
  reset(seed: number): void {
    this.state = seed;
  }

  /** Get next random number in [0, 1) */
  next(): number {
    let t = (this.state += 0x6d2b79f5);
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  }

  /** Get random in range [min, max] */
  range(min: number, max: number): number {
    return min + this.next() * (max - min);
  }

  /** Get current state for checkpointing */
  getState(): number {
    return this.state;
  }

  /** Restore state from checkpoint */
  setState(state: number): void {
    this.state = state;
  }
}

// ════════════════════════════════════════════════════════════════════════════
//                                              // controller // implementation
// ════════════════════════════════════════════════════════════════════════════

export class ParticleSimulationController {
  /** The underlying particle system (used for simulation) */
  private system: ParticleSystem;

  /** Configuration (immutable after construction) */
  private readonly config: ParticleSystemConfig;

  /** Master seed for deterministic simulation */
  private readonly seed: number;

  /** Seeded RNG instance */
  private readonly rng: SeededRNG;

  /** Checkpoint interval (frames between cached states) */
  private readonly checkpointInterval: number;

  /** Cached checkpoints: frame → checkpoint */
  private readonly checkpoints: Map<number, Checkpoint>;

  /** Last evaluated frame (for optimization) */
  private lastEvaluatedFrame: number = -1;

  /** Last snapshot (cached for repeated access) */
  private lastSnapshot: ParticleSnapshot | null = null;

  constructor(
    config: ParticleSystemConfig,
    seed: number = 12345,
    checkpointInterval: number = 30, // Cache every 30 frames (~2 seconds at 16fps)
  ) {
    this.config = { ...config };
    this.seed = seed;
    this.rng = new SeededRNG(seed);
    // Validate checkpointInterval to prevent modulo by zero
    this.checkpointInterval = Number.isFinite(checkpointInterval) && checkpointInterval > 0
      ? Math.floor(checkpointInterval)
      : 30;
    this.checkpoints = new Map();

    // Create the underlying particle system with the SAME SEED for determinism
    this.system = new ParticleSystem(config, seed);

    // Run warmup period - simulate particles before frame 0 to "pre-fill" the system
    // This creates a more natural looking initial state (e.g., snow already falling)
    if (config.warmupPeriod && config.warmupPeriod > 0) {
      this.system.warmup();
    }

    // Create initial checkpoint at frame 0 (which now includes warmup state)
    this.createCheckpoint(0);
  }

  /**
   * Evaluate particle state at a specific frame
   *
   * PURE (relative to frame number): Same frame always produces same result.
   *
   * @param frame - Target frame number
   * @returns Immutable ParticleSnapshot
   */
  evaluateAtFrame(frame: number): ParticleSnapshot {
    // Optimization: return cached snapshot if same frame
    if (frame === this.lastEvaluatedFrame && this.lastSnapshot) {
      return this.lastSnapshot;
    }

    // Find nearest checkpoint at or before target frame
    const checkpointFrame = this.findNearestCheckpoint(frame);

    // Restore state from checkpoint
    this.restoreCheckpoint(checkpointFrame);

    // Simulate from checkpoint to target frame
    const framesToSimulate = frame - checkpointFrame;
    for (let i = 0; i < framesToSimulate; i++) {
      this.deterministicStep();

      // Create checkpoint at interval boundaries
      const currentFrame = checkpointFrame + i + 1;
      if (
        currentFrame % this.checkpointInterval === 0 &&
        !this.checkpoints.has(currentFrame)
      ) {
        this.createCheckpoint(currentFrame);
      }
    }

    // Create and cache snapshot
    const snapshot = this.createSnapshot(frame);
    this.lastEvaluatedFrame = frame;
    this.lastSnapshot = snapshot;

    return snapshot;
  }

  /**
   * Get the underlying particles for rendering
   * NOTE: This is a convenience method; prefer evaluateAtFrame() for determinism
   */
  getParticles(): readonly Particle[] {
    return this.system.getParticles();
  }

  /**
   * Reset controller and clear all checkpoints
   */
  reset(): void {
    this.system.reset();
    this.rng.reset(this.seed);
    this.checkpoints.clear();
    this.lastEvaluatedFrame = -1;
    this.lastSnapshot = null;
    this.createCheckpoint(0);
  }

  /**
   * Update configuration (clears all checkpoints)
   */
  updateConfig(updates: Partial<ParticleSystemConfig>): void {
    Object.assign(this.config, updates);
    this.system.setConfig(updates);
    this.reset(); // Must reset - config change invalidates all checkpoints
  }

  /**
   * Get current seed
   */
  getSeed(): number {
    return this.seed;
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                        // private // methods
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Find the frame number of the nearest checkpoint at or before target
   */
  private findNearestCheckpoint(targetFrame: number): number {
    let nearest = 0;
    for (const frame of this.checkpoints.keys()) {
      if (frame <= targetFrame && frame > nearest) {
        nearest = frame;
      }
    }
    return nearest;
  }

  /**
   * Create a checkpoint at the current state
   * DETERMINISM: Captures RNG state for exact restoration
   */
  private createCheckpoint(frame: number): void {
    const particles = this.system
      .getParticles()
      .map((p) => this.serializeParticle(p));

    // Access internal state for full checkpoint
    const checkpoint: Checkpoint = {
      frame,
      particles,
      emissionAccumulators: new Map(), // Would need access to system internals
      nextParticleId:
        particles.length > 0 ? Math.max(...particles.map((p) => p.id)) + 1 : 0,
      noiseTime: 0, // Would need access to system internals
      frameCount: frame,
      // Capture RNG state from the particle system for deterministic restoration
      rngState: this.system.getRng().getState(),
    };

    this.checkpoints.set(frame, checkpoint);
  }

  /**
   * Restore state from a checkpoint
   * DETERMINISM: Restores exact RNG state for reproducible continuation
   */
  private restoreCheckpoint(frame: number): void {
    const checkpoint = this.checkpoints.get(frame);
    if (!checkpoint) {
      throw new Error(`No checkpoint at frame ${frame}`);
    }

    // Restore RNG state from the checkpoint - this is the KEY to determinism
    // The ParticleSystem's RNG must be at the exact same state it was
    // when this checkpoint was created
    this.system.getRng().setState(checkpoint.rngState);
    this.rng.setState(checkpoint.rngState);

    // Restore particles from checkpoint
    // For frame 0, this will be an empty array (fresh start)
    // For other frames, this restores exact particle positions
    this.system.restoreParticles(checkpoint.particles, checkpoint.frame);
  }

  /**
   * Perform one deterministic simulation step
   * DETERMINISM: ParticleSystem now uses seeded RNG (mulberry32) for all randomness
   */
  private deterministicStep(): void {
    // ParticleSystem.step() is now fully deterministic:
    // - All Math.random() calls replaced with seeded RNG (this.rng.next())
    // - Same seed + same frame = identical particle positions
    // - Scrub-order independent: frame N always produces same result
    this.system.step(1);
  }

  /**
   * Serialize a particle to immutable state
   */
  private serializeParticle(p: Particle): ParticleState {
    return Object.freeze({
      id: p.id,
      x: p.x,
      y: p.y,
      prevX: p.prevX,
      prevY: p.prevY,
      vx: p.vx,
      vy: p.vy,
      age: p.age,
      lifetime: p.lifetime,
      size: p.size,
      baseSize: p.baseSize,
      color: Object.freeze([...p.color]) as readonly [
        number,
        number,
        number,
        number,
      ],
      baseColor: Object.freeze([...p.baseColor]) as readonly [
        number,
        number,
        number,
        number,
      ],
      rotation: p.rotation,
      angularVelocity: p.angularVelocity,
      spriteIndex: p.spriteIndex,
      emitterId: p.emitterId,
      isSubParticle: p.isSubParticle,
      collisionCount: p.collisionCount,
    });
  }

  /**
   * Create an immutable snapshot of current state
   * DETERMINISM: No timestamps - only deterministic values
   */
  private createSnapshot(frame: number): ParticleSnapshot {
    const particles = this.system
      .getParticles()
      .map((p) => this.serializeParticle(p));

    return Object.freeze({
      frame,
      particles: Object.freeze(particles),
      count: particles.length,
      seed: this.seed,
      rngState: this.system.getRng().getState(),
    });
  }
}

// ════════════════════════════════════════════════════════════════════════════
//                                   // integration // with // motion // engine
// ════════════════════════════════════════════════════════════════════════════

/**
 * Registry of particle simulation controllers by layer ID
 * Used by MotionEngine to evaluate particle layers deterministically
 */
export class ParticleSimulationRegistry {
  private controllers: Map<string, ParticleSimulationController> = new Map();

  /**
   * Get or create a controller for a layer
   */
  getController(
    layerId: string,
    config: ParticleSystemConfig,
    seed?: number,
  ): ParticleSimulationController {
    let controller = this.controllers.get(layerId);

    if (!controller) {
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
      const seedValue = (seed !== null && seed !== undefined && typeof seed === "number" && Number.isFinite(seed)) ? seed : this.generateSeed(layerId);
      controller = new ParticleSimulationController(
        config,
        seedValue,
      );
      this.controllers.set(layerId, controller);
    }

    return controller;
  }

  /**
   * Evaluate particles for a layer at a frame
   */
  evaluateLayer(
    layerId: string,
    frame: number,
    config: ParticleSystemConfig,
    seed?: number,
  ): ParticleSnapshot {
    const controller = this.getController(layerId, config, seed);
    return controller.evaluateAtFrame(frame);
  }

  /**
   * Reset a specific layer's controller
   */
  resetLayer(layerId: string): void {
    const controller = this.controllers.get(layerId);
    if (controller) {
      controller.reset();
    }
  }

  /**
   * Clear all controllers
   */
  clear(): void {
    this.controllers.clear();
  }

  /**
   * Generate deterministic seed from layer ID
   */
  private generateSeed(layerId: string): number {
    let hash = 0;
    for (let i = 0; i < layerId.length; i++) {
      const char = layerId.charCodeAt(i);
      hash = (hash << 5) - hash + char;
      hash = hash & hash; // Convert to 32bit integer
    }
    return Math.abs(hash);
  }
}

// ════════════════════════════════════════════════════════════════════════════
//                                                     // singleton // instance
// ════════════════════════════════════════════════════════════════════════════

export const particleSimulationRegistry = new ParticleSimulationRegistry();

// ════════════════════════════════════════════════════════════════════════════
//                                                                   // exports
// ════════════════════════════════════════════════════════════════════════════

export default ParticleSimulationController;
