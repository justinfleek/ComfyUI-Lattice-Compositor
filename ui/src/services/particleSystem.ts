/**
 * Particle System Engine (CPU-based)
 *
 * @deprecated ARCHITECTURE NOTE:
 * ===============================
 * This is the legacy CPU-based particle system. For new particle features,
 * prefer using engine/particles/GPUParticleSystem.ts which provides:
 * - GPU-accelerated physics via WebGL2 transform feedback
 * - Instanced rendering for 100k+ particles
 * - Sprite sheet animation and motion blur
 * - Particle trails and connections
 * - Better performance through parallel GPU execution
 *
 * This module is kept for:
 * - ParticleSimulationController (deterministic timeline scrubbing)
 * - SeededRandom utility (used by shapeOperations.ts)
 * - Type definitions shared across the codebase
 *
 * DETERMINISM NOTICE:
 * ===================
 * This module uses a SEEDED RNG for all randomness to ensure deterministic
 * simulation. The same seed + config + frame produces identical results.
 * Math.random() is NEVER used directly.
 */
import { EASING_PRESETS, applyEasing } from './interpolation';
import { createNoise2D } from 'simplex-noise';

// ============================================================================
// IMPORTS FROM SUBMODULES
// ============================================================================

// Import types for local use (with underscore prefix for internal use)
import type {
  Particle as _Particle,
  TurbulenceConfig as _TurbulenceConfig,
  ConnectionConfig as _ConnectionConfig,
  SubEmitterConfig as _SubEmitterConfig,
  EmitterShape as _EmitterShape,
  SplinePathEmission as _SplinePathEmission,
  SplineQueryResult as _SplineQueryResult,
  SplinePathProvider as _SplinePathProvider,
  SpriteConfig as _SpriteConfig,
  EmitterConfig as _EmitterConfig,
  GravityWellConfig as _GravityWellConfig,
  VortexConfig as _VortexConfig,
  LorenzAttractorConfig as _LorenzAttractorConfig,
  ParticleModulation as _ParticleModulation,
  CollisionConfig as _CollisionConfig,
  ParticleSystemConfig as _ParticleSystemConfig,
  RenderOptions as _RenderOptions,
  SpatialGrid as _SpatialGrid,
} from './particles/particleTypes';

// Import factory functions for local use
import {
  resetIdCounter as _resetIdCounter,
  createDefaultSpriteConfig as _createDefaultSpriteConfig,
  createDefaultSplinePathEmission as _createDefaultSplinePathEmission,
  createDefaultCollisionConfig as _createDefaultCollisionConfig,
  createDefaultEmitterConfig as _createDefaultEmitterConfig,
  createDefaultTurbulenceConfig as _createDefaultTurbulenceConfig,
  createDefaultConnectionConfig as _createDefaultConnectionConfig,
  createDefaultSubEmitterConfig as _createDefaultSubEmitterConfig,
  createDefaultGravityWellConfig as _createDefaultGravityWellConfig,
  createDefaultVortexConfig as _createDefaultVortexConfig,
  createDefaultSystemConfig as _createDefaultSystemConfig,
  createDefaultRenderOptions as _createDefaultRenderOptions,
} from './particles/particleDefaults';

// Import SeededRandom class
import { SeededRandom as _SeededRandom } from './particles/SeededRandom';

// ============================================================================
// RE-EXPORTS FOR BACKWARDS COMPATIBILITY
// ============================================================================

// Re-export all types
export type {
  Particle,
  TurbulenceConfig,
  ConnectionConfig,
  SubEmitterConfig,
  EmitterShape,
  SplinePathEmission,
  SplineQueryResult,
  SplinePathProvider,
  SpriteConfig,
  EmitterConfig,
  GravityWellConfig,
  VortexConfig,
  LorenzAttractorConfig,
  ParticleModulation,
  CollisionConfig,
  ParticleSystemConfig,
  RenderOptions,
  SpatialGrid,
} from './particles/particleTypes';

// Re-export factory functions
export {
  resetIdCounter,
  createDefaultSpriteConfig,
  createDefaultSplinePathEmission,
  createDefaultCollisionConfig,
  createDefaultEmitterConfig,
  createDefaultTurbulenceConfig,
  createDefaultConnectionConfig,
  createDefaultSubEmitterConfig,
  createDefaultGravityWellConfig,
  createDefaultVortexConfig,
  createDefaultSystemConfig,
  createDefaultRenderOptions,
} from './particles/particleDefaults';

// Re-export SeededRandom
export { SeededRandom } from './particles/SeededRandom';

// ============================================================================
// LOCAL ALIASES FOR INTERNAL USE
// ============================================================================

// Type aliases for internal use
type Particle = _Particle;
type TurbulenceConfig = _TurbulenceConfig;
type ConnectionConfig = _ConnectionConfig;
type SubEmitterConfig = _SubEmitterConfig;
type EmitterShape = _EmitterShape;
type SplinePathEmission = _SplinePathEmission;
type SplineQueryResult = _SplineQueryResult;
type SplinePathProvider = _SplinePathProvider;
type SpriteConfig = _SpriteConfig;
type EmitterConfig = _EmitterConfig;
type GravityWellConfig = _GravityWellConfig;
type VortexConfig = _VortexConfig;
type LorenzAttractorConfig = _LorenzAttractorConfig;
type ParticleModulation = _ParticleModulation;
type CollisionConfig = _CollisionConfig;
type ParticleSystemConfig = _ParticleSystemConfig;
type RenderOptions = _RenderOptions;
type SpatialGrid = _SpatialGrid;

// Function aliases for internal use
const resetIdCounter = _resetIdCounter;
const createDefaultSpriteConfig = _createDefaultSpriteConfig;
const createDefaultSplinePathEmission = _createDefaultSplinePathEmission;
const createDefaultCollisionConfig = _createDefaultCollisionConfig;
const createDefaultEmitterConfig = _createDefaultEmitterConfig;
const createDefaultTurbulenceConfig = _createDefaultTurbulenceConfig;
const createDefaultConnectionConfig = _createDefaultConnectionConfig;
const createDefaultSubEmitterConfig = _createDefaultSubEmitterConfig;
const createDefaultGravityWellConfig = _createDefaultGravityWellConfig;
const createDefaultVortexConfig = _createDefaultVortexConfig;
const createDefaultSystemConfig = _createDefaultSystemConfig;
const createDefaultRenderOptions = _createDefaultRenderOptions;

// SeededRandom alias
const SeededRandom = _SeededRandom;

// ============================================================================
// Particle System Class
// ============================================================================

export class ParticleSystem {
  private particles: Particle[] = [];
  private emitters: Map<string, EmitterConfig> = new Map();
  private gravityWells: Map<string, GravityWellConfig> = new Map();
  private vortices: Map<string, VortexConfig> = new Map();
  private lorenzAttractors: Map<string, LorenzAttractorConfig> = new Map();
  private modulations: ParticleModulation[] = [];
  private config: ParticleSystemConfig;
  private boundaryMask: ImageData | null = null;
  private frameCount: number = 0;
  private emissionAccumulators: Map<string, number> = new Map();
  private nextParticleId: number = 0;
  private trailHistory: Map<number, Array<{x: number; y: number}>> = new Map();

  // ============================================================================
  // PARTICLE POOL - Recycles dead particles to reduce GC pressure
  // Memory management: Pool limited to maxParticles to prevent unbounded growth
  // ============================================================================
  private particlePool: Particle[] = [];
  private readonly poolMaxSize: number = 10000; // Cap pool size

  // Audio reactivity state
  private featureOverrides: Map<string, number> = new Map();

  // Turbulence noise generator (seeded for determinism)
  private noise2D: ReturnType<typeof createNoise2D>;
  private noiseTime: number = 0;

  // Render options cache for spatial grid
  private renderOptions: RenderOptions = createDefaultRenderOptions();

  // Sprite image cache - maps emitter ID to loaded image
  private spriteCache: Map<string, HTMLImageElement | ImageBitmap> = new Map();

  // Collision spatial hash grid
  private collisionGrid: Map<string, Particle[]> = new Map();
  private collisionGridCellSize: number = 50;

  // SEEDED RNG - For deterministic simulation
  // Same seed + same config + same frame = identical particle state
  private rng: SeededRandom;

  // Spline path provider for emitters with shape='spline'
  // Set by the engine integration (e.g., WeylEngine) to resolve spline paths
  private splineProvider: SplinePathProvider | null = null;

  // Current frame for spline queries
  private currentFrame: number = 0;

  // Sequential emit state per emitter (for 'sequential' emit mode)
  private sequentialEmitT: Map<string, number> = new Map();

  constructor(config: Partial<ParticleSystemConfig> = {}, seed: number = 12345) {
    this.config = { ...createDefaultSystemConfig(), ...config };
    this.rng = new SeededRandom(seed);
    // Create seeded noise using our RNG to seed simplex
    this.noise2D = createNoise2D(() => this.rng.next());
    if (this.config.collision) {
      this.collisionGridCellSize = this.config.collision.spatialHashCellSize;
    }
  }

  /**
   * Get the RNG instance (for external access/checkpointing)
   */
  getRng(): SeededRandom {
    return this.rng;
  }

  /**
   * Set new seed and reset RNG
   */
  setSeed(seed: number): void {
    this.rng.setSeed(seed);
    // Recreate noise with new seed
    this.noise2D = createNoise2D(() => this.rng.next());
  }

  /**
   * Set the spline path provider callback
   * This allows emitters with shape='spline' to query spline positions
   */
  setSplineProvider(provider: SplinePathProvider | null): void {
    this.splineProvider = provider;
  }

  /**
   * Get the current spline provider
   */
  getSplineProvider(): SplinePathProvider | null {
    return this.splineProvider;
  }

  /**
   * Set the current frame for spline queries
   * Called by the engine before stepping the simulation
   */
  setCurrentFrame(frame: number): void {
    this.currentFrame = frame;
  }

  // ============================================================================
  // Sprite Management
  // ============================================================================

  /**
   * Load a sprite image for an emitter
   */
  async loadSprite(emitterId: string, imageUrl: string): Promise<void> {
    return new Promise((resolve, reject) => {
      const img = new Image();
      img.crossOrigin = 'anonymous';
      img.onload = () => {
        this.spriteCache.set(emitterId, img);
        const emitter = this.emitters.get(emitterId);
        if (emitter && emitter.sprite) {
          emitter.sprite.imageData = img;
        }
        resolve();
      };
      img.onerror = reject;
      img.src = imageUrl;
    });
  }

  /**
   * Set sprite image directly (for pre-loaded images)
   */
  setSpriteImage(emitterId: string, image: HTMLImageElement | ImageBitmap): void {
    this.spriteCache.set(emitterId, image);
    const emitter = this.emitters.get(emitterId);
    if (emitter && emitter.sprite) {
      emitter.sprite.imageData = image;
    }
  }

  /**
   * Get sprite image for an emitter
   */
  getSpriteImage(emitterId: string): HTMLImageElement | ImageBitmap | null {
    return this.spriteCache.get(emitterId) ?? null;
  }

  // ============================================================================
  // Emitter Management
  // ============================================================================

  addEmitter(config: EmitterConfig): void {
    this.emitters.set(config.id, { ...config });
    this.emissionAccumulators.set(config.id, 0);

    // Handle initial burst
    if (config.initialBurst > 0 && config.enabled) {
      const burstCount = Math.floor(config.emissionRate * config.initialBurst * 10);
      for (let i = 0; i < burstCount; i++) {
        this.spawnParticle(config);
      }
    }
  }

  updateEmitter(id: string, updates: Partial<EmitterConfig>): void {
    const emitter = this.emitters.get(id);
    if (emitter) {
      Object.assign(emitter, updates);
    }
  }

  removeEmitter(id: string): void {
    this.emitters.delete(id);
    this.emissionAccumulators.delete(id);
  }

  getEmitter(id: string): EmitterConfig | undefined {
    return this.emitters.get(id);
  }

  getEmitters(): EmitterConfig[] {
    return Array.from(this.emitters.values());
  }

  // ============================================================================
  // Gravity Well Management
  // ============================================================================

  addGravityWell(config: GravityWellConfig): void {
    this.gravityWells.set(config.id, { ...config });
  }

  updateGravityWell(id: string, updates: Partial<GravityWellConfig>): void {
    const well = this.gravityWells.get(id);
    if (well) {
      Object.assign(well, updates);
    }
  }

  removeGravityWell(id: string): void {
    this.gravityWells.delete(id);
  }

  getGravityWells(): GravityWellConfig[] {
    return Array.from(this.gravityWells.values());
  }

  // ============================================================================
  // Vortex Management
  // ============================================================================

  addVortex(config: VortexConfig): void {
    this.vortices.set(config.id, { ...config });
  }

  updateVortex(id: string, updates: Partial<VortexConfig>): void {
    const vortex = this.vortices.get(id);
    if (vortex) {
      Object.assign(vortex, updates);
    }
  }

  removeVortex(id: string): void {
    this.vortices.delete(id);
  }

  getVortices(): VortexConfig[] {
    return Array.from(this.vortices.values());
  }

  // ============================================================================
  // Lorenz Attractor Management
  // ============================================================================

  addLorenzAttractor(config: LorenzAttractorConfig): void {
    this.lorenzAttractors.set(config.id, { ...config });
  }

  updateLorenzAttractor(id: string, updates: Partial<LorenzAttractorConfig>): void {
    const attractor = this.lorenzAttractors.get(id);
    if (attractor) {
      Object.assign(attractor, updates);
    }
  }

  removeLorenzAttractor(id: string): void {
    this.lorenzAttractors.delete(id);
  }

  getLorenzAttractors(): LorenzAttractorConfig[] {
    return Array.from(this.lorenzAttractors.values());
  }

  // ============================================================================
  // Modulation Management
  // ============================================================================

  addModulation(mod: ParticleModulation): void {
    this.modulations.push({ ...mod });
  }

  removeModulation(id: string): void {
    const index = this.modulations.findIndex(m => m.id === id);
    if (index >= 0) {
      this.modulations.splice(index, 1);
    }
  }

  getModulations(): ParticleModulation[] {
    return [...this.modulations];
  }

  // ============================================================================
  // Boundary Mask
  // ============================================================================

  setBoundaryMask(mask: ImageData | null): void {
    this.boundaryMask = mask;
  }

  // ============================================================================
  // Audio Reactivity
  // ============================================================================

  setFeatureValue(param: string, value: number, emitterId?: string): void {
    const key = emitterId ? `${emitterId}:${param}` : `*:${param}`;
    this.featureOverrides.set(key, value);
  }

  private getFeatureValue(param: string, emitterId: string): number | undefined {
    // Check specific emitter first, then global
    return this.featureOverrides.get(`${emitterId}:${param}`)
        ?? this.featureOverrides.get(`*:${param}`);
  }

  // ============================================================================
  // Simulation
  // ============================================================================

  step(deltaTime: number = 1): void {
    // 1. Spawn new particles from emitters
    this.emitters.forEach((emitter, id) => {
      if (!emitter.enabled) return;

      // Get potentially audio-modified emission rate
      const baseRate = this.getFeatureValue('emissionRate', id) ?? emitter.emissionRate;
      const particlesToEmit = baseRate * deltaTime;

      // Accumulate fractional particles
      let accumulated = (this.emissionAccumulators.get(id) || 0) + particlesToEmit;

      while (accumulated >= 1 && this.particles.length < this.config.maxParticles) {
        this.spawnParticle(emitter);
        accumulated -= 1;
      }

      this.emissionAccumulators.set(id, accumulated);
    });

    // 2. Update each particle
    const windRadians = (this.config.windDirection * Math.PI) / 180;
    const windX = Math.cos(windRadians) * this.config.windStrength * 0.001;
    const windY = Math.sin(windRadians) * this.config.windStrength * 0.001;

    // Get potentially audio-modified global values
    const gravity = this.getFeatureValue('gravity', '*') ?? this.config.gravity;
    const windStrength = this.getFeatureValue('windStrength', '*') ?? this.config.windStrength;
    const actualWindX = windX * (windStrength / Math.max(1, this.config.windStrength));
    const actualWindY = windY * (windStrength / Math.max(1, this.config.windStrength));

    for (let i = this.particles.length - 1; i >= 0; i--) {
      const p = this.particles[i];

      // Store previous position for trails
      p.prevX = p.x;
      p.prevY = p.y;

      // Update trail history
      if (this.trailHistory.has(p.id)) {
        const trail = this.trailHistory.get(p.id)!;
        trail.unshift({ x: p.x, y: p.y });
        if (trail.length > 20) trail.pop();
      }

      // a. Apply global gravity
      p.vy += gravity * 0.001 * deltaTime;

      // b. Apply wind
      p.vx += actualWindX * deltaTime;
      p.vy += actualWindY * deltaTime;

      // c. Apply gravity wells
      this.gravityWells.forEach(well => {
        if (!well.enabled) return;

        const dx = well.x - p.x;
        const dy = well.y - p.y;
        const dist = Math.sqrt(dx * dx + dy * dy);

        if (dist < well.radius && dist > 0.001) {
          let force = well.strength * 0.0001;

          // Apply falloff
          switch (well.falloff) {
            case 'linear':
              force *= 1 - (dist / well.radius);
              break;
            case 'quadratic':
              force *= Math.pow(1 - (dist / well.radius), 2);
              break;
            case 'constant':
              // No falloff
              break;
          }

          // Normalize and apply force
          const nx = dx / dist;
          const ny = dy / dist;
          p.vx += nx * force * deltaTime;
          p.vy += ny * force * deltaTime;
        }
      });

      // d. Apply vortices
      this.vortices.forEach(vortex => {
        if (!vortex.enabled) return;

        const dx = vortex.x - p.x;
        const dy = vortex.y - p.y;
        const dist = Math.sqrt(dx * dx + dy * dy);

        if (dist < vortex.radius && dist > 0.001) {
          const influence = 1 - (dist / vortex.radius);
          const strength = vortex.strength * 0.0001 * influence;

          // Perpendicular force (tangential)
          const nx = dx / dist;
          const ny = dy / dist;
          const perpX = -ny;
          const perpY = nx;

          p.vx += perpX * strength * deltaTime;
          p.vy += perpY * strength * deltaTime;

          // Inward pull (spiral)
          const inward = vortex.inwardPull * 0.0001 * influence;
          p.vx += nx * inward * deltaTime;
          p.vy += ny * inward * deltaTime;
        }
      });

      // d2. Apply lorenz attractors (strange attractors for chaotic motion)
      this.lorenzAttractors.forEach(attractor => {
        if (!attractor.enabled) return;

        const dx = p.x - attractor.x;
        const dy = p.y - attractor.y;
        const dist = Math.sqrt(dx * dx + dy * dy);

        if (dist < attractor.radius && dist > 0.001) {
          const influence = 1 - (dist / attractor.radius);

          // Lorenz attractor equations (adapted for 2D)
          // We use particle's local position relative to attractor as x,y
          // and simulate z as a function of distance from center
          const sigma = attractor.sigma;
          const rho = attractor.rho;
          const beta = attractor.beta;

          // Simulate z-coordinate based on distance (creates 3D-like behavior in 2D)
          const pseudoZ = dist * 0.1;

          // Lorenz equations
          const ldx = sigma * (dy - dx);
          const ldy = dx * (rho - pseudoZ) - dy;

          // Apply force based on lorenz dynamics
          const strength = attractor.strength * 0.001 * influence;
          p.vx += ldx * strength * deltaTime;
          p.vy += ldy * strength * deltaTime;
        }
      });

      // e. Apply turbulence fields
      this.applyTurbulence(p, deltaTime);

      // f. Apply friction
      const frictionFactor = 1 - this.config.friction;
      p.vx *= frictionFactor;
      p.vy *= frictionFactor;

      // f2. Update rotation (for sprites)
      if (p.angularVelocity !== 0) {
        p.rotation += p.angularVelocity * deltaTime;
      }

      // f3. Align to velocity if emitter configured for it
      const emitter = this.emitters.get(p.emitterId);
      if (emitter?.sprite?.alignToVelocity && (p.vx !== 0 || p.vy !== 0)) {
        p.rotation = Math.atan2(p.vy, p.vx);
      }

      // f4. Update sprite animation frame
      if (emitter?.sprite?.isSheet && emitter.sprite.totalFrames > 1) {
        this.updateSpriteFrame(p, emitter.sprite, deltaTime);
      }

      // g. Update position
      p.x += p.vx * deltaTime;
      p.y += p.vy * deltaTime;

      // g. Check boundary collision
      if (this.boundaryMask && this.config.respectMaskBoundary) {
        this.handleBoundaryCollision(p);
      }

      // Simple canvas boundary handling
      this.handleCanvasBoundary(p);

      // h. Apply modulations based on age/lifetime ratio
      this.applyModulations(p);

      // j. Increment age
      p.age += deltaTime;

      // k. Remove if age > lifetime, trigger sub-emitters on death
      if (p.age > p.lifetime) {
        // Trigger sub-emitters for non-sub particles
        if (!p.isSubParticle) {
          this.triggerSubEmitters(p);
        }

        // Return particle to pool for reuse (if pool not full)
        if (this.particlePool.length < this.poolMaxSize) {
          this.particlePool.push(p);
        }

        this.particles.splice(i, 1);
        this.trailHistory.delete(p.id);
      }
    }

    // Particle-to-particle collision detection (after all positions updated)
    if (this.config.collision?.enabled && this.config.collision.particleCollision) {
      this.handleParticleCollisions();
    }

    // Floor/ceiling/wall collision
    if (this.config.collision?.enabled) {
      this.handleEnvironmentCollisions();
    }

    // Increment noise time for turbulence evolution
    this.noiseTime += deltaTime;
    this.frameCount++;
  }

  /**
   * Update sprite animation frame based on age and play mode
   */
  private updateSpriteFrame(p: Particle, sprite: SpriteConfig, _deltaTime: number): void {
    const totalFrames = sprite.totalFrames;
    const lifeRatio = p.age / p.lifetime;

    switch (sprite.playMode) {
      case 'loop': {
        // Calculate frame based on age and frame rate
        const framesElapsed = Math.floor(p.age * sprite.frameRate / 60); // Assuming 60fps base
        p.spriteIndex = framesElapsed % totalFrames;
        break;
      }
      case 'once': {
        // Play through once, stop at last frame
        const framesElapsed = Math.floor(p.age * sprite.frameRate / 60);
        p.spriteIndex = Math.min(framesElapsed, totalFrames - 1);
        break;
      }
      case 'pingpong': {
        // Play forward then backward
        const framesElapsed = Math.floor(p.age * sprite.frameRate / 60);
        const cycle = Math.floor(framesElapsed / (totalFrames - 1));
        const frameInCycle = framesElapsed % (totalFrames - 1);
        p.spriteIndex = cycle % 2 === 0 ? frameInCycle : (totalFrames - 1 - frameInCycle);
        break;
      }
      case 'random': {
        // Frame already set randomly at spawn, but can also change over time
        if (this.rng.bool(0.1)) { // 10% chance per frame to change
          p.spriteIndex = this.rng.int(0, totalFrames - 1);
        }
        break;
      }
    }
  }

  /**
   * Handle particle-to-particle collisions using spatial hashing
   */
  private handleParticleCollisions(): void {
    const collision = this.config.collision;
    if (!collision || !collision.particleCollision) return;

    // Build spatial hash grid
    this.collisionGrid.clear();
    const cellSize = this.collisionGridCellSize / 1000; // Normalize to 0-1 space

    for (const p of this.particles) {
      const cellX = Math.floor(p.x / cellSize);
      const cellY = Math.floor(p.y / cellSize);
      const key = `${cellX},${cellY}`;
      if (!this.collisionGrid.has(key)) {
        this.collisionGrid.set(key, []);
      }
      this.collisionGrid.get(key)!.push(p);
    }

    // Check collisions within neighboring cells
    const checked = new Set<string>();

    for (const p of this.particles) {
      const cellX = Math.floor(p.x / cellSize);
      const cellY = Math.floor(p.y / cellSize);

      // Check this cell and 8 neighbors
      for (let dx = -1; dx <= 1; dx++) {
        for (let dy = -1; dy <= 1; dy++) {
          const key = `${cellX + dx},${cellY + dy}`;
          const cell = this.collisionGrid.get(key);
          if (!cell) continue;

          for (const other of cell) {
            if (other.id <= p.id) continue; // Only check each pair once

            const pairKey = `${Math.min(p.id, other.id)}-${Math.max(p.id, other.id)}`;
            if (checked.has(pairKey)) continue;
            checked.add(pairKey);

            // Calculate collision distance
            const radiusP = (p.size / 1000) * collision.particleCollisionRadius;
            const radiusO = (other.size / 1000) * collision.particleCollisionRadius;
            const minDist = radiusP + radiusO;

            const dx2 = other.x - p.x;
            const dy2 = other.y - p.y;
            const distSq = dx2 * dx2 + dy2 * dy2;

            if (distSq < minDist * minDist && distSq > 0.000001) {
              // Collision detected!
              const dist = Math.sqrt(distSq);
              const nx = dx2 / dist;
              const ny = dy2 / dist;

              // Response based on collision type
              switch (collision.particleCollisionResponse) {
                case 'bounce': {
                  // Elastic collision with damping
                  const dvx = p.vx - other.vx;
                  const dvy = p.vy - other.vy;
                  const dvDotN = dvx * nx + dvy * ny;

                  if (dvDotN > 0) { // Only if moving towards each other
                    const damping = collision.particleCollisionDamping;
                    p.vx -= dvDotN * nx * damping;
                    p.vy -= dvDotN * ny * damping;
                    other.vx += dvDotN * nx * damping;
                    other.vy += dvDotN * ny * damping;

                    // Separate particles to prevent overlap
                    const overlap = minDist - dist;
                    p.x -= nx * overlap * 0.5;
                    p.y -= ny * overlap * 0.5;
                    other.x += nx * overlap * 0.5;
                    other.y += ny * overlap * 0.5;
                  }
                  break;
                }
                case 'absorb': {
                  // Smaller particle dies, larger grows
                  if (p.size > other.size) {
                    p.size += other.size * 0.1;
                    other.age = other.lifetime + 1; // Kill
                  } else {
                    other.size += p.size * 0.1;
                    p.age = p.lifetime + 1; // Kill
                  }
                  break;
                }
                case 'explode': {
                  // Both particles die (sub-emitters will trigger)
                  p.age = p.lifetime + 1;
                  other.age = other.lifetime + 1;
                  break;
                }
              }

              p.collisionCount++;
              other.collisionCount++;
            }
          }
        }
      }
    }
  }

  /**
   * Handle floor, ceiling, and wall collisions
   */
  private handleEnvironmentCollisions(): void {
    const collision = this.config.collision;
    if (!collision?.enabled) return;

    const bounciness = collision.bounciness;
    const friction = collision.friction;

    for (const p of this.particles) {
      // Floor collision
      if (collision.floorEnabled && p.y > collision.floorY) {
        p.y = collision.floorY;
        p.vy = -p.vy * bounciness;
        p.vx *= (1 - friction);
        p.collisionCount++;
      }

      // Ceiling collision
      if (collision.ceilingEnabled && p.y < collision.ceilingY) {
        p.y = collision.ceilingY;
        p.vy = -p.vy * bounciness;
        p.vx *= (1 - friction);
        p.collisionCount++;
      }

      // Wall collisions
      if (collision.wallsEnabled) {
        if (p.x < 0) {
          p.x = 0;
          p.vx = -p.vx * bounciness;
          p.vy *= (1 - friction);
          p.collisionCount++;
        }
        if (p.x > 1) {
          p.x = 1;
          p.vx = -p.vx * bounciness;
          p.vy *= (1 - friction);
          p.collisionCount++;
        }
      }
    }
  }

  private spawnParticle(emitter: EmitterConfig): void {
    if (this.particles.length >= this.config.maxParticles) return;

    // Calculate spawn position based on emitter shape
    const spawnPos = this.getEmitterSpawnPosition(emitter);

    // Use spline-provided direction if available, otherwise use emitter direction
    const baseDirection = spawnPos.direction !== undefined ? spawnPos.direction : emitter.direction;

    // Calculate emission direction with spread (using seeded RNG)
    const spreadRad = (emitter.spread * Math.PI) / 180;
    const baseRad = (baseDirection * Math.PI) / 180;
    const angle = baseRad + (this.rng.next() - 0.5) * spreadRad;

    // Calculate speed with variance (using seeded RNG)
    const speed = this.rng.variance(emitter.speed, emitter.speedVariance);
    const speedNormalized = speed * 0.001;

    // Calculate size with variance (using seeded RNG)
    const size = Math.max(1, this.rng.variance(emitter.size, emitter.sizeVariance));

    // Calculate lifetime with variance (using seeded RNG)
    const lifetime = Math.max(1, this.rng.variance(emitter.particleLifetime, emitter.lifetimeVariance));

    // Calculate initial rotation and angular velocity
    let rotation = 0;
    let angularVelocity = 0;
    const sprite = emitter.sprite;
    if (sprite && sprite.rotationEnabled) {
      rotation = this.rng.angle(); // Random initial rotation (seeded)
      const rotSpeed = sprite.rotationSpeed * (Math.PI / 180); // Convert to radians
      const rotVariance = sprite.rotationSpeedVariance * (Math.PI / 180);
      angularVelocity = this.rng.variance(rotSpeed, rotVariance);
    }

    // Align to velocity if configured
    if (sprite && sprite.alignToVelocity) {
      rotation = angle;
    }

    // Calculate sprite frame for animated sprites (using seeded RNG)
    let spriteIndex = 0;
    if (sprite && sprite.isSheet && sprite.playMode === 'random') {
      spriteIndex = this.rng.int(0, sprite.totalFrames - 1);
    }

    // Try to reuse a particle from the pool (20-30% allocation reduction)
    let particle: Particle;
    if (this.particlePool.length > 0) {
      particle = this.particlePool.pop()!;
      // Reset all properties
      particle.id = this.nextParticleId++;
      particle.x = spawnPos.x;
      particle.y = spawnPos.y;
      particle.prevX = spawnPos.x;
      particle.prevY = spawnPos.y;
      particle.vx = Math.cos(angle) * speedNormalized;
      particle.vy = Math.sin(angle) * speedNormalized;
      particle.age = 0;
      particle.lifetime = lifetime;
      particle.size = size;
      particle.baseSize = size;
      particle.color[0] = emitter.color[0];
      particle.color[1] = emitter.color[1];
      particle.color[2] = emitter.color[2];
      particle.color[3] = 255;
      particle.baseColor[0] = emitter.color[0];
      particle.baseColor[1] = emitter.color[1];
      particle.baseColor[2] = emitter.color[2];
      particle.baseColor[3] = 255;
      particle.emitterId = emitter.id;
      particle.isSubParticle = false;
      particle.rotation = rotation;
      particle.angularVelocity = angularVelocity;
      particle.spriteIndex = spriteIndex;
      particle.collisionCount = 0;
    } else {
      // Create new particle
      particle = {
        id: this.nextParticleId++,
        x: spawnPos.x,
        y: spawnPos.y,
        prevX: spawnPos.x,
        prevY: spawnPos.y,
        vx: Math.cos(angle) * speedNormalized,
        vy: Math.sin(angle) * speedNormalized,
        age: 0,
        lifetime,
        size,
        baseSize: size,
        color: [...emitter.color, 255] as [number, number, number, number],
        baseColor: [...emitter.color, 255] as [number, number, number, number],
        emitterId: emitter.id,
        isSubParticle: false,
        rotation,
        angularVelocity,
        spriteIndex,
        collisionCount: 0
      };
    }

    this.particles.push(particle);
    this.trailHistory.set(particle.id, [{ x: particle.x, y: particle.y }]);
  }

  /**
   * Calculate spawn position based on emitter shape
   * DETERMINISM: Uses seeded RNG (this.rng) for all randomness
   * Returns position and optionally a direction override for spline emission
   */
  private getEmitterSpawnPosition(emitter: EmitterConfig): { x: number; y: number; direction?: number } {
    const shape = emitter.shape || 'point';

    switch (shape) {
      case 'point':
        return { x: emitter.x, y: emitter.y };

      case 'line': {
        // Line from emitter position extending in direction
        const t = this.rng.next();
        const halfWidth = emitter.shapeWidth / 2;
        const dirRad = (emitter.direction * Math.PI) / 180;
        // Perpendicular to direction
        const perpX = -Math.sin(dirRad);
        const perpY = Math.cos(dirRad);
        return {
          x: emitter.x + perpX * (t - 0.5) * halfWidth * 2,
          y: emitter.y + perpY * (t - 0.5) * halfWidth * 2
        };
      }

      case 'circle': {
        const radius = emitter.shapeRadius;
        if (emitter.emitFromEdge) {
          // Emit from edge only
          const angle = this.rng.angle();
          return {
            x: emitter.x + Math.cos(angle) * radius,
            y: emitter.y + Math.sin(angle) * radius
          };
        } else {
          // Emit from filled circle (uniform distribution)
          const angle = this.rng.angle();
          const r = radius * Math.sqrt(this.rng.next()); // sqrt for uniform area distribution
          return {
            x: emitter.x + Math.cos(angle) * r,
            y: emitter.y + Math.sin(angle) * r
          };
        }
      }

      case 'ring': {
        // Donut shape - emit between inner and outer radius
        const innerR = emitter.shapeInnerRadius;
        const outerR = emitter.shapeRadius;
        const angle = this.rng.angle();
        // Uniform distribution in ring area
        const r = Math.sqrt(this.rng.next() * (outerR * outerR - innerR * innerR) + innerR * innerR);
        return {
          x: emitter.x + Math.cos(angle) * r,
          y: emitter.y + Math.sin(angle) * r
        };
      }

      case 'box': {
        const halfW = emitter.shapeWidth / 2;
        const halfH = emitter.shapeHeight / 2;
        if (emitter.emitFromEdge) {
          // Emit from edges only
          const perimeter = 2 * (emitter.shapeWidth + emitter.shapeHeight);
          const t = this.rng.next() * perimeter;
          if (t < emitter.shapeWidth) {
            // Top edge
            return { x: emitter.x - halfW + t, y: emitter.y - halfH };
          } else if (t < emitter.shapeWidth + emitter.shapeHeight) {
            // Right edge
            return { x: emitter.x + halfW, y: emitter.y - halfH + (t - emitter.shapeWidth) };
          } else if (t < 2 * emitter.shapeWidth + emitter.shapeHeight) {
            // Bottom edge
            return { x: emitter.x + halfW - (t - emitter.shapeWidth - emitter.shapeHeight), y: emitter.y + halfH };
          } else {
            // Left edge
            return { x: emitter.x - halfW, y: emitter.y + halfH - (t - 2 * emitter.shapeWidth - emitter.shapeHeight) };
          }
        } else {
          // Emit from filled box
          return {
            x: emitter.x + (this.rng.next() - 0.5) * emitter.shapeWidth,
            y: emitter.y + (this.rng.next() - 0.5) * emitter.shapeHeight
          };
        }
      }

      case 'sphere': {
        // 3D sphere projected to 2D - use rejection sampling for uniform distribution
        const radius = emitter.shapeRadius;
        if (emitter.emitFromEdge) {
          // Surface of sphere
          const theta = this.rng.angle();
          const phi = Math.acos(2 * this.rng.next() - 1);
          return {
            x: emitter.x + Math.sin(phi) * Math.cos(theta) * radius,
            y: emitter.y + Math.sin(phi) * Math.sin(theta) * radius
            // z would be: Math.cos(phi) * radius
          };
        } else {
          // Volume of sphere - use cube rejection
          let x, y, z;
          do {
            x = (this.rng.next() - 0.5) * 2;
            y = (this.rng.next() - 0.5) * 2;
            z = (this.rng.next() - 0.5) * 2;
          } while (x * x + y * y + z * z > 1);
          return {
            x: emitter.x + x * radius,
            y: emitter.y + y * radius
          };
        }
      }

      case 'spline': {
        // Emit along a spline path
        return this.getSplineEmitPosition(emitter);
      }

      case 'depth-map': {
        // Emit from depth map values
        return this.getDepthMapEmitPosition(emitter);
      }

      case 'mask': {
        // Emit from mask/matte
        return this.getMaskEmitPosition(emitter);
      }

      default:
        return { x: emitter.x, y: emitter.y };
    }
  }

  /**
   * Get emission position along a spline path
   * Returns position and optionally modifies emission direction
   * DETERMINISM: Uses seeded RNG (this.rng) for random positions
   */
  private getSplineEmitPosition(emitter: EmitterConfig): { x: number; y: number; direction?: number } {
    const splinePath = emitter.splinePath;

    // Fall back to point emission if no spline path configured or no provider
    if (!splinePath || !this.splineProvider) {
      return { x: emitter.x, y: emitter.y };
    }

    // Calculate t parameter based on emit mode
    let t: number;

    switch (splinePath.emitMode) {
      case 'start':
        // Emit near the start of the path
        t = splinePath.parameter * this.rng.next() * 0.1; // 0-10% of path
        break;

      case 'end':
        // Emit near the end of the path
        t = 1 - (splinePath.parameter * this.rng.next() * 0.1); // 90-100% of path
        break;

      case 'random':
        // Emit at random position along path
        t = this.rng.next();
        break;

      case 'uniform':
        // Emit at evenly spaced intervals
        // Uses parameter as spacing interval (0-1 range)
        const interval = Math.max(0.01, splinePath.parameter);
        const numSlots = Math.ceil(1 / interval);
        const slot = this.rng.int(0, numSlots - 1);
        t = slot * interval;
        break;

      case 'sequential':
        // Emit sequentially along path, advancing each emission
        // Uses parameter as speed (how much t advances per emission)
        const currentT = this.sequentialEmitT.get(emitter.id) ?? 0;
        t = currentT;
        // Advance for next emission
        const speed = Math.max(0.001, splinePath.parameter);
        let nextT = currentT + speed;
        // Wrap around
        if (nextT > 1) nextT = nextT - 1;
        this.sequentialEmitT.set(emitter.id, nextT);
        break;

      default:
        t = this.rng.next();
    }

    // Clamp t to valid range
    t = Math.max(0, Math.min(1, t));

    // Query spline for position and tangent
    const result = this.splineProvider(splinePath.layerId, t, this.currentFrame);

    if (!result) {
      // Spline not found, fall back to point emission
      return { x: emitter.x, y: emitter.y };
    }

    // Base position from spline
    let x = result.point.x;
    let y = result.point.y;

    // Apply perpendicular offset if specified
    if (splinePath.offset !== 0) {
      // Calculate perpendicular direction from tangent
      const tangentLength = Math.sqrt(result.tangent.x ** 2 + result.tangent.y ** 2);
      if (tangentLength > 0.0001) {
        const perpX = -result.tangent.y / tangentLength;
        const perpY = result.tangent.x / tangentLength;
        x += perpX * splinePath.offset;
        y += perpY * splinePath.offset;
      }
    }

    // Calculate emission direction if aligned to path
    let direction: number | undefined;
    if (splinePath.alignToPath) {
      // Calculate angle from tangent
      const tangentAngle = Math.atan2(result.tangent.y, result.tangent.x) * (180 / Math.PI);

      if (splinePath.bidirectional && this.rng.bool(0.5)) {
        // Emit in opposite direction
        direction = tangentAngle + 180;
      } else {
        direction = tangentAngle;
      }

      // Add perpendicular offset (emit outward from path)
      direction += 90;
    }

    return { x, y, direction };
  }

  /**
   * Get emission position from depth map
   * Emits particles from positions where depth values fall within the configured range
   * Uses cached emission points for performance
   */
  private getDepthMapEmitPosition(emitter: EmitterConfig): { x: number; y: number } {
    const config = (emitter as any).depthMapEmission;

    // Fall back to point emission if no depth map config
    if (!config) {
      return { x: emitter.x, y: emitter.y };
    }

    // Check for cached emission points
    const cacheKey = `depth_${config.sourceLayerId}`;
    let emissionPoints = this.imageEmissionCache.get(cacheKey);

    // If no cache or cache is stale, regenerate points
    if (!emissionPoints) {
      emissionPoints = this.sampleDepthMapEmissionPoints(config);
      this.imageEmissionCache.set(cacheKey, emissionPoints);
    }

    // If no valid emission points, fall back to emitter position
    if (emissionPoints.length === 0) {
      return { x: emitter.x, y: emitter.y };
    }

    // Select a random emission point
    const idx = this.rng.int(0, emissionPoints.length - 1);
    const point = emissionPoints[idx];

    return { x: point.x + emitter.x, y: point.y + emitter.y };
  }

  /**
   * Sample valid emission points from a depth map
   */
  private sampleDepthMapEmissionPoints(config: any): Array<{ x: number; y: number; depth: number }> {
    const points: Array<{ x: number; y: number; depth: number }> = [];

    // Try to get the depth map image data from the layer provider
    if (!this.depthMapProvider) {
      // No provider available - use a grid pattern as fallback
      const gridSize = 20;
      for (let y = 0; y < gridSize; y++) {
        for (let x = 0; x < gridSize; x++) {
          const depth = (x + y) / (gridSize * 2); // Gradient fallback
          if (depth >= config.depthMin && depth <= config.depthMax) {
            points.push({
              x: (x / gridSize - 0.5) * 500,
              y: (y / gridSize - 0.5) * 500,
              depth
            });
          }
        }
      }
      return points;
    }

    // Get actual depth map data
    const depthData = this.depthMapProvider(config.sourceLayerId, this.currentFrame);
    if (!depthData) {
      return points;
    }

    // Sample the depth map
    const sampleRate = Math.max(1, Math.floor(1 / config.density));
    for (let y = 0; y < depthData.height; y += sampleRate) {
      for (let x = 0; x < depthData.width; x += sampleRate) {
        const idx = (y * depthData.width + x) * 4;
        let depthValue = depthData.data[idx] / 255; // Normalize to 0-1

        // Handle depth mode (white=near or black=near)
        if (config.depthMode === 'near-black') {
          depthValue = 1 - depthValue;
        }

        // Check if depth is within emission range
        if (depthValue >= config.depthMin && depthValue <= config.depthMax) {
          points.push({
            x: x - depthData.width / 2,
            y: y - depthData.height / 2,
            depth: depthValue
          });
        }
      }
    }

    return points;
  }

  /**
   * Get emission position from mask/matte
   * Emits particles from bright areas of the mask
   */
  private getMaskEmitPosition(emitter: EmitterConfig): { x: number; y: number } {
    const config = (emitter as any).maskEmission;

    // Fall back to point emission if no mask config
    if (!config) {
      return { x: emitter.x, y: emitter.y };
    }

    // Check for cached emission points
    const cacheKey = `mask_${config.sourceLayerId}_${config.channel}_${config.threshold}`;
    let emissionPoints = this.imageEmissionCache.get(cacheKey);

    // If no cache, regenerate points
    if (!emissionPoints) {
      emissionPoints = this.sampleMaskEmissionPoints(config);
      this.imageEmissionCache.set(cacheKey, emissionPoints);
    }

    // If no valid emission points, fall back to emitter position
    if (emissionPoints.length === 0) {
      return { x: emitter.x, y: emitter.y };
    }

    // Select a random emission point
    const idx = this.rng.int(0, emissionPoints.length - 1);
    const point = emissionPoints[idx];

    return { x: point.x + emitter.x, y: point.y + emitter.y };
  }

  /**
   * Sample valid emission points from a mask
   */
  private sampleMaskEmissionPoints(config: any): Array<{ x: number; y: number }> {
    const points: Array<{ x: number; y: number }> = [];

    // Try to get the mask image data from the layer provider
    if (!this.maskProvider) {
      // No provider available - use emitter area as fallback
      return points;
    }

    // Get actual mask data
    const maskData = this.maskProvider(config.sourceLayerId, this.currentFrame);
    if (!maskData) {
      return points;
    }

    // Determine which channel to sample
    const channelIdx = config.channel === 'alpha' ? 3 :
                       config.channel === 'red' ? 0 :
                       config.channel === 'green' ? 1 :
                       config.channel === 'blue' ? 2 : -1; // luminance

    const sampleRate = Math.max(1, config.sampleRate || 1);

    for (let y = 0; y < maskData.height; y += sampleRate) {
      for (let x = 0; x < maskData.width; x += sampleRate) {
        const idx = (y * maskData.width + x) * 4;

        let value: number;
        if (channelIdx === -1) {
          // Luminance: weighted sum of RGB
          value = (maskData.data[idx] * 0.299 +
                   maskData.data[idx + 1] * 0.587 +
                   maskData.data[idx + 2] * 0.114) / 255;
        } else {
          value = maskData.data[idx + channelIdx] / 255;
        }

        // Handle inversion
        if (config.invert) {
          value = 1 - value;
        }

        // Check threshold
        if (value >= config.threshold) {
          // Add some randomness based on density
          if (this.rng.next() < config.density) {
            points.push({
              x: x - maskData.width / 2,
              y: y - maskData.height / 2
            });
          }
        }
      }
    }

    return points;
  }

  // Cache for image-based emission points
  private imageEmissionCache: Map<string, Array<{ x: number; y: number; depth?: number }>> = new Map();

  // Provider functions for image data (set by the engine)
  private depthMapProvider?: (layerId: string, frame: number) => ImageData | null;
  private maskProvider?: (layerId: string, frame: number) => ImageData | null;

  /**
   * Set the depth map provider function
   */
  setDepthMapProvider(provider: (layerId: string, frame: number) => ImageData | null): void {
    this.depthMapProvider = provider;
  }

  /**
   * Set the mask provider function
   */
  setMaskProvider(provider: (layerId: string, frame: number) => ImageData | null): void {
    this.maskProvider = provider;
  }

  /**
   * Clear the image emission cache (call when source layers change)
   */
  clearEmissionCache(): void {
    this.imageEmissionCache.clear();
  }

  private handleBoundaryCollision(p: Particle): void {
    if (!this.boundaryMask) return;

    const px = Math.floor(p.x * this.boundaryMask.width);
    const py = Math.floor(p.y * this.boundaryMask.height);

    if (px < 0 || px >= this.boundaryMask.width || py < 0 || py >= this.boundaryMask.height) {
      return;
    }

    const idx = (py * this.boundaryMask.width + px) * 4;
    const maskValue = this.boundaryMask.data[idx]; // Use red channel

    // If mask is black (0), particle is in restricted area
    if (maskValue < 128) {
      switch (this.config.boundaryBehavior) {
        case 'bounce':
          // Simple bounce - reverse velocity
          p.vx *= -0.8;
          p.vy *= -0.8;
          // Move back
          p.x = p.prevX;
          p.y = p.prevY;
          break;
        case 'kill':
          p.age = p.lifetime + 1;
          break;
        case 'wrap':
          // Find valid position (simplified) - DETERMINISM: use seeded RNG
          p.x = this.rng.next();
          p.y = this.rng.next();
          break;
      }
    }
  }

  private handleCanvasBoundary(p: Particle): void {
    switch (this.config.boundaryBehavior) {
      case 'bounce':
        if (p.x < 0) { p.x = 0; p.vx *= -0.8; }
        if (p.x > 1) { p.x = 1; p.vx *= -0.8; }
        if (p.y < 0) { p.y = 0; p.vy *= -0.8; }
        if (p.y > 1) { p.y = 1; p.vy *= -0.8; }
        break;
      case 'kill':
        if (p.x < -0.1 || p.x > 1.1 || p.y < -0.1 || p.y > 1.1) {
          p.age = p.lifetime + 1;
        }
        break;
      case 'wrap':
        if (p.x < 0) p.x += 1;
        if (p.x > 1) p.x -= 1;
        if (p.y < 0) p.y += 1;
        if (p.y > 1) p.y -= 1;
        break;
    }
  }

  private applyModulations(p: Particle): void {
    const lifeRatio = p.age / p.lifetime;

    for (const mod of this.modulations) {
      // Check if modulation applies to this particle's emitter
      if (mod.emitterId !== '*' && mod.emitterId !== p.emitterId) continue;

      // Get eased value
      const easingKey = mod.easing as keyof typeof EASING_PRESETS;
      const easing = EASING_PRESETS[easingKey] || EASING_PRESETS.linear;
      const easedRatio = applyEasing(lifeRatio, easing);
      const value = mod.startValue + (mod.endValue - mod.startValue) * easedRatio;

      switch (mod.property) {
        case 'size':
          p.size = p.baseSize * value;
          break;
        case 'speed':
          // Modulate current velocity magnitude
          const currentSpeed = Math.sqrt(p.vx * p.vx + p.vy * p.vy);
          if (currentSpeed > 0.0001) {
            const scale = value / Math.max(0.0001, currentSpeed * 1000);
            p.vx *= scale;
            p.vy *= scale;
          }
          break;
        case 'opacity':
          p.color[3] = Math.max(0, Math.min(255, p.baseColor[3] * value));
          break;
        case 'colorR':
          p.color[0] = Math.max(0, Math.min(255, value * 255));
          break;
        case 'colorG':
          p.color[1] = Math.max(0, Math.min(255, value * 255));
          break;
        case 'colorB':
          p.color[2] = Math.max(0, Math.min(255, value * 255));
          break;
      }
    }
  }

  // ============================================================================
  // Turbulence
  // ============================================================================

  private applyTurbulence(p: Particle, deltaTime: number): void {
    const turbFields = this.config.turbulenceFields || [];
    for (const turb of turbFields) {
      if (!turb.enabled) continue;
      const nx = p.x * turb.scale * 1000;  // Scale up for noise variation
      const ny = p.y * turb.scale * 1000;
      const nt = this.noiseTime * turb.evolutionSpeed;
      const angle = this.noise2D(nx + nt, ny + nt) * Math.PI * 2;
      const force = turb.strength * 0.00001;
      p.vx += Math.cos(angle) * force * deltaTime;
      p.vy += Math.sin(angle) * force * deltaTime;
    }
  }

  addTurbulence(config: TurbulenceConfig): void {
    if (!this.config.turbulenceFields) this.config.turbulenceFields = [];
    this.config.turbulenceFields.push(config);
  }

  updateTurbulence(id: string, updates: Partial<TurbulenceConfig>): void {
    const turb = this.config.turbulenceFields?.find(t => t.id === id);
    if (turb) Object.assign(turb, updates);
  }

  removeTurbulence(id: string): void {
    if (this.config.turbulenceFields) {
      this.config.turbulenceFields = this.config.turbulenceFields.filter(t => t.id !== id);
    }
  }

  getTurbulenceFields(): TurbulenceConfig[] {
    return this.config.turbulenceFields || [];
  }

  // ============================================================================
  // Sub-Emitters
  // ============================================================================

  /**
   * Trigger sub-emitters when a particle dies
   * DETERMINISM: Uses seeded RNG (this.rng) for all randomness
   */
  private triggerSubEmitters(deadParticle: Particle): void {
    const subEmitters = this.config.subEmitters || [];
    for (const sub of subEmitters) {
      if (!sub.enabled) continue;
      if (sub.parentEmitterId !== '*' && sub.parentEmitterId !== deadParticle.emitterId) continue;

      for (let i = 0; i < sub.spawnCount; i++) {
        const angle = (this.rng.next() - 0.5) * sub.spread * Math.PI / 180;
        const baseAngle = Math.atan2(deadParticle.vy, deadParticle.vx);
        const emitAngle = baseAngle + angle;
        const inheritedSpeed = Math.sqrt(deadParticle.vx ** 2 + deadParticle.vy ** 2) * sub.inheritVelocity;
        const totalSpeed = sub.speed * 0.001 + inheritedSpeed;

        const particle: Particle = {
          id: this.nextParticleId++,
          x: deadParticle.x,
          y: deadParticle.y,
          prevX: deadParticle.x,
          prevY: deadParticle.y,
          vx: Math.cos(emitAngle) * totalSpeed + deadParticle.vx * sub.inheritVelocity,
          vy: Math.sin(emitAngle) * totalSpeed + deadParticle.vy * sub.inheritVelocity,
          age: 0,
          lifetime: sub.lifetime * (1 + (this.rng.next() - 0.5) * 0.2),
          size: sub.size * (1 + (this.rng.next() - 0.5) * sub.sizeVariance / sub.size),
          baseSize: sub.size,
          color: [...sub.color, 255] as [number, number, number, number],
          baseColor: [...sub.color, 255] as [number, number, number, number],
          emitterId: sub.id,
          isSubParticle: true,
          rotation: deadParticle.rotation, // Inherit parent rotation
          angularVelocity: 0,
          spriteIndex: 0,
          collisionCount: 0
        };

        this.particles.push(particle);
        this.trailHistory.set(particle.id, [{ x: particle.x, y: particle.y }]);
      }
    }
  }

  addSubEmitter(config: SubEmitterConfig): void {
    if (!this.config.subEmitters) this.config.subEmitters = [];
    this.config.subEmitters.push(config);
  }

  updateSubEmitter(id: string, updates: Partial<SubEmitterConfig>): void {
    const sub = this.config.subEmitters?.find(s => s.id === id);
    if (sub) Object.assign(sub, updates);
  }

  removeSubEmitter(id: string): void {
    if (this.config.subEmitters) {
      this.config.subEmitters = this.config.subEmitters.filter(s => s.id !== id);
    }
  }

  getSubEmitters(): SubEmitterConfig[] {
    return this.config.subEmitters || [];
  }

  // ============================================================================
  // Burst on Beat
  // ============================================================================

  triggerBurst(emitterId: string, count?: number): void {
    const emitter = this.emitters.get(emitterId);
    if (!emitter || !emitter.enabled) return;
    const burstCount = count ?? emitter.burstCount ?? 20;
    for (let i = 0; i < burstCount; i++) {
      this.spawnParticle(emitter);
    }
  }

  triggerAllBursts(): void {
    for (const emitter of this.emitters.values()) {
      if (emitter.burstOnBeat && emitter.enabled) {
        this.triggerBurst(emitter.id);
      }
    }
  }

  // ============================================================================
  // Particle Connections - Spatial Grid
  // ============================================================================

  private buildSpatialGrid(): SpatialGrid {
    const cellSize = this.renderOptions.connections?.maxDistance || 100;
    const cells = new Map<string, Particle[]>();
    for (const p of this.particles) {
      const cellX = Math.floor(p.x * 1000 / cellSize);  // Scale normalized coords
      const cellY = Math.floor(p.y * 1000 / cellSize);
      const key = `${cellX},${cellY}`;
      if (!cells.has(key)) cells.set(key, []);
      cells.get(key)!.push(p);
    }
    return { cellSize, cells };
  }

  private getNeighborParticles(p: Particle, grid: SpatialGrid): Particle[] {
    const cellX = Math.floor(p.x * 1000 / grid.cellSize);
    const cellY = Math.floor(p.y * 1000 / grid.cellSize);
    const neighbors: Particle[] = [];
    for (let dx = -1; dx <= 1; dx++) {
      for (let dy = -1; dy <= 1; dy++) {
        const key = `${cellX + dx},${cellY + dy}`;
        const cell = grid.cells.get(key);
        if (cell) neighbors.push(...cell);
      }
    }
    return neighbors;
  }

  private renderConnections(
    ctx: CanvasRenderingContext2D | OffscreenCanvasRenderingContext2D,
    width: number,
    height: number
  ): void {
    const config = this.renderOptions.connections;
    if (!config?.enabled || this.particles.length < 2) return;

    const grid = this.buildSpatialGrid();
    const maxDist = config.maxDistance / 1000;  // Normalize to 0-1
    const maxDistSq = maxDist * maxDist;

    ctx.lineWidth = config.lineWidth;

    for (const p of this.particles) {
      const neighbors = this.getNeighborParticles(p, grid);
      let connectionCount = 0;

      for (const other of neighbors) {
        if (other.id <= p.id) continue;  // Only draw each connection once
        if (connectionCount >= config.maxConnections) break;

        const dx = other.x - p.x;
        const dy = other.y - p.y;
        const distSq = dx * dx + dy * dy;

        if (distSq < maxDistSq) {
          const dist = Math.sqrt(distSq);
          let opacity = config.lineOpacity;
          if (config.fadeByDistance) {
            opacity *= 1 - (dist / maxDist);
          }

          const r = Math.round((p.color[0] + other.color[0]) / 2);
          const g = Math.round((p.color[1] + other.color[1]) / 2);
          const b = Math.round((p.color[2] + other.color[2]) / 2);

          ctx.strokeStyle = `rgba(${r},${g},${b},${opacity})`;
          ctx.beginPath();
          ctx.moveTo(p.x * width, p.y * height);
          ctx.lineTo(other.x * width, other.y * height);
          ctx.stroke();

          connectionCount++;
        }
      }
    }
  }

  reset(): void {
    this.particles = [];
    this.particlePool = []; // Clear pool to free memory
    this.frameCount = 0;
    this.trailHistory.clear();
    this.emissionAccumulators.forEach((_, key) => {
      this.emissionAccumulators.set(key, 0);
    });
    this.nextParticleId = 0;
    this.sequentialEmitT.clear();
    this.currentFrame = 0;
  }

  /**
   * Get particle pool statistics for debugging
   */
  getPoolStats(): { poolSize: number; maxPoolSize: number; activeParticles: number } {
    return {
      poolSize: this.particlePool.length,
      maxPoolSize: this.poolMaxSize,
      activeParticles: this.particles.length
    };
  }

  /**
   * Clear the particle pool to free memory
   * Call this when memory pressure is high
   */
  clearPool(): void {
    this.particlePool = [];
  }

  /**
   * Restore particles from serialized state (for checkpoint restoration)
   * DETERMINISM: Restores exact particle positions for scrub-safe simulation
   *
   * @param particleStates - Array of serialized particle states from a checkpoint
   * @param frameCount - The frame number being restored to
   */
  restoreParticles(
    particleStates: readonly {
      readonly id: number;
      readonly x: number;
      readonly y: number;
      readonly vx: number;
      readonly vy: number;
      readonly age: number;
      readonly lifetime: number;
      readonly size: number;
      readonly color: readonly [number, number, number, number];
      readonly rotation: number;
      readonly emitterId: string;
    }[],
    frameCount: number
  ): void {
    // Clear existing particles
    this.particles = [];
    this.trailHistory.clear();

    // Track highest ID for next particle generation
    let maxId = 0;

    // Restore each particle
    for (const state of particleStates) {
      const particle: Particle = {
        id: state.id,
        x: state.x,
        y: state.y,
        prevX: state.x, // Previous position set to current (no trail initially)
        prevY: state.y,
        vx: state.vx,
        vy: state.vy,
        age: state.age,
        lifetime: state.lifetime,
        size: state.size,
        baseSize: state.size, // Base size set to current
        color: [...state.color] as [number, number, number, number],
        baseColor: [...state.color] as [number, number, number, number],
        emitterId: state.emitterId,
        isSubParticle: false,
        rotation: state.rotation,
        angularVelocity: 0, // Default angular velocity
        spriteIndex: 0,
        collisionCount: 0, // Reset collision count on restore
      };

      this.particles.push(particle);
      maxId = Math.max(maxId, state.id);
    }

    // Set next particle ID to continue from highest restored ID
    this.nextParticleId = maxId + 1;
    this.frameCount = frameCount;
  }

  warmup(): void {
    for (let i = 0; i < this.config.warmupPeriod; i++) {
      this.step(1);
    }
  }

  getParticles(): readonly Particle[] {
    return this.particles;
  }

  getParticleCount(): number {
    return this.particles.length;
  }

  getConfig(): ParticleSystemConfig {
    return { ...this.config };
  }

  setConfig(updates: Partial<ParticleSystemConfig>): void {
    Object.assign(this.config, updates);
  }

  // ============================================================================
  // Rendering
  // ============================================================================

  renderToCanvas(
    ctx: CanvasRenderingContext2D,
    width: number,
    height: number,
    options: RenderOptions = createDefaultRenderOptions()
  ): void {
    // Cache render options for spatial grid
    this.renderOptions = options;
    ctx.save();

    // Set blend mode
    switch (options.blendMode) {
      case 'additive':
        ctx.globalCompositeOperation = 'lighter';
        break;
      case 'multiply':
        ctx.globalCompositeOperation = 'multiply';
        break;
      case 'screen':
        ctx.globalCompositeOperation = 'screen';
        break;
      default:
        ctx.globalCompositeOperation = 'source-over';
    }

    // Render particle connections first, before particles
    this.renderConnections(ctx, width, height);

    for (const p of this.particles) {
      const x = p.x * width;
      const y = p.y * height;
      const size = p.size;

      // Render trails first
      if (options.renderTrails) {
        const trail = this.trailHistory.get(p.id);
        if (trail && trail.length > 1) {
          ctx.beginPath();
          ctx.moveTo(x, y);

          const trailLen = Math.min(trail.length, options.trailLength);
          for (let i = 0; i < trailLen; i++) {
            const tp = trail[i];
            const opacity = p.color[3] * Math.pow(options.trailOpacityFalloff, i + 1);
            ctx.strokeStyle = `rgba(${p.color[0]}, ${p.color[1]}, ${p.color[2]}, ${opacity / 255})`;
            ctx.lineWidth = size * Math.pow(options.trailOpacityFalloff, i);
            ctx.lineTo(tp.x * width, tp.y * height);
          }
          ctx.stroke();
        }
      }

      // Apply glow
      if (options.glowEnabled) {
        ctx.shadowBlur = options.glowRadius;
        ctx.shadowColor = `rgba(${p.color[0]}, ${p.color[1]}, ${p.color[2]}, ${options.glowIntensity})`;
      } else {
        ctx.shadowBlur = 0;
      }

      // Motion blur rendering
      if (options.motionBlur && (p.vx !== 0 || p.vy !== 0)) {
        this.renderParticleWithMotionBlur(ctx, p, x, y, size, width, height, options);
      } else {
        // Standard particle rendering (pass particle for sprite rendering)
        this.renderParticleShape(ctx, x, y, size, p.color, options.particleShape, p, options);
      }
    }

    ctx.restore();
  }

  /**
   * Render a single particle with motion blur effect
   */
  private renderParticleWithMotionBlur(
    ctx: CanvasRenderingContext2D,
    p: Particle,
    x: number,
    y: number,
    size: number,
    _width: number,
    _height: number,
    options: RenderOptions
  ): void {
    // Calculate velocity magnitude
    const velocityMag = Math.sqrt(p.vx * p.vx + p.vy * p.vy);

    // If velocity is too small, render normally
    if (velocityMag < 0.0001) {
      this.renderParticleShape(ctx, x, y, size, p.color, options.particleShape);
      return;
    }

    // Calculate blur stretch based on velocity
    const stretchFactor = options.motionBlurStrength * velocityMag * 500;
    const samples = Math.min(options.motionBlurSamples, 16);

    // Direction of motion
    const dirX = p.vx / velocityMag;
    const dirY = p.vy / velocityMag;

    // Calculate stretch distance in pixels
    const stretchDistance = Math.min(stretchFactor * size, size * 10);

    // Render multiple samples along the motion vector
    for (let i = 0; i < samples; i++) {
      const t = i / (samples - 1); // 0 to 1
      const sampleOpacity = (1 - t * 0.8) / samples; // Fade towards the back

      // Position along the blur streak (from current position to where we were)
      const sampleX = x - dirX * stretchDistance * t;
      const sampleY = y - dirY * stretchDistance * t;

      // Size reduces towards back of blur
      const sampleSize = size * (1 - t * 0.3);

      // Set color with adjusted opacity
      const alpha = (p.color[3] / 255) * sampleOpacity * samples;
      ctx.fillStyle = `rgba(${p.color[0]}, ${p.color[1]}, ${p.color[2]}, ${Math.min(1, alpha)})`;

      // Draw sample
      this.renderParticleShape(ctx, sampleX, sampleY, sampleSize, null, options.particleShape, p, options);
    }

    // Draw the main particle at full opacity
    ctx.fillStyle = `rgba(${p.color[0]}, ${p.color[1]}, ${p.color[2]}, ${p.color[3] / 255})`;
    this.renderParticleShape(ctx, x, y, size, p.color, options.particleShape, p, options);
  }

  /**
   * Render a particle shape at given position
   */
  private renderParticleShape(
    ctx: CanvasRenderingContext2D,
    x: number,
    y: number,
    size: number,
    color: [number, number, number, number] | null,
    shape: RenderOptions['particleShape'],
    particle?: Particle,
    options?: RenderOptions
  ): void {
    // Set fill color if provided
    if (color) {
      ctx.fillStyle = `rgba(${color[0]}, ${color[1]}, ${color[2]}, ${color[3] / 255})`;
    }

    // Handle sprite rendering
    if (shape === 'sprite' && particle) {
      this.renderSprite(ctx, x, y, size, particle, options);
      return;
    }

    // Check if this particle has rotation (for non-sprite shapes)
    const hasRotation = particle && particle.rotation !== 0;

    if (hasRotation && particle) {
      ctx.save();
      ctx.translate(x, y);
      ctx.rotate(particle.rotation);
      // Draw at origin since we've translated
      this.drawShapeAtOrigin(ctx, size, shape);
      ctx.restore();
    } else {
      // Draw particle shape without rotation
      switch (shape) {
        case 'circle':
          ctx.beginPath();
          ctx.arc(x, y, size / 2, 0, Math.PI * 2);
          ctx.fill();
          break;

        case 'square':
          ctx.fillRect(x - size / 2, y - size / 2, size, size);
          break;

        case 'triangle':
          ctx.beginPath();
          ctx.moveTo(x, y - size / 2);
          ctx.lineTo(x - size / 2, y + size / 2);
          ctx.lineTo(x + size / 2, y + size / 2);
          ctx.closePath();
          ctx.fill();
          break;

        case 'star':
          this.drawStar(ctx, x, y, 5, size / 2, size / 4);
          ctx.fill();
          break;
      }
    }
  }

  /**
   * Draw shape at origin (for rotated shapes)
   */
  private drawShapeAtOrigin(
    ctx: CanvasRenderingContext2D,
    size: number,
    shape: RenderOptions['particleShape']
  ): void {
    switch (shape) {
      case 'circle':
        ctx.beginPath();
        ctx.arc(0, 0, size / 2, 0, Math.PI * 2);
        ctx.fill();
        break;

      case 'square':
        ctx.fillRect(-size / 2, -size / 2, size, size);
        break;

      case 'triangle':
        ctx.beginPath();
        ctx.moveTo(0, -size / 2);
        ctx.lineTo(-size / 2, size / 2);
        ctx.lineTo(size / 2, size / 2);
        ctx.closePath();
        ctx.fill();
        break;

      case 'star':
        this.drawStar(ctx, 0, 0, 5, size / 2, size / 4);
        ctx.fill();
        break;
    }
  }

  /**
   * Render a sprite/texture particle
   */
  private renderSprite(
    ctx: CanvasRenderingContext2D,
    x: number,
    y: number,
    size: number,
    particle: Particle,
    options?: RenderOptions
  ): void {
    const emitter = this.emitters.get(particle.emitterId);
    if (!emitter?.sprite?.enabled) {
      // Fallback to circle if no sprite
      ctx.beginPath();
      ctx.arc(x, y, size / 2, 0, Math.PI * 2);
      ctx.fill();
      return;
    }

    const sprite = emitter.sprite;
    const image = sprite.imageData || this.spriteCache.get(particle.emitterId);
    if (!image) {
      // Fallback to circle if no image loaded
      ctx.beginPath();
      ctx.arc(x, y, size / 2, 0, Math.PI * 2);
      ctx.fill();
      return;
    }

    ctx.save();

    // Set image smoothing
    ctx.imageSmoothingEnabled = options?.spriteSmoothing ?? true;

    // Apply opacity based on particle age if enabled
    let alpha = particle.color[3] / 255;
    if (options?.spriteOpacityByAge) {
      const lifeRatio = particle.age / particle.lifetime;
      // Fade out in the last 20% of life
      if (lifeRatio > 0.8) {
        alpha *= 1 - (lifeRatio - 0.8) / 0.2;
      }
    }
    ctx.globalAlpha = alpha;

    // Calculate sprite sheet frame coordinates
    let sx = 0;
    let sy = 0;
    let sw = image.width;
    let sh = image.height;

    if (sprite.isSheet && sprite.columns > 1 || sprite.rows > 1) {
      const frameWidth = image.width / sprite.columns;
      const frameHeight = image.height / sprite.rows;
      const col = particle.spriteIndex % sprite.columns;
      const row = Math.floor(particle.spriteIndex / sprite.columns) % sprite.rows;
      sx = col * frameWidth;
      sy = row * frameHeight;
      sw = frameWidth;
      sh = frameHeight;
    }

    // Translate to particle position
    ctx.translate(x, y);

    // Apply rotation
    if (particle.rotation !== 0) {
      ctx.rotate(particle.rotation);
    }

    // Draw the sprite centered at the particle position
    const halfSize = size / 2;
    ctx.drawImage(
      image,
      sx, sy, sw, sh,      // Source rectangle
      -halfSize, -halfSize, size, size  // Destination rectangle
    );

    ctx.restore();
  }

  private drawStar(
    ctx: CanvasRenderingContext2D,
    cx: number,
    cy: number,
    spikes: number,
    outerRadius: number,
    innerRadius: number
  ): void {
    ctx.beginPath();
    let rotation = -Math.PI / 2;

    for (let i = 0; i < spikes; i++) {
      const outerX = cx + Math.cos(rotation) * outerRadius;
      const outerY = cy + Math.sin(rotation) * outerRadius;

      if (i === 0) {
        ctx.moveTo(outerX, outerY);
      } else {
        ctx.lineTo(outerX, outerY);
      }

      rotation += Math.PI / spikes;

      const innerX = cx + Math.cos(rotation) * innerRadius;
      const innerY = cy + Math.sin(rotation) * innerRadius;
      ctx.lineTo(innerX, innerY);

      rotation += Math.PI / spikes;
    }

    ctx.closePath();
  }

  renderToMask(width: number, height: number): ImageData {
    const canvas = new OffscreenCanvas(width, height);
    const ctx = canvas.getContext('2d')!;

    // Start with white (include all)
    ctx.fillStyle = '#FFFFFF';
    ctx.fillRect(0, 0, width, height);

    // Draw connections as black (exclude) if enabled
    const connConfig = this.renderOptions.connections;
    if (connConfig?.enabled && this.particles.length >= 2) {
      ctx.strokeStyle = '#000000';
      ctx.lineWidth = connConfig.lineWidth * 2;  // Slightly thicker for matte
      this.renderConnections(ctx, width, height);
    }

    // Draw particles as black (exclude)
    ctx.fillStyle = '#000000';
    for (const p of this.particles) {
      const x = p.x * width;
      const y = p.y * height;
      const size = p.size * 1.5; // Slightly larger for matte

      ctx.beginPath();
      ctx.arc(x, y, size / 2, 0, Math.PI * 2);
      ctx.fill();
    }

    return ctx.getImageData(0, 0, width, height);
  }

  // ============================================================================
  // Serialization
  // ============================================================================

  serialize(): object {
    return {
      config: this.config,
      emitters: Array.from(this.emitters.values()),
      gravityWells: Array.from(this.gravityWells.values()),
      vortices: Array.from(this.vortices.values()),
      modulations: this.modulations,
      frameCount: this.frameCount
    };
  }

  static deserialize(data: any): ParticleSystem {
    const system = new ParticleSystem(data.config);

    if (data.emitters) {
      for (const emitter of data.emitters) {
        system.addEmitter(emitter);
      }
    }

    if (data.gravityWells) {
      for (const well of data.gravityWells) {
        system.addGravityWell(well);
      }
    }

    if (data.vortices) {
      for (const vortex of data.vortices) {
        system.addVortex(vortex);
      }
    }

    if (data.modulations) {
      for (const mod of data.modulations) {
        system.addModulation(mod);
      }
    }

    return system;
  }
}

export default ParticleSystem;
