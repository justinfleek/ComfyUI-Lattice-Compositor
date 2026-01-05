/**
 * GPU Particle System - Main Implementation
 *
 * This is the PRIMARY particle system for Lattice Compositor.
 * Use this for all particle rendering and simulation.
 *
 * FEATURES:
 * =========
 * Physics & Simulation:
 * - WebGL2 Transform Feedback for GPU-accelerated physics
 * - Double-buffered particle state for smooth updates
 * - Multiple force fields (gravity, vortex, turbulence, wind, drag)
 * - Flocking/swarming behavior (separation, alignment, cohesion)
 * - Particle-particle and boundary collision detection
 * - Deterministic seeded RNG for reproducible results
 *
 * Emitters:
 * - Multiple emitter shapes (point, line, circle, sphere, box, cone, spline, mesh)
 * - Sub-emitter system (spawn on birth/death/collision)
 * - Audio-reactive emission (burst on beat)
 * - Configurable variance for all parameters
 *
 * Rendering:
 * - Instanced rendering for 100k+ particles at 60fps
 * - Sprite sheet animation (time-based or life-based)
 * - Procedural shapes (circle, ring, square, star)
 * - Motion blur (velocity-based stretched billboards)
 * - Particle trails with configurable fade
 * - Particle connections (lines between nearby particles)
 * - Blending modes (normal, additive, multiply)
 *
 * Integration:
 * - Audio feature binding for any parameter
 * - Spline-based emission via provider callback
 * - Frame caching for timeline scrubbing
 *
 * ARCHITECTURE:
 * =============
 * - services/particleSystem.ts: Legacy CPU implementation (for deterministic scrubbing)
 * - engine/particles/GPUParticleSystem.ts: THIS FILE - main GPU implementation
 * - engine/particles/types.ts: Type definitions
 * - engine/particles/particleShaders.ts: GLSL shaders
 * - engine/ParticleSimulationController.ts: Deterministic evaluation wrapper
 *
 * Performance characteristics:
 * - CPU physics: ~10-50k particles at 60fps
 * - GPU physics (Transform Feedback): 100k+ particles at 60fps
 * - Memory: 64 bytes per particle (cache-line aligned)
 */

import * as THREE from "three";
import { ParticleAudioReactive } from "./ParticleAudioReactive";
import {
  type CollisionConfig,
  ParticleCollisionSystem,
} from "./ParticleCollisionSystem";
import { ParticleConnectionSystem } from "./ParticleConnectionSystem";
import {
  getEmissionDirection,
  getEmitterPosition,
  type SplineProvider,
} from "./ParticleEmitterLogic";
import { ParticleFlockingSystem } from "./ParticleFlockingSystem";
import { calculateForceField } from "./ParticleForceCalculator";
import { ParticleFrameCacheSystem } from "./ParticleFrameCache";
import { ParticleGPUPhysics } from "./ParticleGPUPhysics";
import { ParticleModulationCurves } from "./ParticleModulationCurves";
import type { ParticleSubEmitter } from "./ParticleSubEmitter";
import { ParticleTextureSystem } from "./ParticleTextureSystem";
import {
  ParticleTrailSystem,
  type TrailBlendingConfig,
  type TrailConfig,
} from "./ParticleTrailSystem";
import {
  PARTICLE_FRAGMENT_SHADER,
  PARTICLE_VERTEX_SHADER,
} from "./particleShaders";
import { SpatialHashGrid } from "./SpatialHashGrid";
import {
  type AudioFeature,
  type ConnectionConfig,
  type EmitterConfig,
  type FlockingConfig,
  type ForceFieldConfig,
  type GPUParticleSystemConfig,
  type ModulationCurve,
  PARTICLE_STRIDE,
  type ParticleEvent,
  type ParticleEventHandler,
  type ParticleSystemState,
  type SubEmitterConfig,
} from "./types";

// ============================================================================
// Constants
// ============================================================================

// PARTICLE_STRIDE is imported from ./types
// MAX_FORCE_FIELDS is imported from ./ParticleGPUPhysics
const _MAX_EMITTERS = 32;
const SPATIAL_CELL_SIZE = 50; // Pixels

/**
 * Cached particle state for a specific frame
 * Used for fast scrubbing - restore state instead of replaying from frame 0
 */
interface ParticleFrameCache {
  frame: number;
  version: number; // Cache version when this was created
  particleBuffer: Float32Array; // Copy of particle data
  freeIndices: number[]; // Copy of free indices
  particleCount: number;
  simulationTime: number;
  rngState: number; // RNG state at this frame for determinism
  emitterAccumulators: Map<string, number>; // Emitter accumulator values
}

// Attribute layout for transform feedback
const _PARTICLE_ATTRIBUTES = {
  position: { size: 3, offset: 0 },
  velocity: { size: 3, offset: 3 },
  life: { size: 2, offset: 6 },
  physical: { size: 2, offset: 8 },
  rotation: { size: 2, offset: 10 },
  color: { size: 4, offset: 12 },
};

// ============================================================================
// Default Configurations
// ============================================================================

export function createDefaultEmitter(id?: string): EmitterConfig {
  return {
    id: id || `emitter_${Date.now()}`,
    name: "Emitter",
    enabled: true,
    // Default to center of standard 832x480 composition
    position: { x: 416, y: 240, z: 0 },
    rotation: { x: 0, y: 0, z: 0 },
    shape: { type: "point" },
    emissionRate: 100,
    emissionRateVariance: 0,
    burstCount: 0,
    burstInterval: 0,
    initialSpeed: 200,
    speedVariance: 50,
    inheritEmitterVelocity: 0,
    initialSize: 10,
    sizeVariance: 2,
    initialMass: 1,
    massVariance: 0,
    lifetime: 120,
    lifetimeVariance: 20,
    initialRotation: 0,
    rotationVariance: 360,
    initialAngularVelocity: 0,
    angularVelocityVariance: 0,
    colorStart: [1, 1, 1, 1],
    colorEnd: [1, 1, 1, 0],
    colorVariance: 0,
    emissionDirection: { x: 0, y: -1, z: 0 },
    emissionSpread: 30,
    burstOnBeat: false,
    beatEmissionMultiplier: 5,
  };
}

export function createDefaultForceField(
  type: ForceFieldConfig["type"],
  id?: string,
): ForceFieldConfig {
  const base: ForceFieldConfig = {
    id: id || `force_${Date.now()}`,
    name: type.charAt(0).toUpperCase() + type.slice(1),
    type,
    enabled: true,
    strength: 100,
    // Default to center of standard 832x480 composition
    position: { x: 416, y: 240, z: 0 },
    falloffStart: 0,
    falloffEnd: 500,
    falloffType: "linear",
  };

  switch (type) {
    case "gravity":
      base.direction = { x: 0, y: 1, z: 0 };
      base.strength = 98;
      break;
    case "vortex":
      base.vortexAxis = { x: 0, y: 0, z: 1 };
      base.inwardForce = 20;
      break;
    case "turbulence":
      base.noiseScale = 0.005;
      base.noiseSpeed = 0.5;
      base.noiseOctaves = 3;
      base.noiseLacunarity = 2;
      base.noiseGain = 0.5;
      break;
    case "drag":
      base.linearDrag = 0.1;
      base.quadraticDrag = 0.01;
      break;
    case "wind":
      base.windDirection = { x: 1, y: 0, z: 0 };
      base.gustStrength = 50;
      base.gustFrequency = 0.1;
      break;
    case "lorenz":
      base.lorenzSigma = 10;
      base.lorenzRho = 28;
      base.lorenzBeta = 2.667;
      break;
  }

  return base;
}

export function createDefaultConfig(): GPUParticleSystemConfig {
  return {
    maxParticles: 100000,
    simulationSpace: "world",
    deltaTimeMode: "variable",
    fixedDeltaTime: 1 / 60,
    timeScale: 1,
    warmupFrames: 0,
    emitters: [],
    forceFields: [],
    subEmitters: [],
    lifetimeModulation: {},
    render: {
      mode: "billboard",
      sortByDepth: true,
      depthWrite: false,
      depthTest: true,
      blendMode: "normal",
      stretchFactor: 1,
      minStretch: 1,
      maxStretch: 4,
      trailLength: 0,
      trailSegments: 8,
      trailWidthStart: 1,
      trailWidthEnd: 0,
      trailFadeMode: "both",
      texture: {},
      shadow: {
        castShadows: false,
        receiveShadows: false,
        shadowSoftness: 1,
        shadowBias: 0.001,
        aoEnabled: false,
        aoRadius: 10,
        aoIntensity: 0.5,
        aoSamples: 8,
      },
      lighting: {
        receiveLighting: false,
        roughness: 0.5,
        metalness: 0,
        emissiveIntensity: 0,
        subsurfaceScattering: false,
        subsurfaceColor: [1, 0.5, 0.5],
        subsurfaceRadius: 1,
      },
      motionBlur: false,
      motionBlurSamples: 4,
      motionBlurStrength: 0.5,
      lodEnabled: false,
      lodDistances: [100, 500, 1000],
      lodSizeMultipliers: [1, 0.5, 0.25],
    },
    audioBindings: [],
    spatialHashCellSize: SPATIAL_CELL_SIZE,
    updateFrequency: 1,
    cullOffscreen: true,
  };
}

// ============================================================================
// GPU Particle System Class
// ============================================================================

export class GPUParticleSystem {
  private config: GPUParticleSystemConfig;
  private gl: WebGL2RenderingContext | null = null;

  // Double-buffered particle data
  private particleBufferA: Float32Array;
  private particleBufferB: Float32Array;
  private currentBuffer: "A" | "B" = "A";

  // Three.js integration
  private particleMesh: THREE.Mesh | null = null;
  private instancedGeometry: THREE.InstancedBufferGeometry | null = null;
  private material: THREE.ShaderMaterial | null = null;

  // Textures for modulation curves
  private sizeOverLifetimeTexture: THREE.DataTexture | null = null;
  private opacityOverLifetimeTexture: THREE.DataTexture | null = null;
  private colorOverLifetimeTexture: THREE.DataTexture | null = null;

  // Emitter state
  private emitters: Map<
    string,
    EmitterConfig & { accumulator: number; velocity: THREE.Vector3 }
  > = new Map();
  private forceFields: Map<string, ForceFieldConfig> = new Map();
  private subEmitters: Map<string, SubEmitterConfig> = new Map();

  // Runtime state
  private state: ParticleSystemState = {
    particleCount: 0,
    activeEmitters: 0,
    simulationTime: 0,
    frameCount: 0,
    updateTimeMs: 0,
    renderTimeMs: 0,
    gpuMemoryBytes: 0,
    currentAudioFeatures: new Map(),
  };

  // Event system
  private eventHandlers: Map<string, Set<ParticleEventHandler>> = new Map();

  // Pool of free particle indices
  private freeIndices: number[] = [];

  // Track which emitter spawned each particle (for sub-emitter filtering)
  private particleEmitters: Map<number, string> = new Map();

  // BUG-073 fix: Store initial size/opacity for lifetime modulation
  // Without this, *= modulation causes exponential decay
  // BUG-070 fix: Also store random offset for deterministic random modulation
  private particleInitialValues: Map<
    number,
    { size: number; opacity: number; randomOffset: number }
  > = new Map();

  // Trail system - extracted to ParticleTrailSystem.ts
  private trailSystem: ParticleTrailSystem | null = null;

  // Connection system - extracted to ParticleConnectionSystem.ts
  private connectionSystem: ParticleConnectionSystem | null = null;

  // Collision system - extracted to ParticleCollisionSystem.ts
  private collisionSystem: ParticleCollisionSystem | null = null;

  // Flocking system - extracted to ParticleFlockingSystem.ts
  private flockingSystem: ParticleFlockingSystem | null = null;

  // Sub-emitter system - extracted to ParticleSubEmitter.ts
  private subEmitterSystem: ParticleSubEmitter | null = null;

  // Spline provider for spline-based emission
  private splineProvider: SplineProvider | null = null;

  // Texture system - extracted to ParticleTextureSystem.ts
  private textureSystem: ParticleTextureSystem | null = null;

  // Audio reactive system - extracted to ParticleAudioReactive.ts
  private audioSystem: ParticleAudioReactive | null = null;

  // Frame cache system - extracted to ParticleFrameCache.ts
  private frameCacheSystem: ParticleFrameCacheSystem | null = null;

  // Shared spatial hash grid - used by flocking and collision systems
  private spatialHash: SpatialHashGrid | null = null;

  // Modulation curves system - extracted to ParticleModulationCurves.ts
  private modulationSystem: ParticleModulationCurves | null = null;

  // Random number generator with seed
  private rng: () => number;
  private initialRngSeed: number;
  private currentRngState: number; // Tracks RNG state for save/restore

  constructor(config: Partial<GPUParticleSystemConfig> = {}) {
    this.config = { ...createDefaultConfig(), ...config };

    // Validate and cap maxParticles to prevent memory exhaustion (max 1M particles = ~64MB per buffer)
    const MAX_SAFE_PARTICLES = 1000000;
    if (
      !Number.isFinite(this.config.maxParticles) ||
      this.config.maxParticles <= 0
    ) {
      this.config.maxParticles = 100000; // Default
    } else if (this.config.maxParticles > MAX_SAFE_PARTICLES) {
      console.warn(
        `GPUParticleSystem: maxParticles capped from ${this.config.maxParticles} to ${MAX_SAFE_PARTICLES}`,
      );
      this.config.maxParticles = MAX_SAFE_PARTICLES;
    }

    // Initialize buffers
    const bufferSize = this.config.maxParticles * PARTICLE_STRIDE;
    this.particleBufferA = new Float32Array(bufferSize);
    this.particleBufferB = new Float32Array(bufferSize);

    // Initialize free indices
    for (let i = this.config.maxParticles - 1; i >= 0; i--) {
      this.freeIndices.push(i);
    }

    // Initialize RNG with saved seed for deterministic replay
    // Use consistent fallback (12345) - never Date.now() which breaks determinism
    this.initialRngSeed = this.config.randomSeed ?? 12345;
    this.currentRngState = this.initialRngSeed;
    this.rng = this.createSeededRandom(this.initialRngSeed);

    // Add configured emitters and force fields
    this.config.emitters.forEach((e) => this.addEmitter(e));
    this.config.forceFields.forEach((f) => this.addForceField(f));
    this.config.subEmitters.forEach((s) => this.addSubEmitter(s));

    // Initialize extracted subsystems
    this.textureSystem = new ParticleTextureSystem();
    this.audioSystem = new ParticleAudioReactive();
    this.audioSystem.setBindings(this.config.audioBindings);
    this.frameCacheSystem = new ParticleFrameCacheSystem(
      this.config.maxParticles,
      5,
      200,
    );

    // Initialize shared spatial hash grid (used by flocking and collision)
    this.spatialHash = new SpatialHashGrid({
      cellSize: this.config.spatialHashCellSize ?? SPATIAL_CELL_SIZE,
      maxParticles: this.config.maxParticles,
    });

    // Initialize modulation curves system (size/opacity/color over lifetime)
    this.modulationSystem = new ParticleModulationCurves(this.rng);
  }

  // ============================================================================
  // Initialization
  // ============================================================================

  // GPU physics system (handles WebGPU and Transform Feedback)
  private gpuPhysics: ParticleGPUPhysics | null = null;

  /**
   * Initialize GPU resources. Must be called before simulation.
   */
  initialize(renderer: THREE.WebGLRenderer): void {
    this.renderer = renderer;
    this.gl = renderer.getContext() as WebGL2RenderingContext;

    if (!this.gl) {
      throw new Error("WebGL2 context required for GPU particle system");
    }

    // Create Three.js mesh for rendering (creates material)
    this.createParticleMesh();

    // Create modulation textures (after material exists so we can set uniforms)
    this.createModulationTextures();

    // Initialize trail system if enabled
    if (this.config.render.trailLength > 0) {
      this.initializeTrails();
    }

    // Initialize GPU physics system (handles WebGPU / Transform Feedback)
    this.gpuPhysics = new ParticleGPUPhysics({
      maxParticles: this.config.maxParticles,
    });
    this.gpuPhysics.initialize(
      renderer,
      this.particleBufferA,
      this.particleBufferB,
    );

    // Calculate GPU memory usage
    this.state.gpuMemoryBytes =
      this.config.maxParticles * PARTICLE_STRIDE * 4 * 2; // Double buffered
  }

  /**
   * Enable or disable GPU physics
   * Delegates to ParticleGPUPhysics
   */
  setGPUPhysicsEnabled(enabled: boolean): void {
    this.gpuPhysics?.setEnabled(enabled);
  }

  /**
   * Check if GPU physics is currently enabled
   */
  isGPUPhysicsEnabled(): boolean {
    return this.gpuPhysics?.isEnabled() ?? false;
  }

  /**
   * Create textures for lifetime modulation curves
   * Delegates to ParticleModulationCurves
   */
  private createModulationTextures(): void {
    if (!this.modulationSystem) return;

    const textures = this.modulationSystem.createTextures(
      this.config.lifetimeModulation,
    );
    this.sizeOverLifetimeTexture = textures.sizeOverLifetime;
    this.opacityOverLifetimeTexture = textures.opacityOverLifetime;
    this.colorOverLifetimeTexture = textures.colorOverLifetime;

    // BUG-072 fix: Wire up colorOverLifetime texture to shader
    // Check if user configured colorOverLifetime (not just default white)
    const hasColorConfig =
      this.config.lifetimeModulation.colorOverLifetime &&
      this.config.lifetimeModulation.colorOverLifetime.length > 0;
    if (this.material && this.colorOverLifetimeTexture) {
      this.material.uniforms.colorOverLifetime.value =
        this.colorOverLifetimeTexture;
      this.material.uniforms.hasColorOverLifetime.value = hasColorConfig
        ? 1
        : 0;
    }
  }

  /**
   * Evaluate a modulation curve at time t
   * Delegates to ParticleModulationCurves
   * @param randomOffset - BUG-070 fix: Per-particle random offset for deterministic random curves
   */
  private evaluateModulationCurve(
    curve: ModulationCurve,
    t: number,
    randomOffset?: number,
  ): number {
    return this.modulationSystem?.evaluateCurve(curve, t, randomOffset) ?? 1;
  }

  /**
   * Create the Three.js mesh for particle rendering
   */
  private createParticleMesh(): void {
    // Create quad geometry for billboards
    const quadVertices = new Float32Array([
      -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1, 1,
    ]);
    const quadUVs = new Float32Array([0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1]);

    this.instancedGeometry = new THREE.InstancedBufferGeometry();
    this.instancedGeometry.setAttribute(
      "position",
      new THREE.BufferAttribute(quadVertices, 2),
    );
    this.instancedGeometry.setAttribute(
      "uv",
      new THREE.BufferAttribute(quadUVs, 2),
    );

    // Create instanced attributes from particle buffer
    const positionAttr = new THREE.InstancedBufferAttribute(
      new Float32Array(this.config.maxParticles * 3),
      3,
    );
    const velocityAttr = new THREE.InstancedBufferAttribute(
      new Float32Array(this.config.maxParticles * 3),
      3,
    );
    const lifeAttr = new THREE.InstancedBufferAttribute(
      new Float32Array(this.config.maxParticles * 2),
      2,
    );
    const physicalAttr = new THREE.InstancedBufferAttribute(
      new Float32Array(this.config.maxParticles * 2),
      2,
    );
    const rotationAttr = new THREE.InstancedBufferAttribute(
      new Float32Array(this.config.maxParticles * 2),
      2,
    );
    const colorAttr = new THREE.InstancedBufferAttribute(
      new Float32Array(this.config.maxParticles * 4),
      4,
    );

    positionAttr.setUsage(THREE.DynamicDrawUsage);
    velocityAttr.setUsage(THREE.DynamicDrawUsage);
    lifeAttr.setUsage(THREE.DynamicDrawUsage);
    physicalAttr.setUsage(THREE.DynamicDrawUsage);
    rotationAttr.setUsage(THREE.DynamicDrawUsage);
    colorAttr.setUsage(THREE.DynamicDrawUsage);

    this.instancedGeometry.setAttribute("i_position", positionAttr);
    this.instancedGeometry.setAttribute("i_velocity", velocityAttr);
    this.instancedGeometry.setAttribute("i_life", lifeAttr);
    this.instancedGeometry.setAttribute("i_physical", physicalAttr);
    this.instancedGeometry.setAttribute("i_rotation", rotationAttr);
    this.instancedGeometry.setAttribute("i_color", colorAttr);

    // Create shader material
    this.material = new THREE.ShaderMaterial({
      vertexShader: PARTICLE_VERTEX_SHADER,
      fragmentShader: PARTICLE_FRAGMENT_SHADER,
      uniforms: this.createUniforms(),
      transparent: true,
      depthWrite: this.config.render.depthWrite,
      depthTest: this.config.render.depthTest,
      blending: this.getThreeBlending(),
    });

    this.particleMesh = new THREE.Mesh(this.instancedGeometry, this.material);
    this.particleMesh.frustumCulled = false;
  }

  /**
   * Initialize trail system - delegates to ParticleTrailSystem
   */
  private initializeTrails(): void {
    const trailConfig: TrailConfig = {
      trailLength: this.config.render.trailLength,
      trailSegments: this.config.render.trailSegments ?? 8,
      trailWidthStart: this.config.render.trailWidthStart ?? 1,
      trailWidthEnd: this.config.render.trailWidthEnd ?? 0.5,
      trailFadeMode: this.config.render.trailFadeMode ?? "alpha",
    };

    const blendingConfig: TrailBlendingConfig = {
      blendMode: this.config.render.blendMode,
    };

    this.trailSystem = new ParticleTrailSystem(
      this.config.maxParticles,
      trailConfig,
      blendingConfig,
    );
    this.trailSystem.initialize();
  }

  /**
   * Update trail positions for all particles - delegates to ParticleTrailSystem
   */
  private updateTrails(): void {
    if (!this.trailSystem) return;
    const buffer =
      this.currentBuffer === "A" ? this.particleBufferA : this.particleBufferB;
    this.trailSystem.update(buffer);
  }

  /**
   * Get the trail mesh for adding to scene
   */
  getTrailMesh(): THREE.LineSegments | null {
    return this.trailSystem?.getMesh() ?? null;
  }

  /**
   * Initialize particle connection system
   */
  initializeConnections(config: ConnectionConfig): void {
    this.connectionSystem = new ParticleConnectionSystem(
      this.config.maxParticles,
      config,
    );
    this.connectionSystem.initialize();
  }

  /**
   * Update particle connections
   * Uses spatial hash for efficient neighbor queries
   */
  private updateConnections(): void {
    if (!this.connectionSystem) return;
    const buffer =
      this.currentBuffer === "A" ? this.particleBufferA : this.particleBufferB;
    this.connectionSystem.update(buffer);
  }

  /**
   * Get the connection mesh for adding to scene
   */
  getConnectionMesh(): THREE.LineSegments | null {
    return this.connectionSystem?.getMesh() ?? null;
  }

  /**
   * Enable or disable particle connections
   */
  setConnectionsEnabled(enabled: boolean): void {
    this.connectionSystem?.setEnabled(enabled);
  }
  /**
   * Initialize collision system
   */
  initializeCollisions(config: Partial<CollisionConfig>): void {
    this.collisionSystem = new ParticleCollisionSystem(
      this.config.maxParticles,
      config,
    );
    // Share the spatial hash grid with collision system
    if (this.spatialHash) {
      this.collisionSystem.setSpatialHash(this.spatialHash);
    }
  }

  /**
   * Apply collision detection and response
   */
  private applyCollisions(): void {
    if (!this.collisionSystem) return;
    const buffer =
      this.currentBuffer === "A" ? this.particleBufferA : this.particleBufferB;
    this.collisionSystem.update(buffer);
  }

  /**
   * Initialize flocking system
   */
  initializeFlocking(config: FlockingConfig): void {
    this.flockingSystem = new ParticleFlockingSystem(
      this.config.maxParticles,
      config,
    );
    // Share the spatial hash grid with flocking system
    if (this.spatialHash) {
      this.flockingSystem.setSpatialHash(this.spatialHash);
    }
  }

  /**
   * Update flocking configuration
   */
  updateFlocking(config: Partial<FlockingConfig>): void {
    this.flockingSystem?.updateConfig(config);
  }

  /**
   * Enable or disable flocking
   */
  setFlockingEnabled(enabled: boolean): void {
    this.flockingSystem?.setEnabled(enabled);
  }

  // ============================================================================
  // Texture/Sprite System
  // ============================================================================

  /**
   * Load a particle texture from URL or data URI
   * Delegates to ParticleTextureSystem
   */
  loadTexture(
    url: string,
    spriteSheet?: {
      columns?: number;
      rows?: number;
      animate?: boolean;
      frameRate?: number;
      randomStart?: boolean;
    },
  ): Promise<void> {
    if (this.textureSystem) {
      this.textureSystem.setRenderTargets(
        this.material,
        this.instancedGeometry,
      );
      return this.textureSystem.loadTexture(url, spriteSheet);
    }
    return Promise.resolve();
  }

  /**
   * Set procedural shape (no texture)
   * BUG-067 fix: All 9 shapes now supported
   * Delegates to ParticleTextureSystem
   */
  setProceduralShape(
    shape:
      | "none"
      | "circle"
      | "ring"
      | "square"
      | "star"
      | "noise"
      | "line"
      | "triangle"
      | "shadedSphere"
      | "fadedSphere",
  ): void {
    if (this.textureSystem) {
      this.textureSystem.setRenderTargets(
        this.material,
        this.instancedGeometry,
      );
      this.textureSystem.setProceduralShape(shape);
    }
  }

  /**
   * Update time uniform for sprite animation
   * Delegates to ParticleTextureSystem
   */
  private updateSpriteAnimation(time: number): void {
    this.textureSystem?.updateSpriteAnimation(time);
  }

  /**
   * Configure motion blur effect
   * Delegates to ParticleTextureSystem
   */
  setMotionBlur(config: {
    enabled: boolean;
    strength?: number;
    minStretch?: number;
    maxStretch?: number;
  }): void {
    if (this.textureSystem) {
      this.textureSystem.setRenderTargets(
        this.material,
        this.instancedGeometry,
      );
      this.textureSystem.setMotionBlur(
        {
          enabled: config.enabled,
          strength: config.strength ?? 0.1,
          minStretch: config.minStretch ?? 1.0,
          maxStretch: config.maxStretch ?? 4.0,
        },
        this.config.render,
      );
    }
  }

  /**
   * Initialize glow effect rendering
   * Delegates to ParticleTextureSystem
   */
  initializeGlow(config: {
    enabled: boolean;
    radius: number;
    intensity: number;
  }): void {
    if (this.textureSystem) {
      this.textureSystem.setRenderTargets(
        this.material,
        this.instancedGeometry,
      );
      this.textureSystem.initializeGlow(config);
    }
  }

  /**
   * Update glow configuration
   * Delegates to ParticleTextureSystem
   */
  setGlow(config: {
    enabled?: boolean;
    radius?: number;
    intensity?: number;
  }): void {
    this.textureSystem?.setGlow(config);
  }

  /**
   * Get the glow mesh for adding to scene
   * Delegates to ParticleTextureSystem
   */
  getGlowMesh(): THREE.Mesh | null {
    return this.textureSystem?.getGlowMesh() ?? null;
  }

  // ============================================================================
  // Emitter Management
  // ============================================================================

  addEmitter(config: EmitterConfig): void {
    this.emitters.set(config.id, {
      ...config,
      accumulator: 0,
      velocity: new THREE.Vector3(),
    });
    this.state.activeEmitters = this.emitters.size;
    this.invalidateCache(); // Emitter changes require re-simulation
  }

  updateEmitter(id: string, updates: Partial<EmitterConfig>): void {
    const emitter = this.emitters.get(id);
    if (emitter) {
      Object.assign(emitter, updates);
      this.invalidateCache(); // Emitter changes require re-simulation
    }
  }

  removeEmitter(id: string): void {
    this.emitters.delete(id);
    this.state.activeEmitters = this.emitters.size;
    this.invalidateCache(); // Emitter changes require re-simulation
  }

  getEmitter(id: string): EmitterConfig | undefined {
    return this.emitters.get(id);
  }

  // ============================================================================
  // Force Field Management
  // ============================================================================

  addForceField(config: ForceFieldConfig): void {
    this.forceFields.set(config.id, config);
    this.invalidateCache(); // Force field changes require re-simulation
  }

  updateForceField(id: string, updates: Partial<ForceFieldConfig>): void {
    const field = this.forceFields.get(id);
    if (field) {
      Object.assign(field, updates);
      this.invalidateCache(); // Force field changes require re-simulation
    }
  }

  removeForceField(id: string): void {
    this.forceFields.delete(id);
    this.invalidateCache(); // Force field changes require re-simulation
  }

  // ============================================================================
  // Sub-Emitter Management
  // ============================================================================

  addSubEmitter(config: SubEmitterConfig): void {
    this.subEmitters.set(config.id, config);
    this.invalidateCache(); // Sub-emitter changes require re-simulation
  }

  removeSubEmitter(id: string): void {
    this.subEmitters.delete(id);
    this.invalidateCache(); // Sub-emitter changes require re-simulation
  }

  // ============================================================================
  // Simulation
  // ============================================================================

  /**
   * Step the particle simulation forward
   */
  step(deltaTime: number): void {
    const startTime = performance.now();

    const dt =
      this.config.deltaTimeMode === "fixed"
        ? this.config.fixedDeltaTime
        : deltaTime * this.config.timeScale;

    // 1. Emit new particles
    this.emitParticles(dt);

    // 2. Update physics - GPU (WebGPU/Transform Feedback) > CPU
    if (this.gpuPhysics?.isEnabled()) {
      const result = this.gpuPhysics.update(
        dt,
        {
          simulationTime: this.state.simulationTime,
          frameCount: this.state.frameCount,
        },
        this.particleBufferA,
        this.particleBufferB,
        this.forceFields,
        this.freeIndices,
        (index) => this.emit("particleDeath", { index }),
      );
      if (result.particleCount >= 0) {
        this.state.particleCount = result.particleCount;
      }
      this.currentBuffer = result.currentBuffer;
    } else {
      this.updatePhysics(dt);
    }

    // 3. Handle sub-emitter triggers (using extracted module)
    if (this.subEmitterSystem?.hasSubEmitters()) {
      const buffer =
        this.currentBuffer === "A"
          ? this.particleBufferA
          : this.particleBufferB;
      const spawnCount = this.subEmitterSystem.processDeathEvents(
        buffer,
        this.freeIndices,
      );
      this.state.particleCount += spawnCount;
    }

    // 4. Rebuild shared spatial hash (used by both flocking and collision)
    // Only rebuild if either system needs it - avoids O(n) when neither is enabled
    const needsSpatialHash =
      this.flockingSystem?.isEnabled() ||
      (this.collisionSystem?.isEnabled() &&
        this.collisionSystem.getConfig().particleCollision);
    if (needsSpatialHash && this.spatialHash) {
      const buffer =
        this.currentBuffer === "A"
          ? this.particleBufferA
          : this.particleBufferB;
      this.spatialHash.rebuild(buffer);
    }

    // 5. Apply flocking (using extracted module and shared spatial hash)
    if (this.flockingSystem?.isEnabled()) {
      const buffer =
        this.currentBuffer === "A"
          ? this.particleBufferA
          : this.particleBufferB;
      this.flockingSystem.applyFlocking(buffer, dt);
    }

    // 6. Apply collisions
    if (this.collisionSystem?.isEnabled()) {
      this.applyCollisions();
    }

    // 7. Apply audio modulation
    this.applyAudioModulation();

    // 8. Update trail positions
    if (this.config.render.trailLength > 0) {
      this.updateTrails();
    }

    // 9. Update particle connections
    if (this.connectionSystem?.isEnabled()) {
      this.updateConnections();
    }

    // 10. Update instance buffers
    this.updateInstanceBuffers();

    // 11. Update sprite animation
    this.updateSpriteAnimation(this.state.simulationTime);

    // Update state
    this.state.simulationTime += dt;
    this.state.frameCount++;
    this.state.updateTimeMs = performance.now() - startTime;
  }

  /**
   * Emit particles from all active emitters
   */
  private emitParticles(dt: number): void {
    for (const emitter of this.emitters.values()) {
      if (!emitter.enabled) continue;

      // Get audio-modulated emission rate (validate to prevent NaN accumulator)
      let emissionRate = Number.isFinite(emitter.emissionRate)
        ? emitter.emissionRate
        : 100;
      const audioMod = this.getAudioModulation(
        "emitter",
        emitter.id,
        "emissionRate",
      );
      if (audioMod !== undefined && Number.isFinite(audioMod)) {
        emissionRate *= audioMod;
      }
      // Cap emission rate to prevent runaway particle spawning
      emissionRate = Math.max(0, Math.min(emissionRate, 100000));

      // Check for beat-triggered burst (uses 'onsets' from audio analysis)
      if (
        emitter.burstOnBeat &&
        this.state.currentAudioFeatures.get("onsets") === 1
      ) {
        const burstCount = Math.floor(
          emitter.burstCount * emitter.beatEmissionMultiplier,
        );
        for (let i = 0; i < burstCount; i++) {
          this.spawnParticle(emitter);
        }
      }

      // Regular emission
      emitter.accumulator += emissionRate * dt;

      while (emitter.accumulator >= 1) {
        this.spawnParticle(emitter);
        emitter.accumulator -= 1;
      }
    }
  }

  /**
   * Spawn a single particle from an emitter
   */
  private spawnParticle(
    emitter: EmitterConfig & { velocity: THREE.Vector3 },
  ): number {
    if (this.freeIndices.length === 0) {
      // Find oldest particle to recycle
      let oldestIndex = 0;
      let oldestAge = 0;
      const buffer =
        this.currentBuffer === "A"
          ? this.particleBufferA
          : this.particleBufferB;

      for (let i = 0; i < this.config.maxParticles; i++) {
        const age = buffer[i * PARTICLE_STRIDE + 6];
        if (age > oldestAge) {
          oldestAge = age;
          oldestIndex = i;
        }
      }
      this.freeIndices.push(oldestIndex);
    }

    const index = this.freeIndices.pop()!;
    const buffer =
      this.currentBuffer === "A" ? this.particleBufferA : this.particleBufferB;
    const offset = index * PARTICLE_STRIDE;

    // Track which emitter spawned this particle (for sub-emitter filtering)
    this.particleEmitters.set(index, emitter.id);

    // Calculate spawn position based on emitter shape (using extracted module)
    const pos = getEmitterPosition(emitter, this.rng, this.splineProvider);

    // Calculate initial velocity (using extracted module)
    const dir = getEmissionDirection(emitter, this.rng);
    // Validate speed (NaN would corrupt velocity calculations)
    const rawSpeed =
      emitter.initialSpeed + (this.rng() - 0.5) * 2 * emitter.speedVariance;
    const speed = Number.isFinite(rawSpeed) ? rawSpeed : 200;

    // Inherit emitter velocity
    const inheritVel = emitter.velocity
      .clone()
      .multiplyScalar(emitter.inheritEmitterVelocity);

    // Write particle data
    buffer[offset + 0] = pos.x;
    buffer[offset + 1] = pos.y;
    buffer[offset + 2] = pos.z;

    buffer[offset + 3] = dir.x * speed + inheritVel.x;
    buffer[offset + 4] = dir.y * speed + inheritVel.y;
    buffer[offset + 5] = dir.z * speed + inheritVel.z;

    buffer[offset + 6] = 0; // age
    // Validate lifetime (NaN/0 would cause division by zero in age/lifetime calculations)
    const rawLifetime =
      emitter.lifetime + (this.rng() - 0.5) * 2 * emitter.lifetimeVariance;
    buffer[offset + 7] =
      Number.isFinite(rawLifetime) && rawLifetime > 0 ? rawLifetime : 120;

    buffer[offset + 8] =
      emitter.initialMass + (this.rng() - 0.5) * 2 * emitter.massVariance;
    buffer[offset + 9] =
      emitter.initialSize + (this.rng() - 0.5) * 2 * emitter.sizeVariance;

    buffer[offset + 10] =
      emitter.initialRotation + this.rng() * emitter.rotationVariance;
    buffer[offset + 11] =
      emitter.initialAngularVelocity +
      (this.rng() - 0.5) * 2 * emitter.angularVelocityVariance;

    // Interpolate color
    const colorT = this.rng() * emitter.colorVariance;
    buffer[offset + 12] =
      emitter.colorStart[0] +
      (emitter.colorEnd[0] - emitter.colorStart[0]) * colorT;
    buffer[offset + 13] =
      emitter.colorStart[1] +
      (emitter.colorEnd[1] - emitter.colorStart[1]) * colorT;
    buffer[offset + 14] =
      emitter.colorStart[2] +
      (emitter.colorEnd[2] - emitter.colorStart[2]) * colorT;
    buffer[offset + 15] = emitter.colorStart[3];

    // BUG-073 fix: Store initial size/opacity for lifetime modulation
    // This allows us to compute initialValue * modFactor instead of *= which causes exponential decay
    // BUG-070 fix: Store random offset for deterministic random modulation curves
    this.particleInitialValues.set(index, {
      size: buffer[offset + 9],
      opacity: buffer[offset + 15],
      randomOffset: this.rng(), // Computed once at spawn, used throughout lifetime
    });

    this.state.particleCount++;
    this.emit("particleBirth", { index, emitterId: emitter.id });

    return index;
  }

  /**
   * Set the spline provider function for spline-based emission
   */
  setSplineProvider(provider: SplineProvider | null): void {
    this.splineProvider = provider;
  }

  /**
   * Update particle physics (CPU implementation)
   */
  private updatePhysics(dt: number): void {
    const buffer =
      this.currentBuffer === "A" ? this.particleBufferA : this.particleBufferB;

    for (let i = 0; i < this.config.maxParticles; i++) {
      const offset = i * PARTICLE_STRIDE;

      const age = buffer[offset + 6];
      const lifetime = buffer[offset + 7];

      // Skip dead particles
      if (lifetime <= 0 || age >= lifetime) continue;

      // Read particle state
      let px = buffer[offset + 0];
      let py = buffer[offset + 1];
      let pz = buffer[offset + 2];
      let vx = buffer[offset + 3];
      let vy = buffer[offset + 4];
      let vz = buffer[offset + 5];
      const mass = buffer[offset + 8];
      const angularVelocity = buffer[offset + 11];

      // BUG-073 fix: Get initial values for modulation to prevent exponential decay
      // BUG-070 fix: Get randomOffset for deterministic random curves
      const initialValues = this.particleInitialValues.get(i);
      const initialSize = initialValues?.size ?? buffer[offset + 9];
      const initialOpacity = initialValues?.opacity ?? buffer[offset + 15];
      const randomOffset = initialValues?.randomOffset ?? 0.5;

      // BUG-071 fix: Evaluate all lifetime modulation curves BEFORE physics
      const lifeRatio = age / lifetime;
      const sizeMod = this.evaluateModulationCurve(
        this.config.lifetimeModulation.sizeOverLifetime || {
          type: "constant",
          value: 1,
        },
        lifeRatio,
        randomOffset,
      );
      const opacityMod = this.evaluateModulationCurve(
        this.config.lifetimeModulation.opacityOverLifetime || {
          type: "constant",
          value: 1,
        },
        lifeRatio,
        randomOffset,
      );
      // BUG-071 fix: New lifetime modulation properties
      const speedMod = this.evaluateModulationCurve(
        this.config.lifetimeModulation.speedOverLifetime || {
          type: "constant",
          value: 1,
        },
        lifeRatio,
        randomOffset,
      );
      const rotationSpeedMod = this.evaluateModulationCurve(
        this.config.lifetimeModulation.rotationSpeedOverLifetime || {
          type: "constant",
          value: 1,
        },
        lifeRatio,
        randomOffset,
      );
      const gravityMod = this.evaluateModulationCurve(
        this.config.lifetimeModulation.gravityModifier || {
          type: "constant",
          value: 1,
        },
        lifeRatio,
        randomOffset,
      );
      const dragMod = this.evaluateModulationCurve(
        this.config.lifetimeModulation.dragOverLifetime || {
          type: "constant",
          value: 0,
        },
        lifeRatio,
        randomOffset,
      );
      const noiseMod = this.evaluateModulationCurve(
        this.config.lifetimeModulation.noiseAmplitudeOverLifetime || {
          type: "constant",
          value: 1,
        },
        lifeRatio,
        randomOffset,
      );

      // Accumulate forces
      let fx = 0,
        fy = 0,
        fz = 0;

      // Apply force fields with BUG-071 modifiers
      for (const field of this.forceFields.values()) {
        if (!field.enabled) continue;

        const force = calculateForceField(
          field,
          px,
          py,
          pz,
          vx,
          vy,
          vz,
          mass,
          this.state.simulationTime,
        );

        // BUG-071 fix: Apply gravityModifier to gravity forces
        if (field.type === "gravity") {
          fx += force.x * gravityMod;
          fy += force.y * gravityMod;
          fz += force.z * gravityMod;
        }
        // BUG-071 fix: Apply noiseAmplitudeOverLifetime to turbulence forces
        else if (field.type === "turbulence") {
          fx += force.x * noiseMod;
          fy += force.y * noiseMod;
          fz += force.z * noiseMod;
        } else {
          fx += force.x;
          fy += force.y;
          fz += force.z;
        }
      }

      // Apply acceleration (F = ma)
      const ax = fx / Math.max(mass, 0.1);
      const ay = fy / Math.max(mass, 0.1);
      const az = fz / Math.max(mass, 0.1);

      // Integrate velocity
      vx += ax * dt;
      vy += ay * dt;
      vz += az * dt;

      // BUG-071 fix: Apply dragOverLifetime to velocity
      // Drag reduces velocity proportionally: v = v * (1 - drag * dt)
      if (dragMod > 0) {
        const dragFactor = Math.max(0, 1 - dragMod * dt);
        vx *= dragFactor;
        vy *= dragFactor;
        vz *= dragFactor;
      }

      // BUG-071 fix: Apply speedOverLifetime to velocity magnitude
      // This scales the velocity vector while preserving direction
      if (speedMod !== 1) {
        vx *= speedMod;
        vy *= speedMod;
        vz *= speedMod;
      }

      // Integrate position
      px += vx * dt;
      py += vy * dt;
      pz += vz * dt;

      // BUG-071 fix: Apply rotationSpeedOverLifetime to angular velocity
      const effectiveAngularVelocity = angularVelocity * rotationSpeedMod;

      // Update rotation
      const rotation = buffer[offset + 10] + effectiveAngularVelocity * dt;

      // Write updated state
      buffer[offset + 0] = px;
      buffer[offset + 1] = py;
      buffer[offset + 2] = pz;
      buffer[offset + 3] = vx;
      buffer[offset + 4] = vy;
      buffer[offset + 5] = vz;
      buffer[offset + 6] = age + dt;
      buffer[offset + 9] = initialSize * sizeMod; // BUG-073 fix: multiply initial, not current
      buffer[offset + 10] = rotation;
      buffer[offset + 15] = initialOpacity * opacityMod; // BUG-073 fix: multiply initial, not current

      // Check if particle died
      if (age + dt >= lifetime) {
        // Queue for sub-emitter processing before freeing index
        if (this.subEmitterSystem) {
          const emitterId = this.particleEmitters.get(i);
          this.subEmitterSystem.queueDeathEvent({ index: i, emitterId });
        }
        // Clean up emitter tracking
        this.particleEmitters.delete(i);
        // BUG-073 fix: Clean up initial values tracking
        this.particleInitialValues.delete(i);
        this.freeIndices.push(i);
        this.state.particleCount--;
        this.emit("particleDeath", { index: i });
      }
    }
  }

  /**
   * Apply audio modulation to parameters
   * Delegates to ParticleAudioReactive
   */
  private applyAudioModulation(): void {
    this.audioSystem?.applyModulation(this.emitters, this.forceFields);
  }

  /**
   * Get audio modulation for a specific parameter
   * Delegates to ParticleAudioReactive
   */
  private getAudioModulation(
    target: string,
    targetId: string,
    parameter: string,
  ): number | undefined {
    return this.audioSystem?.getModulation(target, targetId, parameter);
  }

  /**
   * Update instance buffer attributes for rendering
   */
  private updateInstanceBuffers(): void {
    if (!this.instancedGeometry) return;

    const buffer =
      this.currentBuffer === "A" ? this.particleBufferA : this.particleBufferB;

    const posAttr = this.instancedGeometry.getAttribute(
      "i_position",
    ) as THREE.InstancedBufferAttribute;
    const velAttr = this.instancedGeometry.getAttribute(
      "i_velocity",
    ) as THREE.InstancedBufferAttribute;
    const lifeAttr = this.instancedGeometry.getAttribute(
      "i_life",
    ) as THREE.InstancedBufferAttribute;
    const physAttr = this.instancedGeometry.getAttribute(
      "i_physical",
    ) as THREE.InstancedBufferAttribute;
    const rotAttr = this.instancedGeometry.getAttribute(
      "i_rotation",
    ) as THREE.InstancedBufferAttribute;
    const colAttr = this.instancedGeometry.getAttribute(
      "i_color",
    ) as THREE.InstancedBufferAttribute;

    // Copy data from particle buffer to instance attributes
    for (let i = 0; i < this.config.maxParticles; i++) {
      const src = i * PARTICLE_STRIDE;

      posAttr.setXYZ(i, buffer[src + 0], buffer[src + 1], buffer[src + 2]);
      velAttr.setXYZ(i, buffer[src + 3], buffer[src + 4], buffer[src + 5]);
      lifeAttr.setXY(i, buffer[src + 6], buffer[src + 7]);
      physAttr.setXY(i, buffer[src + 8], buffer[src + 9]);
      rotAttr.setXY(i, buffer[src + 10], buffer[src + 11]);
      colAttr.setXYZW(
        i,
        buffer[src + 12],
        buffer[src + 13],
        buffer[src + 14],
        buffer[src + 15],
      );
    }

    posAttr.needsUpdate = true;
    velAttr.needsUpdate = true;
    lifeAttr.needsUpdate = true;
    physAttr.needsUpdate = true;
    rotAttr.needsUpdate = true;
    colAttr.needsUpdate = true;
  }

  // ============================================================================
  // Audio Integration - delegates to ParticleAudioReactive
  // ============================================================================

  /**
   * Set audio feature value
   */
  setAudioFeature(feature: AudioFeature, value: number): void {
    this.audioSystem?.setFeature(feature, value);
    this.state.currentAudioFeatures.set(feature, value);
  }

  /**
   * Trigger beat event
   */
  triggerBeat(): void {
    this.audioSystem?.triggerBeat();
  }

  /**
   * Trigger burst on all beat-enabled emitters
   */
  triggerBurst(emitterId?: string): void {
    if (emitterId) {
      const emitter = this.emitters.get(emitterId);
      if (emitter) {
        for (let i = 0; i < emitter.burstCount; i++) {
          this.spawnParticle(emitter);
        }
      }
    } else {
      for (const emitter of this.emitters.values()) {
        if (emitter.burstOnBeat && emitter.enabled) {
          for (let i = 0; i < emitter.burstCount; i++) {
            this.spawnParticle(emitter);
          }
        }
      }
    }
  }

  // ============================================================================
  // Rendering
  // ============================================================================

  /**
   * Get the Three.js mesh for adding to scene
   */
  getMesh(): THREE.Mesh | null {
    return this.particleMesh;
  }

  /**
   * Create shader uniforms
   */
  private createUniforms(): Record<string, THREE.IUniform> {
    return {
      diffuseMap: { value: null },
      hasDiffuseMap: { value: 0 },
      proceduralShape: { value: 1 }, // Circle by default
      // Sprite sheet uniforms
      spriteSheetSize: { value: new THREE.Vector2(1, 1) }, // columns, rows
      spriteFrameCount: { value: 1 },
      animateSprite: { value: 0 },
      spriteFrameRate: { value: 10 },
      time: { value: 0 },
      randomStartFrame: { value: 0 }, // BUG-068 fix: Per-particle random start frame
      // Motion blur uniforms
      motionBlurEnabled: { value: this.config.render.motionBlur ? 1 : 0 },
      motionBlurStrength: {
        value: this.config.render.motionBlurStrength ?? 0.1,
      },
      minStretch: { value: this.config.render.minStretch ?? 1.0 },
      maxStretch: { value: this.config.render.maxStretch ?? 4.0 },
      // BUG-072 fix: Color over lifetime texture
      colorOverLifetime: { value: null },
      hasColorOverLifetime: { value: 0 },
    };
  }

  /**
   * Get Three.js blending mode
   */
  private getThreeBlending(): THREE.Blending {
    switch (this.config.render.blendMode) {
      case "additive":
        return THREE.AdditiveBlending;
      case "multiply":
        return THREE.MultiplyBlending;
      case "screen":
        return THREE.CustomBlending;
      default:
        return THREE.NormalBlending;
    }
  }

  // ============================================================================
  // Event System
  // ============================================================================

  on(event: string, handler: ParticleEventHandler): void {
    if (!this.eventHandlers.has(event)) {
      this.eventHandlers.set(event, new Set());
    }
    this.eventHandlers.get(event)?.add(handler);
  }

  off(event: string, handler: ParticleEventHandler): void {
    this.eventHandlers.get(event)?.delete(handler);
  }

  private emit(type: string, data: Record<string, unknown>): void {
    const event: ParticleEvent = {
      type: type as any,
      timestamp: performance.now(),
      data,
    };
    this.eventHandlers.get(type)?.forEach((handler) => handler(event));
  }

  // ============================================================================
  // Utilities
  // ============================================================================

  /**
   * Create seeded random number generator
   * State is tracked externally via currentRngState for save/restore
   */
  private createSeededRandom(seed: number): () => number {
    this.currentRngState = seed;
    return () => {
      this.currentRngState =
        (this.currentRngState * 1103515245 + 12345) & 0x7fffffff;
      return this.currentRngState / 0x7fffffff;
    };
  }

  /**
   * Get current state
   */
  getState(): ParticleSystemState {
    return { ...this.state };
  }

  /**
   * Get current configuration (emitters and force fields)
   */
  getConfig(): { emitters: EmitterConfig[]; forceFields: ForceFieldConfig[] } {
    // Extract EmitterConfig from the stored emitters (removing runtime-only fields)
    const emitters: EmitterConfig[] = Array.from(this.emitters.values()).map(
      (e) => {
        // eslint-disable-next-line @typescript-eslint/no-unused-vars
        const { accumulator, velocity, ...config } = e;
        return config;
      },
    );

    return {
      emitters,
      forceFields: Array.from(this.forceFields.values()),
    };
  }

  // ============================================================================
  // FRAME CACHING METHODS - delegates to ParticleFrameCacheSystem
  // ============================================================================

  /**
   * Cache the current particle state for a specific frame
   */
  cacheCurrentState(frame: number): void {
    if (!this.frameCacheSystem) return;
    const currentBuffer =
      this.currentBuffer === "A" ? this.particleBufferA : this.particleBufferB;
    this.frameCacheSystem.cacheState(
      frame,
      currentBuffer,
      this.freeIndices,
      this.state.particleCount,
      this.state.simulationTime,
      this.currentRngState,
      this.emitters,
      this.particleEmitters, // BUG-063 fix: Cache particle-to-emitter tracking
      this.audioSystem?.getSmoothedAudioValues() ?? new Map(), // BUG-064 fix: Cache audio EMA history
      this.particleInitialValues, // BUG-073 fix: Cache initial size/opacity for modulation
    );
  }

  /**
   * Restore particle state from a cached frame
   */
  restoreFromCache(frame: number): boolean {
    if (!this.frameCacheSystem) return false;
    const cached = this.frameCacheSystem.restoreFromCache(frame);
    if (!cached) return false;

    // Restore particle buffers
    const targetBuffer =
      this.currentBuffer === "A" ? this.particleBufferA : this.particleBufferB;
    targetBuffer.set(cached.particleBuffer);

    // Restore state
    this.freeIndices = [...cached.freeIndices];
    this.state.particleCount = cached.particleCount;
    this.state.simulationTime = cached.simulationTime;
    this.state.frameCount = frame;
    this.frameCacheSystem.setCurrentFrame(frame);

    // Restore RNG state
    this.currentRngState = cached.rngState;

    // Restore emitter accumulators
    for (const [id, accumulator] of cached.emitterAccumulators) {
      const emitter = this.emitters.get(id);
      if (emitter) {
        emitter.accumulator = accumulator;
      }
    }

    // BUG-063 fix: Restore particle-to-emitter tracking for sub-emitter filtering
    this.particleEmitters = new Map(cached.particleEmitters);

    // BUG-064 fix: Restore audio EMA smoothed values for deterministic audio reactivity
    this.audioSystem?.setSmoothedAudioValues(cached.audioSmoothedValues);

    // BUG-073 fix: Restore initial size/opacity values for lifetime modulation
    this.particleInitialValues = new Map(cached.particleInitialValues);

    this.updateInstanceBuffers();
    return true;
  }

  /**
   * Find the nearest cached frame at or before the target frame
   */
  findNearestCache(targetFrame: number): number {
    return this.frameCacheSystem?.findNearestCache(targetFrame) ?? -1;
  }

  /**
   * Clear all cached frames
   */
  clearCache(): void {
    this.frameCacheSystem?.clearCache();
  }

  /**
   * Invalidate the cache by incrementing version
   */
  invalidateCache(): void {
    this.frameCacheSystem?.invalidateCache();
  }

  /**
   * Simulate particles to a specific frame, using cache when available
   */
  simulateToFrame(targetFrame: number, fps: number = 16): number {
    if (!this.frameCacheSystem) return 0;
    const deltaTime = 1 / fps;
    const currentFrame = this.frameCacheSystem.getCurrentFrame();

    // If we're already at this frame, nothing to do
    if (currentFrame === targetFrame) {
      return 0;
    }

    // Check if we can continue from current position (forward scrubbing)
    if (this.frameCacheSystem.canContinueFrom(targetFrame)) {
      let steps = 0;
      for (let f = currentFrame + 1; f <= targetFrame; f++) {
        this.step(deltaTime);
        this.frameCacheSystem.setCurrentFrame(f);
        if (this.frameCacheSystem.shouldCacheFrame(f)) {
          this.cacheCurrentState(f);
        }
        steps++;
      }
      return steps;
    }

    // Find nearest cached frame before target
    const nearestCache = this.findNearestCache(targetFrame);
    let startFrame = 0;
    if (nearestCache >= 0 && this.restoreFromCache(nearestCache)) {
      startFrame = nearestCache;
    }

    // If starting from 0, reset first
    if (startFrame === 0) {
      this.reset();
      const warmupFrames = this.config.warmupFrames || 0;
      if (warmupFrames > 0) {
        for (let w = 0; w < warmupFrames; w++) {
          this.step(deltaTime);
        }
        this.state.frameCount = 0;
        this.state.simulationTime = 0;
      }
      this.frameCacheSystem.setCurrentFrame(0);
      this.cacheCurrentState(0);
    }

    // Simulate forward to target frame
    let steps = 0;
    for (let f = startFrame + 1; f <= targetFrame; f++) {
      this.step(deltaTime);
      this.frameCacheSystem.setCurrentFrame(f);
      if (this.frameCacheSystem.shouldCacheFrame(f)) {
        this.cacheCurrentState(f);
      }
      steps++;
    }
    return steps;
  }

  /**
   * Get cache statistics for debugging/UI
   */
  getCacheStats(): {
    cachedFrames: number;
    version: number;
    currentFrame: number;
    cacheInterval: number;
    maxCacheSize: number;
  } {
    return (
      this.frameCacheSystem?.getStats() ?? {
        cachedFrames: 0,
        version: 0,
        currentFrame: -1,
        cacheInterval: 5,
        maxCacheSize: 200,
      }
    );
  }

  /**
   * Set the cache interval (how often to cache frames)
   */
  setCacheInterval(interval: number): void {
    this.frameCacheSystem?.setCacheInterval(interval);
  }

  /**
   * Reset the particle system
   * DETERMINISM: Resets RNG to initial seed for reproducible simulation
   */
  reset(): void {
    this.particleBufferA.fill(0);
    this.particleBufferB.fill(0);
    this.freeIndices = [];
    for (let i = this.config.maxParticles - 1; i >= 0; i--) {
      this.freeIndices.push(i);
    }
    this.state.particleCount = 0;
    this.state.simulationTime = 0;
    this.state.frameCount = 0;
    // Clear particle-to-emitter tracking
    this.particleEmitters.clear();
    // BUG-073 fix: Clear initial values tracking
    this.particleInitialValues.clear();
    // Reset shared spatial hash
    if (this.spatialHash) {
      this.spatialHash.clear();
    }
    // Reset flocking system
    if (this.flockingSystem) {
      this.flockingSystem.reset();
    }
    // Reset sub-emitter system
    if (this.subEmitterSystem) {
      this.subEmitterSystem.reset();
    }

    // Reset emitter accumulators
    for (const emitter of this.emitters.values()) {
      emitter.accumulator = 0;
    }

    // Reset frame cache tracking
    this.frameCacheSystem?.setCurrentFrame(-1);

    // Reset RNG to initial seed for deterministic replay
    // Use stored initialRngSeed to ensure reset() produces same results as initial state
    this.rng = this.createSeededRandom(this.initialRngSeed);

    // Reset trail system
    this.trailSystem?.reset();

    // Reset connection system
    this.connectionSystem?.reset();

    // Reset audio system
    this.audioSystem?.reset();
  }

  /**
   * Get the current seed
   */
  getSeed(): number {
    return this.config.randomSeed ?? 12345;
  }

  /**
   * Set a new seed and reset the system
   * DETERMINISM: Used to ensure layer-specific reproducible seeds
   */
  setSeed(seed: number): void {
    this.config.randomSeed = seed;
    this.initialRngSeed = seed;
    this.clearCache(); // Seed change invalidates all cached data
    this.reset();
  }

  /**
   * Dispose all resources
   */
  dispose(): void {
    // Dispose Three.js resources
    this.instancedGeometry?.dispose();
    this.material?.dispose();
    this.sizeOverLifetimeTexture?.dispose();
    this.opacityOverLifetimeTexture?.dispose();
    this.colorOverLifetimeTexture?.dispose();

    // Dispose trail system
    if (this.trailSystem) {
      this.trailSystem.dispose();
      this.trailSystem = null;
    }

    // Dispose connection system
    if (this.connectionSystem) {
      this.connectionSystem.dispose();
      this.connectionSystem = null;
    }

    // Dispose GPU physics resources (handles WebGPU and Transform Feedback cleanup)
    if (this.gpuPhysics) {
      this.gpuPhysics.dispose();
      this.gpuPhysics = null;
    }

    // Dispose extracted subsystems
    this.textureSystem?.dispose();
    this.textureSystem = null;
    this.audioSystem?.clear();
    this.audioSystem = null;
    this.frameCacheSystem?.clearCache();
    this.frameCacheSystem = null;

    // Clear collections
    this.emitters.clear();
    this.forceFields.clear();
    this.subEmitters.clear();
    this.eventHandlers.clear();
  }
}

export default GPUParticleSystem;
