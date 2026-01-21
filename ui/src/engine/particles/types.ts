/**
 * GPU Particle System - Type Definitions
 *
 * Production-grade particle system with:
 * - GPU-accelerated physics via WebGL2 transform feedback
 * - Instanced rendering for 100k+ particles
 * - Full 3D physics with mass, drag, and forces
 * - Behavioral systems (flocking, avoidance, following)
 * - Audio/MIDI reactivity
 * - Soft shadows and ambient occlusion
 */

import type * as THREE from "three";

// ============================================================================
// Constants
// ============================================================================

/**
 * Number of floats per particle in GPU buffers
 * Total: 16 floats = 64 bytes (cache-line aligned)
 */
export const PARTICLE_STRIDE = 16;

/**
 * Maximum number of particle groups
 * Groups allow particles to be organized for selective interactions
 */
export const MAX_PARTICLE_GROUPS = 32;

// ============================================================================
// Spatial Hash Interface
// ============================================================================

/**
 * Common interface for spatial hash implementations
 *
 * PROVEN: Any implementation must satisfy completeness guarantee:
 * Lean4: theorem spatial_hash_complete :
 *   ∀ p1 p2, distSq p1 p2 ≤ cellSize² → cellNeighbors (cell p1) (cell p2)
 *
 * This interface allows VerifiedSpatialHashAdapter to be used interchangeably
 * with SpatialHashGrid in collision and flocking systems.
 */
export interface ISpatialHash {
  /**
   * Rebuild spatial hash from particle buffer
   * @param particleBuffer - Particle data in AOS format
   */
  rebuild(particleBuffer: Float32Array): void;

  /**
   * Get neighbors of a position (generator for memory efficiency)
   *
   * PROVEN: Returns all particles within 3x3x3 cell neighborhood
   *
   * @param px - X coordinate
   * @param py - Y coordinate
   * @param pz - Z coordinate
   * @returns Generator yielding neighbor particle indices
   */
  getNeighbors(px: number, py: number, pz: number): Generator<number, void, unknown>;

}

// ============================================================================
// Particle Groups
// ============================================================================

/**
 * Particle group configuration
 * Groups allow organizing particles for selective collisions/connections
 */
export interface ParticleGroupConfig {
  /** Unique group identifier */
  id: string;
  /** Human-readable group name */
  name: string;
  /** Group index (0-31, used for bitmask operations) */
  index: number;
  /** Group color for visualization */
  color?: [number, number, number];
  /** Whether this group participates in collisions */
  enableCollision?: boolean;
  /** Which other groups this group can collide with (bitmask) */
  collisionMask?: number;
  /** Whether this group participates in connections */
  enableConnections?: boolean;
  /** Which other groups this group can connect with (bitmask) */
  connectionMask?: number;
}

// ============================================================================
// Core Particle Data (GPU-side, tightly packed for performance)
// ============================================================================

/**
 * Per-particle attributes stored in GPU buffers
 * Total: 64 bytes per particle (cache-line aligned)
 */
export interface ParticleGPUData {
  // Position (12 bytes)
  positionX: number;
  positionY: number;
  positionZ: number;

  // Velocity (12 bytes)
  velocityX: number;
  velocityY: number;
  velocityZ: number;

  // Life (8 bytes)
  age: number;
  lifetime: number;

  // Physical properties (8 bytes)
  mass: number;
  size: number;

  // Rotation (8 bytes)
  rotation: number;
  angularVelocity: number;

  // Color (16 bytes - RGBA + target RGBA for interpolation)
  colorR: number;
  colorG: number;
  colorB: number;
  colorA: number;
}

// ============================================================================
// Emitter Types
// ============================================================================

export type EmitterShape =
  | "point"
  | "line"
  | "circle"
  | "sphere"
  | "box"
  | "cone"
  | "mesh"
  | "spline"
  | "image" // Emit from non-transparent pixels
  | "depthEdge"; // Emit from depth discontinuities

export interface EmitterShapeConfig {
  type: EmitterShape;

  // Point: no additional config

  // Line
  lineStart?: { x: number; y: number; z: number };
  lineEnd?: { x: number; y: number; z: number };

  // Circle/Sphere
  radius?: number;
  radiusVariance?: number;
  emitFromEdge?: boolean; // Edge only vs filled

  // Box
  boxSize?: { x: number; y: number; z: number };

  // Cone
  coneAngle?: number;
  coneRadius?: number;
  coneLength?: number;

  // Mesh (vertex emission)
  meshVertices?: Float32Array;
  meshNormals?: Float32Array;

  // Spline
  splineId?: string;
  splineOffset?: number; // 0-1 along path

  // Image-based
  imageData?: ImageData;
  depthData?: Float32Array;
  emissionThreshold?: number;
}

export interface EmitterConfig {
  id: string;
  name: string;
  enabled: boolean;

  // Position & orientation
  position: { x: number; y: number; z: number };
  rotation: { x: number; y: number; z: number };

  // Shape
  shape: EmitterShapeConfig;

  // Emission
  emissionRate: number; // Particles per second
  emissionRateVariance: number;
  burstCount: number; // For burst emission
  burstInterval: number; // Frames between bursts (0 = manual)

  // Initial particle properties
  initialSpeed: number;
  speedVariance: number;
  inheritEmitterVelocity: number; // 0-1

  initialSize: number;
  sizeVariance: number;

  initialMass: number;
  massVariance: number;

  lifetime: number;
  lifetimeVariance: number;

  initialRotation: number;
  rotationVariance: number;
  initialAngularVelocity: number;
  angularVelocityVariance: number;

  // Color
  colorStart: [number, number, number, number];
  colorEnd: [number, number, number, number];
  colorVariance: number;

  // Direction
  emissionDirection: { x: number; y: number; z: number };
  emissionSpread: number; // Cone angle in degrees

  // Audio reactivity
  burstOnBeat: boolean;
  beatEmissionMultiplier: number;

  // Sub-emitter reference
  subEmitterId?: string;

  // Particle group assignment (for selective collisions/connections)
  groupId?: string;  // Group ID that spawned particles belong to
  groupIndex?: number;  // Group index (0-31) for bitmask operations
}

// ============================================================================
// Force Fields
// ============================================================================

export type ForceFieldType =
  | "gravity" // Directional gravity (GPU type 0)
  | "point" // Point attractor/repeller (GPU type 1)
  | "vortex" // Rotational force (GPU type 2)
  | "turbulence" // Noise-based displacement (GPU type 3)
  | "drag" // Velocity damping (GPU type 4)
  | "wind" // Directional with gusts (GPU type 5)
  | "lorenz" // Strange attractor (GPU type 6)
  | "curl" // Curl noise for fluid-like motion (GPU type 7)
  | "magnetic" // Lorentz force (velocity-dependent) (GPU type 8)
  | "orbit" // Orbital/centripetal force (GPU type 9)
  | "bounds" // Bounding box/sphere containment
  | "collision" // Surface collision
  | "noise" // General noise displacement
  | "path"; // Follow spline

export interface ForceFieldConfig {
  id: string;
  name: string;
  type: ForceFieldType;
  enabled: boolean;
  strength: number;

  // Spatial bounds
  position: { x: number; y: number; z: number };
  falloffStart: number;
  falloffEnd: number;
  falloffType: "none" | "linear" | "quadratic" | "exponential" | "smoothstep";

  // Type-specific parameters

  // Gravity
  direction?: { x: number; y: number; z: number };

  // Point attractor
  attractorMass?: number;

  // Vortex
  vortexAxis?: { x: number; y: number; z: number };
  inwardForce?: number;

  // Turbulence/Noise
  noiseScale?: number;
  noiseSpeed?: number;
  noiseOctaves?: number;
  noiseLacunarity?: number;
  noiseGain?: number;

  // Wind
  windDirection?: { x: number; y: number; z: number };
  gustStrength?: number;
  gustFrequency?: number;

  // Drag
  dragCoefficient?: number;
  linearDrag?: number;
  quadraticDrag?: number;

  // Bounds
  boundsMin?: { x: number; y: number; z: number };
  boundsMax?: { x: number; y: number; z: number };
  boundsBehavior?: "none" | "kill" | "bounce" | "wrap" | "clamp" | "stick";
  bounceDamping?: number;

  // Collision
  collisionMesh?: Float32Array;
  collisionRestitution?: number;
  collisionFriction?: number;

  // Path following
  pathSplineId?: string;
  pathStrength?: number;
  pathRadius?: number;

  // Lorenz attractor
  lorenzSigma?: number;
  lorenzRho?: number;
  lorenzBeta?: number;

  // Audio modulation
  audioModulation?: {
    feature: string;
    parameter: string;
    min: number;
    max: number;
  };
}

// ============================================================================
// Behavioral Systems
// ============================================================================

export interface FlockingConfig {
  enabled: boolean;

  // Separation (avoid crowding)
  separationWeight: number;
  separationRadius: number;

  // Alignment (match velocity)
  alignmentWeight: number;
  alignmentRadius: number;

  // Cohesion (move toward center)
  cohesionWeight: number;
  cohesionRadius: number;

  // Perception
  perceptionAngle: number; // Field of view in degrees
  maxSpeed: number;
  maxForce: number;

  // Group behavior
  groupId?: string; // Only flock with same group
}

export interface AvoidanceConfig {
  enabled: boolean;

  // Obstacles to avoid
  obstacles: Array<{
    type: "sphere" | "box" | "mesh";
    position: { x: number; y: number; z: number };
    size: { x: number; y: number; z: number };
    meshData?: Float32Array;
  }>;

  avoidanceRadius: number;
  avoidanceStrength: number;
  predictionTime: number; // Look ahead for collision
}

export interface PathFollowConfig {
  enabled: boolean;
  splineId: string;

  followStrength: number;
  arrivalRadius: number; // Slow down when close
  loopBehavior: "stop" | "loop" | "pingpong";

  speedAlongPath: number;
  speedVariance: number;

  offsetRadius: number; // Random offset from path
}

// ============================================================================
// Sub-Emitter System
// ============================================================================

export type SubEmitterTrigger =
  | "birth"
  | "death"
  | "collision"
  | "age" // At specific age percentage
  | "manual"; // Triggered by event

export interface SubEmitterConfig {
  id: string;
  parentEmitterId: string;
  trigger: SubEmitterTrigger;

  // Trigger conditions
  triggerProbability: number; // 0-1
  triggerAgeMin?: number; // For 'age' trigger
  triggerAgeMax?: number;
  maxTriggersPerParticle?: number;

  // Emission
  emitCount: number;
  emitCountVariance: number;

  // Inheritance
  inheritPosition: boolean;
  inheritVelocity: number; // 0-1 multiplier
  inheritSize: number;
  inheritColor: number;
  inheritRotation: number;

  // Override emitter settings
  overrides: Partial<EmitterConfig>;
}

// ============================================================================
// Rendering
// ============================================================================

export type ParticleRenderMode =
  | "billboard" // Always face camera
  | "stretchedBillboard" // Stretch along velocity
  | "mesh" // 3D mesh per particle
  | "trail" // Connected trail
  | "ribbon" // Width-varying trail
  | "point"; // GL points (fastest)

export interface ParticleTextureConfig {
  diffuseMap?: string; // URL or data URI
  normalMap?: string;
  emissiveMap?: string;

  // Sprite sheet
  spriteSheetColumns?: number;
  spriteSheetRows?: number;
  animateSprite?: boolean;
  spriteFrameRate?: number;
  randomStartFrame?: boolean;

  // Procedural
  proceduralType?:
    | "circle"
    | "square"
    | "star"
    | "ring"
    | "noise"
    | "line"
    | "triangle"
    | "shadedSphere"
    | "fadedSphere";
  proceduralParams?: Record<string, number>;
}

export interface ParticleShadowConfig {
  castShadows: boolean;
  receiveShadows: boolean;

  // Soft shadows
  shadowSoftness: number;
  shadowBias: number;

  // Ambient occlusion
  aoEnabled: boolean;
  aoRadius: number;
  aoIntensity: number;
  aoSamples: number;
}

export interface ParticleLightingConfig {
  receiveLighting: boolean;

  // Material properties
  roughness: number;
  metalness: number;
  emissiveIntensity: number;

  // Subsurface scattering (for soft particles)
  subsurfaceScattering: boolean;
  subsurfaceColor: [number, number, number];
  subsurfaceRadius: number;
}

export interface RenderConfig {
  mode: ParticleRenderMode;

  // Billboard
  sortByDepth: boolean;
  depthWrite: boolean;
  depthTest: boolean;

  // Blending
  blendMode: "normal" | "additive" | "multiply" | "screen" | "premultiplied";

  // Stretched billboard
  stretchFactor: number;
  minStretch: number;
  maxStretch: number;

  // Trail/Ribbon
  trailLength: number;
  trailSegments: number;
  trailWidthStart: number;
  trailWidthEnd: number;
  trailFadeMode: "none" | "alpha" | "width" | "both";

  // Mesh rendering
  /** 
   * Mesh geometry type for 3D particle rendering
   * 'billboard' = standard 2D sprite (default)
   * 'cube', 'sphere', 'cylinder', etc. = built-in 3D shapes
   * 'custom' = use customMeshGeometry
   */
  meshGeometry: 'billboard' | 'cube' | 'sphere' | 'cylinder' | 'cone' | 'torus' | 'octahedron' | 'icosahedron' | 'custom';
  
  /** Custom geometry (when meshGeometry === 'custom') */
  customMeshGeometry?: THREE.BufferGeometry;

  // Textures
  texture: ParticleTextureConfig;

  // Shadows & lighting
  shadow: ParticleShadowConfig;
  lighting: ParticleLightingConfig;

  // Motion blur
  motionBlur: boolean;
  motionBlurSamples: number;
  motionBlurStrength: number;

  // LOD
  lodEnabled: boolean;
  lodDistances: number[];
  lodSizeMultipliers: number[];

  // Depth of Field
  dofEnabled?: boolean;
  dofFocusDistance?: number;  // Distance from camera to focus plane
  dofFocusRange?: number;     // Range around focus distance that's in focus
  dofMaxBlur?: number;        // Maximum blur amount (0-1, affects alpha)
}

// ============================================================================
// Modulation Over Lifetime
// ============================================================================

export type ModulationCurve =
  | { type: "constant"; value: number }
  | { type: "linear"; start: number; end: number }
  | {
      type: "curve";
      points: Array<{
        time: number;
        value: number;
        inTangent?: number;
        outTangent?: number;
      }>;
    }
  | { type: "random"; min: number; max: number }
  | {
      type: "randomCurve";
      minCurve: ModulationCurve;
      maxCurve: ModulationCurve;
    };

export interface LifetimeModulation {
  // Size
  sizeOverLifetime?: ModulationCurve;

  // Velocity
  speedOverLifetime?: ModulationCurve;
  velocityDamping?: ModulationCurve;

  // Rotation
  rotationOverLifetime?: ModulationCurve;
  rotationSpeedOverLifetime?: ModulationCurve;
  angularVelocityOverLifetime?: ModulationCurve;

  // Color
  colorOverLifetime?: Array<{
    time: number;
    color: [number, number, number, number];
  }>;

  // Opacity
  opacityOverLifetime?: ModulationCurve;

  // Physics modifiers
  gravityModifier?: ModulationCurve;
  dragOverLifetime?: ModulationCurve;

  // Noise
  noiseOverLifetime?: ModulationCurve;
  noiseAmplitudeOverLifetime?: ModulationCurve;
}

// ============================================================================
// Audio Reactivity
// ============================================================================

// AudioFeature type - must match getFeatureAtFrame() switch cases in audioFeatures.ts
// Note: 'bpm' excluded - use getBPM(analysis) for track-level BPM
export type AudioFeature =
  // Basic features
  | "amplitude"
  | "rms"
  | "spectralCentroid"
  | "onsets"
  | "peaks" // Peak detection feature for isPeakAtFrame()
  // Frequency bands
  | "sub"
  | "bass"
  | "lowMid"
  | "mid"
  | "highMid"
  | "high"
  // Spectral features
  | "spectralFlux"
  | "zeroCrossingRate"
  | "zcr"
  | "spectralRolloff"
  | "rolloff"
  | "spectralFlatness"
  | "flatness"
  // Chroma (pitch class)
  | "chromaEnergy"
  | "chromaC"
  | "chromaCs"
  | "chromaDb"
  | "chromaD"
  | "chromaDs"
  | "chromaEb"
  | "chromaE"
  | "chromaF"
  | "chromaFs"
  | "chromaGb"
  | "chromaG"
  | "chromaGs"
  | "chromaAb"
  | "chromaA"
  | "chromaAs"
  | "chromaBb"
  | "chromaB"
  // HPSS (Harmonic-Percussive Source Separation)
  | "harmonicEnergy"
  | "harmonic"
  | "percussiveEnergy"
  | "percussive"
  | "hpRatio"
  | "harmonicPercussiveRatio"
  // MFCC (timbral features)
  | "mfcc0"
  | "mfcc1"
  | "mfcc2"
  | "mfcc3"
  | "mfcc4"
  | "mfcc5"
  | "mfcc6"
  | "mfcc7"
  | "mfcc8"
  | "mfcc9"
  | "mfcc10"
  | "mfcc11"
  | "mfcc12";

export interface AudioBinding {
  feature: AudioFeature;
  smoothing: number; // 0-1, temporal smoothing
  min: number; // Feature value mapping
  max: number;

  // Target
  target: "emitter" | "forceField" | "system";
  targetId: string;
  parameter: string;

  // Mapping
  outputMin: number;
  outputMax: number;
  curve: "linear" | "exponential" | "logarithmic" | "step";
  stepCount?: number; // Number of discrete steps for 'step' curve (default: 5)

  // Trigger mode (for discrete events)
  triggerMode?: "continuous" | "onThreshold" | "onBeat";
  threshold?: number;
}

// ============================================================================
// Main System Config
// ============================================================================

export interface GPUParticleSystemConfig {
  // Capacity
  maxParticles: number;

  // Simulation
  simulationSpace: "local" | "world";
  deltaTimeMode: "variable" | "fixed";
  fixedDeltaTime: number;
  timeScale: number;

  // Warm-up
  warmupFrames: number;

  // Components
  emitters: EmitterConfig[];
  forceFields: ForceFieldConfig[];
  subEmitters: SubEmitterConfig[];

  // Behaviors
  flocking?: FlockingConfig;
  avoidance?: AvoidanceConfig;
  pathFollow?: PathFollowConfig;

  // Lifetime modulation
  lifetimeModulation: LifetimeModulation;

  // Rendering
  render: RenderConfig;

  // Audio
  audioBindings: AudioBinding[];

  // Feature flags
  useVerifiedSystem?: boolean; // Use mathematically-verified particle system (Phase 6+)

  // Optimization
  spatialHashCellSize: number; // For neighbor queries
  updateFrequency: number; // Frames between full updates (1 = every frame)
  cullOffscreen: boolean;

  // Seeds for reproducibility
  randomSeed?: number;

  // Particle groups (for selective interactions)
  groups?: ParticleGroupConfig[];
}

// ============================================================================
// Runtime State
// ============================================================================

export interface ParticleSystemState {
  particleCount: number;
  activeEmitters: number;
  simulationTime: number;
  frameCount: number;

  // Performance metrics
  updateTimeMs: number;
  renderTimeMs: number;
  gpuMemoryBytes: number;

  // Audio state
  currentAudioFeatures: Map<AudioFeature, number>;
}

// ============================================================================
// Events
// ============================================================================

export type ParticleEventType =
  | "particleBirth"
  | "particleDeath"
  | "particleCollision"
  | "emitterBurst"
  | "systemReset"
  | "audioTrigger";

/**
 * Particle event data - explicit properties for each event type
 *
 * Event types and their data:
 * - particleBirth: { index, emitterId }
 * - particleDeath: { index }
 * - particleCollision: { index, collisionPoint, collisionNormal }
 * - emitterBurst: { emitterId, count }
 * - systemReset: {}
 * - audioTrigger: { feature, value }
 */
export interface ParticleEventData {
  /** Particle index in buffer */
  index?: number;
  /** Emitter that spawned the particle */
  emitterId?: string;
  /** Number of particles in burst */
  count?: number;
  /** Collision point in world space */
  collisionPoint?: { x: number; y: number; z: number };
  /** Collision surface normal */
  collisionNormal?: { x: number; y: number; z: number };
  /** Audio feature name for audio triggers */
  feature?: string;
  /** Audio feature value */
  value?: number;
}

export interface ParticleEvent {
  type: ParticleEventType;
  timestamp: number;
  data: ParticleEventData;
}

export type ParticleEventHandler = (event: ParticleEvent) => void;

// ============================================================================
// Connection System (lines between nearby particles)
// ============================================================================

export interface ConnectionConfig {
  enabled: boolean;
  maxDistance: number; // Maximum distance for connection
  maxConnections: number; // Max connections per particle
  lineWidth: number;
  lineOpacity: number;
  fadeByDistance: boolean; // Fade opacity based on distance
  color?: [number, number, number]; // Optional override color
}

// ============================================================================
// Exported Particle Data
// ============================================================================

/**
 * Exported particle data for baking to keyframes or external tools
 */
export interface ExportedParticle {
  id: number;
  x: number;
  y: number;
  z: number;
  vx: number;
  vy: number;
  vz: number;
  age: number;
  lifetime: number;
  size: number;
  opacity: number;
  r: number;
  g: number;
  b: number;
  rotation: number;
  emitterId: string;
}
