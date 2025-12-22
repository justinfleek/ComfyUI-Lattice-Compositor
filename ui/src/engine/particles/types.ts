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
  | 'point'
  | 'line'
  | 'circle'
  | 'sphere'
  | 'box'
  | 'cone'
  | 'mesh'
  | 'spline'
  | 'image'      // Emit from non-transparent pixels
  | 'depthEdge'; // Emit from depth discontinuities

export interface EmitterShapeConfig {
  type: EmitterShape;

  // Point: no additional config

  // Line
  lineStart?: { x: number; y: number; z: number };
  lineEnd?: { x: number; y: number; z: number };

  // Circle/Sphere
  radius?: number;
  radiusVariance?: number;
  emitFromEdge?: boolean;  // Edge only vs filled

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
  splineOffset?: number;  // 0-1 along path

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
  emissionRate: number;           // Particles per second
  emissionRateVariance: number;
  burstCount: number;             // For burst emission
  burstInterval: number;          // Frames between bursts (0 = manual)

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
  emissionSpread: number;  // Cone angle in degrees

  // Audio reactivity
  burstOnBeat: boolean;
  beatEmissionMultiplier: number;

  // Sub-emitter reference
  subEmitterId?: string;
}

// ============================================================================
// Force Fields
// ============================================================================

export type ForceFieldType =
  | 'gravity'       // Directional gravity (GPU type 0)
  | 'point'         // Point attractor/repeller (GPU type 1)
  | 'vortex'        // Rotational force (GPU type 2)
  | 'turbulence'    // Noise-based displacement (GPU type 3)
  | 'drag'          // Velocity damping (GPU type 4)
  | 'wind'          // Directional with gusts (GPU type 5)
  | 'lorenz'        // Strange attractor (GPU type 6)
  | 'curl'          // Curl noise for fluid-like motion (GPU type 7)
  | 'magnetic'      // Lorentz force (velocity-dependent) (GPU type 8)
  | 'orbit'         // Orbital/centripetal force (GPU type 9)
  | 'bounds'        // Bounding box/sphere containment
  | 'collision'     // Surface collision
  | 'noise'         // General noise displacement
  | 'path';         // Follow spline

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
  falloffType: 'none' | 'linear' | 'quadratic' | 'exponential' | 'smoothstep';

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
  boundsBehavior?: 'kill' | 'bounce' | 'wrap' | 'clamp' | 'stick';
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
  perceptionAngle: number;  // Field of view in degrees
  maxSpeed: number;
  maxForce: number;

  // Group behavior
  groupId?: string;  // Only flock with same group
}

export interface AvoidanceConfig {
  enabled: boolean;

  // Obstacles to avoid
  obstacles: Array<{
    type: 'sphere' | 'box' | 'mesh';
    position: { x: number; y: number; z: number };
    size: { x: number; y: number; z: number };
    meshData?: Float32Array;
  }>;

  avoidanceRadius: number;
  avoidanceStrength: number;
  predictionTime: number;  // Look ahead for collision
}

export interface PathFollowConfig {
  enabled: boolean;
  splineId: string;

  followStrength: number;
  arrivalRadius: number;    // Slow down when close
  loopBehavior: 'stop' | 'loop' | 'pingpong';

  speedAlongPath: number;
  speedVariance: number;

  offsetRadius: number;     // Random offset from path
}

// ============================================================================
// Sub-Emitter System
// ============================================================================

export type SubEmitterTrigger =
  | 'birth'
  | 'death'
  | 'collision'
  | 'age'         // At specific age percentage
  | 'manual';     // Triggered by event

export interface SubEmitterConfig {
  id: string;
  parentEmitterId: string;
  trigger: SubEmitterTrigger;

  // Trigger conditions
  triggerProbability: number;  // 0-1
  triggerAgeMin?: number;      // For 'age' trigger
  triggerAgeMax?: number;
  maxTriggersPerParticle?: number;

  // Emission
  emitCount: number;
  emitCountVariance: number;

  // Inheritance
  inheritPosition: boolean;
  inheritVelocity: number;     // 0-1 multiplier
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
  | 'billboard'      // Always face camera
  | 'stretchedBillboard'  // Stretch along velocity
  | 'mesh'           // 3D mesh per particle
  | 'trail'          // Connected trail
  | 'ribbon'         // Width-varying trail
  | 'point';         // GL points (fastest)

export interface ParticleTextureConfig {
  diffuseMap?: string;        // URL or data URI
  normalMap?: string;
  emissiveMap?: string;

  // Sprite sheet
  spriteSheetColumns?: number;
  spriteSheetRows?: number;
  animateSprite?: boolean;
  spriteFrameRate?: number;
  randomStartFrame?: boolean;

  // Procedural
  proceduralType?: 'circle' | 'square' | 'star' | 'ring' | 'noise' | 'line' | 'triangle' | 'shadedSphere' | 'fadedSphere';
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
  blendMode: 'normal' | 'additive' | 'multiply' | 'screen' | 'premultiplied';

  // Stretched billboard
  stretchFactor: number;
  minStretch: number;
  maxStretch: number;

  // Trail/Ribbon
  trailLength: number;
  trailSegments: number;
  trailWidthStart: number;
  trailWidthEnd: number;
  trailFadeMode: 'none' | 'alpha' | 'size' | 'both';

  // Mesh rendering
  meshGeometry?: string;  // Built-in or custom

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
}

// ============================================================================
// Modulation Over Lifetime
// ============================================================================

export type ModulationCurve =
  | { type: 'constant'; value: number }
  | { type: 'linear'; start: number; end: number }
  | { type: 'curve'; points: Array<{ time: number; value: number; inTangent?: number; outTangent?: number }> }
  | { type: 'random'; min: number; max: number }
  | { type: 'randomCurve'; minCurve: ModulationCurve; maxCurve: ModulationCurve };

export interface LifetimeModulation {
  // Size
  sizeOverLifetime?: ModulationCurve;

  // Velocity
  speedOverLifetime?: ModulationCurve;
  velocityDamping?: ModulationCurve;

  // Rotation
  rotationOverLifetime?: ModulationCurve;
  angularVelocityOverLifetime?: ModulationCurve;

  // Color
  colorOverLifetime?: Array<{ time: number; color: [number, number, number, number] }>;

  // Opacity
  opacityOverLifetime?: ModulationCurve;

  // Noise offset
  noiseOverLifetime?: ModulationCurve;
}

// ============================================================================
// Audio Reactivity
// ============================================================================

export type AudioFeature =
  | 'amplitude'
  | 'rms'
  | 'spectralCentroid'
  | 'bass'
  | 'mid'
  | 'high'
  | 'onset'
  | 'beat'
  | 'bpm'
  | 'pitch'
  | 'loudness';

export interface AudioBinding {
  feature: AudioFeature;
  smoothing: number;        // 0-1, temporal smoothing
  min: number;              // Feature value mapping
  max: number;

  // Target
  target: 'emitter' | 'forceField' | 'system';
  targetId: string;
  parameter: string;

  // Mapping
  outputMin: number;
  outputMax: number;
  curve: 'linear' | 'exponential' | 'logarithmic' | 'step';

  // Trigger mode (for discrete events)
  triggerMode?: 'continuous' | 'onThreshold' | 'onBeat';
  threshold?: number;
}

// ============================================================================
// Main System Config
// ============================================================================

export interface GPUParticleSystemConfig {
  // Capacity
  maxParticles: number;

  // Simulation
  simulationSpace: 'local' | 'world';
  deltaTimeMode: 'variable' | 'fixed';
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

  // Optimization
  spatialHashCellSize: number;  // For neighbor queries
  updateFrequency: number;      // Frames between full updates (1 = every frame)
  cullOffscreen: boolean;

  // Seeds for reproducibility
  randomSeed?: number;
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
  | 'particleBirth'
  | 'particleDeath'
  | 'particleCollision'
  | 'emitterBurst'
  | 'systemReset'
  | 'audioTrigger';

export interface ParticleEvent {
  type: ParticleEventType;
  timestamp: number;
  data: Record<string, unknown>;
}

export type ParticleEventHandler = (event: ParticleEvent) => void;

// ============================================================================
// Connection System (lines between nearby particles)
// ============================================================================

export interface ConnectionConfig {
  enabled: boolean;
  maxDistance: number;      // Maximum distance for connection
  maxConnections: number;   // Max connections per particle
  lineWidth: number;
  lineOpacity: number;
  fadeByDistance: boolean;  // Fade opacity based on distance
  color?: [number, number, number]; // Optional override color
}
