// ============================================================
// PARTICLE TYPES - Particle system configuration
// ============================================================
// Extracted from project.ts for better modularity
// ============================================================

import type { AnimatableProperty } from "./animation";
import type { BlendMode } from "./blendModes";

// ============================================================
// LEGACY PARTICLE DATA (for backwards compatibility)
// ============================================================

export interface ParticleData {
  emitter: ParticleEmitter;
  texture: ParticleTexture;
  physics: ParticlePhysics;
  rendering: ParticleRendering;
}

export interface ParticleEmitter {
  type: "point" | "line" | "circle" | "box" | "path";
  position: AnimatableProperty<{ x: number; y: number }>;

  // For path emitter - particles spawn along a spline
  pathLayerId?: string;

  // Emission parameters
  rate: AnimatableProperty<number>; // Particles per frame
  lifetime: AnimatableProperty<number>; // Frames until death
  lifetimeVariance: number; // 0-1 randomness

  // Initial velocity
  speed: AnimatableProperty<number>;
  speedVariance: number;
  direction: AnimatableProperty<number>; // Degrees
  spread: AnimatableProperty<number>; // Cone angle

  // Emission shape parameters
  radius?: AnimatableProperty<number>; // For circle
  width?: AnimatableProperty<number>; // For box
  height?: AnimatableProperty<number>; // For box
}

export interface ParticleTexture {
  type: "builtin" | "image" | "generated" | "extracted";

  // Built-in shapes
  builtinShape?: "circle" | "square" | "star" | "spark" | "smoke";

  // Custom image
  imageAssetId?: string;

  // AI-generated (SDXL)
  generatedPrompt?: string;

  // Extracted from image (MatSeg)
  extractedFromAssetId?: string;
  extractedRegion?: { x: number; y: number; width: number; height: number };

  // PBR maps (optional, for 3D-like rendering)
  albedo?: string; // Base64
  normal?: string;
  roughness?: string;
}

export interface ParticlePhysics {
  gravity: AnimatableProperty<{ x: number; y: number }>;
  wind: AnimatableProperty<{ x: number; y: number }>;
  drag: AnimatableProperty<number>; // 0-1, air resistance
  turbulence: AnimatableProperty<number>; // Random motion
  turbulenceScale: number; // Noise scale

  // Collision (optional, uses depth map)
  depthCollision: boolean;
  depthLayerId?: string;
  bounciness: number;
}

export interface ParticleRendering {
  startSize: AnimatableProperty<number>;
  endSize: AnimatableProperty<number>;
  sizeVariance: number;

  startColor: AnimatableProperty<string>; // Hex
  endColor: AnimatableProperty<string>;
  colorVariance: number;

  startOpacity: AnimatableProperty<number>;
  endOpacity: AnimatableProperty<number>;

  rotation: AnimatableProperty<number>;
  rotationSpeed: AnimatableProperty<number>;

  blendMode: BlendMode;

  // Advanced
  stretchToVelocity: boolean;
  stretchFactor: number;
}

// ============================================================
// NEW PARTICLE SYSTEM LAYER DATA (matching RyanOnTheInside)
// ============================================================

export interface ParticleLayerData {
  systemConfig: ParticleSystemLayerConfig;
  emitters: ParticleEmitterConfig[];
  gravityWells: GravityWellConfig[];
  vortices: VortexConfig[];
  modulations: ParticleModulationConfig[];
  renderOptions: ParticleRenderOptions;
  turbulenceFields?: TurbulenceFieldConfig[];
  subEmitters?: SubEmitterConfig[];
  flocking?: FlockingConfig;
  collision?: CollisionConfig;
  audioBindings?: AudioBindingConfig[];

  // Time remapping support (like VideoLayer)
  speedMapEnabled?: boolean;
  speedMap?: import("./animation").AnimatableProperty<number>;

  // CC Particle World style visualization
  visualization?: ParticleVisualizationConfig;

  // Particle groups for selective interactions
  groups?: ParticleGroupConfig[];

  // Spring system for cloth/soft body simulation
  springConfig?: SpringSystemConfig;

  // SPH fluid simulation
  sphConfig?: SPHFluidConfig;

  // LOD (Level of Detail) config
  lodConfig?: ParticleLODConfig;

  // DOF (Depth of Field) config for particles
  dofConfig?: ParticleDOFConfig;

  // Custom collision planes
  collisionPlanes?: CollisionPlaneConfig[];

  // Particle groups (renamed from 'groups' for clarity)
  particleGroups?: ParticleGroupConfig[];
}

// ============================================================
// LOD (LEVEL OF DETAIL) CONFIGURATION
// ============================================================

export interface ParticleLODConfig {
  enabled: boolean;
  distances: number[]; // [near, mid, far] e.g. [100, 300, 600]
  sizeMultipliers: number[]; // [near, mid, far] e.g. [1.0, 0.5, 0.25]
}

// ============================================================
// DOF (DEPTH OF FIELD) CONFIGURATION FOR PARTICLES
// ============================================================

export interface ParticleDOFConfig {
  enabled: boolean;
  focusDistance: number;
  focusRange: number;
  blurAmount: number; // matches component usage (not maxBlur)
}

// ============================================================
// PARTICLE GROUP CONFIGURATION
// ============================================================

export interface ParticleGroupConfig {
  id: string;
  name: string;
  enabled: boolean;
  color: [number, number, number, number]; // RGBA tint
  collisionMask: number; // Bitmask for which groups this collides with
  connectionMask: number; // Bitmask for which groups this connects to
}

// ============================================================
// SPRING SYSTEM CONFIGURATION (Cloth, Soft Body, Ropes)
// ============================================================

export interface SpringSystemConfig {
  enabled: boolean;
  useVerlet: boolean; // Verlet integration (more stable) vs Euler
  solverIterations: number; // 1-16, more = stiffer but slower
  globalStiffness: number; // 0.001-10000
  globalDamping: number; // 0-1000
  enableBreaking: boolean; // Allow springs to break under tension
  gravity: { x: number; y: number; z: number };
  // Pre-built structures
  structures?: SpringStructure[];
}

export interface SpringStructure {
  id: string;
  type: "cloth" | "rope" | "softbody" | "custom";
  // Cloth-specific
  width?: number; // Particles in X
  height?: number; // Particles in Y
  // Rope-specific
  length?: number; // Number of particles
  // Common
  startParticle: number;
  pinnedParticles: number[]; // Indices of fixed particles
  stiffness: number;
  damping: number;
  breakThreshold: number; // 0 = unbreakable
}

// ============================================================
// SPH FLUID SIMULATION CONFIGURATION
// ============================================================

export interface SPHFluidConfig {
  enabled: boolean;
  preset: "water" | "honey" | "lava" | "gas" | "custom";
  smoothingRadius: number; // h, affects neighbor search
  restDensity: number; // ρ₀, fluid rest density
  gasConstant: number; // k, pressure stiffness
  viscosity: number; // μ, how "thick" the fluid is
  surfaceTension: number; // σ, surface cohesion
  gravity: { x: number; y: number; z: number };
  boundaryDamping: number; // Energy loss at boundaries
}

// CC Particle World style visualization helpers
export interface ParticleVisualizationConfig {
  showHorizon: boolean; // Show horizon line at floor position
  showGrid: boolean; // Show 3D perspective grid
  showAxis: boolean; // Show XYZ axis at origin
  gridSize: number; // Grid cell size in pixels
  gridDepth: number; // Grid depth into Z axis
}

export interface ParticleSystemLayerConfig {
  maxParticles: number;
  gravity: number;
  windStrength: number;
  windDirection: number;
  warmupPeriod: number;
  respectMaskBoundary: boolean;
  boundaryBehavior: "bounce" | "kill" | "wrap";
  friction: number;
  turbulenceFields?: TurbulenceFieldConfig[];
  subEmitters?: SubEmitterConfig[];
  useGPU?: boolean; // Enable WebGPU compute acceleration
}

export interface TurbulenceFieldConfig {
  id: string;
  enabled: boolean;
  scale: number; // Noise frequency, 0.001-0.01 (smaller = larger swirls)
  strength: number; // Force magnitude, 0-500
  evolutionSpeed: number; // How fast noise changes over time, 0-1
  octaves?: number; // Number of noise octaves for detail (default: 1)
  persistence?: number; // Amplitude multiplier per octave (default: 0.5)
  animationSpeed?: number; // Speed of noise evolution animation
}

// Flocking (boids) behavior configuration
export interface FlockingConfig {
  enabled: boolean;
  // Separation - avoid crowding neighbors
  separationWeight: number; // 0-100, strength of separation force
  separationRadius: number; // Pixels, distance to maintain from neighbors
  // Alignment - steer towards average heading of neighbors
  alignmentWeight: number; // 0-100, strength of alignment force
  alignmentRadius: number; // Pixels, radius to find neighbors for alignment
  // Cohesion - steer towards average position of neighbors
  cohesionWeight: number; // 0-100, strength of cohesion force
  cohesionRadius: number; // Pixels, radius to find neighbors for cohesion
  // Limits
  maxSpeed: number; // Maximum particle speed
  maxForce: number; // Maximum steering force
  perceptionAngle: number; // Field of view in degrees (180 = hemisphere)
}

// Collision detection configuration
export interface CollisionConfig {
  enabled: boolean;
  // Particle-particle collision
  particleCollision: boolean;
  particleRadius: number; // Collision radius per particle
  bounciness: number; // 0-1, how much velocity is retained on bounce
  friction: number; // 0-1, velocity reduction on collision
  // Boundary collision
  boundaryEnabled: boolean;
  boundaryBehavior: "none" | "kill" | "bounce" | "wrap" | "stick";
  // Boundary box (relative to composition)
  boundaryPadding: number; // Pixels from edge
  // Floor collision (CC Particle World style)
  floorEnabled?: boolean;
  floorY?: number; // Normalized Y position (0=top, 1=bottom), default 1.0
  floorBehavior?: "none" | "bounce" | "stick" | "kill"; // What happens at floor
  floorFriction?: number; // Surface friction when bouncing/sliding (0-1)
  // Optional ceiling
  ceilingEnabled?: boolean;
  ceilingY?: number; // Normalized Y position (0=top), default 0.0

  // Custom collision planes (walls, floors at any angle)
  planes?: CollisionPlaneConfig[];
}

// Individual collision plane (for walls, floors at any angle)
export interface CollisionPlaneConfig {
  id: string;
  name?: string;
  enabled: boolean;
  // Plane definition (point + normal)
  point: { x: number; y: number; z: number }; // A point on the plane
  normal: { x: number; y: number; z: number }; // Plane normal (outward direction)
  // Physics properties
  bounciness: number; // 0-1
  friction: number; // 0-1
}

export interface ConnectionRenderConfig {
  enabled: boolean;
  maxDistance: number; // Pixels, connect if closer than this
  maxConnections: number; // Per particle, 1-5 (HARD LIMIT for performance)
  lineWidth: number; // 0.5-3
  lineOpacity: number; // 0-1
  fadeByDistance: boolean; // Opacity decreases with distance
  color?: [number, number, number]; // Optional RGB color override (0-1 range)
}

// Audio-reactive particle binding
export type AudioFeatureName =
  | "amplitude"
  | "bass"
  | "mid"
  | "high"
  | "beat"
  | "spectralCentroid";
export type AudioTargetType = "emitter" | "system" | "forceField";
export type AudioCurveType = "linear" | "exponential" | "logarithmic" | "step";

export type AudioTriggerMode = "continuous" | "onThreshold" | "onBeat";

export interface AudioBindingConfig {
  id: string;
  enabled: boolean;
  feature: AudioFeatureName; // Which audio feature to use
  smoothing: number; // 0-1, temporal smoothing
  min: number; // Feature value mapping input min
  max: number; // Feature value mapping input max
  target: AudioTargetType; // What to affect
  targetId: string; // Emitter/force field ID, or 'system'
  parameter: string; // Parameter name (e.g., 'emissionRate', 'size')
  outputMin: number; // Output range min
  outputMax: number; // Output range max
  curve: AudioCurveType; // Response curve
  stepCount?: number; // Number of discrete steps for 'step' curve (default: 5)
  triggerMode?: AudioTriggerMode; // When to apply: continuous, on threshold, or on beat
  threshold?: number; // Threshold value for 'onThreshold' mode (0-1)
}

export interface SubEmitterConfig {
  id: string;
  parentEmitterId: string; // Which emitter's particles trigger this, or '*' for all
  trigger: "death"; // Only death trigger for now
  spawnCount: number; // 1-10 particles on trigger
  inheritVelocity: number; // 0-1, how much parent velocity inherited
  size: number;
  sizeVariance: number;
  lifetime: number; // Frames
  speed: number;
  spread: number; // Degrees, emission cone
  color: [number, number, number];
  enabled: boolean;
}

export type EmitterShape =
  | "point"
  | "line"
  | "circle"
  | "box"
  | "sphere"
  | "ring"
  | "spline"
  | "depth-map"
  | "mask"
  | "cone" // Cone-shaped emission volume
  | "image" // Emit from non-transparent pixels of an image/layer
  | "depthEdge"; // Emit from depth discontinuities (silhouette edges)

// Depth map emission configuration
export interface DepthMapEmission {
  /** Layer ID containing the depth map */
  sourceLayerId: string;
  /** Emit from depth values in this range (0-1) */
  depthMin: number;
  depthMax: number;
  /** Emission density per pixel */
  density: number;
  /** Scale velocity by depth (far particles move slower) */
  velocityByDepth: boolean;
  /** Scale size by depth (far particles appear smaller) */
  sizeByDepth: boolean;
  /** Depth value interpretation */
  depthMode: "near-white" | "near-black";
}

// Mask emission configuration
export interface MaskEmission {
  /** Layer ID containing the mask/matte */
  sourceLayerId: string;
  /** Emit from pixels above this threshold (0-1) */
  threshold: number;
  /** Emission density per pixel */
  density: number;
  /** Use luminance or alpha channel */
  channel: "luminance" | "alpha" | "red" | "green" | "blue";
  /** Invert the mask */
  invert: boolean;
  /** Sample rate (1 = every pixel, 2 = every 2nd pixel, etc.) */
  sampleRate: number;
}

// Spline path emission configuration
export interface SplinePathEmission {
  layerId: string; // ID of the SplineLayer to emit along
  emitMode: "uniform" | "random" | "start" | "end" | "sequential";
  parameter: number; // For 'start'/'end': offset, for 'uniform': interval, for 'sequential': speed
  alignToPath: boolean; // Align emission direction with path tangent
  offset: number; // Perpendicular offset from path (normalized)
  bidirectional: boolean; // Emit from both directions along tangent
}

export interface SpriteConfig {
  enabled: boolean;
  imageUrl: string | null;
  imageData: ImageBitmap | HTMLImageElement | null;
  isSheet: boolean;
  columns: number;
  rows: number;
  totalFrames: number;
  frameRate: number;
  playMode: "loop" | "once" | "pingpong" | "random";
  billboard: boolean;
  rotationEnabled: boolean;
  rotationSpeed: number;
  rotationSpeedVariance: number;
  alignToVelocity: boolean;
}

export interface ParticleEmitterConfig {
  id: string;
  name: string;
  x: number;
  y: number;
  z?: number; // Depth position (CC Particle World Producer Z)
  direction: number;
  spread: number;
  speed: number;
  speedVariance: number;
  size: number;
  sizeVariance: number;
  color: [number, number, number];
  emissionRate: number;
  initialBurst: number;
  particleLifetime: number;
  lifetimeVariance: number;
  enabled: boolean;
  burstOnBeat: boolean;
  burstCount: number;
  // Geometric emitter shape (required by EmitterConfig)
  shape: EmitterShape;
  shapeRadius: number;
  shapeWidth: number;
  shapeHeight: number;
  shapeDepth: number;
  shapeInnerRadius: number;
  emitFromEdge: boolean;
  emitFromVolume: boolean;
  // Spline path emission (when shape = 'spline')
  splinePath: SplinePathEmission | null;
  // Depth map emission (when shape = 'depth-map')
  depthMapEmission?: DepthMapEmission;
  // Mask emission (when shape = 'mask')
  maskEmission?: MaskEmission;
  // Sprite configuration
  sprite: SpriteConfig;

  // ============================================================
  // CONE SHAPE PROPERTIES (when shape = 'cone')
  // ============================================================
  /** Cone opening angle in degrees (0-180) */
  coneAngle?: number;
  /** Cone base radius */
  coneRadius?: number;
  /** Cone length/height */
  coneLength?: number;

  // ============================================================
  // IMAGE SHAPE PROPERTIES (when shape = 'image')
  // Emit from non-transparent pixels of a layer
  // ============================================================
  /** Layer ID to use as emission source */
  imageSourceLayerId?: string;
  /** Minimum alpha threshold for emission (0-1) */
  emissionThreshold?: number;
  /** Emit from edges of the mask only */
  emitFromMaskEdge?: boolean;

  // ============================================================
  // DEPTH EDGE SHAPE PROPERTIES (when shape = 'depthEdge')
  // Emit from depth discontinuities (silhouette edges)
  // ============================================================
  /** Layer ID containing the depth map */
  depthSourceLayerId?: string;
  /** Depth gradient threshold for edge detection */
  depthEdgeThreshold?: number;
  /** Scale factor for Z position from depth */
  depthScale?: number;

  // ============================================================
  // ALTERNATIVE PROPERTY NAMES (for preset compatibility)
  // ============================================================
  /** Alias for particleLifetime (seconds instead of frames) */
  lifespan?: number;
  /** Initial particle size (alias for size) */
  startSize?: number;
  /** Final particle size at end of life */
  endSize?: number;
  /** Initial particle color (hex string) */
  startColor?: string;
  /** Final particle color at end of life (hex string) */
  endColor?: string;
  /** Initial particle opacity (0-1) */
  startOpacity?: number;
  /** Final particle opacity at end of life (0-1) */
  endOpacity?: number;
  /** Velocity spread/variance */
  velocitySpread?: number;
}

export interface GravityWellConfig {
  id: string;
  name: string;
  x: number;
  y: number;
  strength: number;
  radius: number;
  falloff: "linear" | "quadratic" | "constant";
  enabled: boolean;
}

export interface VortexConfig {
  id: string;
  name: string;
  x: number;
  y: number;
  strength: number;
  radius: number;
  rotationSpeed: number;
  inwardPull: number;
  enabled: boolean;
}

export interface ParticleModulationConfig {
  id: string;
  emitterId: string;
  property: "size" | "speed" | "opacity" | "colorR" | "colorG" | "colorB";
  startValue: number;
  endValue: number;
  easing: string;
}

export interface ParticleRenderOptions {
  blendMode: "normal" | "additive" | "multiply" | "screen";
  renderTrails: boolean;
  trailLength: number;
  trailOpacityFalloff: number;
  particleShape: "circle" | "square" | "triangle" | "star";
  glowEnabled: boolean;
  glowRadius: number;
  glowIntensity: number;
  // Motion blur settings
  motionBlur: boolean;
  motionBlurStrength: number; // 0-1, how much to stretch based on velocity
  motionBlurSamples: number; // Number of samples for blur (1-16)
  // Particle connection settings
  connections: ConnectionRenderConfig;
  // Sprite sheet settings
  spriteEnabled?: boolean;
  spriteImageUrl?: string;
  spriteColumns?: number; // Number of columns in sprite sheet
  spriteRows?: number; // Number of rows in sprite sheet
  spriteAnimate?: boolean; // Animate through frames
  spriteFrameRate?: number; // Frames per second
  spriteRandomStart?: boolean; // Start at random frame

  // LOD (Level of Detail) settings - for performance optimization
  lodEnabled?: boolean;
  lodDistances?: number[]; // Distance thresholds [near, mid, far]
  lodSizeMultipliers?: number[]; // Size multipliers at each level

  // Depth of Field settings - for cinematic depth blur
  dofEnabled?: boolean;
  dofFocusDistance?: number; // Distance from camera to focus plane
  dofFocusRange?: number; // Range around focus distance that's in focus
  dofMaxBlur?: number; // Maximum blur amount (0-1)

  // Shadow settings
  shadowsEnabled?: boolean;
  castShadows?: boolean;
  receiveShadows?: boolean;
  shadowSoftness?: number;

  // 3D mesh particles
  meshMode?: "billboard" | "mesh";
  meshGeometry?: "cube" | "sphere" | "cylinder" | "cone" | "torus" | "custom";
}

// ============================================================
// AUDIO PARTICLE MAPPING
// ============================================================

export interface AudioParticleMapping {
  feature: "amplitude" | "rms" | "bass" | "mid" | "high" | "onsets";
  parameter: "emissionRate" | "speed" | "size" | "gravity" | "windStrength";
  emitterId?: string;
  sensitivity: number;
  smoothing: number;
}
