/**
 * Particle System Types
 *
 * All interfaces and type definitions for the particle system.
 * Extracted from particleSystem.ts for modularity.
 */

// ============================================================================
// Core Particle Type
// ============================================================================

export interface Particle {
  id: number;
  x: number;
  y: number;
  prevX: number;
  prevY: number;
  vx: number;
  vy: number;
  age: number;
  lifetime: number;
  size: number;
  baseSize: number;
  color: [number, number, number, number];
  baseColor: [number, number, number, number];
  emitterId: string;
  isSubParticle: boolean;
  // Sprite/texture support
  rotation: number; // Current rotation in radians
  angularVelocity: number; // Rotation speed in radians/frame
  spriteIndex: number; // For sprite sheets (frame index)
  // Collision tracking
  collisionCount: number; // Number of collisions this particle has had
}

// ============================================================================
// Force Field Types
// ============================================================================

export interface TurbulenceConfig {
  id: string;
  enabled: boolean;
  scale: number; // Noise frequency, 0.001-0.01 (smaller = larger swirls)
  strength: number; // Force magnitude, 0-500
  evolutionSpeed: number; // How fast noise changes over time, 0-1
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

// 2D Lorenz-like strange attractor for chaotic motion
export interface LorenzAttractorConfig {
  id: string;
  name: string;
  x: number; // Center position X
  y: number; // Center position Y
  sigma: number; // Lorenz sigma parameter (default: 10)
  rho: number; // Lorenz rho parameter (default: 28)
  beta: number; // Lorenz beta parameter (default: 2.667)
  strength: number; // Force strength multiplier
  radius: number; // Influence radius
  enabled: boolean;
}

// ============================================================================
// Emitter Types
// ============================================================================

// Import and re-export from canonical source
import type { EmitterShape } from "@/types/particles";
export type { EmitterShape };

// Spline path emission configuration
export interface SplinePathEmission {
  layerId: string; // ID of the SplineLayer to emit along
  emitMode: "uniform" | "random" | "start" | "end" | "sequential";
  parameter: number; // For 'start'/'end': offset, for 'uniform': interval, for 'sequential': speed
  alignToPath: boolean; // Align emission direction with path tangent
  offset: number; // Perpendicular offset from path (normalized)
  bidirectional: boolean; // Emit from both directions along tangent
}

// Spline point query result from provider
export interface SplineQueryResult {
  point: { x: number; y: number; z: number };
  tangent: { x: number; y: number };
  length: number;
}

// Spline provider callback type
export type SplinePathProvider = (
  layerId: string,
  t: number,
  frame: number,
) => SplineQueryResult | null;

// Sprite/texture configuration for particles
export interface SpriteConfig {
  enabled: boolean;
  imageUrl: string | null; // URL or data URL for sprite image
  imageData: ImageBitmap | HTMLImageElement | null; // Loaded image data
  // Sprite sheet settings
  isSheet: boolean; // Is this a sprite sheet?
  columns: number; // Grid columns for sprite sheet
  rows: number; // Grid rows for sprite sheet
  totalFrames: number; // Total frames in sheet
  frameRate: number; // Animation FPS
  playMode: "loop" | "once" | "pingpong" | "random";
  // Billboard behavior
  billboard: boolean; // Always face camera
  // Rotation
  rotationEnabled: boolean;
  rotationSpeed: number; // Degrees per frame
  rotationSpeedVariance: number;
  alignToVelocity: boolean; // Rotate to face movement direction
}

export interface EmitterConfig {
  id: string;
  name: string;
  x: number;
  y: number;
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
  // Geometric emitter shape
  shape: EmitterShape;
  // Shape parameters (normalized 0-1 coordinates)
  shapeRadius: number; // For circle, sphere, ring
  shapeWidth: number; // For box, line
  shapeHeight: number; // For box
  shapeDepth: number; // For box (3D), sphere
  shapeInnerRadius: number; // For ring (donut)
  emitFromEdge: boolean; // Emit from edge only (not filled)
  emitFromVolume: boolean; // Emit from volume (3D shapes)
  // Spline path emission (when shape = 'spline')
  splinePath: SplinePathEmission | null;
  // Sprite/texture configuration
  sprite: SpriteConfig;
  // Cone emission parameters (when shape = 'cone')
  coneAngle?: number; // Opening angle in degrees, default 45
  coneRadius?: number; // Base radius, default 0.1
  coneLength?: number; // Cone height, default 0.2
  // Depth map emission parameters (when shape = 'depth-map')
  depthMapEmission?: import("@/types/particles").DepthMapEmission;
  // Mask emission parameters (when shape = 'mask')
  maskEmission?: import("@/types/particles").MaskEmission;
  // Image-based emission parameters (when shape = 'image')
  imageSourceLayerId?: string;
  emissionThreshold?: number;
  // Depth edge emission parameters (when shape = 'depthEdge')
  depthSourceLayerId?: string;
  depthEdgeThreshold?: number;
}

// ============================================================================
// Sub-Emitter Types
// ============================================================================

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

// ============================================================================
// Connection Types
// ============================================================================

export interface ConnectionConfig {
  enabled: boolean;
  maxDistance: number; // Pixels, connect if closer than this
  maxConnections: number; // Per particle, 1-5 (HARD LIMIT for performance)
  lineWidth: number; // 0.5-3
  lineOpacity: number; // 0-1
  fadeByDistance: boolean; // Opacity decreases with distance
}

// ============================================================================
// Collision Types
// ============================================================================

export interface CollisionConfig {
  enabled: boolean;
  // Particle-to-particle collision
  particleCollision: boolean;
  particleCollisionRadius: number; // Multiplier on particle size for collision
  particleCollisionResponse: "bounce" | "absorb" | "explode";
  particleCollisionDamping: number; // 0-1, velocity retained after collision
  // Layer/boundary collision
  layerCollision: boolean;
  layerCollisionLayerId: string | null; // Depth map layer for collision
  layerCollisionThreshold: number; // Depth threshold for collision
  // Floor/ceiling collision
  floorEnabled: boolean;
  floorY: number; // Normalized Y position of floor (0-1)
  ceilingEnabled: boolean;
  ceilingY: number; // Normalized Y position of ceiling
  wallsEnabled: boolean;
  // Collision physics
  bounciness: number; // 0-1, how much velocity is preserved
  friction: number; // Surface friction on collision
  // Spatial hashing for performance
  spatialHashCellSize: number; // Cell size for spatial hash (pixels)
}

// ============================================================================
// Modulation Types
// ============================================================================

export interface ParticleModulation {
  id: string;
  emitterId: string;
  property: "size" | "speed" | "opacity" | "colorR" | "colorG" | "colorB";
  startValue: number;
  endValue: number;
  easing: string;
}

// ============================================================================
// System Configuration Types
// ============================================================================

export interface ParticleSystemConfig {
  maxParticles: number;
  gravity: number;
  windStrength: number;
  windDirection: number;
  warmupPeriod: number;
  respectMaskBoundary: boolean;
  boundaryBehavior: "bounce" | "kill" | "wrap";
  friction: number;
  turbulenceFields: TurbulenceConfig[];
  subEmitters: SubEmitterConfig[];
  // Collision configuration
  collision: CollisionConfig;
}

// ============================================================================
// Render Options Types
// ============================================================================

export interface RenderOptions {
  blendMode: "normal" | "additive" | "multiply" | "screen";
  renderTrails: boolean;
  trailLength: number;
  trailOpacityFalloff: number;
  particleShape: "circle" | "square" | "triangle" | "star" | "sprite";
  glowEnabled: boolean;
  glowRadius: number;
  glowIntensity: number;
  // Motion blur settings
  motionBlur: boolean;
  motionBlurStrength: number; // 0-1, how much to stretch based on velocity
  motionBlurSamples: number; // Number of samples for blur (1-16)
  // Particle connection settings
  connections: ConnectionConfig;
  // Sprite rendering settings
  spriteSmoothing: boolean; // Enable image smoothing for sprites
  spriteOpacityByAge: boolean; // Fade sprites based on particle age
  // Emissive/bloom settings (for 3D rendering)
  emissiveEnabled: boolean; // Render particles as emissive (for bloom)
  emissiveIntensity: number; // Emissive intensity multiplier (0-10)
  emissiveColor: [number, number, number] | null; // Override color for emissive (null = use particle color)
}

// ============================================================================
// Internal Types
// ============================================================================

export interface SpatialGrid {
  cellSize: number;
  cells: Map<string, Particle[]>;
}
