/**
 * Particle System Default Factory Functions
 *
 * All createDefault* factory functions for particle system configs.
 * Extracted from particleSystem.ts for modularity.
 */

import type {
  CollisionConfig,
  ConnectionConfig,
  EmitterConfig,
  GravityWellConfig,
  LorenzAttractorConfig,
  ParticleSystemConfig,
  RenderOptions,
  SplinePathEmission,
  SpriteConfig,
  SubEmitterConfig,
  TurbulenceConfig,
  VortexConfig,
} from "./particleTypes";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                         // deterministic // id // generator
// Counter-based ID generation for deterministic project creation
// ═══════════════════════════════════════════════════════════════════════════

let idCounter = 0;

/**
 * Generate a deterministic, unique ID
 * Uses a counter to ensure uniqueness without Date.now() or Math.random()
 */
function generateDeterministicId(prefix: string): string {
  return `${prefix}_${(++idCounter).toString(36).padStart(8, "0")}`;
}

/**
 * Reset ID counter (for testing purposes)
 */
export function resetIdCounter(value: number = 0): void {
  idCounter = value;
}

// ═══════════════════════════════════════════════════════════════════════════
// Default Configurations
// ═══════════════════════════════════════════════════════════════════════════

export function createDefaultSpriteConfig(): SpriteConfig {
  return {
    enabled: false,
    imageUrl: null,
    imageData: null,
    isSheet: false,
    columns: 1,
    rows: 1,
    totalFrames: 1,
    frameRate: 30,
    playMode: "loop",
    billboard: true,
    rotationEnabled: false,
    rotationSpeed: 0,
    rotationSpeedVariance: 0,
    alignToVelocity: false,
  };
}

export function createDefaultSplinePathEmission(
  layerId: string = "",
): SplinePathEmission {
  return {
    layerId,
    emitMode: "random",
    parameter: 0,
    alignToPath: true,
    offset: 0,
    bidirectional: false,
  };
}

export function createDefaultCollisionConfig(): CollisionConfig {
  return {
    enabled: false,
    particleCollision: false,
    particleCollisionRadius: 1.0,
    particleCollisionResponse: "bounce",
    particleCollisionDamping: 0.8,
    layerCollision: false,
    layerCollisionLayerId: null,
    layerCollisionThreshold: 0.5,
    floorEnabled: false,
    floorY: 1.0,
    ceilingEnabled: false,
    ceilingY: 0.0,
    wallsEnabled: false,
    bounciness: 0.7,
    friction: 0.1,
    spatialHashCellSize: 50,
  };
}

export function createDefaultEmitterConfig(id?: string): EmitterConfig {
  return {
    id: id || generateDeterministicId("emitter"),
    name: "Emitter",
    x: 0.5,
    y: 0.5,
    direction: 270,
    spread: 30,
    speed: 330,
    speedVariance: 50,
    size: 17,
    sizeVariance: 5,
    color: [255, 255, 255],
    emissionRate: 10,
    initialBurst: 0,
    particleLifetime: 60,
    lifetimeVariance: 10,
    enabled: true,
    burstOnBeat: false,
    burstCount: 20,
    // Geometric emitter defaults
    shape: "point",
    shapeRadius: 0.1,
    shapeWidth: 0.2,
    shapeHeight: 0.2,
    shapeDepth: 0.2,
    shapeInnerRadius: 0.05,
    emitFromEdge: false,
    emitFromVolume: false,
    // Spline path emission (null = disabled)
    splinePath: null,
    // Sprite configuration
    sprite: createDefaultSpriteConfig(),
  };
}

export function createDefaultTurbulenceConfig(id?: string): TurbulenceConfig {
  return {
    id: id || generateDeterministicId("turb"),
    enabled: true,
    scale: 0.005,
    strength: 100,
    evolutionSpeed: 0.3,
  };
}

export function createDefaultConnectionConfig(): ConnectionConfig {
  return {
    enabled: false,
    maxDistance: 100,
    maxConnections: 3,
    lineWidth: 1,
    lineOpacity: 0.5,
    fadeByDistance: true,
  };
}

export function createDefaultSubEmitterConfig(id?: string): SubEmitterConfig {
  return {
    id: id || generateDeterministicId("sub"),
    parentEmitterId: "*",
    trigger: "death",
    spawnCount: 3,
    inheritVelocity: 0.3,
    size: 8,
    sizeVariance: 2,
    lifetime: 30,
    speed: 0.1,
    spread: 180,
    color: [255, 200, 100],
    enabled: true,
  };
}

export function createDefaultGravityWellConfig(id?: string): GravityWellConfig {
  return {
    id: id || generateDeterministicId("well"),
    name: "Gravity Well",
    x: 0.5,
    y: 0.5,
    strength: 100,
    radius: 0.3,
    falloff: "quadratic",
    enabled: true,
  };
}

export function createDefaultVortexConfig(id?: string): VortexConfig {
  return {
    id: id || generateDeterministicId("vortex"),
    name: "Vortex",
    x: 0.5,
    y: 0.5,
    strength: 200,
    radius: 0.3,
    rotationSpeed: 5,
    inwardPull: 10,
    enabled: true,
  };
}

export function createDefaultLorenzAttractorConfig(
  id?: string,
): LorenzAttractorConfig {
  return {
    id: id || generateDeterministicId("lorenz"),
    name: "Lorenz Attractor",
    x: 0.5,
    y: 0.5,
    sigma: 10,
    rho: 28,
    beta: 2.667,
    strength: 50,
    radius: 0.3,
    enabled: true,
  };
}

export function createDefaultSystemConfig(): ParticleSystemConfig {
  return {
    maxParticles: 10000,
    gravity: 0,
    windStrength: 0,
    windDirection: 0,
    warmupPeriod: 0,
    respectMaskBoundary: false,
    boundaryBehavior: "kill",
    friction: 0.01,
    turbulenceFields: [],
    subEmitters: [],
    collision: createDefaultCollisionConfig(),
  };
}

export function createDefaultRenderOptions(): RenderOptions {
  return {
    blendMode: "additive",
    renderTrails: false,
    trailLength: 5,
    trailOpacityFalloff: 0.7,
    particleShape: "circle",
    glowEnabled: false,
    glowRadius: 10,
    glowIntensity: 0.5,
    motionBlur: false,
    motionBlurStrength: 0.5,
    motionBlurSamples: 8,
    connections: createDefaultConnectionConfig(),
    spriteSmoothing: true,
    spriteOpacityByAge: true,
    emissiveEnabled: false,
    emissiveIntensity: 2.0,
    emissiveColor: null,
  };
}
