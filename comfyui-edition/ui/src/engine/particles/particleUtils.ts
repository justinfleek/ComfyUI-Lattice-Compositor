/**
 * Particle System Utility Functions
 * 
 * Extracted from GPUParticleSystem.ts for use by both GPUParticleSystem
 * and VerifiedGPUParticleSystem. These are stateless utility functions
 * for creating default configurations.
 */

import type { EmitterConfig, ForceFieldConfig, GPUParticleSystemConfig } from "./types";

const SPATIAL_CELL_SIZE = 50; // Pixels

/**
 * Create default emitter configuration
 */
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

/**
 * Create default force field configuration
 */
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

/**
 * Create default particle system configuration
 */
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
      // 3D mesh geometry (default = billboard for standard 2D sprites)
      meshGeometry: "billboard" as const,
      // Depth of Field defaults
      dofEnabled: false,
      dofFocusDistance: 500,
      dofFocusRange: 200,
      dofMaxBlur: 0.5,
    },
    audioBindings: [],
    spatialHashCellSize: SPATIAL_CELL_SIZE,
    updateFrequency: 1,
    cullOffscreen: true,
  };
}
