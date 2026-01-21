/**
 * ParticleLayer - GPU-Accelerated Particle System Layer
 *
 * Integrates the high-performance GPU particle system into the
 * Three.js layer hierarchy. Features:
 *
 * - 100k+ particles via instanced rendering
 * - Full 3D physics with mass, drag, and forces
 * - Emitter shapes: point, circle, sphere, box, line, cone, mesh, spline
 * - Force fields: gravity, vortex, turbulence, drag, wind, attractors
 * - Flocking/swarming behaviors
 * - Audio/MIDI reactivity
 * - Soft shadows and ambient occlusion
 */

import { isFiniteNumber, isNonEmptyString } from "@/utils/typeGuards";
import * as THREE from "three";
import type {
  Layer,
  ParticleEmitterConfig,
  ParticleLayerData,
} from "@/types/project";
import {
  createDefaultConfig,
  createDefaultEmitter,
  createDefaultForceField,
} from "../particles/particleUtils";
// Use verified system - GPUParticleSystem class has been removed
import { VerifiedGPUParticleSystem } from "../particles/VerifiedGPUParticleSystem";
import type {
  AudioFeature,
  EmitterConfig,
  EmitterShapeConfig,
  ForceFieldConfig,
  GPUParticleSystemConfig,
  SubEmitterConfig as GPUSubEmitterConfig,
  ExportedParticle,
} from "../particles/types";
import { BaseLayer } from "./BaseLayer";
import { PropertyEvaluator } from "@/services/animation/PropertyEvaluator";

export class ParticleLayer extends BaseLayer {
  /** The GPU particle system instance (verified system only) */
  private particleSystem: VerifiedGPUParticleSystem;

  /** Particle system configuration */
  private systemConfig: GPUParticleSystemConfig;

  /** Whether the system has been initialized with a renderer */
  private initialized = false;

  /** Stored renderer reference for reinitialization */
  private rendererRef: THREE.WebGLRenderer | null = null;

  /** Composition FPS for time calculation */
  private fps: number = 16;

  /** Deterministic seed derived from layer ID */
  private readonly layerSeed: number;

  /** Base emitter values for audio reactivity (prevents compounding) */
  private baseEmitterValues: Map<
    string,
    { initialSpeed: number; initialSize: number; emissionRate: number }
  > = new Map();

  /** Base force field values for audio reactivity (prevents compounding) */
  private baseForceFieldValues: Map<string, { strength: number }> = new Map();

  /** Per-emitter audio modifiers from MotionEngine */
  private currentEmitterAudioModifiers:
    | Map<
        string,
        import("@/services/audioReactiveMapping").ParticleAudioReactiveModifiers
      >
    | undefined;

  /** Performance stats */
  private stats = {
    particleCount: 0,
    updateTimeMs: 0,
    renderTimeMs: 0,
  };

  /** Particle layer data (for time remapping support) */
  private particleData: import("@/types/particles").ParticleLayerData | null = null;

  /** Property evaluator for speed map */
  private particleEvaluator = new PropertyEvaluator(16);

  /** Last evaluated frame (for determinism) */
  private lastEvaluatedFrame: number = -1;

  // ============================================================================
  // EMITTER GIZMO VISUALIZATION
  // ============================================================================

  /** Emitter visualization icons */
  private emitterGizmos: Map<string, THREE.Group> = new Map();

  /** Force field visualization icons */
  private forceFieldGizmos: Map<string, THREE.Group> = new Map();

  /** Whether emitter gizmos are visible */
  private showEmitterGizmos: boolean = true;

  /** Whether force field gizmos are visible */
  private showForceFieldGizmos: boolean = true;

  /** Horizon line mesh (CC Particle World style) */
  private horizonLine: THREE.Line | null = null;

  /** Whether horizon line is visible */
  private showHorizonLine: boolean = false;

  /** Particle space grid (CC Particle World style) */
  private particleGrid: THREE.Group | null = null;

  /** Whether particle grid is visible */
  private showParticleGrid: boolean = false;

  /** Axis visualization for particle space */
  private particleAxis: THREE.Group | null = null;

  /** Whether particle axis is visible */
  private showParticleAxis: boolean = false;

  /** Spline provider for path-based emission */
  private splineProvider: import("../particles/ParticleEmitterLogic").SplineProvider | null = null;

  constructor(layerData: Layer) {
    super(layerData);

    // Store particle data for time remapping support
    this.particleData = layerData.data as import("@/types/particles").ParticleLayerData | null;

    // Generate deterministic seed from layer ID
    // DETERMINISM: Same layer ID always produces same seed
    this.layerSeed = this.generateSeedFromId(layerData.id);

    // Build configuration from layer data (with deterministic seed)
    this.systemConfig = this.buildSystemConfig(layerData);
    this.systemConfig.randomSeed = this.layerSeed;

    // Create particle system with deterministic seed
    // Always use verified system - GPUParticleSystem class has been removed
    this.particleSystem = new VerifiedGPUParticleSystem(this.systemConfig);

    // Apply initial blend mode
    this.initializeBlendMode();
  }

  /**
   * Generate deterministic seed from layer ID
   * DETERMINISM: Same layer ID always produces identical seed
   */
  private generateSeedFromId(layerId: string): number {
    let hash = 0;
    for (let i = 0; i < layerId.length; i++) {
      const char = layerId.charCodeAt(i);
      hash = (hash << 5) - hash + char;
      hash = hash & hash; // Convert to 32bit integer
    }
    return Math.abs(hash) || 12345; // Fallback to 12345 if 0
  }

  /**
   * Convert emitter shape from project format to GPU format
   * Supports: point, circle, sphere, box, line, ring, cone, spline
   */
  private convertEmitterShape(
    emitter: ParticleEmitterConfig,
  ): EmitterShapeConfig {
    // Type proof: shape ∈ string | undefined → "point" | "circle" | "sphere" | "box" | "line" | "ring" | "cone" | "spline" | "depthEdge" | "image" | "depth-map" | "mask"
    const shape = emitter !== undefined && typeof emitter === "object" && emitter !== null && "shape" in emitter && isNonEmptyString(emitter.shape) && (emitter.shape === "point" || emitter.shape === "circle" || emitter.shape === "sphere" || emitter.shape === "box" || emitter.shape === "line" || emitter.shape === "ring" || emitter.shape === "cone" || emitter.shape === "spline" || emitter.shape === "depthEdge" || emitter.shape === "image" || emitter.shape === "depth-map" || emitter.shape === "mask")
      ? emitter.shape
      : "point";

    switch (shape) {
      case "point":
        return { type: "point" };

      case "circle":
        // Type proof: shapeRadius ∈ number | undefined → number
        const circleRadius = isFiniteNumber(emitter.shapeRadius) && emitter.shapeRadius >= 0
          ? emitter.shapeRadius
          : 50;
        // Type proof: emitFromEdge ∈ boolean | undefined → boolean
        const circleEmitFromEdge = emitter !== undefined && typeof emitter === "object" && emitter !== null && "emitFromEdge" in emitter && typeof emitter.emitFromEdge === "boolean"
          ? emitter.emitFromEdge
          : false;
        return {
          type: "circle",
          radius: circleRadius,
          emitFromEdge: circleEmitFromEdge,
        };

      case "sphere":
        // Type proof: shapeRadius ∈ number | undefined → number
        const sphereRadius = isFiniteNumber(emitter.shapeRadius) && emitter.shapeRadius >= 0
          ? emitter.shapeRadius
          : 50;
        // Type proof: emitFromEdge ∈ boolean | undefined → boolean
        const sphereEmitFromEdge = emitter !== undefined && typeof emitter === "object" && emitter !== null && "emitFromEdge" in emitter && typeof emitter.emitFromEdge === "boolean"
          ? emitter.emitFromEdge
          : false;
        return {
          type: "sphere",
          radius: sphereRadius,
          emitFromEdge: sphereEmitFromEdge,
        };

      case "box":
        // Type proof: shapeWidth ∈ number | undefined → number
        const boxWidth = isFiniteNumber(emitter.shapeWidth) && emitter.shapeWidth >= 0
          ? emitter.shapeWidth
          : 100;
        // Type proof: shapeHeight ∈ number | undefined → number
        const boxHeight = isFiniteNumber(emitter.shapeHeight) && emitter.shapeHeight >= 0
          ? emitter.shapeHeight
          : 100;
        // Type proof: shapeDepth ∈ ℝ ∪ {undefined} → z ∈ ℝ
        const boxDepth = isFiniteNumber(emitter.shapeDepth) ? emitter.shapeDepth : 0;
        return {
          type: "box",
          boxSize: {
            x: boxWidth,
            y: boxHeight,
            z: boxDepth,
          },
        };

      case "line": {
        // Line extends from emitter position in both directions
        // Type proof: shapeWidth ∈ number | undefined → number
        const lineWidth = isFiniteNumber(emitter.shapeWidth) && emitter.shapeWidth >= 0
          ? emitter.shapeWidth
          : 100;
        const halfWidth = lineWidth / 2;
        return {
          type: "line",
          lineStart: { x: -halfWidth, y: 0, z: 0 },
          lineEnd: { x: halfWidth, y: 0, z: 0 },
        };
      }

      case "ring":
        // Type proof: shapeRadius ∈ number | undefined → number
        const ringRadius = isFiniteNumber(emitter.shapeRadius) && emitter.shapeRadius >= 0
          ? emitter.shapeRadius
          : 50;
        // Type proof: shapeInnerRadius ∈ number | undefined → number
        const ringInnerRadius = isFiniteNumber(emitter.shapeInnerRadius) && emitter.shapeInnerRadius >= 0
          ? emitter.shapeInnerRadius
          : 0;
        return {
          type: "circle",
          radius: ringRadius,
          radiusVariance: ringInnerRadius,
          emitFromEdge: true, // Ring always emits from edge
        };

      case "spline":
        // Spline emission - use splinePath config if available
        if (emitter.splinePath) {
          // Type proof: parameter ∈ number | undefined → number
          const splineOffset = emitter.splinePath !== undefined && typeof emitter.splinePath === "object" && emitter.splinePath !== null && "parameter" in emitter.splinePath && isFiniteNumber(emitter.splinePath.parameter)
            ? emitter.splinePath.parameter
            : 0;
          return {
            type: "spline",
            splineId: emitter.splinePath.layerId,
            splineOffset,
          };
        }
        return { type: "point" }; // Fallback if no spline configured

      case "depth-map":
        // Depth-based emission - uses both image data and depth data
        // Image data must be set via setEmitterImageData() at runtime
        // Type proof: depthMin ∈ number | undefined → number
        const depthMin = emitter.depthMapEmission !== undefined && typeof emitter.depthMapEmission === "object" && emitter.depthMapEmission !== null && "depthMin" in emitter.depthMapEmission && isFiniteNumber(emitter.depthMapEmission.depthMin) && emitter.depthMapEmission.depthMin >= 0
          ? emitter.depthMapEmission.depthMin
          : 0.1;
        return {
          type: "depthEdge", // Use depth edge emission (emits from depth discontinuities)
          emissionThreshold: depthMin,
          // imageData and depthData will be provided at runtime
        };

      case "mask":
        // Mask-based emission - emits from non-transparent/bright pixels
        // Image data must be set via setEmitterImageData() at runtime
        // Type proof: threshold ∈ number | undefined → number (clamped 0-1)
        const maskThreshold = emitter.maskEmission !== undefined && typeof emitter.maskEmission === "object" && emitter.maskEmission !== null && "threshold" in emitter.maskEmission && isFiniteNumber(emitter.maskEmission.threshold) && emitter.maskEmission.threshold >= 0 && emitter.maskEmission.threshold <= 1
          ? emitter.maskEmission.threshold
          : 0.5;
        return {
          type: "image",
          emissionThreshold: maskThreshold,
          // imageData will be provided at runtime
        };

      default:
        return { type: "point" };
    }
  }

  /**
   * Build GPUParticleSystemConfig from layer data
   */
  private buildSystemConfig(layerData: Layer): GPUParticleSystemConfig {
    const data = layerData.data as ParticleLayerData | null;
    const config = createDefaultConfig();

    if (!data) {
      // Create a default emitter
      config.emitters = [createDefaultEmitter("default")];
      return config;
    }

    // System settings
    if (data.systemConfig) {
      // Cap maxParticles to prevent GPU memory exhaustion (1M max)
      const MAX_PARTICLES = 1000000;
      // Type proof: maxParticles ∈ number | undefined → number
      const rawMaxParticles = data.systemConfig !== undefined && typeof data.systemConfig === "object" && data.systemConfig !== null && "maxParticles" in data.systemConfig && isFiniteNumber(data.systemConfig.maxParticles) && data.systemConfig.maxParticles > 0
        ? data.systemConfig.maxParticles
        : 100000;
      config.maxParticles = Number.isFinite(rawMaxParticles)
        ? Math.max(1, Math.min(MAX_PARTICLES, rawMaxParticles))
        : 100000;
      config.timeScale = 1;

      // Add global gravity as a force field
      if (data.systemConfig.gravity !== 0) {
        config.forceFields.push({
          id: "global_gravity",
          name: "Gravity",
          type: "gravity",
          enabled: true,
          strength: data.systemConfig.gravity * 10,
          position: { x: 0, y: 0, z: 0 },
          falloffStart: 0,
          falloffEnd: 10000,
          falloffType: "none",
          direction: { x: 0, y: 1, z: 0 },
        });
      }

      // Add global wind as a force field
      if (data.systemConfig.windStrength !== 0) {
        // Type proof: windDirection ∈ number | undefined → number
        const windDirection = isFiniteNumber(data.systemConfig.windDirection)
          ? data.systemConfig.windDirection
          : 0;
        const windAngle = (windDirection * Math.PI) / 180;
        config.forceFields.push({
          id: "global_wind",
          name: "Wind",
          type: "wind",
          enabled: true,
          strength: data.systemConfig.windStrength,
          position: { x: 0, y: 0, z: 0 },
          falloffStart: 0,
          falloffEnd: 10000,
          falloffType: "none",
          windDirection: {
            x: Math.cos(windAngle),
            y: Math.sin(windAngle),
            z: 0,
          },
          gustStrength: data.systemConfig.windStrength * 0.3,
          gustFrequency: 0.1,
        });
      }

      // Add global friction as drag
      if (data.systemConfig.friction > 0) {
        config.forceFields.push({
          id: "global_drag",
          name: "Friction",
          type: "drag",
          enabled: true,
          strength: 1,
          position: { x: 0, y: 0, z: 0 },
          falloffStart: 0,
          falloffEnd: 10000,
          falloffType: "none",
          linearDrag: data.systemConfig.friction,
          quadraticDrag: data.systemConfig.friction * 0.1,
        });
      }

      // Add turbulence fields
      if (data.systemConfig.turbulenceFields) {
        for (const turbField of data.systemConfig.turbulenceFields) {
          if (turbField.enabled) {
            config.forceFields.push({
              id: turbField.id,
              name: "Turbulence",
              type: "turbulence",
              enabled: true,
              strength: turbField.strength,
              position: { x: 0, y: 0, z: 0 },
              falloffStart: 0,
              falloffEnd: 10000,
              falloffType: "none",
              noiseScale: turbField.scale,
              noiseSpeed: turbField.evolutionSpeed,
              noiseOctaves: 3,
              noiseLacunarity: 2,
              noiseGain: 0.5,
            });
          }
        }
      }
    }

    // Convert emitters
    if (data.emitters) {
      for (const emitter of data.emitters) {
        if (!emitter.enabled) continue;

        // Type proof: direction ∈ number | undefined → number
        const emitterDirection = isFiniteNumber(emitter.direction)
          ? emitter.direction
          : 0;
        const dirRad = (emitterDirection * Math.PI) / 180;

        // Convert emitter shape from project format to GPU format
        const shapeConfig = this.convertEmitterShape(emitter);

        const gpuEmitter: EmitterConfig = {
          id: emitter.id,
          name: emitter.name,
          enabled: true,
          position: { x: emitter.x, y: emitter.y, z: 0 },
          rotation: { x: 0, y: 0, z: 0 },
          shape: shapeConfig,
          emissionRate: emitter.emissionRate,
          emissionRateVariance: 0,
          burstCount: emitter.burstCount,
          burstInterval: 0,
          initialSpeed: emitter.speed,
          speedVariance: emitter.speedVariance,
          inheritEmitterVelocity: 0,
          initialSize: emitter.size,
          sizeVariance: emitter.sizeVariance,
          initialMass: 1,
          massVariance: 0,
          lifetime: emitter.particleLifetime,
          lifetimeVariance: emitter.lifetimeVariance,
          initialRotation: 0,
          rotationVariance: 360,
          initialAngularVelocity: 0,
          angularVelocityVariance: 0,
          colorStart: [
            emitter.color[0] / 255,
            emitter.color[1] / 255,
            emitter.color[2] / 255,
            1,
          ],
          colorEnd: [
            emitter.color[0] / 255,
            emitter.color[1] / 255,
            emitter.color[2] / 255,
            0,
          ],
          colorVariance: 0,
          emissionDirection: {
            x: Math.cos(dirRad),
            y: Math.sin(dirRad),
            z: 0,
          },
          emissionSpread: emitter.spread,
          burstOnBeat: emitter.burstOnBeat,
          beatEmissionMultiplier: 5,
        };

        config.emitters.push(gpuEmitter);
      }
    }

    // Convert gravity wells to point attractors
    if (data.gravityWells) {
      for (const well of data.gravityWells) {
        if (!well.enabled) continue;

        config.forceFields.push({
          id: well.id,
          name: well.name,
          type: "point",
          enabled: true,
          strength: well.strength,
          position: { x: well.x, y: well.y, z: 0 },
          falloffStart: 0,
          falloffEnd: well.radius,
          falloffType:
            well.falloff === "linear"
              ? "linear"
              : well.falloff === "quadratic"
                ? "quadratic"
                : "none",
        });
      }
    }

    // Convert vortices
    if (data.vortices) {
      for (const vortex of data.vortices) {
        if (!vortex.enabled) continue;

        config.forceFields.push({
          id: vortex.id,
          name: vortex.name,
          type: "vortex",
          enabled: true,
          strength: vortex.strength * vortex.rotationSpeed,
          position: { x: vortex.x, y: vortex.y, z: 0 },
          falloffStart: 0,
          falloffEnd: vortex.radius,
          falloffType: "linear",
          vortexAxis: { x: 0, y: 0, z: 1 },
          inwardForce: vortex.inwardPull,
        });
      }
    }

    // Convert modulations to lifetime curves
    if (data.modulations) {
      // Group by emitter
      const sizeModulations = data.modulations.filter(
        (m) => m.property === "size",
      );
      if (sizeModulations.length > 0) {
        const mod = sizeModulations[0];
        config.lifetimeModulation.sizeOverLifetime = {
          type: "linear",
          start: mod.startValue / 100,
          end: mod.endValue / 100,
        };
      }

      const opacityModulations = data.modulations.filter(
        (m) => m.property === "opacity",
      );
      if (opacityModulations.length > 0) {
        const mod = opacityModulations[0];
        config.lifetimeModulation.opacityOverLifetime = {
          type: "linear",
          start: mod.startValue / 100,
          end: mod.endValue / 100,
        };
      }
    }

    // Convert sub-emitters
    if (data.subEmitters) {
      for (const sub of data.subEmitters) {
        if (!sub.enabled) continue;

        const gpuSubEmitter: GPUSubEmitterConfig = {
          id: sub.id,
          parentEmitterId: sub.parentEmitterId,
          trigger: sub.trigger,
          triggerProbability: 1.0,
          emitCount: sub.spawnCount,
          emitCountVariance: 0,
          inheritPosition: true,
          inheritVelocity: sub.inheritVelocity,
          inheritSize: 0,
          inheritColor: 0,
          inheritRotation: 0,
          overrides: {
            initialSpeed: sub.speed,
            emissionSpread: sub.spread,
            initialSize: sub.size,
            initialMass: 1,
            lifetime: sub.lifetime,
            lifetimeVariance: sub.sizeVariance, // Use size variance for lifetime variance
            colorStart: [
              sub.color[0] / 255,
              sub.color[1] / 255,
              sub.color[2] / 255,
              1,
            ],
            colorEnd: [
              sub.color[0] / 255,
              sub.color[1] / 255,
              sub.color[2] / 255,
              0,
            ],
          },
        };

        config.subEmitters.push(gpuSubEmitter);
      }
    }

    // Convert flocking configuration
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const flocking = (data != null && typeof data === "object" && "flocking" in data && data.flocking != null && typeof data.flocking === "object") ? data.flocking : undefined;
    if (flocking != null && typeof flocking === "object" && "enabled" in flocking && flocking.enabled) {
      // Helper to validate numeric params (NaN would corrupt flocking behavior)
      const safeNum = (val: number | undefined, def: number) =>
        Number.isFinite(val) ? val! : def;

      config.flocking = {
        enabled: true,
        separationWeight: safeNum(flocking.separationWeight, 50) / 100,
        separationRadius: safeNum(flocking.separationRadius, 25),
        alignmentWeight: safeNum(flocking.alignmentWeight, 50) / 100,
        alignmentRadius: safeNum(flocking.alignmentRadius, 50),
        cohesionWeight: safeNum(flocking.cohesionWeight, 50) / 100,
        cohesionRadius: safeNum(flocking.cohesionRadius, 50),
        maxSpeed: safeNum(flocking.maxSpeed, 200),
        maxForce: safeNum(flocking.maxForce, 10),
        perceptionAngle: safeNum(flocking.perceptionAngle, 270),
      };
    }

    // Store collision configuration for initialization after GPU setup
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const collision = (data != null && typeof data === "object" && "collision" in data && data.collision != null && typeof data.collision === "object") ? data.collision : undefined;
    if (collision != null && typeof collision === "object" && "enabled" in collision && collision.enabled) {
      // Type proofs: all collision properties with explicit checks
      const particleCollision = collision !== undefined && typeof collision === "object" && collision !== null && "particleCollision" in collision && typeof collision.particleCollision === "boolean"
        ? collision.particleCollision
        : false;
      const particleRadius = isFiniteNumber(collision.particleRadius) && collision.particleRadius > 0
        ? collision.particleRadius
        : 5;
      const bounciness = isFiniteNumber(collision.bounciness) && collision.bounciness >= 0 && collision.bounciness <= 1
        ? collision.bounciness
        : 0.5;
      const friction = isFiniteNumber(collision.friction) && collision.friction >= 0 && collision.friction <= 1
        ? collision.friction
        : 0.1;
      this.pendingCollisionConfig = {
        enabled: true,
        particleCollision,
        particleRadius,
        bounciness,
        friction,
        bounds: collision.boundaryEnabled
          ? {
              min: {
                x: collision.boundaryPadding,
                y: collision.boundaryPadding,
                z: -1000,
              },
              max: {
                x: 1920 - collision.boundaryPadding,
                y: 1080 - collision.boundaryPadding,
                z: 1000,
              },
            }
          : undefined,
        // Type proof: boundaryBehavior ∈ string | undefined → "none" | "bounce" | "wrap" | "kill"
        boundsBehavior: collision !== undefined && typeof collision === "object" && collision !== null && "boundaryBehavior" in collision && typeof collision.boundaryBehavior === "string" && (collision.boundaryBehavior === "none" || collision.boundaryBehavior === "bounce" || collision.boundaryBehavior === "wrap" || collision.boundaryBehavior === "kill")
          ? collision.boundaryBehavior
          : "none",
      };
    }

    // Render options
    if (data.renderOptions) {
      // Type proof: blendMode ∈ string | undefined → string
      const blendMode = data.renderOptions !== undefined && typeof data.renderOptions === "object" && data.renderOptions !== null && "blendMode" in data.renderOptions && typeof data.renderOptions.blendMode === "string"
        ? data.renderOptions.blendMode
        : "normal";
      // Type proof: motionBlur ∈ boolean | undefined → boolean
      const motionBlur = data.renderOptions !== undefined && typeof data.renderOptions === "object" && data.renderOptions !== null && "motionBlur" in data.renderOptions && typeof data.renderOptions.motionBlur === "boolean"
        ? data.renderOptions.motionBlur
        : false;
      // Type proof: motionBlurStrength ∈ number | undefined → number (clamped 0-1)
      const motionBlurStrength = data.renderOptions !== undefined && typeof data.renderOptions === "object" && data.renderOptions !== null && "motionBlurStrength" in data.renderOptions && isFiniteNumber(data.renderOptions.motionBlurStrength) && data.renderOptions.motionBlurStrength >= 0 && data.renderOptions.motionBlurStrength <= 1
        ? data.renderOptions.motionBlurStrength
        : 0.5;
      // Type proof: motionBlurSamples ∈ number | undefined → number (2-16)
      const motionBlurSamples = data.renderOptions !== undefined && typeof data.renderOptions === "object" && data.renderOptions !== null && "motionBlurSamples" in data.renderOptions && isFiniteNumber(data.renderOptions.motionBlurSamples) && Number.isInteger(data.renderOptions.motionBlurSamples) && data.renderOptions.motionBlurSamples >= 2 && data.renderOptions.motionBlurSamples <= 16
        ? data.renderOptions.motionBlurSamples
        : 4;
      config.render.blendMode = blendMode;
      config.render.motionBlur = motionBlur;
      config.render.motionBlurStrength = motionBlurStrength;
      config.render.motionBlurSamples = motionBlurSamples;

      // Trails
      if (data.renderOptions.renderTrails) {
        config.render.mode = "trail";
        config.render.trailLength = data.renderOptions.trailLength;
        // Type proof: trailOpacityFalloff ∈ number | undefined → number (clamped 0-1)
        const trailOpacityFalloff = data.renderOptions !== undefined && typeof data.renderOptions === "object" && data.renderOptions !== null && "trailOpacityFalloff" in data.renderOptions && isFiniteNumber(data.renderOptions.trailOpacityFalloff) && data.renderOptions.trailOpacityFalloff >= 0 && data.renderOptions.trailOpacityFalloff <= 1
          ? data.renderOptions.trailOpacityFalloff
          : 0.8;
        config.render.trailWidthEnd = 1 - trailOpacityFalloff;
      }

      // Particle shape affects procedural rendering
      config.render.texture.proceduralType =
        data.renderOptions.particleShape === "star"
          ? "star"
          : data.renderOptions.particleShape === "square"
            ? "square"
            : "circle";

      // Connections - wire UI settings to GPU config
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const renderOptions = (data != null && typeof data === "object" && "renderOptions" in data && data.renderOptions != null && typeof data.renderOptions === "object") ? data.renderOptions : undefined;
      const connections = (renderOptions != null && typeof renderOptions === "object" && "connections" in renderOptions && renderOptions.connections != null && typeof renderOptions.connections === "object") ? renderOptions.connections : undefined;
      if (connections != null && typeof connections === "object" && "enabled" in connections && connections.enabled) {
        // Store connection config for initialization after GPU setup
        // Note: ConnectionRenderConfig.color is already in 0-1 RGB range (per type definition)
        // Type proofs: all connection properties with explicit checks
        const maxDistance = connections !== undefined && typeof connections === "object" && connections !== null && "maxDistance" in connections && isFiniteNumber(connections.maxDistance) && connections.maxDistance > 0
          ? connections.maxDistance
          : 100;
        const maxConnections = connections !== undefined && typeof connections === "object" && connections !== null && "maxConnections" in connections && isFiniteNumber(connections.maxConnections) && Number.isInteger(connections.maxConnections) && connections.maxConnections > 0
          ? connections.maxConnections
          : 5;
        const lineWidth = connections !== undefined && typeof connections === "object" && connections !== null && "lineWidth" in connections && isFiniteNumber(connections.lineWidth) && connections.lineWidth > 0
          ? connections.lineWidth
          : 1;
        const lineOpacity = connections !== undefined && typeof connections === "object" && connections !== null && "lineOpacity" in connections && isFiniteNumber(connections.lineOpacity) && connections.lineOpacity >= 0 && connections.lineOpacity <= 1
          ? connections.lineOpacity
          : 0.5;
        const fadeByDistance = connections !== undefined && typeof connections === "object" && connections !== null && "fadeByDistance" in connections && typeof connections.fadeByDistance === "boolean"
          ? connections.fadeByDistance
          : true;
        this.pendingConnectionConfig = {
          enabled: true,
          maxDistance,
          maxConnections,
          lineWidth,
          lineOpacity,
          fadeByDistance,
          color: connections !== undefined && typeof connections === "object" && connections !== null && "color" in connections
            ? connections.color
            : undefined,
        };
      }

      // Glow settings - store for post-processing
      if (data.renderOptions.glowEnabled) {
        // Type proof: glowRadius ∈ number | undefined → number
        const glowRadius = data.renderOptions !== undefined && typeof data.renderOptions === "object" && data.renderOptions !== null && "glowRadius" in data.renderOptions && isFiniteNumber(data.renderOptions.glowRadius) && data.renderOptions.glowRadius >= 0
          ? data.renderOptions.glowRadius
          : 10;
        // Type proof: glowIntensity ∈ number | undefined → number (clamped 0-1)
        const glowIntensity = data.renderOptions !== undefined && typeof data.renderOptions === "object" && data.renderOptions !== null && "glowIntensity" in data.renderOptions && isFiniteNumber(data.renderOptions.glowIntensity) && data.renderOptions.glowIntensity >= 0 && data.renderOptions.glowIntensity <= 1
          ? data.renderOptions.glowIntensity
          : 0.5;
        this.pendingGlowConfig = {
          enabled: true,
          radius: glowRadius,
          intensity: glowIntensity,
        };
      }

      // Sprite sheet settings
      if (
        data.renderOptions.spriteEnabled &&
        data.renderOptions.spriteImageUrl
      ) {
        // Type proofs: all sprite properties with explicit checks
        const spriteColumns = data.renderOptions !== undefined && typeof data.renderOptions === "object" && data.renderOptions !== null && "spriteColumns" in data.renderOptions && isFiniteNumber(data.renderOptions.spriteColumns) && Number.isInteger(data.renderOptions.spriteColumns) && data.renderOptions.spriteColumns >= 1
          ? data.renderOptions.spriteColumns
          : 1;
        const spriteRows = data.renderOptions !== undefined && typeof data.renderOptions === "object" && data.renderOptions !== null && "spriteRows" in data.renderOptions && isFiniteNumber(data.renderOptions.spriteRows) && Number.isInteger(data.renderOptions.spriteRows) && data.renderOptions.spriteRows >= 1
          ? data.renderOptions.spriteRows
          : 1;
        const spriteAnimate = data.renderOptions !== undefined && typeof data.renderOptions === "object" && data.renderOptions !== null && "spriteAnimate" in data.renderOptions && typeof data.renderOptions.spriteAnimate === "boolean"
          ? data.renderOptions.spriteAnimate
          : false;
        const spriteFrameRate = data.renderOptions !== undefined && typeof data.renderOptions === "object" && data.renderOptions !== null && "spriteFrameRate" in data.renderOptions && isFiniteNumber(data.renderOptions.spriteFrameRate) && data.renderOptions.spriteFrameRate > 0
          ? data.renderOptions.spriteFrameRate
          : 10;
        const spriteRandomStart = data.renderOptions !== undefined && typeof data.renderOptions === "object" && data.renderOptions !== null && "spriteRandomStart" in data.renderOptions && typeof data.renderOptions.spriteRandomStart === "boolean"
          ? data.renderOptions.spriteRandomStart
          : false;
        this.pendingSpriteConfig = {
          url: data.renderOptions.spriteImageUrl,
          columns: spriteColumns,
          rows: spriteRows,
          animate: spriteAnimate,
          frameRate: spriteFrameRate,
          randomStart: spriteRandomStart,
        };
      }

      // LOD (Level of Detail) settings
      if (data.renderOptions.lodEnabled !== undefined) {
        config.render.lodEnabled = data.renderOptions.lodEnabled;
      }
      if (data.renderOptions.lodDistances) {
        config.render.lodDistances = data.renderOptions.lodDistances;
      }
      if (data.renderOptions.lodSizeMultipliers) {
        config.render.lodSizeMultipliers = data.renderOptions.lodSizeMultipliers;
      }

      // Depth of Field settings
      if (data.renderOptions.dofEnabled !== undefined) {
        config.render.dofEnabled = data.renderOptions.dofEnabled;
      }
      if (data.renderOptions.dofFocusDistance !== undefined) {
        config.render.dofFocusDistance = data.renderOptions.dofFocusDistance;
      }
      if (data.renderOptions.dofFocusRange !== undefined) {
        config.render.dofFocusRange = data.renderOptions.dofFocusRange;
      }
      if (data.renderOptions.dofMaxBlur !== undefined) {
        config.render.dofMaxBlur = data.renderOptions.dofMaxBlur;
      }

      // Shadow settings - store for initialization
      if (data.renderOptions.shadowsEnabled !== undefined) {
        // Type proofs: all shadow properties with explicit checks
        const castShadows = data.renderOptions !== undefined && typeof data.renderOptions === "object" && data.renderOptions !== null && "castShadows" in data.renderOptions && typeof data.renderOptions.castShadows === "boolean"
          ? data.renderOptions.castShadows
          : true;
        const receiveShadows = data.renderOptions !== undefined && typeof data.renderOptions === "object" && data.renderOptions !== null && "receiveShadows" in data.renderOptions && typeof data.renderOptions.receiveShadows === "boolean"
          ? data.renderOptions.receiveShadows
          : true;
        const shadowSoftness = data.renderOptions !== undefined && typeof data.renderOptions === "object" && data.renderOptions !== null && "shadowSoftness" in data.renderOptions && isFiniteNumber(data.renderOptions.shadowSoftness) && data.renderOptions.shadowSoftness >= 0
          ? data.renderOptions.shadowSoftness
          : 1.0;
        this.pendingShadowConfig = {
          enabled: data.renderOptions.shadowsEnabled,
          castShadows,
          receiveShadows,
          shadowSoftness,
        };
      }

      // 3D mesh mode
      if (data.renderOptions.meshMode !== undefined) {
        // Type proof: meshGeometry ∈ string | undefined → string
        const meshGeometry = data.renderOptions !== undefined && typeof data.renderOptions === "object" && data.renderOptions !== null && "meshGeometry" in data.renderOptions && typeof data.renderOptions.meshGeometry === "string"
          ? data.renderOptions.meshGeometry
          : "sphere";
        config.render.meshGeometry = data.renderOptions.meshMode === "mesh"
          ? meshGeometry
          : "billboard";
      }
    }

    return config;
  }

  // Pending configs to apply after initialization
  private pendingConnectionConfig: {
    enabled: boolean;
    maxDistance: number;
    maxConnections: number;
    lineWidth: number;
    lineOpacity: number;
    fadeByDistance: boolean;
    color?: [number, number, number];
  } | null = null;

  private pendingGlowConfig: {
    enabled: boolean;
    radius: number;
    intensity: number;
  } | null = null;

  private pendingSpriteConfig: {
    url: string;
    columns: number;
    rows: number;
    animate: boolean;
    frameRate: number;
    randomStart: boolean;
  } | null = null;

  private pendingCollisionConfig: {
    enabled: boolean;
    particleCollision: boolean;
    particleRadius: number;
    bounciness: number;
    friction: number;
    bounds?: {
      min: { x: number; y: number; z: number };
      max: { x: number; y: number; z: number };
    };
    boundsBehavior: "none" | "kill" | "bounce" | "wrap" | "clamp" | "stick";
  } | null = null;

  private pendingShadowConfig: {
    enabled: boolean;
    castShadows: boolean;
    receiveShadows: boolean;
    shadowSoftness: number;
  } | null = null;

  /**
   * Initialize the particle system with a WebGL renderer
   */
  initializeWithRenderer(renderer: THREE.WebGLRenderer): void {
    if (this.initialized) return;

    this.rendererRef = renderer;
    this.particleSystem.initialize(renderer);
    this.initialized = true;

    // Add particle mesh to group
    const mesh = this.particleSystem.getMesh();
    if (mesh) {
      this.group.add(mesh);
    }

    // Apply pending connection config and add connection mesh
    if (this.pendingConnectionConfig) {
      this.particleSystem.initializeConnections(this.pendingConnectionConfig);
      const connectionMesh = this.particleSystem.getConnectionMesh();
      if (connectionMesh) {
        this.group.add(connectionMesh);
      }
      this.pendingConnectionConfig = null;
    }

    // Add trail mesh if trails are enabled
    const trailMesh = this.particleSystem.getTrailMesh();
    if (trailMesh) {
      this.group.add(trailMesh);
    }

    // Apply pending sprite config
    if (this.pendingSpriteConfig) {
      this.particleSystem
        .loadTexture(this.pendingSpriteConfig.url, {
          columns: this.pendingSpriteConfig.columns,
          rows: this.pendingSpriteConfig.rows,
          animate: this.pendingSpriteConfig.animate,
          frameRate: this.pendingSpriteConfig.frameRate,
          randomStart: this.pendingSpriteConfig.randomStart,
        })
        .catch((err) => {
          console.warn("Failed to load particle sprite:", err);
        });
      this.pendingSpriteConfig = null;
    }

    // Initialize glow effect and add glow mesh
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    if (this.pendingGlowConfig != null && typeof this.pendingGlowConfig === "object" && "enabled" in this.pendingGlowConfig && this.pendingGlowConfig.enabled) {
      this.particleSystem.initializeGlow(this.pendingGlowConfig);
      const glowMesh = this.particleSystem.getGlowMesh();
      if (glowMesh) {
        this.group.add(glowMesh);
      }
      this.glowConfig = this.pendingGlowConfig;
      this.pendingGlowConfig = null;
    }

    // Initialize collision detection
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    if (this.pendingCollisionConfig != null && typeof this.pendingCollisionConfig === "object" && "enabled" in this.pendingCollisionConfig && this.pendingCollisionConfig.enabled) {
      this.particleSystem.initializeCollisions(this.pendingCollisionConfig);
      this.pendingCollisionConfig = null;
    }

    // Initialize shadow settings
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    if (this.pendingShadowConfig != null && typeof this.pendingShadowConfig === "object" && "enabled" in this.pendingShadowConfig && this.pendingShadowConfig.enabled) {
      this.particleSystem.updateShadowConfig({
        castShadows: this.pendingShadowConfig.castShadows,
        receiveShadows: this.pendingShadowConfig.receiveShadows,
        shadowSoftness: this.pendingShadowConfig.shadowSoftness,
      });
      this.pendingShadowConfig = null;
    }

    // Wire up spline provider for spline-based emission
    if (this.splineProvider) {
      this.particleSystem.setSplineProvider(this.splineProvider);
    }

    // Create emitter and force field gizmos for visualization
    this.createGizmos();

    // Store base emitter/force field values for audio reactivity
    this.storeBaseValues();
  }

  /**
   * Store base emitter and force field values for audio reactivity
   * This prevents compounding when audio values are applied each frame
   */
  private storeBaseValues(): void {
    const config = this.particleSystem.getConfig();

    // Store emitter base values
    this.baseEmitterValues.clear();
    for (const emitter of config.emitters) {
      this.baseEmitterValues.set(emitter.id, {
        initialSpeed: emitter.initialSpeed,
        initialSize: emitter.initialSize,
        emissionRate: emitter.emissionRate, // Store base rate before audio modulation
      });
    }

    // Store force field base values
    this.baseForceFieldValues.clear();
    for (const field of config.forceFields) {
      this.baseForceFieldValues.set(field.id, {
        strength: field.strength,
      });
    }
  }

  // Glow configuration
  private glowConfig: {
    enabled: boolean;
    radius: number;
    intensity: number;
  } | null = null;

  /**
   * Get glow configuration
   */
  getGlowConfig(): {
    enabled: boolean;
    radius: number;
    intensity: number;
  } | null {
    return this.glowConfig;
  }

  /**
   * Update glow settings at runtime
   */
  setGlow(config: {
    enabled?: boolean;
    radius?: number;
    intensity?: number;
  }): void {
    this.particleSystem.setGlow(config);
    if (this.glowConfig) {
      Object.assign(this.glowConfig, config);
    }
  }

  /**
   * Set renderer for lazy initialization
   */
  setRenderer(renderer: THREE.WebGLRenderer): void {
    this.rendererRef = renderer;
    if (!this.initialized) {
      this.initializeWithRenderer(renderer);
    }
  }

  /**
   * Set the spline provider for spline-based particle emission
   * This allows emitters with shape='spline' to emit particles along spline paths
   * @param provider - Function that queries spline positions
   */
  setSplineProvider(provider: import("../particles/ParticleEmitterLogic").SplineProvider | null): void {
    this.splineProvider = provider;
    this.particleSystem.setSplineProvider(provider);
  }

  /**
   * Update shadow maps from scene lights
   * Call this when the layer is added to a scene with shadow-casting lights
   */
  updateShadowsFromScene(scene: THREE.Scene): void {
    // Find first shadow-casting light in scene
    scene.traverse((obj) => {
      if (obj instanceof THREE.DirectionalLight ||
          obj instanceof THREE.SpotLight ||
          obj instanceof THREE.PointLight) {
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
        const shadow = (obj != null && typeof obj === "object" && "shadow" in obj && obj.shadow != null && typeof obj.shadow === "object") ? obj.shadow : undefined;
        const shadowMap = (shadow != null && typeof shadow === "object" && "map" in shadow && shadow.map != null && typeof shadow.map === "object") ? shadow.map : undefined;
        const shadowTexture = (shadowMap != null && typeof shadowMap === "object" && "texture" in shadowMap && shadowMap.texture != null) ? shadowMap.texture : undefined;
        if (obj.castShadow && shadowTexture) {
          this.particleSystem.updateShadowFromLight(obj);
        }
      }
    });
  }

  /**
   * Set composition FPS for accurate time calculation
   */
  setFPS(fps: number): void {
    // Validate fps (NaN would break time calculations and cache simulation)
    this.fps = Number.isFinite(fps) && fps > 0 ? fps : 16;
  }

  // ============================================================================
  // EMITTER MANAGEMENT
  // ============================================================================

  /**
   * Add a new emitter
   */
  addEmitter(config?: Partial<EmitterConfig>): string {
    const emitter = createDefaultEmitter();
    if (config) {
      Object.assign(emitter, config);
    }
    this.particleSystem.addEmitter(emitter);
    return emitter.id;
  }

  /**
   * Update an emitter
   */
  updateEmitter(id: string, updates: Partial<EmitterConfig>): void {
    this.particleSystem.updateEmitter(id, updates);
  }

  /**
   * Remove an emitter
   */
  removeEmitter(id: string): void {
    this.particleSystem.removeEmitter(id);
  }

  // ============================================================================
  // FORCE FIELD MANAGEMENT
  // ============================================================================

  /**
   * Add a force field
   */
  addForceField(
    type: ForceFieldConfig["type"],
    config?: Partial<ForceFieldConfig>,
  ): string {
    const field = createDefaultForceField(type);
    if (config) {
      Object.assign(field, config);
    }
    this.particleSystem.addForceField(field);
    return field.id;
  }

  /**
   * Update a force field
   */
  updateForceField(id: string, updates: Partial<ForceFieldConfig>): void {
    this.particleSystem.updateForceField(id, updates);
  }

  /**
   * Remove a force field
   */
  removeForceField(id: string): void {
    this.particleSystem.removeForceField(id);
  }

  // ============================================================================
  // AUDIO REACTIVITY
  // ============================================================================

  /**
   * Set audio feature value for reactivity
   */
  setAudioFeature(feature: AudioFeature, value: number): void {
    this.particleSystem.setAudioFeature(feature, value);
  }

  /**
   * Trigger a beat event (causes burst on beat-enabled emitters)
   */
  triggerBeat(): void {
    this.particleSystem.triggerBeat();
  }

  /**
   * Trigger a burst emission
   */
  triggerBurst(emitterId?: string): void {
    this.particleSystem.triggerBurst(emitterId);
  }

  /**
   * Set image data for mask/depth-map emission
   * Call this each frame with rendered layer data to enable image-based emission
   *
   * @param emitterId - The emitter ID to update
   * @param imageData - The image data to emit from (for mask emission)
   * @param depthData - Optional Float32Array of depth values (for depth-map emission)
   */
  setEmitterImageData(
    emitterId: string,
    imageData: ImageData,
    depthData?: Float32Array,
  ): void {
    const emitter = this.particleSystem.getEmitter(emitterId);
    if (emitter) {
      // Update the shape config with the new image data
      emitter.shape.imageData = imageData;
      if (depthData) {
        emitter.shape.depthData = depthData;
      }
    }
  }

  // ============================================================================
  // SIMULATION
  // ============================================================================

  /**
   * Step the particle simulation
   */
  step(deltaTime: number): void {
    if (!this.initialized) return;

    this.particleSystem.step(deltaTime);

    // Update stats
    const state = this.particleSystem.getState();
    this.stats.particleCount = state.particleCount;
    this.stats.updateTimeMs = state.updateTimeMs;
    this.stats.renderTimeMs = state.renderTimeMs;
  }

  /**
   * Get current performance stats
   */
  getStats(): typeof this.stats {
    return { ...this.stats };
  }

  /**
   * Reset the particle system
   * DETERMINISM: Resets to initial state with original seed
   */
  reset(): void {
    this.particleSystem.reset();
    this.lastEvaluatedFrame = -1;
  }

  /**
   * Clear the particle cache (used when user wants to free memory)
   */
  clearCache(): void {
    this.particleSystem.clearCache();
  }

  /**
   * Get cache statistics for UI display
   */
  getCacheStats(): ReturnType<typeof this.particleSystem.getCacheStats> {
    return this.particleSystem.getCacheStats();
  }

  /**
   * Pre-cache frames from startFrame to endFrame
   * Used by Preview panel to build cache before playback
   * @returns Progress callback will be called with (current, total)
   */
  async preCacheFrames(
    startFrame: number,
    endFrame: number,
    onProgress?: (current: number, total: number) => void,
  ): Promise<void> {
    // Validate frame bounds (NaN/Infinity would cause infinite loop or no-op)
    const validStart = Number.isFinite(startFrame)
      ? Math.max(0, Math.floor(startFrame))
      : 0;
    const validEnd = Number.isFinite(endFrame)
      ? Math.floor(endFrame)
      : validStart;

    // Sanity check: cap at 10,000 frames to prevent resource exhaustion
    const MAX_CACHE_FRAMES = 10000;
    const cappedEnd = Math.min(validEnd, validStart + MAX_CACHE_FRAMES);

    if (cappedEnd < validStart) return;

    const totalFrames = cappedEnd - validStart + 1;

    // Simulate from start to end, building cache along the way
    for (let frame = validStart; frame <= cappedEnd; frame++) {
      this.particleSystem.simulateToFrame(frame, this.fps);

      if (onProgress) {
        onProgress(frame - validStart + 1, totalFrames);
      }

      // Yield to prevent blocking UI (every 10 frames)
      if ((frame - validStart) % 10 === 0) {
        await new Promise((resolve) => setTimeout(resolve, 0));
      }
    }
  }

  /**
   * Set the cache interval (frames between cached snapshots)
   */
  setCacheInterval(interval: number): void {
    this.particleSystem.setCacheInterval(interval);
  }

  // ============================================================================
  // BAKE TO KEYFRAMES / TRAJECTORY EXPORT
  // ============================================================================

  /**
   * Export particle trajectories for a frame range
   * Returns per-frame particle states that can be baked to keyframes
   *
   * @param startFrame - Start frame (default: 0)
   * @param endFrame - End frame (default: composition length)
   * @param onProgress - Progress callback (frame, total)
   * @returns Map of frame number to particle array
   */
  async exportTrajectories(
    startFrame: number = 0,
    endFrame: number = 80,
    onProgress?: (frame: number, total: number) => void,
  ): Promise<Map<number, ExportedParticle[]>> {
    return this.particleSystem.exportTrajectories(
      startFrame,
      endFrame,
      this.fps,
      onProgress,
    );
  }

  /**
   * Get current active particles (for single-frame export)
   */
  getActiveParticles(): ExportedParticle[] {
    return this.particleSystem.getActiveParticles();
  }

  // ============================================================================
  // ABSTRACT IMPLEMENTATIONS
  // ============================================================================

  /**
   * Calculate time-remapped frame for particle simulation
   * Supports speed map (time remapping) like VideoLayer
   */
  private calculateRemappedFrame(compositionFrame: number): number {
    // If speed map is enabled, use that
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const particleData = this.particleData;
    const speedMapEnabled = (particleData != null && typeof particleData === "object" && "speedMapEnabled" in particleData && particleData.speedMapEnabled === true) ? particleData.speedMapEnabled : false;
    const speedMap = (particleData != null && typeof particleData === "object" && "speedMap" in particleData && particleData.speedMap != null && typeof particleData.speedMap === "object") ? particleData.speedMap : undefined;
    const speedMapAnimated = (speedMap != null && typeof speedMap === "object" && "animated" in speedMap && speedMap.animated === true) ? speedMap.animated : false;
    if (speedMapEnabled && speedMapAnimated) {
      const remappedTime = this.particleEvaluator.evaluate(
        speedMap,
        compositionFrame,
      );
      // Validate remapped time (NaN would break simulation)
      const validTime = Number.isFinite(remappedTime) ? remappedTime : 0;
      // Convert time to frame (speed map is in seconds)
      return Math.floor(validTime * this.fps);
    }

    // Get layer's timeStretch if available (100 = normal, 200 = half speed, -100 = reversed)
    // Type proof: timeStretch ∈ number | undefined → number
    const rawTimeStretch = isFiniteNumber(this.layerData.timeStretch)
      ? this.layerData.timeStretch
      : 100;
    const timeStretch = Number.isFinite(rawTimeStretch) ? rawTimeStretch : 100;
    const isReversed = timeStretch < 0;

    // Calculate effective speed: 100% stretch = 1x, 200% = 0.5x, 50% = 2x
    const stretchFactor = timeStretch !== 0 ? 100 / Math.abs(timeStretch) : 0;

    // Calculate frame relative to layer start
    // Type proof: startFrame ∈ number | undefined → number
    const layerStartFrame = isFiniteNumber(this.layerData.startFrame) && Number.isInteger(this.layerData.startFrame)
      ? this.layerData.startFrame
      : 0;
    const relativeFrame = compositionFrame - layerStartFrame;

    // Apply time stretch
    let simulationFrame = Math.floor(relativeFrame * stretchFactor);

    // Handle reversed playback
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const systemConfig = (particleData != null && typeof particleData === "object" && "systemConfig" in particleData && particleData.systemConfig != null && typeof particleData.systemConfig === "object") ? particleData.systemConfig : undefined;
    if (isReversed && systemConfig) {
      // For reversed particles, simulate to max then play backwards
      // This requires a different approach - simulate fully then index backwards
      const maxFrames = systemConfig.maxParticles > 0 ? 300 : 0; // Reasonable max
      simulationFrame = Math.max(0, maxFrames - simulationFrame);
    }

    // Final validation - NaN frame would break simulation
    return Number.isFinite(simulationFrame) && simulationFrame >= 0 ? simulationFrame : 0;
  }

  protected onEvaluateFrame(frame: number): void {
    // Calculate remapped frame for time remapping support
    const simulationFrame = this.calculateRemappedFrame(frame);

    // DETERMINISM: Use frame caching system for scrub-safe particle evaluation
    // The simulateToFrame method handles:
    // - Sequential playback (single step)
    // - Forward scrubbing (continue from current)
    // - Backward/random scrubbing (restore from nearest cache or reset)
    // - Automatic caching every N frames
    const stepsPerformed = this.particleSystem.simulateToFrame(simulationFrame, this.fps);

    this.lastEvaluatedFrame = frame;

    // Apply audio-reactive values after simulation
    this.applyAudioReactivity();

    // Update stats
    const state = this.particleSystem.getState();
    this.stats.particleCount = state.particleCount;
    this.stats.updateTimeMs = state.updateTimeMs;
    this.stats.renderTimeMs = state.renderTimeMs;

    // Log cache performance for debugging (only when significant work done)
    if (stepsPerformed > 10) {
      const cacheStats = this.particleSystem.getCacheStats();
      console.debug(
        `ParticleLayer: Simulated ${stepsPerformed} frames to reach frame ${simulationFrame}. ` +
          `Cache: ${cacheStats.cachedFrames} frames cached`,
      );
    }
  }

  protected override onApplyEvaluatedState(
    state: import("../MotionEngine").EvaluatedLayer,
  ): void {
    // ParticleLayer needs to step the simulation for the current frame
    // The evaluated state includes the frame number for deterministic simulation
    // Type proof: frame ∈ number | undefined → number
    const frame = isFiniteNumber(state.frame) && Number.isInteger(state.frame) && state.frame >= 0
      ? state.frame
      : 0;

    // Store per-emitter audio modifiers for targeted emission rate control
    this.currentEmitterAudioModifiers = state.emitterAudioModifiers as
      | Map<
          string,
          import("@/services/audioReactiveMapping").ParticleAudioReactiveModifiers
        >
      | undefined;

    // Apply audio-reactive emission rate modifiers before simulation.
    // Must happen before step() since emission occurs during simulation.
    this.applyEmissionRateModifiers();

    // Step the particle simulation (deterministic replay if needed)
    this.onEvaluateFrame(frame);
  }

  /**
   * Evaluate particles at a specific frame (scrub-safe)
   * DETERMINISM: Returns identical results regardless of evaluation order
   * Uses frame caching for performance
   */
  evaluateAtFrame(frame: number): void {
    // Use the caching system for efficient frame evaluation
    this.particleSystem.simulateToFrame(frame, this.fps);
    this.lastEvaluatedFrame = frame;
  }

  /**
   * Apply emission rate modifiers BEFORE simulation step.
   * Emission rate must be set before step() because emitParticles() uses it during step.
   */
  private applyEmissionRateModifiers(): void {
    const layerEmissionRate = this.getAudioReactiveValue(
      "particle.emissionRate",
    );

    const emitters = this.particleSystem.getConfig().emitters;
    for (const emitter of emitters) {
      const baseValues = this.baseEmitterValues.get(emitter.id);
      if (!baseValues) continue;

      // Get emitter-specific audio modifiers (may have different emission rate multiplier)
      // Type proof: emitterMods ∈ ParticleAudioReactiveModifiers | undefined
      const emitterMods = this.currentEmitterAudioModifiers !== undefined && this.currentEmitterAudioModifiers !== null && typeof this.currentEmitterAudioModifiers === "object" && typeof this.currentEmitterAudioModifiers.get === "function"
        ? this.currentEmitterAudioModifiers.get(emitter.id)
        : undefined;
      // Type proof: emissionRate ∈ number | undefined → number
      const emissionRateMod = emitterMods !== undefined && typeof emitterMods === "object" && emitterMods !== null && "emissionRate" in emitterMods && isFiniteNumber(emitterMods.emissionRate)
        ? emitterMods.emissionRate
        : layerEmissionRate;

      if (emissionRateMod !== 0) {
        // Modulate emission rate: base * (0.5 + mod) for range 0.5x to 1.5x
        this.particleSystem.updateEmitter(emitter.id, {
          emissionRate: baseValues.emissionRate * (0.5 + emissionRateMod),
        });
      } else {
        // Reset to base value when no modulation
        this.particleSystem.updateEmitter(emitter.id, {
          emissionRate: baseValues.emissionRate,
        });
      }
    }
  }

  /**
   * Apply audio-reactive values to particle system emitters and force fields.
   * Uses per-emitter audio modifiers when targetEmitterId is specified.
   * NOTE: Emission rate is handled separately in applyEmissionRateModifiers() BEFORE simulation
   */
  private applyAudioReactivity(): void {
    // Layer-level audio values (for emitters without specific targeting)
    const layerSpeed = this.getAudioReactiveValue("particle.speed");
    const layerSize = this.getAudioReactiveValue("particle.size");
    const layerGravity = this.getAudioReactiveValue("particle.gravity");
    const layerWindStrength = this.getAudioReactiveValue(
      "particle.windStrength",
    );

    // Update emitters based on audio (using BASE values to prevent compounding)
    // NOTE: Emission rate is handled in applyEmissionRateModifiers() BEFORE step()
    const emitters = this.particleSystem.getConfig().emitters;
    for (const emitter of emitters) {
      const baseValues = this.baseEmitterValues.get(emitter.id);
      if (!baseValues) continue;

      // Get emitter-specific modifiers (allows different audio response per emitter)
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const emitterMods = (this.currentEmitterAudioModifiers != null && typeof this.currentEmitterAudioModifiers === "object" && typeof this.currentEmitterAudioModifiers.get === "function") ? this.currentEmitterAudioModifiers.get(emitter.id) : undefined;

      // Use emitter-specific values if available, otherwise fall back to layer-level
      // Type proof: speed ∈ number | undefined → number
      const speed = emitterMods !== undefined && typeof emitterMods === "object" && emitterMods !== null && "speed" in emitterMods && isFiniteNumber(emitterMods.speed)
        ? emitterMods.speed
        : layerSpeed;
      // Type proof: size ∈ number | undefined → number
      const size = emitterMods !== undefined && typeof emitterMods === "object" && emitterMods !== null && "size" in emitterMods && isFiniteNumber(emitterMods.size)
        ? emitterMods.size
        : layerSize;

      // CRITICAL: Always reset to base values FIRST to prevent compounding
      // This ensures values are correct even if GPUParticleSystem.applyAudioModulation() ran during step()
      this.particleSystem.updateEmitter(emitter.id, {
        initialSpeed: baseValues.initialSpeed,
        initialSize: baseValues.initialSize,
      });

      // Speed modulation (0.5 base + audio value for range 0.5x to 1.5x)
      if (speed !== 0) {
        this.particleSystem.updateEmitter(emitter.id, {
          initialSpeed: baseValues.initialSpeed * (0.5 + speed),
        });
      }

      // Size modulation
      if (size !== 0) {
        this.particleSystem.updateEmitter(emitter.id, {
          initialSize: baseValues.initialSize * (0.5 + size),
        });
      }
    }

    // Update force fields based on audio (using BASE values to prevent compounding)
    const gravity = layerGravity;
    const windStrength = layerWindStrength;
    if (gravity !== 0 || windStrength !== 0) {
      const forceFields = this.particleSystem.getConfig().forceFields;
      for (const field of forceFields) {
        const baseFieldValues = this.baseForceFieldValues.get(field.id);
        if (!baseFieldValues) continue;

        // CRITICAL: Always reset to base values FIRST to prevent compounding
        // This ensures values are correct even if GPUParticleSystem.applyAudioModulation() ran during step()
        this.particleSystem.updateForceField(field.id, {
          strength: baseFieldValues.strength,
        });

        if (field.type === "gravity" && gravity !== 0) {
          this.particleSystem.updateForceField(field.id, {
            strength: baseFieldValues.strength * (0.5 + gravity),
          });
        }
        if (field.type === "wind" && windStrength !== 0) {
          this.particleSystem.updateForceField(field.id, {
            strength: baseFieldValues.strength * (0.5 + windStrength),
          });
        }
      }
    }

    // Check for beat/onset to trigger bursts
    // This is handled by the audio system calling triggerBeat() externally
  }

  protected onUpdate(properties: Partial<Layer>): void {
    const data = properties.data as ParticleLayerData | undefined;

    if (data) {
      // Update particle data for time remapping support
      this.particleData = data as import("@/types/particles").ParticleLayerData;

      // Remove old mesh from group
      const oldMesh = this.particleSystem.getMesh();
      if (oldMesh) {
        this.group.remove(oldMesh);
      }

      // Rebuild configuration and reinitialize
      this.systemConfig = this.buildSystemConfig({
        ...properties,
        id: this.id,
        type: "particles",
      } as Layer);

      // DETERMINISM: Preserve the layer-specific seed
      this.systemConfig.randomSeed = this.layerSeed;

      // Dispose old system
      this.particleSystem.dispose();

      // Create new system with deterministic seed
      // Always use verified system - GPUParticleSystem class has been removed
      this.particleSystem = new VerifiedGPUParticleSystem(this.systemConfig);

      // Reset evaluation state
      this.lastEvaluatedFrame = -1;

      // Reinitialize if we have a renderer
      if (this.rendererRef) {
        this.initialized = false;
        this.initializeWithRenderer(this.rendererRef);
      }
    }
  }

  protected onDispose(): void {
    this.particleSystem.dispose();
    this.disposeGizmos();
  }

  // ============================================================================
  // EMITTER GIZMO VISUALIZATION
  // ============================================================================

  /**
   * Create visual gizmos for all emitters and force fields
   */
  createGizmos(): void {
    this.disposeGizmos();

    const config = this.particleSystem.getConfig();

    // Create emitter gizmos
    for (const emitter of config.emitters) {
      this.createEmitterGizmo(emitter);
    }

    // Create force field gizmos
    for (const field of config.forceFields) {
      this.createForceFieldGizmo(field);
    }
  }

  /**
   * Create a visual gizmo for an emitter
   */
  private createEmitterGizmo(emitter: EmitterConfig): void {
    const gizmo = new THREE.Group();
    gizmo.name = `emitter_gizmo_${emitter.id}`;

    const size = 30;

    // Create emitter icon based on shape type
    switch (emitter.shape.type) {
      case "point": {
        // Point emitter: small cone shape
        const coneGeom = new THREE.ConeGeometry(8, 20, 8);
        const coneMat = new THREE.MeshBasicMaterial({
          color: 0x00ff88,
          transparent: true,
          opacity: 0.7,
          wireframe: true,
          depthTest: false,
        });
        const cone = new THREE.Mesh(coneGeom, coneMat);
        cone.rotation.x = Math.PI;
        gizmo.add(cone);

        // Add center sphere
        const sphereGeom = new THREE.SphereGeometry(5, 8, 8);
        const sphereMat = new THREE.MeshBasicMaterial({
          color: 0x00ff88,
          transparent: true,
          opacity: 0.9,
          depthTest: false,
        });
        const sphere = new THREE.Mesh(sphereGeom, sphereMat);
        gizmo.add(sphere);
        break;
      }

      case "circle": {
        // Circle emitter: ring shape
        // Type proof: radius ∈ number | undefined → number
        const circleRadiusGizmo = emitter.shape !== undefined && typeof emitter.shape === "object" && emitter.shape !== null && "radius" in emitter.shape && isFiniteNumber(emitter.shape.radius) && emitter.shape.radius >= 0
          ? emitter.shape.radius
          : 50;
        const ringGeom = new THREE.RingGeometry(
          circleRadiusGizmo * 0.8,
          circleRadiusGizmo,
          32,
        );
        const ringMat = new THREE.MeshBasicMaterial({
          color: 0x00ff88,
          transparent: true,
          opacity: 0.5,
          side: THREE.DoubleSide,
          depthTest: false,
        });
        const ring = new THREE.Mesh(ringGeom, ringMat);
        gizmo.add(ring);
        break;
      }

      case "sphere": {
        // Sphere emitter: wireframe sphere
        // Type proof: radius ∈ number | undefined → number
        const sphereRadiusGizmo = emitter.shape !== undefined && typeof emitter.shape === "object" && emitter.shape !== null && "radius" in emitter.shape && isFiniteNumber(emitter.shape.radius) && emitter.shape.radius >= 0
          ? emitter.shape.radius
          : 50;
        const sphereGeom = new THREE.SphereGeometry(
          sphereRadiusGizmo,
          16,
          16,
        );
        const sphereMat = new THREE.MeshBasicMaterial({
          color: 0x00ff88,
          transparent: true,
          opacity: 0.3,
          wireframe: true,
          depthTest: false,
        });
        const sphere = new THREE.Mesh(sphereGeom, sphereMat);
        gizmo.add(sphere);
        break;
      }

      case "box": {
        // Box emitter: wireframe box
        // Type proof: boxSize.x ∈ number | undefined → number
        const boxSizeX = emitter.shape !== undefined && typeof emitter.shape === "object" && emitter.shape !== null && "boxSize" in emitter.shape && emitter.shape.boxSize !== undefined && typeof emitter.shape.boxSize === "object" && emitter.shape.boxSize !== null && "x" in emitter.shape.boxSize && isFiniteNumber(emitter.shape.boxSize.x) && emitter.shape.boxSize.x >= 0
          ? emitter.shape.boxSize.x
          : 100;
        // Type proof: boxSize.y ∈ number | undefined → number
        const boxSizeY = emitter.shape !== undefined && typeof emitter.shape === "object" && emitter.shape !== null && "boxSize" in emitter.shape && emitter.shape.boxSize !== undefined && typeof emitter.shape.boxSize === "object" && emitter.shape.boxSize !== null && "y" in emitter.shape.boxSize && isFiniteNumber(emitter.shape.boxSize.y) && emitter.shape.boxSize.y >= 0
          ? emitter.shape.boxSize.y
          : 100;
        // Type proof: boxSize.z ∈ ℝ ∪ {undefined} → z ∈ ℝ
        const boxSizeZ = emitter.shape !== undefined && typeof emitter.shape === "object" && emitter.shape !== null && "boxSize" in emitter.shape && emitter.shape.boxSize !== undefined && typeof emitter.shape.boxSize === "object" && emitter.shape.boxSize !== null && "z" in emitter.shape.boxSize && isFiniteNumber(emitter.shape.boxSize.z)
          ? emitter.shape.boxSize.z
          : 0;
        const boxGeom = new THREE.BoxGeometry(
          boxSizeX,
          boxSizeY,
          boxSizeZ,
        );
        const boxMat = new THREE.MeshBasicMaterial({
          color: 0x00ff88,
          transparent: true,
          opacity: 0.3,
          wireframe: true,
          depthTest: false,
        });
        const box = new THREE.Mesh(boxGeom, boxMat);
        gizmo.add(box);
        break;
      }

      case "cone": {
        // Cone emitter: wireframe cone
        // Type proof: coneRadius ∈ number | undefined → number
        const coneRadiusGizmoFinal = emitter.shape !== undefined && typeof emitter.shape === "object" && emitter.shape !== null && "coneRadius" in emitter.shape && isFiniteNumber(emitter.shape.coneRadius) && emitter.shape.coneRadius >= 0
          ? emitter.shape.coneRadius
          : 30;
        // Type proof: coneLength ∈ number | undefined → number
        const coneLengthGizmoFinal = emitter.shape !== undefined && typeof emitter.shape === "object" && emitter.shape !== null && "coneLength" in emitter.shape && isFiniteNumber(emitter.shape.coneLength) && emitter.shape.coneLength >= 0
          ? emitter.shape.coneLength
          : 100;
        const coneGeom = new THREE.ConeGeometry(
          coneRadiusGizmoFinal,
          coneLengthGizmoFinal,
          16,
          1,
          true,
        );
        const coneMat = new THREE.MeshBasicMaterial({
          color: 0x00ff88,
          transparent: true,
          opacity: 0.3,
          wireframe: true,
          depthTest: false,
        });
        const cone = new THREE.Mesh(coneGeom, coneMat);
        gizmo.add(cone);
        break;
      }

      default: {
        // Default: cross icon
        const lineMat = new THREE.LineBasicMaterial({
          color: 0x00ff88,
          depthTest: false,
        });

        const hPoints = [
          new THREE.Vector3(-size, 0, 0),
          new THREE.Vector3(size, 0, 0),
        ];
        const vPoints = [
          new THREE.Vector3(0, -size, 0),
          new THREE.Vector3(0, size, 0),
        ];

        const hLine = new THREE.Line(
          new THREE.BufferGeometry().setFromPoints(hPoints),
          lineMat,
        );
        const vLine = new THREE.Line(
          new THREE.BufferGeometry().setFromPoints(vPoints),
          lineMat.clone(),
        );

        gizmo.add(hLine, vLine);
      }
    }

    // Add direction arrow
    const dir = emitter.emissionDirection;
    if (dir) {
      const arrowLength = 40;
      const arrowGeom = new THREE.BufferGeometry().setFromPoints([
        new THREE.Vector3(0, 0, 0),
        new THREE.Vector3(
          dir.x * arrowLength,
          -dir.y * arrowLength,
          dir.z * arrowLength,
        ),
      ]);
      const arrowMat = new THREE.LineBasicMaterial({
        color: 0xffff00,
        depthTest: false,
      });
      const arrow = new THREE.Line(arrowGeom, arrowMat);
      gizmo.add(arrow);
    }

    // Position gizmo
    const pos = emitter.position;
    gizmo.position.set(pos.x, -pos.y, pos.z);

    gizmo.visible = this.showEmitterGizmos;
    gizmo.renderOrder = 997;

    this.emitterGizmos.set(emitter.id, gizmo);
    this.group.add(gizmo);
  }

  /**
   * Create a visual gizmo for a force field
   */
  private createForceFieldGizmo(field: ForceFieldConfig): void {
    const gizmo = new THREE.Group();
    gizmo.name = `forcefield_gizmo_${field.id}`;

    const radius = field.falloffEnd || 100;

    switch (field.type) {
      case "gravity":
      case "wind": {
        // Arrow pointing in force direction
        // Type proof: direction ∈ { x: number; y: number; z: number } | undefined → { x: number; y: number; z: number }
        const fieldDirection = field !== undefined && typeof field === "object" && field !== null && "direction" in field && field.direction !== undefined && typeof field.direction === "object" && field.direction !== null && "x" in field.direction && "y" in field.direction && "z" in field.direction && isFiniteNumber(field.direction.x) && isFiniteNumber(field.direction.y) && isFiniteNumber(field.direction.z)
          ? field.direction
          : { x: 0, y: 1, z: 0 };
        const dir =
          field.type === "wind" && field.windDirection !== undefined && typeof field.windDirection === "object" && field.windDirection !== null && "x" in field.windDirection && "y" in field.windDirection && "z" in field.windDirection && isFiniteNumber(field.windDirection.x) && isFiniteNumber(field.windDirection.y) && isFiniteNumber(field.windDirection.z)
            ? field.windDirection
            : fieldDirection;

        const arrowLength = 60;
        const arrowPoints = [
          new THREE.Vector3(0, 0, 0),
          new THREE.Vector3(
            dir.x * arrowLength,
            -dir.y * arrowLength,
            dir.z * arrowLength,
          ),
        ];
        const arrowGeom = new THREE.BufferGeometry().setFromPoints(arrowPoints);
        const arrowMat = new THREE.LineBasicMaterial({
          color: field.type === "gravity" ? 0xff8800 : 0x00aaff,
          linewidth: 2,
          depthTest: false,
        });
        const arrow = new THREE.Line(arrowGeom, arrowMat);
        gizmo.add(arrow);

        // Add arrowhead
        const headGeom = new THREE.ConeGeometry(5, 15, 6);
        const headMat = new THREE.MeshBasicMaterial({
          color: field.type === "gravity" ? 0xff8800 : 0x00aaff,
          depthTest: false,
        });
        const head = new THREE.Mesh(headGeom, headMat);
        head.position.set(
          dir.x * arrowLength,
          -dir.y * arrowLength,
          dir.z * arrowLength,
        );
        // Point arrowhead in direction
        head.lookAt(0, 0, 0);
        gizmo.add(head);
        break;
      }

      case "vortex": {
        // Spiral icon
        const spiralPoints: THREE.Vector3[] = [];
        for (let t = 0; t < Math.PI * 4; t += 0.2) {
          const r = (t / (Math.PI * 4)) * radius * 0.5;
          spiralPoints.push(
            new THREE.Vector3(Math.cos(t) * r, Math.sin(t) * r, t * 2),
          );
        }
        const spiralGeom = new THREE.BufferGeometry().setFromPoints(
          spiralPoints,
        );
        const spiralMat = new THREE.LineBasicMaterial({
          color: 0xff00ff,
          depthTest: false,
        });
        const spiral = new THREE.Line(spiralGeom, spiralMat);
        gizmo.add(spiral);
        break;
      }

      case "turbulence": {
        // Wavy lines
        const waveMat = new THREE.LineBasicMaterial({
          color: 0xffaa00,
          depthTest: false,
        });

        for (let i = 0; i < 3; i++) {
          const wavePoints: THREE.Vector3[] = [];
          for (let t = 0; t < Math.PI * 2; t += 0.3) {
            wavePoints.push(
              new THREE.Vector3(t * 10, Math.sin(t * 3 + i) * 10, (i - 1) * 15),
            );
          }
          const waveGeom = new THREE.BufferGeometry().setFromPoints(wavePoints);
          const wave = new THREE.Line(waveGeom, waveMat.clone());
          wave.position.x = -30;
          gizmo.add(wave);
        }
        break;
      }

      case "point": {
        // Attractor/repeller sphere with arrows
        const sphereGeom = new THREE.SphereGeometry(15, 12, 12);
        const sphereMat = new THREE.MeshBasicMaterial({
          color: field.strength > 0 ? 0xff0000 : 0x0000ff,
          transparent: true,
          opacity: 0.5,
          wireframe: true,
          depthTest: false,
        });
        const sphere = new THREE.Mesh(sphereGeom, sphereMat);
        gizmo.add(sphere);

        // Add range indicator
        const rangeGeom = new THREE.RingGeometry(radius * 0.9, radius, 32);
        const rangeMat = new THREE.MeshBasicMaterial({
          color: field.strength > 0 ? 0xff0000 : 0x0000ff,
          transparent: true,
          opacity: 0.2,
          side: THREE.DoubleSide,
          depthTest: false,
        });
        const range = new THREE.Mesh(rangeGeom, rangeMat);
        gizmo.add(range);
        break;
      }

      case "drag": {
        // Resistance symbol (parallel lines)
        const lineMat = new THREE.LineBasicMaterial({
          color: 0x888888,
          depthTest: false,
        });

        for (let i = -2; i <= 2; i++) {
          const linePoints = [
            new THREE.Vector3(-20, i * 8, 0),
            new THREE.Vector3(20, i * 8, 0),
          ];
          const lineGeom = new THREE.BufferGeometry().setFromPoints(linePoints);
          const line = new THREE.Line(lineGeom, lineMat.clone());
          gizmo.add(line);
        }
        break;
      }
    }

    // Position gizmo
    const pos = field.position;
    gizmo.position.set(pos.x, -pos.y, pos.z);

    gizmo.visible = this.showForceFieldGizmos;
    gizmo.renderOrder = 996;

    this.forceFieldGizmos.set(field.id, gizmo);
    this.group.add(gizmo);
  }

  /**
   * Update gizmo positions from current config
   */
  updateGizmoPositions(): void {
    const config = this.particleSystem.getConfig();

    for (const emitter of config.emitters) {
      const gizmo = this.emitterGizmos.get(emitter.id);
      if (gizmo) {
        gizmo.position.set(
          emitter.position.x,
          -emitter.position.y,
          emitter.position.z,
        );
      }
    }

    for (const field of config.forceFields) {
      const gizmo = this.forceFieldGizmos.get(field.id);
      if (gizmo) {
        gizmo.position.set(
          field.position.x,
          -field.position.y,
          field.position.z,
        );
      }
    }
  }

  /**
   * Set emitter gizmo visibility
   */
  setEmitterGizmosVisible(visible: boolean): void {
    this.showEmitterGizmos = visible;
    for (const gizmo of this.emitterGizmos.values()) {
      gizmo.visible = visible;
    }
  }

  /**
   * Set force field gizmo visibility
   */
  setForceFieldGizmosVisible(visible: boolean): void {
    this.showForceFieldGizmos = visible;
    for (const gizmo of this.forceFieldGizmos.values()) {
      gizmo.visible = visible;
    }
  }

  /**
   * Dispose all gizmos
   */
  private disposeGizmos(): void {
    // Dispose emitter gizmos
    for (const gizmo of this.emitterGizmos.values()) {
      this.group.remove(gizmo);
      gizmo.traverse((child) => {
        if (child instanceof THREE.Mesh) {
          child.geometry.dispose();
          (child.material as THREE.Material).dispose();
        }
        if (child instanceof THREE.Line) {
          child.geometry.dispose();
          (child.material as THREE.Material).dispose();
        }
      });
    }
    this.emitterGizmos.clear();

    // Dispose force field gizmos
    for (const gizmo of this.forceFieldGizmos.values()) {
      this.group.remove(gizmo);
      gizmo.traverse((child) => {
        if (child instanceof THREE.Mesh) {
          child.geometry.dispose();
          (child.material as THREE.Material).dispose();
        }
        if (child instanceof THREE.Line) {
          child.geometry.dispose();
          (child.material as THREE.Material).dispose();
        }
      });
    }
    this.forceFieldGizmos.clear();

    // Dispose horizon line
    if (this.horizonLine) {
      this.group.remove(this.horizonLine);
      this.horizonLine.geometry.dispose();
      (this.horizonLine.material as THREE.Material).dispose();
      this.horizonLine = null;
    }

    // Dispose particle grid
    if (this.particleGrid) {
      this.group.remove(this.particleGrid);
      this.particleGrid.traverse((child) => {
        if (child instanceof THREE.Line) {
          child.geometry.dispose();
          (child.material as THREE.Material).dispose();
        }
      });
      this.particleGrid = null;
    }

    // Dispose particle axis
    if (this.particleAxis) {
      this.group.remove(this.particleAxis);
      this.particleAxis.traverse((child) => {
        if (child instanceof THREE.Line) {
          child.geometry.dispose();
          (child.material as THREE.Material).dispose();
        }
      });
      this.particleAxis = null;
    }
  }

  // ============================================================================
  // CC PARTICLE WORLD STYLE VISUALIZATION (Horizon, Grid, Axis)
  // ============================================================================

  /**
   * Create or update horizon line at floor position (CC Particle World style)
   */
  createHorizonLine(
    floorY: number = 1.0,
    compWidth: number = 1920,
    compHeight: number = 1080,
  ): void {
    // Dispose existing
    if (this.horizonLine) {
      this.group.remove(this.horizonLine);
      this.horizonLine.geometry.dispose();
      (this.horizonLine.material as THREE.Material).dispose();
    }

    // Calculate Y position from normalized floor value (0=top, 1=bottom)
    const y = -(floorY * compHeight - compHeight / 2);

    // Create horizon line spanning composition width
    const points = [
      new THREE.Vector3(-compWidth, y, 0),
      new THREE.Vector3(compWidth * 2, y, 0),
    ];

    const geometry = new THREE.BufferGeometry().setFromPoints(points);
    const material = new THREE.LineDashedMaterial({
      color: 0x00ffff,
      dashSize: 10,
      gapSize: 5,
      transparent: true,
      opacity: 0.7,
      depthTest: false,
    });

    this.horizonLine = new THREE.Line(geometry, material);
    this.horizonLine.computeLineDistances(); // Required for dashed lines
    this.horizonLine.name = "particle_horizon";
    this.horizonLine.renderOrder = 996;
    this.horizonLine.visible = this.showHorizonLine;

    this.group.add(this.horizonLine);
  }

  /**
   * Create particle space grid (CC Particle World style)
   */
  createParticleGrid(
    compWidth: number = 1920,
    compHeight: number = 1080,
    gridSize: number = 100,
    depth: number = 500,
  ): void {
    // Validate gridSize to prevent infinite loop
    const safeGridSize = Number.isFinite(gridSize) && gridSize > 0 ? gridSize : 100;
    const safeDepth = Number.isFinite(depth) && depth > 0 ? depth : 500;
    const safeCompWidth = Number.isFinite(compWidth) && compWidth > 0 ? compWidth : 1920;
    const safeCompHeight = Number.isFinite(compHeight) && compHeight > 0 ? compHeight : 1080;
    
    // Dispose existing
    if (this.particleGrid) {
      this.group.remove(this.particleGrid);
      this.particleGrid.traverse((child) => {
        if (child instanceof THREE.Line) {
          child.geometry.dispose();
          (child.material as THREE.Material).dispose();
        }
      });
    }

    this.particleGrid = new THREE.Group();
    this.particleGrid.name = "particle_grid";

    const material = new THREE.LineBasicMaterial({
      color: 0x444488,
      transparent: true,
      opacity: 0.4,
      depthTest: false,
    });

    const halfWidth = safeCompWidth / 2;
    const halfHeight = safeCompHeight / 2;

    // Horizontal grid lines (XZ plane at Y = halfHeight, i.e., bottom of comp)
    for (let z = 0; z <= safeDepth; z += safeGridSize) {
      const points = [
        new THREE.Vector3(-halfWidth, halfHeight, -z),
        new THREE.Vector3(halfWidth, halfHeight, -z),
      ];
      const geometry = new THREE.BufferGeometry().setFromPoints(points);
      const line = new THREE.Line(geometry, material.clone());
      this.particleGrid.add(line);
    }

    // Vertical grid lines (going into Z depth)
    const xCount = Math.ceil(safeCompWidth / safeGridSize);
    for (let i = 0; i <= xCount; i++) {
      const x = -halfWidth + i * safeGridSize;
      const points = [
        new THREE.Vector3(x, halfHeight, 0),
        new THREE.Vector3(x, halfHeight, -safeDepth),
      ];
      const geometry = new THREE.BufferGeometry().setFromPoints(points);
      const line = new THREE.Line(geometry, material.clone());
      this.particleGrid.add(line);
    }

    // Side grid lines (YZ plane at X = -halfWidth)
    for (let z = 0; z <= safeDepth; z += safeGridSize) {
      const points = [
        new THREE.Vector3(-halfWidth, -halfHeight, -z),
        new THREE.Vector3(-halfWidth, halfHeight, -z),
      ];
      const geometry = new THREE.BufferGeometry().setFromPoints(points);
      const line = new THREE.Line(geometry, material.clone());
      this.particleGrid.add(line);
    }

    this.particleGrid.renderOrder = 995;
    this.particleGrid.visible = this.showParticleGrid;

    this.group.add(this.particleGrid);
  }

  /**
   * Create particle space axis (CC Particle World style)
   */
  createParticleAxis(length: number = 200): void {
    // Dispose existing
    if (this.particleAxis) {
      this.group.remove(this.particleAxis);
      this.particleAxis.traverse((child) => {
        if (child instanceof THREE.Line) {
          child.geometry.dispose();
          (child.material as THREE.Material).dispose();
        }
      });
    }

    this.particleAxis = new THREE.Group();
    this.particleAxis.name = "particle_axis";

    // X axis (Red)
    const xMaterial = new THREE.LineBasicMaterial({
      color: 0xff0000,
      depthTest: false,
    });
    const xPoints = [
      new THREE.Vector3(0, 0, 0),
      new THREE.Vector3(length, 0, 0),
    ];
    const xLine = new THREE.Line(
      new THREE.BufferGeometry().setFromPoints(xPoints),
      xMaterial,
    );
    this.particleAxis.add(xLine);

    // Y axis (Green) - inverted for screen coordinates
    const yMaterial = new THREE.LineBasicMaterial({
      color: 0x00ff00,
      depthTest: false,
    });
    const yPoints = [
      new THREE.Vector3(0, 0, 0),
      new THREE.Vector3(0, -length, 0),
    ];
    const yLine = new THREE.Line(
      new THREE.BufferGeometry().setFromPoints(yPoints),
      yMaterial,
    );
    this.particleAxis.add(yLine);

    // Z axis (Blue)
    const zMaterial = new THREE.LineBasicMaterial({
      color: 0x0088ff,
      depthTest: false,
    });
    const zPoints = [
      new THREE.Vector3(0, 0, 0),
      new THREE.Vector3(0, 0, -length),
    ];
    const zLine = new THREE.Line(
      new THREE.BufferGeometry().setFromPoints(zPoints),
      zMaterial,
    );
    this.particleAxis.add(zLine);

    // Add axis labels (as small spheres at ends)
    const labelGeo = new THREE.SphereGeometry(5, 8, 8);
    const xLabel = new THREE.Mesh(
      labelGeo,
      new THREE.MeshBasicMaterial({ color: 0xff0000 }),
    );
    xLabel.position.set(length, 0, 0);
    this.particleAxis.add(xLabel);

    const yLabel = new THREE.Mesh(
      labelGeo.clone(),
      new THREE.MeshBasicMaterial({ color: 0x00ff00 }),
    );
    yLabel.position.set(0, -length, 0);
    this.particleAxis.add(yLabel);

    const zLabel = new THREE.Mesh(
      labelGeo.clone(),
      new THREE.MeshBasicMaterial({ color: 0x0088ff }),
    );
    zLabel.position.set(0, 0, -length);
    this.particleAxis.add(zLabel);

    this.particleAxis.renderOrder = 998;
    this.particleAxis.visible = this.showParticleAxis;

    this.group.add(this.particleAxis);
  }

  /**
   * Toggle horizon line visibility
   */
  setHorizonLineVisible(visible: boolean): void {
    this.showHorizonLine = visible;
    if (this.horizonLine) {
      this.horizonLine.visible = visible;
    }
  }

  /**
   * Toggle particle grid visibility
   */
  setParticleGridVisible(visible: boolean): void {
    this.showParticleGrid = visible;
    if (this.particleGrid) {
      this.particleGrid.visible = visible;
    }
  }

  /**
   * Toggle particle axis visibility
   */
  setParticleAxisVisible(visible: boolean): void {
    this.showParticleAxis = visible;
    if (this.particleAxis) {
      this.particleAxis.visible = visible;
    }
  }

  /**
   * Update horizon line position when floor Y changes
   */
  updateHorizonLine(floorY: number, compHeight: number = 1080): void {
    if (this.horizonLine) {
      const y = -(floorY * compHeight - compHeight / 2);
      const positions = this.horizonLine.geometry.attributes.position;
      (positions.array as Float32Array)[1] = y;
      (positions.array as Float32Array)[4] = y;
      positions.needsUpdate = true;
    }
  }

  /**
   * Get visualization visibility states
   */
  getVisualizationState(): {
    horizonLine: boolean;
    particleGrid: boolean;
    particleAxis: boolean;
  } {
    return {
      horizonLine: this.showHorizonLine,
      particleGrid: this.showParticleGrid,
      particleAxis: this.showParticleAxis,
    };
  }

  // ============================================================================
  // ACCESSORS
  // ============================================================================

  /**
   * Get the underlying particle system for advanced operations
   */
  getParticleSystem(): VerifiedGPUParticleSystem {
    return this.particleSystem;
  }

  /**
   * Get current particle count
   */
  getParticleCount(): number {
    return this.particleSystem.getState().particleCount;
  }

  /**
   * Check if system is initialized
   */
  isInitialized(): boolean {
    return this.initialized;
  }
}
