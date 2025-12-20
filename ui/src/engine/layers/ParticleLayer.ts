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

import * as THREE from 'three';
import type { Layer, ParticleLayerData, ParticleEmitterConfig } from '@/types/project';
import type {
  EmitterConfig,
  ForceFieldConfig,
  AudioFeature,
  GPUParticleSystemConfig,
  SubEmitterConfig as GPUSubEmitterConfig,
  FlockingConfig,
  EmitterShapeConfig,
} from '../particles/types';
import { BaseLayer } from './BaseLayer';
import { GPUParticleSystem, createDefaultConfig, createDefaultEmitter, createDefaultForceField } from '../particles/GPUParticleSystem';

export class ParticleLayer extends BaseLayer {
  /** The GPU particle system instance */
  private particleSystem: GPUParticleSystem;

  /** Particle system configuration */
  private systemConfig: GPUParticleSystemConfig;

  /** Whether the system has been initialized with a renderer */
  private initialized = false;

  /** Stored renderer reference for reinitialization */
  private rendererRef: THREE.WebGLRenderer | null = null;

  /** Composition FPS for time calculation */
  private fps: number = 60;

  /** Deterministic seed derived from layer ID */
  private readonly layerSeed: number;

  /** Last evaluated frame (for scrub detection) */
  private lastEvaluatedFrame: number = -1;

  /** Performance stats */
  private stats = {
    particleCount: 0,
    updateTimeMs: 0,
    renderTimeMs: 0,
  };

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

  constructor(layerData: Layer) {
    super(layerData);

    // Generate deterministic seed from layer ID
    // DETERMINISM: Same layer ID always produces same seed
    this.layerSeed = this.generateSeedFromId(layerData.id);

    // Build configuration from layer data (with deterministic seed)
    this.systemConfig = this.buildSystemConfig(layerData);
    this.systemConfig.randomSeed = this.layerSeed;

    // Create particle system with deterministic seed
    this.particleSystem = new GPUParticleSystem(this.systemConfig);

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
      hash = ((hash << 5) - hash) + char;
      hash = hash & hash; // Convert to 32bit integer
    }
    return Math.abs(hash) || 12345; // Fallback to 12345 if 0
  }

  /**
   * Convert emitter shape from project format to GPU format
   * Supports: point, circle, sphere, box, line, ring, cone, spline
   */
  private convertEmitterShape(emitter: ParticleEmitterConfig): EmitterShapeConfig {
    const shape = emitter.shape ?? 'point';

    switch (shape) {
      case 'point':
        return { type: 'point' };

      case 'circle':
        return {
          type: 'circle',
          radius: emitter.shapeRadius ?? 50,
          emitFromEdge: emitter.emitFromEdge ?? false,
        };

      case 'sphere':
        return {
          type: 'sphere',
          radius: emitter.shapeRadius ?? 50,
          emitFromEdge: emitter.emitFromEdge ?? false,
        };

      case 'box':
        return {
          type: 'box',
          boxSize: {
            x: emitter.shapeWidth ?? 100,
            y: emitter.shapeHeight ?? 100,
            z: emitter.shapeDepth ?? 0,
          },
        };

      case 'line':
        // Line extends from emitter position in both directions
        const halfWidth = (emitter.shapeWidth ?? 100) / 2;
        return {
          type: 'line',
          lineStart: { x: -halfWidth, y: 0, z: 0 },
          lineEnd: { x: halfWidth, y: 0, z: 0 },
        };

      case 'ring':
        return {
          type: 'circle',
          radius: emitter.shapeRadius ?? 50,
          radiusVariance: emitter.shapeInnerRadius ?? 0,
          emitFromEdge: true, // Ring always emits from edge
        };

      case 'spline':
        // Spline emission - use splinePath config if available
        if (emitter.splinePath) {
          return {
            type: 'spline',
            splineId: emitter.splinePath.layerId,
            splineOffset: emitter.splinePath.parameter ?? 0,
          };
        }
        return { type: 'point' }; // Fallback if no spline configured

      case 'depth-map':
      case 'mask':
        // These require additional setup - fall back to point for now
        // TODO: Wire depth-map and mask emission when image data is available
        return { type: 'point' };

      default:
        return { type: 'point' };
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
      config.emitters = [createDefaultEmitter('default')];
      return config;
    }

    // System settings
    if (data.systemConfig) {
      config.maxParticles = data.systemConfig.maxParticles ?? 100000;
      config.timeScale = 1;

      // Add global gravity as a force field
      if (data.systemConfig.gravity !== 0) {
        config.forceFields.push({
          id: 'global_gravity',
          name: 'Gravity',
          type: 'gravity',
          enabled: true,
          strength: data.systemConfig.gravity * 10,
          position: { x: 0, y: 0, z: 0 },
          falloffStart: 0,
          falloffEnd: 10000,
          falloffType: 'none',
          direction: { x: 0, y: 1, z: 0 },
        });
      }

      // Add global wind as a force field
      if (data.systemConfig.windStrength !== 0) {
        const windAngle = (data.systemConfig.windDirection ?? 0) * Math.PI / 180;
        config.forceFields.push({
          id: 'global_wind',
          name: 'Wind',
          type: 'wind',
          enabled: true,
          strength: data.systemConfig.windStrength,
          position: { x: 0, y: 0, z: 0 },
          falloffStart: 0,
          falloffEnd: 10000,
          falloffType: 'none',
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
          id: 'global_drag',
          name: 'Friction',
          type: 'drag',
          enabled: true,
          strength: 1,
          position: { x: 0, y: 0, z: 0 },
          falloffStart: 0,
          falloffEnd: 10000,
          falloffType: 'none',
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
              name: 'Turbulence',
              type: 'turbulence',
              enabled: true,
              strength: turbField.strength,
              position: { x: 0, y: 0, z: 0 },
              falloffStart: 0,
              falloffEnd: 10000,
              falloffType: 'none',
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

        const dirRad = (emitter.direction ?? 0) * Math.PI / 180;

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
          type: 'point',
          enabled: true,
          strength: well.strength,
          position: { x: well.x, y: well.y, z: 0 },
          falloffStart: 0,
          falloffEnd: well.radius,
          falloffType: well.falloff === 'linear' ? 'linear' :
                       well.falloff === 'quadratic' ? 'quadratic' : 'none',
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
          type: 'vortex',
          enabled: true,
          strength: vortex.strength * vortex.rotationSpeed,
          position: { x: vortex.x, y: vortex.y, z: 0 },
          falloffStart: 0,
          falloffEnd: vortex.radius,
          falloffType: 'linear',
          vortexAxis: { x: 0, y: 0, z: 1 },
          inwardForce: vortex.inwardPull,
        });
      }
    }

    // Convert modulations to lifetime curves
    if (data.modulations) {
      // Group by emitter
      const sizeModulations = data.modulations.filter(m => m.property === 'size');
      if (sizeModulations.length > 0) {
        const mod = sizeModulations[0];
        config.lifetimeModulation.sizeOverLifetime = {
          type: 'linear',
          start: mod.startValue / 100,
          end: mod.endValue / 100,
        };
      }

      const opacityModulations = data.modulations.filter(m => m.property === 'opacity');
      if (opacityModulations.length > 0) {
        const mod = opacityModulations[0];
        config.lifetimeModulation.opacityOverLifetime = {
          type: 'linear',
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
    if (data.flocking?.enabled) {
      config.flocking = {
        enabled: true,
        separationWeight: (data.flocking.separationWeight ?? 50) / 100,
        separationRadius: data.flocking.separationRadius ?? 25,
        alignmentWeight: (data.flocking.alignmentWeight ?? 50) / 100,
        alignmentRadius: data.flocking.alignmentRadius ?? 50,
        cohesionWeight: (data.flocking.cohesionWeight ?? 50) / 100,
        cohesionRadius: data.flocking.cohesionRadius ?? 50,
        maxSpeed: data.flocking.maxSpeed ?? 200,
        maxForce: data.flocking.maxForce ?? 10,
        perceptionAngle: data.flocking.perceptionAngle ?? 270,
      };
    }

    // Store collision configuration for initialization after GPU setup
    if (data.collision?.enabled) {
      this.pendingCollisionConfig = {
        enabled: true,
        particleCollision: data.collision.particleCollision ?? false,
        particleRadius: data.collision.particleRadius ?? 5,
        bounciness: data.collision.bounciness ?? 0.5,
        friction: data.collision.friction ?? 0.1,
        bounds: data.collision.boundaryEnabled ? {
          min: { x: data.collision.boundaryPadding, y: data.collision.boundaryPadding, z: -1000 },
          max: { x: 1920 - data.collision.boundaryPadding, y: 1080 - data.collision.boundaryPadding, z: 1000 },
        } : undefined,
        boundsBehavior: data.collision.boundaryBehavior ?? 'none',
      };
    }

    // Render options
    if (data.renderOptions) {
      config.render.blendMode = data.renderOptions.blendMode ?? 'normal';
      config.render.motionBlur = data.renderOptions.motionBlur ?? false;
      config.render.motionBlurStrength = data.renderOptions.motionBlurStrength ?? 0.5;
      config.render.motionBlurSamples = data.renderOptions.motionBlurSamples ?? 4;

      // Trails
      if (data.renderOptions.renderTrails) {
        config.render.mode = 'trail';
        config.render.trailLength = data.renderOptions.trailLength;
        config.render.trailWidthEnd = 1 - (data.renderOptions.trailOpacityFalloff ?? 0.8);
      }

      // Particle shape affects procedural rendering
      config.render.texture.proceduralType =
        data.renderOptions.particleShape === 'star' ? 'star' :
        data.renderOptions.particleShape === 'square' ? 'square' :
        'circle';

      // Connections - wire UI settings to GPU config
      if (data.renderOptions.connections?.enabled) {
        // Store connection config for initialization after GPU setup
        this.pendingConnectionConfig = {
          enabled: true,
          maxDistance: data.renderOptions.connections.maxDistance ?? 100,
          maxConnections: data.renderOptions.connections.maxConnections ?? 5,
          lineWidth: data.renderOptions.connections.lineWidth ?? 1,
          lineOpacity: data.renderOptions.connections.lineOpacity ?? 0.5,
          fadeByDistance: data.renderOptions.connections.fadeByDistance ?? true,
          color: data.renderOptions.connections.color ?
            [data.renderOptions.connections.color[0] / 255,
             data.renderOptions.connections.color[1] / 255,
             data.renderOptions.connections.color[2] / 255] : undefined,
        };
      }

      // Glow settings - store for post-processing
      if (data.renderOptions.glowEnabled) {
        this.pendingGlowConfig = {
          enabled: true,
          radius: data.renderOptions.glowRadius ?? 10,
          intensity: data.renderOptions.glowIntensity ?? 0.5,
        };
      }

      // Sprite sheet settings
      if (data.renderOptions.spriteEnabled && data.renderOptions.spriteImageUrl) {
        this.pendingSpriteConfig = {
          url: data.renderOptions.spriteImageUrl,
          columns: data.renderOptions.spriteColumns ?? 1,
          rows: data.renderOptions.spriteRows ?? 1,
          animate: data.renderOptions.spriteAnimate ?? false,
          frameRate: data.renderOptions.spriteFrameRate ?? 10,
          randomStart: data.renderOptions.spriteRandomStart ?? false,
        };
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
    bounds?: { min: { x: number; y: number; z: number }; max: { x: number; y: number; z: number } };
    boundsBehavior: 'none' | 'kill' | 'bounce' | 'wrap';
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
      this.particleSystem.loadTexture(this.pendingSpriteConfig.url, {
        columns: this.pendingSpriteConfig.columns,
        rows: this.pendingSpriteConfig.rows,
        animate: this.pendingSpriteConfig.animate,
        frameRate: this.pendingSpriteConfig.frameRate,
        randomStart: this.pendingSpriteConfig.randomStart,
      }).catch(err => {
        console.warn('Failed to load particle sprite:', err);
      });
      this.pendingSpriteConfig = null;
    }

    // Initialize glow effect and add glow mesh
    if (this.pendingGlowConfig && this.pendingGlowConfig.enabled) {
      this.particleSystem.initializeGlow(this.pendingGlowConfig);
      const glowMesh = this.particleSystem.getGlowMesh();
      if (glowMesh) {
        this.group.add(glowMesh);
      }
      this.glowConfig = this.pendingGlowConfig;
      this.pendingGlowConfig = null;
    }

    // Initialize collision detection
    if (this.pendingCollisionConfig && this.pendingCollisionConfig.enabled) {
      this.particleSystem.initializeCollisions(this.pendingCollisionConfig);
      this.pendingCollisionConfig = null;
    }

    // Create emitter and force field gizmos for visualization
    this.createGizmos();
  }

  // Glow configuration
  private glowConfig: { enabled: boolean; radius: number; intensity: number } | null = null;

  /**
   * Get glow configuration
   */
  getGlowConfig(): { enabled: boolean; radius: number; intensity: number } | null {
    return this.glowConfig;
  }

  /**
   * Update glow settings at runtime
   */
  setGlow(config: { enabled?: boolean; radius?: number; intensity?: number }): void {
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
   * Set composition FPS for accurate time calculation
   */
  setFPS(fps: number): void {
    this.fps = fps;
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
  addForceField(type: ForceFieldConfig['type'], config?: Partial<ForceFieldConfig>): string {
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
    onProgress?: (current: number, total: number) => void
  ): Promise<void> {
    const totalFrames = endFrame - startFrame + 1;

    // Simulate from start to end, building cache along the way
    for (let frame = startFrame; frame <= endFrame; frame++) {
      this.particleSystem.simulateToFrame(frame, this.fps);

      if (onProgress) {
        onProgress(frame - startFrame + 1, totalFrames);
      }

      // Yield to prevent blocking UI (every 10 frames)
      if ((frame - startFrame) % 10 === 0) {
        await new Promise(resolve => setTimeout(resolve, 0));
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
  // ABSTRACT IMPLEMENTATIONS
  // ============================================================================

  protected onEvaluateFrame(frame: number): void {
    // DETERMINISM: Use frame caching system for scrub-safe particle evaluation
    // The simulateToFrame method handles:
    // - Sequential playback (single step)
    // - Forward scrubbing (continue from current)
    // - Backward/random scrubbing (restore from nearest cache or reset)
    // - Automatic caching every N frames
    const stepsPerformed = this.particleSystem.simulateToFrame(frame, this.fps);

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
        `ParticleLayer: Simulated ${stepsPerformed} frames to reach frame ${frame}. ` +
        `Cache: ${cacheStats.cachedFrames} frames cached`
      );
    }
  }

  protected override onApplyEvaluatedState(state: import('../MotionEngine').EvaluatedLayer): void {
    // ParticleLayer needs to step the simulation for the current frame
    // The evaluated state includes the frame number for deterministic simulation
    const frame = state.frame ?? 0;

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
   * Apply audio-reactive values to particle system emitters and force fields
   */
  private applyAudioReactivity(): void {
    // Map audio reactive targets to particle system features
    const emissionRate = this.getAudioReactiveValue('particle.emissionRate');
    const speed = this.getAudioReactiveValue('particle.speed');
    const size = this.getAudioReactiveValue('particle.size');
    const gravity = this.getAudioReactiveValue('particle.gravity');
    const windStrength = this.getAudioReactiveValue('particle.windStrength');

    // Set audio features on the particle system (values are 0-1 normalized)
    if (emissionRate !== 0) {
      this.particleSystem.setAudioFeature('amplitude', emissionRate);
    }

    // Update emitters based on audio
    if (speed !== 0 || size !== 0 || emissionRate !== 0) {
      const emitters = this.particleSystem.getConfig().emitters;
      for (const emitter of emitters) {
        // Speed modulation (0.5 base + audio value for range 0.5x to 1.5x)
        if (speed !== 0) {
          this.particleSystem.updateEmitter(emitter.id, {
            initialSpeed: emitter.initialSpeed * (0.5 + speed)
          });
        }

        // Size modulation
        if (size !== 0) {
          this.particleSystem.updateEmitter(emitter.id, {
            initialSize: emitter.initialSize * (0.5 + size)
          });
        }
      }
    }

    // Update force fields based on audio
    if (gravity !== 0 || windStrength !== 0) {
      const forceFields = this.particleSystem.getConfig().forceFields;
      for (const field of forceFields) {
        if (field.type === 'gravity' && gravity !== 0) {
          this.particleSystem.updateForceField(field.id, {
            strength: field.strength * (0.5 + gravity)
          });
        }
        if (field.type === 'wind' && windStrength !== 0) {
          this.particleSystem.updateForceField(field.id, {
            strength: field.strength * (0.5 + windStrength)
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
      // Remove old mesh from group
      const oldMesh = this.particleSystem.getMesh();
      if (oldMesh) {
        this.group.remove(oldMesh);
      }

      // Rebuild configuration and reinitialize
      this.systemConfig = this.buildSystemConfig({
        ...properties,
        id: this.id,
        type: 'particles',
      } as Layer);

      // DETERMINISM: Preserve the layer-specific seed
      this.systemConfig.randomSeed = this.layerSeed;

      // Dispose old system
      this.particleSystem.dispose();

      // Create new system with deterministic seed
      this.particleSystem = new GPUParticleSystem(this.systemConfig);

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
      case 'point': {
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

      case 'circle': {
        // Circle emitter: ring shape
        const ringGeom = new THREE.RingGeometry(
          (emitter.shape.radius ?? 50) * 0.8,
          emitter.shape.radius ?? 50,
          32
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

      case 'sphere': {
        // Sphere emitter: wireframe sphere
        const sphereGeom = new THREE.SphereGeometry(emitter.shape.radius ?? 50, 16, 16);
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

      case 'box': {
        // Box emitter: wireframe box
        const boxGeom = new THREE.BoxGeometry(
          emitter.shape.boxSize?.x ?? 100,
          emitter.shape.boxSize?.y ?? 100,
          emitter.shape.boxSize?.z ?? 100
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

      case 'cone': {
        // Cone emitter: wireframe cone
        const coneGeom = new THREE.ConeGeometry(
          emitter.shape.coneRadius ?? 30,
          emitter.shape.coneLength ?? 100,
          16,
          1,
          true
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

        const hPoints = [new THREE.Vector3(-size, 0, 0), new THREE.Vector3(size, 0, 0)];
        const vPoints = [new THREE.Vector3(0, -size, 0), new THREE.Vector3(0, size, 0)];

        const hLine = new THREE.Line(
          new THREE.BufferGeometry().setFromPoints(hPoints),
          lineMat
        );
        const vLine = new THREE.Line(
          new THREE.BufferGeometry().setFromPoints(vPoints),
          lineMat.clone()
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
        new THREE.Vector3(dir.x * arrowLength, -dir.y * arrowLength, dir.z * arrowLength),
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
      case 'gravity':
      case 'wind': {
        // Arrow pointing in force direction
        const dir = field.type === 'wind' && field.windDirection
          ? field.windDirection
          : (field.direction ?? { x: 0, y: 1, z: 0 });

        const arrowLength = 60;
        const arrowPoints = [
          new THREE.Vector3(0, 0, 0),
          new THREE.Vector3(dir.x * arrowLength, -dir.y * arrowLength, dir.z * arrowLength),
        ];
        const arrowGeom = new THREE.BufferGeometry().setFromPoints(arrowPoints);
        const arrowMat = new THREE.LineBasicMaterial({
          color: field.type === 'gravity' ? 0xff8800 : 0x00aaff,
          linewidth: 2,
          depthTest: false,
        });
        const arrow = new THREE.Line(arrowGeom, arrowMat);
        gizmo.add(arrow);

        // Add arrowhead
        const headGeom = new THREE.ConeGeometry(5, 15, 6);
        const headMat = new THREE.MeshBasicMaterial({
          color: field.type === 'gravity' ? 0xff8800 : 0x00aaff,
          depthTest: false,
        });
        const head = new THREE.Mesh(headGeom, headMat);
        head.position.set(
          dir.x * arrowLength,
          -dir.y * arrowLength,
          dir.z * arrowLength
        );
        // Point arrowhead in direction
        head.lookAt(0, 0, 0);
        gizmo.add(head);
        break;
      }

      case 'vortex': {
        // Spiral icon
        const spiralPoints: THREE.Vector3[] = [];
        for (let t = 0; t < Math.PI * 4; t += 0.2) {
          const r = (t / (Math.PI * 4)) * radius * 0.5;
          spiralPoints.push(new THREE.Vector3(
            Math.cos(t) * r,
            Math.sin(t) * r,
            t * 2
          ));
        }
        const spiralGeom = new THREE.BufferGeometry().setFromPoints(spiralPoints);
        const spiralMat = new THREE.LineBasicMaterial({
          color: 0xff00ff,
          depthTest: false,
        });
        const spiral = new THREE.Line(spiralGeom, spiralMat);
        gizmo.add(spiral);
        break;
      }

      case 'turbulence': {
        // Wavy lines
        const waveMat = new THREE.LineBasicMaterial({
          color: 0xffaa00,
          depthTest: false,
        });

        for (let i = 0; i < 3; i++) {
          const wavePoints: THREE.Vector3[] = [];
          for (let t = 0; t < Math.PI * 2; t += 0.3) {
            wavePoints.push(new THREE.Vector3(
              t * 10,
              Math.sin(t * 3 + i) * 10,
              (i - 1) * 15
            ));
          }
          const waveGeom = new THREE.BufferGeometry().setFromPoints(wavePoints);
          const wave = new THREE.Line(waveGeom, waveMat.clone());
          wave.position.x = -30;
          gizmo.add(wave);
        }
        break;
      }

      case 'point': {
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

      case 'drag': {
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
        gizmo.position.set(emitter.position.x, -emitter.position.y, emitter.position.z);
      }
    }

    for (const field of config.forceFields) {
      const gizmo = this.forceFieldGizmos.get(field.id);
      if (gizmo) {
        gizmo.position.set(field.position.x, -field.position.y, field.position.z);
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
  }

  // ============================================================================
  // ACCESSORS
  // ============================================================================

  /**
   * Get the underlying particle system for advanced operations
   */
  getParticleSystem(): GPUParticleSystem {
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
