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
import type { Layer, ParticleLayerData } from '@/types/project';
import type {
  EmitterConfig,
  ForceFieldConfig,
  AudioFeature,
  GPUParticleSystemConfig,
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
        const gpuEmitter: EmitterConfig = {
          id: emitter.id,
          name: emitter.name,
          enabled: true,
          position: { x: emitter.x, y: emitter.y, z: 0 },
          rotation: { x: 0, y: 0, z: 0 },
          shape: { type: 'point' },
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
    }

    return config;
  }

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

  // ============================================================================
  // ABSTRACT IMPLEMENTATIONS
  // ============================================================================

  protected onEvaluateFrame(frame: number): void {
    // DETERMINISM: Scrub-safe particle evaluation
    // When scrubbing backwards or to a non-sequential frame, we must
    // reset and replay to ensure consistent results
    const isSequential = frame === this.lastEvaluatedFrame + 1;
    const needsReplay = !isSequential && frame !== this.lastEvaluatedFrame;

    if (needsReplay) {
      // Reset to initial state (restores RNG seed)
      this.particleSystem.reset();

      // Replay from frame 0 to target frame
      // This ensures identical results regardless of scrub order
      const deltaTime = 1 / this.fps;
      for (let f = 0; f < frame; f++) {
        this.particleSystem.step(deltaTime);
      }
    } else if (isSequential) {
      // Sequential playback - just step once
      const deltaTime = 1 / this.fps;
      this.particleSystem.step(deltaTime);
    }
    // If frame === lastEvaluatedFrame, no stepping needed (cached result)

    this.lastEvaluatedFrame = frame;

    // Apply audio-reactive values after simulation
    this.applyAudioReactivity();

    // Update stats
    const state = this.particleSystem.getState();
    this.stats.particleCount = state.particleCount;
    this.stats.updateTimeMs = state.updateTimeMs;
    this.stats.renderTimeMs = state.renderTimeMs;
  }

  /**
   * Evaluate particles at a specific frame (scrub-safe)
   * DETERMINISM: Returns identical results regardless of evaluation order
   */
  evaluateAtFrame(frame: number): void {
    // Reset to initial state
    this.particleSystem.reset();

    // Step to target frame
    const deltaTime = 1 / this.fps;
    for (let f = 0; f < frame; f++) {
      this.particleSystem.step(deltaTime);
    }

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
