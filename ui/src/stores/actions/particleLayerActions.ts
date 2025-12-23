/**
 * Particle Layer Actions
 *
 * Particle system layer creation and emitter management.
 *
 * Extracted from compositorStore.ts for modularity.
 */

import type {
  Layer,
  Composition,
  ParticleLayerData,
  ParticleEmitterConfig
} from '@/types/project';

// ============================================================================
// STORE INTERFACE
// ============================================================================

export interface ParticleLayerStore {
  project: {
    composition: {
      width: number;
      height: number;
    };
    meta: { modified: string };
  };

  // Methods the actions need to call
  getActiveComp(): Composition | null;
  getActiveCompLayers(): Layer[];
  createLayer(type: Layer['type'], name?: string): Layer;
}

// ============================================================================
// PARTICLE LAYER CREATION
// ============================================================================

/**
 * Create a particle system layer
 */
export function createParticleLayer(store: ParticleLayerStore): Layer {
  const layer = store.createLayer('particles', 'Particle System');

  // Get active composition dimensions for emitter positioning
  const activeComp = store.getActiveComp();
  const compWidth = activeComp?.settings.width || store.project.composition.width;
  const compHeight = activeComp?.settings.height || store.project.composition.height;

  // Set up particle layer data
  const particleData: ParticleLayerData = {
    systemConfig: {
      maxParticles: 10000,
      gravity: 0,
      windStrength: 0,
      windDirection: 0,
      warmupPeriod: 0,
      respectMaskBoundary: false,
      boundaryBehavior: 'kill',
      friction: 0.01
    },
    emitters: [{
      id: `emitter_${Date.now()}`,
      name: 'Emitter 1',
      // Use pixel coordinates - center of composition
      x: compWidth / 2,
      y: compHeight / 2,
      direction: 270, // Up direction (270 degrees)
      spread: 30,
      speed: 150, // Pixels per second
      speedVariance: 30,
      size: 8,
      sizeVariance: 2,
      color: [255, 200, 100] as [number, number, number],
      emissionRate: 30, // Particles per second
      initialBurst: 0,
      particleLifetime: 90,
      lifetimeVariance: 15,
      enabled: true,
      burstOnBeat: false,
      burstCount: 20,
      // Geometric emitter shape defaults (in pixels)
      shape: 'point' as const,
      shapeRadius: 50,
      shapeWidth: 100,
      shapeHeight: 100,
      shapeDepth: 100,
      shapeInnerRadius: 25,
      emitFromEdge: false,
      emitFromVolume: false,
      // Spline path emission (null = disabled)
      splinePath: null,
      // Sprite configuration
      sprite: {
        enabled: false,
        imageUrl: null,
        imageData: null,
        isSheet: false,
        columns: 1,
        rows: 1,
        totalFrames: 1,
        frameRate: 30,
        playMode: 'loop' as const,
        billboard: true,
        rotationEnabled: false,
        rotationSpeed: 0,
        rotationSpeedVariance: 0,
        alignToVelocity: false
      }
    }],
    gravityWells: [],
    vortices: [],
    modulations: [{
      id: `mod_${Date.now()}`,
      emitterId: '*',
      property: 'opacity',
      startValue: 1,
      endValue: 0,
      easing: 'linear'
    }],
    renderOptions: {
      blendMode: 'additive',
      renderTrails: false,
      trailLength: 5,
      trailOpacityFalloff: 0.7,
      particleShape: 'circle',
      glowEnabled: false,
      glowRadius: 10,
      glowIntensity: 0.5,
      motionBlur: false,
      motionBlurStrength: 0.5,
      motionBlurSamples: 8,
      connections: {
        enabled: false,
        maxDistance: 100,
        maxConnections: 3,
        lineWidth: 1,
        lineOpacity: 0.5,
        fadeByDistance: true
      }
    },
    turbulenceFields: [],
    subEmitters: []
  };

  layer.data = particleData;

  return layer;
}

// ============================================================================
// PARTICLE LAYER DATA UPDATES
// ============================================================================

/**
 * Update particle layer data
 */
export function updateParticleLayerData(
  store: ParticleLayerStore,
  layerId: string,
  updates: Partial<ParticleLayerData>
): void {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer || layer.type !== 'particles') return;

  const data = layer.data as ParticleLayerData;
  Object.assign(data, updates);
  store.project.meta.modified = new Date().toISOString();
}

/**
 * Add emitter to particle layer
 */
export function addParticleEmitter(
  store: ParticleLayerStore,
  layerId: string,
  config: ParticleEmitterConfig
): void {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer || layer.type !== 'particles') return;

  const data = layer.data as ParticleLayerData;
  data.emitters.push(config);
  store.project.meta.modified = new Date().toISOString();
}

/**
 * Update particle emitter
 */
export function updateParticleEmitter(
  store: ParticleLayerStore,
  layerId: string,
  emitterId: string,
  updates: Partial<ParticleEmitterConfig>
): void {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer || layer.type !== 'particles') return;

  const data = layer.data as ParticleLayerData;
  const emitter = data.emitters.find(e => e.id === emitterId);
  if (emitter) {
    Object.assign(emitter, updates);
    store.project.meta.modified = new Date().toISOString();
  }
}

/**
 * Remove particle emitter
 */
export function removeParticleEmitter(
  store: ParticleLayerStore,
  layerId: string,
  emitterId: string
): void {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer || layer.type !== 'particles') return;

  const data = layer.data as ParticleLayerData;
  data.emitters = data.emitters.filter(e => e.id !== emitterId);
  store.project.meta.modified = new Date().toISOString();
}
