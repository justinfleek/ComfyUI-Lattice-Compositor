/**
 * Particle Store
 *
 * Domain store for particle system layer creation and emitter management.
 * Handles particle system configuration, emitter CRUD, and trajectory export.
 *
 * @see docs/MASTER_REFACTOR_PLAN.md
 */

import { defineStore } from "pinia";
import type {
  Composition,
  Layer,
  ParticleEmitterConfig,
  ParticleLayerData,
} from "@/types/project";
import { useLayerStore } from "@/stores/layerStore";

// ============================================================================
// STORE ACCESS INTERFACE
// ============================================================================

export interface ParticleStoreAccess {
  project: {
    composition: {
      width: number;
      height: number;
    };
    meta: { modified: string };
  };
  getActiveComp(): Composition | null;
  getActiveCompLayers(): Layer[];
  createLayer(type: Layer["type"], name?: string): Layer;
}

// ============================================================================
// EXPORT TYPES
// ============================================================================

/**
 * Baked particle trajectory for export.
 */
export interface BakedParticleTrajectory {
  particleId: number;
  emitterId: string;
  birthFrame: number;
  deathFrame: number;
  keyframes: Array<{
    frame: number;
    x: number;
    y: number;
    z: number;
    size: number;
    opacity: number;
    rotation: number;
    r: number;
    g: number;
    b: number;
  }>;
}

/**
 * Options for baking particles.
 */
export interface ParticleBakeOptions {
  startFrame?: number;
  endFrame?: number;
  maxParticles?: number;
  sampleInterval?: number;
  includeVelocity?: boolean;
  simplifyKeyframes?: boolean;
}

/**
 * Result of particle baking.
 */
export interface ParticleBakeResult {
  layerId: string;
  trajectories: BakedParticleTrajectory[];
  totalFrames: number;
  totalParticles: number;
  exportFormat: "trajectories" | "shapeLayers";
}

// ============================================================================
// PINIA STORE
// ============================================================================

export const useParticleStore = defineStore("particle", {
  state: () => ({}),

  getters: {},

  actions: {
    /**
     * Create a particle system layer with default configuration.
     *
     * @param store - Compositor store access
     * @returns The created particle layer
     */
    createParticleLayer(store: ParticleStoreAccess): Layer {
      const layerStore = useLayerStore();
      // Type assertion: compositorStore passed at runtime implements required interface
      const layer = layerStore.createLayer(
        store as unknown as Parameters<typeof layerStore.createLayer>[0],
        "particles",
        "Particle System"
      );

      const activeComp = store.getActiveComp();
      const compWidth =
        activeComp?.settings.width || store.project.composition.width;
      const compHeight =
        activeComp?.settings.height || store.project.composition.height;

      const particleData: ParticleLayerData = {
        systemConfig: {
          maxParticles: 10000,
          gravity: 0,
          windStrength: 0,
          windDirection: 0,
          warmupPeriod: 0,
          respectMaskBoundary: false,
          boundaryBehavior: "kill",
          friction: 0.01,
        },
        emitters: [
          {
            id: `emitter_${Date.now()}`,
            name: "Emitter 1",
            x: compWidth / 2,
            y: compHeight / 2,
            direction: 270,
            spread: 30,
            speed: 150,
            speedVariance: 30,
            size: 8,
            sizeVariance: 2,
            color: [255, 200, 100] as [number, number, number],
            emissionRate: 30,
            initialBurst: 0,
            particleLifetime: 90,
            lifetimeVariance: 15,
            enabled: true,
            burstOnBeat: false,
            burstCount: 20,
            shape: "point" as const,
            shapeRadius: 50,
            shapeWidth: 100,
            shapeHeight: 100,
            shapeDepth: 100,
            shapeInnerRadius: 25,
            emitFromEdge: false,
            emitFromVolume: false,
            splinePath: null,
            sprite: {
              enabled: false,
              imageUrl: null,
              imageData: null,
              isSheet: false,
              columns: 1,
              rows: 1,
              totalFrames: 1,
              frameRate: 30,
              playMode: "loop" as const,
              billboard: true,
              rotationEnabled: false,
              rotationSpeed: 0,
              rotationSpeedVariance: 0,
              alignToVelocity: false,
            },
          },
        ],
        gravityWells: [],
        vortices: [],
        modulations: [
          {
            id: `mod_${Date.now()}`,
            emitterId: "*",
            property: "opacity",
            startValue: 1,
            endValue: 0,
            easing: "linear",
          },
        ],
        renderOptions: {
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
          connections: {
            enabled: false,
            maxDistance: 100,
            maxConnections: 3,
            lineWidth: 1,
            lineOpacity: 0.5,
            fadeByDistance: true,
          },
        },
        turbulenceFields: [],
        subEmitters: [],
      };

      layer.data = particleData;

      return layer;
    },

    /**
     * Update particle layer data.
     *
     * @param store - Compositor store access
     * @param layerId - ID of particle layer to update
     * @param updates - Partial data updates
     */
    updateParticleLayerData(
      store: ParticleStoreAccess,
      layerId: string,
      updates: Partial<ParticleLayerData>,
    ): void {
      const layer = store.getActiveCompLayers().find((l) => l.id === layerId);
      if (!layer || layer.type !== "particles") return;

      const data = layer.data as ParticleLayerData;
      Object.assign(data, updates);
      store.project.meta.modified = new Date().toISOString();
    },

    /**
     * Add emitter to particle layer.
     *
     * @param store - Compositor store access
     * @param layerId - ID of particle layer
     * @param config - Emitter configuration
     */
    addParticleEmitter(
      store: ParticleStoreAccess,
      layerId: string,
      config: ParticleEmitterConfig,
    ): void {
      const layer = store.getActiveCompLayers().find((l) => l.id === layerId);
      if (!layer || layer.type !== "particles") return;

      const data = layer.data as ParticleLayerData;
      data.emitters.push(config);
      store.project.meta.modified = new Date().toISOString();
    },

    /**
     * Update particle emitter configuration.
     *
     * @param store - Compositor store access
     * @param layerId - ID of particle layer
     * @param emitterId - ID of emitter to update
     * @param updates - Partial emitter configuration updates
     */
    updateParticleEmitter(
      store: ParticleStoreAccess,
      layerId: string,
      emitterId: string,
      updates: Partial<ParticleEmitterConfig>,
    ): void {
      const layer = store.getActiveCompLayers().find((l) => l.id === layerId);
      if (!layer || layer.type !== "particles") return;

      const data = layer.data as ParticleLayerData;
      const emitter = data.emitters.find((e) => e.id === emitterId);
      if (emitter) {
        Object.assign(emitter, updates);
        store.project.meta.modified = new Date().toISOString();
      }
    },

    /**
     * Remove particle emitter.
     *
     * @param store - Compositor store access
     * @param layerId - ID of particle layer
     * @param emitterId - ID of emitter to remove
     */
    removeParticleEmitter(
      store: ParticleStoreAccess,
      layerId: string,
      emitterId: string,
    ): void {
      const layer = store.getActiveCompLayers().find((l) => l.id === layerId);
      if (!layer || layer.type !== "particles") return;

      const data = layer.data as ParticleLayerData;
      data.emitters = data.emitters.filter((e) => e.id !== emitterId);
      store.project.meta.modified = new Date().toISOString();
    },

    /**
     * Convert trajectory data to JSON for external tools.
     *
     * @param result - Bake result to export
     * @returns JSON string representation
     */
    exportTrajectoriesToJSON(result: ParticleBakeResult): string {
      return JSON.stringify(
        {
          version: "1.0",
          layerId: result.layerId,
          totalFrames: result.totalFrames,
          totalParticles: result.totalParticles,
          trajectories: result.trajectories.map((t) => ({
            id: t.particleId,
            emitter: t.emitterId,
            birth: t.birthFrame,
            death: t.deathFrame,
            path: t.keyframes.map((k) => ({
              f: k.frame,
              p: [k.x, k.y, k.z],
              s: k.size,
              o: k.opacity,
              r: k.rotation,
              c: [k.r, k.g, k.b],
            })),
          })),
        },
        null,
        2,
      );
    },
  },
});
