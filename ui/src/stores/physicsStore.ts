/**
 * Physics Store
 *
 * Domain store for Newton Physics Simulation integration.
 * Provides control over physics simulation, baking to keyframes,
 * and physics space configuration.
 *
 * @see docs/MASTER_REFACTOR_PLAN.md Phase 4
 */

import { defineStore } from "pinia";
import {
  createPhysicsEngine,
  createBoxBody,
  createCircleBody,
  createGravityForce,
  createClothConfig,
  createRagdollBuilder,
  type PhysicsEngine,
} from "@/services/physics";
import type {
  PhysicsSimulationState,
  PhysicsSpaceConfig,
  PhysicsLayerData,
  RigidBodyConfig,
  ForceField,
} from "@/types/physics";
import type { Keyframe, Layer } from "@/types/project";
import { storeLogger } from "@/utils/logger";
import { useLayerStore } from "@/stores/layerStore";

// ============================================================================
// STORE ACCESS INTERFACE
// ============================================================================

/**
 * Interface for compositorStore access during transition period.
 * Will be removed in Phase 5 when compositorStore is deleted.
 */
export interface PhysicsStoreAccess {
  activeCompositionId: string;
  currentFrame: number;
  project: {
    compositions: Record<
      string,
      {
        layers: Layer[];
        settings: {
          width: number;
          height: number;
          frameCount: number;
          fps: number;
        };
      }
    >;
  };
  getLayerById(id: string): Layer | null;
  updateLayerData(layerId: string, data: Record<string, unknown>): void;
  addKeyframe<T>(
    layerId: string,
    propertyName: string,
    value: T,
    atFrame?: number,
  ): Keyframe<T> | null;
}

// ============================================================================
// BAKING TYPES
// ============================================================================

export interface BakedKeyframe<T> {
  frame: number;
  value: T;
  interpolation: "linear" | "bezier";
}

export interface BakeOptions {
  startFrame?: number;
  endFrame?: number;
  sampleInterval?: number;
  simplify?: boolean;
}

export interface BakeResult {
  layerId: string;
  positionKeyframes: BakedKeyframe<{ x: number; y: number; z: number }>[];
  rotationKeyframes: BakedKeyframe<number>[];
}

// ============================================================================
// MODULE-LEVEL STATE
// ============================================================================

/** Global physics engine instance */
let physicsEngine: PhysicsEngine | null = null;

/** Per-composition physics states for deterministic scrubbing */
const compositionPhysicsStates = new Map<string, PhysicsSimulationState>();

/** Track force fields per composition */
const compositionForceFields = new Map<string, ForceField[]>();

// ============================================================================
// PINIA STORE
// ============================================================================

export const usePhysicsStore = defineStore("physics", {
  state: () => ({}),

  getters: {},

  actions: {
    // ========================================================================
    // Engine Lifecycle
    // ========================================================================

    /**
     * Initialize physics engine for the current composition
     */
    initializePhysicsEngine(
      store: PhysicsStoreAccess,
      config?: Partial<PhysicsSpaceConfig>,
    ): PhysicsEngine {
      const comp = store.project.compositions[store.activeCompositionId];
      if (!comp) {
        throw new Error("No active composition");
      }

      physicsEngine = createPhysicsEngine(config);
      storeLogger.info(
        "Physics engine initialized for composition",
        store.activeCompositionId,
      );
      return physicsEngine;
    },

    /**
     * Get or create physics engine
     */
    getPhysicsEngine(store: PhysicsStoreAccess): PhysicsEngine {
      if (!physicsEngine) {
        return this.initializePhysicsEngine(store);
      }
      return physicsEngine;
    },

    /**
     * Dispose physics engine
     */
    disposePhysicsEngine(): void {
      physicsEngine = null;
      compositionPhysicsStates.clear();
      compositionForceFields.clear();
      storeLogger.info("Physics engine disposed");
    },

    // ========================================================================
    // Rigid Body Management
    // ========================================================================

    /**
     * Enable physics for a layer as a rigid body
     */
    enableLayerPhysics(
      store: PhysicsStoreAccess,
      layerId: string,
      config: Partial<RigidBodyConfig> = {},
    ): void {
      const layer = store.getLayerById(layerId);
      if (!layer) {
        storeLogger.warn("Layer not found for physics:", layerId);
        return;
      }

      const engine = this.getPhysicsEngine(store);

      const position = {
        x: layer.transform?.position?.value?.x ?? 0,
        y: layer.transform?.position?.value?.y ?? 0,
      };

      const bodyConfig =
        config.shape?.type === "circle"
          ? createCircleBody(layerId, layerId, {
              position,
              radius: config.shape.radius ?? 50,
              mass: config.mass ?? 1,
              isStatic: config.type === "static",
            })
          : createBoxBody(layerId, layerId, {
              position,
              width: config.shape?.width ?? 100,
              height: config.shape?.height ?? 100,
              mass: config.mass ?? 1,
              isStatic: config.type === "static",
            });

      const finalConfig: RigidBodyConfig = {
        ...bodyConfig,
        ...config,
        id: layerId,
        layerId,
      };

      engine.addRigidBody(finalConfig);

      const physicsData: PhysicsLayerData = {
        physicsEnabled: true,
        rigidBody: finalConfig,
      };

      store.updateLayerData(layerId, { physics: physicsData });
      storeLogger.info("Physics enabled for layer:", layerId);
    },

    /**
     * Disable physics for a layer
     */
    disableLayerPhysics(store: PhysicsStoreAccess, layerId: string): void {
      const engine = this.getPhysicsEngine(store);
      engine.removeRigidBody(layerId);

      store.updateLayerData(layerId, {
        physics: { physicsEnabled: false },
      });
      storeLogger.info("Physics disabled for layer:", layerId);
    },

    /**
     * Update physics body for a layer
     */
    updateLayerPhysicsConfig(
      store: PhysicsStoreAccess,
      layerId: string,
      updates: Partial<RigidBodyConfig>,
    ): void {
      const layer = store.getLayerById(layerId);
      if (!layer) return;

      const physicsData = (layer.data as unknown as Record<string, unknown>)?.physics as
        | PhysicsLayerData
        | undefined;
      if (!physicsData?.physicsEnabled || !physicsData.rigidBody) return;

      const engine = this.getPhysicsEngine(store);
      engine.removeRigidBody(layerId);

      const newConfig: RigidBodyConfig = {
        ...physicsData.rigidBody,
        ...updates,
      };

      engine.addRigidBody(newConfig);

      store.updateLayerData(layerId, {
        physics: {
          ...physicsData,
          rigidBody: newConfig,
        },
      });
    },

    // ========================================================================
    // Force Field Management
    // ========================================================================

    /**
     * Add a force field to the physics simulation
     */
    addForceField(store: PhysicsStoreAccess, force: ForceField): void {
      const engine = this.getPhysicsEngine(store);
      const compId = store.activeCompositionId;

      const fields = compositionForceFields.get(compId) || [];
      const existingIndex = fields.findIndex((f) => f.id === force.id);

      if (existingIndex >= 0) {
        fields[existingIndex] = force;
      } else {
        fields.push(force);
      }

      compositionForceFields.set(compId, fields);
      engine.setForceFields(fields);
      storeLogger.info("Force field added:", force.id);
    },

    /**
     * Remove a force field
     */
    removeForceField(store: PhysicsStoreAccess, forceId: string): void {
      const engine = this.getPhysicsEngine(store);
      const compId = store.activeCompositionId;

      const fields = compositionForceFields.get(compId) || [];
      const newFields = fields.filter((f) => f.id !== forceId);

      compositionForceFields.set(compId, newFields);
      engine.setForceFields(newFields);
      storeLogger.info("Force field removed:", forceId);
    },

    /**
     * Set global gravity
     */
    setGravity(
      store: PhysicsStoreAccess,
      gravityX: number,
      gravityY: number,
    ): void {
      const safeGravityX = Number.isFinite(gravityX) ? gravityX : 0;
      const safeGravityY = Number.isFinite(gravityY) ? gravityY : 0;

      const engine = this.getPhysicsEngine(store);
      const compId = store.activeCompositionId;

      const fields = compositionForceFields.get(compId) || [];
      const newFields = fields.filter((f) => f.id !== "global-gravity");

      const gravityForce = createGravityForce("global-gravity", {
        x: safeGravityX,
        y: safeGravityY,
      });
      newFields.push(gravityForce);

      compositionForceFields.set(compId, newFields);
      engine.setForceFields(newFields);

      storeLogger.info("Gravity set to:", gravityX, gravityY);
    },

    // ========================================================================
    // Simulation Control
    // ========================================================================

    /**
     * Step the physics simulation to a specific frame
     */
    stepPhysics(store: PhysicsStoreAccess, targetFrame: number): void {
      const engine = this.getPhysicsEngine(store);
      const state = engine.evaluateFrame(targetFrame);
      this._applyPhysicsStateToLayers(store, state);
    },

    /**
     * Evaluate physics at a specific frame (for scrubbing)
     */
    evaluatePhysicsAtFrame(store: PhysicsStoreAccess, targetFrame: number): void {
      const engine = this.getPhysicsEngine(store);
      const state = engine.evaluateFrame(targetFrame);
      this._applyPhysicsStateToLayers(store, state);
    },

    /**
     * Reset physics simulation to initial state
     */
    resetPhysicsSimulation(store: PhysicsStoreAccess): void {
      const engine = this.getPhysicsEngine(store);
      engine.clearCache();

      for (const key of compositionPhysicsStates.keys()) {
        if (key.startsWith(store.activeCompositionId)) {
          compositionPhysicsStates.delete(key);
        }
      }

      const comp = store.project.compositions[store.activeCompositionId];
      if (!comp) return;

      for (const layer of comp.layers) {
        const physicsData = (layer.data as unknown as Record<string, unknown>)?.physics as
          | PhysicsLayerData
          | undefined;
        if (physicsData?.physicsEnabled && physicsData.rigidBody) {
          const initialPos = physicsData.rigidBody.position;
          if (layer.transform?.position) {
            layer.transform.position.value = {
              x: initialPos?.x ?? 0,
              y: initialPos?.y ?? 0,
              z: layer.transform.position.value?.z ?? 0,
            };
          }
        }
      }

      storeLogger.info("Physics simulation reset");
    },

    /**
     * Apply physics state to layer transforms (internal)
     */
    _applyPhysicsStateToLayers(
      store: PhysicsStoreAccess,
      state: PhysicsSimulationState,
    ): void {
      const comp = store.project.compositions[store.activeCompositionId];
      if (!comp) return;

      for (const layer of comp.layers) {
        const physicsData = (layer.data as unknown as Record<string, unknown>)?.physics as
          | PhysicsLayerData
          | undefined;
        if (!physicsData?.physicsEnabled) continue;

        const bodyState = state.rigidBodies.find((b) => b.id === layer.id);
        if (!bodyState) continue;

        if (layer.transform?.position) {
          layer.transform.position.value = {
            x: bodyState.position.x,
            y: bodyState.position.y,
            z: layer.transform.position.value?.z ?? 0,
          };
        }

        if (layer.transform?.rotation) {
          layer.transform.rotation.value = bodyState.angle * (180 / Math.PI);
        }
      }
    },

    // ========================================================================
    // Bake to Keyframes
    // ========================================================================

    /**
     * Bake physics simulation to keyframes
     */
    async bakePhysicsToKeyframes(
      store: PhysicsStoreAccess,
      layerId: string,
      options: BakeOptions = {},
    ): Promise<BakeResult> {
      const layer = store.getLayerById(layerId);
      if (!layer) {
        throw new Error(`Layer not found: ${layerId}`);
      }

      const comp = store.project.compositions[store.activeCompositionId];
      if (!comp) {
        throw new Error("No active composition");
      }

      const startFrame = options.startFrame ?? 0;
      const endFrame = options.endFrame ?? comp.settings.frameCount - 1;
      const sampleInterval: number =
        Number.isFinite(options.sampleInterval) && options.sampleInterval! > 0
          ? options.sampleInterval!
          : 1;

      const engine = this.getPhysicsEngine(store);
      engine.clearCache();

      const positionKeyframes: BakedKeyframe<{ x: number; y: number; z: number }>[] = [];
      const rotationKeyframes: BakedKeyframe<number>[] = [];

      for (let frame = startFrame; frame <= endFrame; frame += sampleInterval) {
        const state = engine.evaluateFrame(frame);
        const bodyState = state.rigidBodies.find((b) => b.id === layerId);

        if (bodyState) {
          positionKeyframes.push({
            frame,
            value: {
              x: bodyState.position.x,
              y: bodyState.position.y,
              z: layer.transform?.position?.value?.z ?? 0,
            },
            interpolation: "linear",
          });

          rotationKeyframes.push({
            frame,
            value: bodyState.angle * (180 / Math.PI),
            interpolation: "linear",
          });
        }
      }

      for (const kf of positionKeyframes) {
        store.addKeyframe(layerId, "transform.position", kf.value, kf.frame);
      }

      for (const kf of rotationKeyframes) {
        store.addKeyframe(layerId, "transform.rotation", kf.value, kf.frame);
      }

      this.disableLayerPhysics(store, layerId);

      storeLogger.info("Physics baked to keyframes:", layerId, {
        positionKeyframes: positionKeyframes.length,
        rotationKeyframes: rotationKeyframes.length,
      });

      return {
        layerId,
        positionKeyframes,
        rotationKeyframes,
      };
    },

    /**
     * Bake all physics-enabled layers to keyframes
     */
    async bakeAllPhysicsToKeyframes(
      store: PhysicsStoreAccess,
      options: BakeOptions = {},
    ): Promise<BakeResult[]> {
      const comp = store.project.compositions[store.activeCompositionId];
      if (!comp) return [];

      const results: BakeResult[] = [];

      for (const layer of comp.layers) {
        const physicsData = (layer.data as unknown as Record<string, unknown>)?.physics as
          | PhysicsLayerData
          | undefined;
        if (physicsData?.physicsEnabled) {
          const result = await this.bakePhysicsToKeyframes(store, layer.id, options);
          results.push(result);
        }
      }

      return results;
    },

    // ========================================================================
    // Cloth Simulation
    // ========================================================================

    /**
     * Create cloth simulation for a layer
     */
    createClothForLayer(
      store: PhysicsStoreAccess,
      layerId: string,
      options: {
        width: number;
        height: number;
        spacing?: number;
        pinnedTop?: boolean;
        pinnedCorners?: boolean;
      },
    ): void {
      const layer = store.getLayerById(layerId);
      if (!layer) return;

      const engine = this.getPhysicsEngine(store);

      const origin = {
        x: layer.transform?.position?.value?.x ?? 0,
        y: layer.transform?.position?.value?.y ?? 0,
      };

      const clothConfig = createClothConfig(layerId, layerId, {
        origin,
        width: options.width,
        height: options.height,
        spacing: options.spacing,
        pinnedTop: options.pinnedTop,
        pinnedCorners: options.pinnedCorners,
      });

      engine.addCloth(clothConfig);

      store.updateLayerData(layerId, {
        physics: {
          enabled: true,
          type: "cloth",
          config: clothConfig,
        },
      });

      storeLogger.info("Cloth created for layer:", layerId);
    },

    // ========================================================================
    // Ragdoll Simulation
    // ========================================================================

    /**
     * Create ragdoll for a pose layer
     */
    createRagdollForLayer(
      store: PhysicsStoreAccess,
      layerId: string,
      preset: "adult" | "child" | "cartoon" = "adult",
    ): void {
      const layer = store.getLayerById(layerId);
      if (!layer || layer.type !== "pose") {
        storeLogger.warn("Ragdoll requires a pose layer");
        return;
      }

      const engine = this.getPhysicsEngine(store);
      const builder = createRagdollBuilder(layerId, layerId);
      const ragdoll = builder.fromPreset(preset).build();

      for (const bone of ragdoll.bones) {
        const bodyConfig: RigidBodyConfig = {
          id: `${ragdoll.id}_${bone.id}`,
          layerId: ragdoll.layerId,
          type: "dynamic",
          mass: bone.mass,
          position: ragdoll.position,
          velocity: { x: 0, y: 0 },
          angle: ragdoll.rotation,
          angularVelocity: 0,
          shape: {
            type: "capsule",
            length: bone.length,
            radius: bone.width / 2,
          },
          material: ragdoll.material,
          filter: ragdoll.filter,
          response: "collide",
          linearDamping: ragdoll.damping,
          angularDamping: ragdoll.damping,
          canSleep: true,
          sleepThreshold: 10,
        };
        engine.addRigidBody(bodyConfig);
      }
      engine.addRagdoll(ragdoll.id, ragdoll.bones);

      store.updateLayerData(layerId, {
        physics: {
          physicsEnabled: true,
          ragdoll: ragdoll,
        },
      });

      storeLogger.info("Ragdoll created for pose layer:", layerId, preset);
    },

    // ========================================================================
    // Collision Configuration
    // ========================================================================

    /**
     * Set collision group for a layer
     */
    setLayerCollisionGroup(
      store: PhysicsStoreAccess,
      layerId: string,
      group: number,
      mask: number = 0xffffffff,
    ): void {
      const layer = store.getLayerById(layerId);
      if (!layer) return;

      this.updateLayerPhysicsConfig(store, layerId, {
        filter: {
          category: 1 << (group - 1),
          mask,
          group: 0,
        },
      });

      storeLogger.info("Collision group set:", layerId, group);
    },

    /**
     * Enable/disable collision between two layers
     */
    setLayersCanCollide(
      _store: PhysicsStoreAccess,
      _layerIdA: string,
      _layerIdB: string,
      _canCollide: boolean,
    ): void {
      storeLogger.warn("setLayersCanCollide not yet implemented");
    },
  },
});
