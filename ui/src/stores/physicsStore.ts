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
import type { JSONValue } from "@/types/dataAsset";

/**
 * All possible JavaScript values that can be validated at runtime
 * Used as input type for validators (replaces unknown)
 */
type RuntimeValue = string | number | boolean | object | null | undefined | bigint | symbol;
import type {
  PhysicsSimulationState,
  PhysicsSpaceConfig,
  PhysicsLayerData,
  RigidBodyConfig,
  ForceField,
} from "@/types/physics";
import type { Keyframe, Layer, LayerDataUnion } from "@/types/project";
import { isFiniteNumber, assertDefined } from "@/utils/typeGuards";
import { storeLogger } from "@/utils/logger";
import { useLayerStore } from "@/stores/layerStore";
import { useProjectStore } from "./projectStore";
import { useAnimationStore } from "./animationStore";
import { useKeyframeStore } from "./keyframeStore";

// ============================================================================
// TYPE GUARDS
// ============================================================================

/**
 * Type guard to check if layer data has physics property
 */
function hasPhysicsData(data: RuntimeValue): data is { physics?: PhysicsLayerData } {
  return data !== null && data !== undefined && typeof data === "object" && "physics" in data;
}

// ============================================================================
// STORE ACCESS INTERFACE (DEPRECATED - Will be removed in Phase 5)
// ============================================================================

/**
 * @deprecated This interface is no longer used. All methods now use domain stores directly.
 * Will be removed when compositorStore is deleted.
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
  updateLayerData(layerId: string, data: Partial<LayerDataUnion>): void;
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
      config?: Partial<PhysicsSpaceConfig>,
    ): PhysicsEngine {
      const projectStore = useProjectStore();
      const comp = projectStore.project.compositions[projectStore.activeCompositionId];
      if (!comp) {
        throw new Error("No active composition");
      }

      physicsEngine = createPhysicsEngine(config);
      storeLogger.info(
        "Physics engine initialized for composition",
        projectStore.activeCompositionId,
      );
      return physicsEngine;
    },

    /**
     * Get or create physics engine
     */
    getPhysicsEngine(): PhysicsEngine {
      if (!physicsEngine) {
        return this.initializePhysicsEngine();
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
      layerId: string,
      config: Partial<RigidBodyConfig> = {},
    ): void {
      const layerStore = useLayerStore();
      const layer = layerStore.getLayerById(layerId);
      if (!layer) {
        storeLogger.warn("Layer not found for physics:", layerId);
        return;
      }

      const engine = this.getPhysicsEngine();

      // Type proof: position.x/y ∈ ℝ ∪ {undefined} → ℝ
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const transform = layer.transform;
      const position = (transform != null && typeof transform === "object" && "position" in transform && transform.position != null && typeof transform.position === "object" && "value" in transform.position && transform.position.value != null && typeof transform.position.value === "object") ? transform.position.value : undefined;
      const positionXValue = (position != null && "x" in position && typeof position.x === "number") ? position.x : undefined;
      const positionX = isFiniteNumber(positionXValue) ? positionXValue : 0;
      const positionYValue = (position != null && "y" in position && typeof position.y === "number") ? position.y : undefined;
      const positionY = isFiniteNumber(positionYValue) ? positionYValue : 0;
      const position = {
        x: positionX,
        y: positionY,
      };

      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const shape = config.shape;
      const bodyConfig =
        (shape != null && typeof shape === "object" && "type" in shape && shape.type === "circle")
          ? createCircleBody(layerId, layerId, {
              position,
              // Type proof: radius ∈ ℝ ∧ finite(radius) → radius ∈ ℝ₊
              radius: (() => {
                const radiusValue = config.shape.radius;
                return isFiniteNumber(radiusValue) && radiusValue > 0 ? radiusValue : 50;
              })(),
              // Type proof: mass ∈ ℝ ∧ finite(mass) → mass ∈ ℝ₊
              mass: (() => {
                const massValue = config.mass;
                return isFiniteNumber(massValue) && massValue > 0 ? massValue : 1;
              })(),
              isStatic: config.type === "static",
            })
          : createBoxBody(layerId, layerId, {
              position,
              // Type proof: width, height ∈ ℝ ∧ finite(width/height) → width/height ∈ ℝ₊
              width: (() => {
                // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
                const shape = config.shape;
                const widthValue = (shape != null && typeof shape === "object" && "width" in shape && typeof shape.width === "number") ? shape.width : undefined;
                return isFiniteNumber(widthValue) && widthValue > 0 ? widthValue : 100;
              })(),
              height: (() => {
                // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
                const shape = config.shape;
                const heightValue = (shape != null && typeof shape === "object" && "height" in shape && typeof shape.height === "number") ? shape.height : undefined;
                return isFiniteNumber(heightValue) && heightValue > 0 ? heightValue : 100;
              })(),
              // Type proof: mass ∈ ℝ ∧ finite(mass) → mass ∈ ℝ₊
              mass: (() => {
                const massValue = config.mass;
                return isFiniteNumber(massValue) && massValue > 0 ? massValue : 1;
              })(),
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

      layerStore.updateLayerData(layerId, { physics: physicsData });
      storeLogger.info("Physics enabled for layer:", layerId);
    },

    /**
     * Disable physics for a layer
     */
    disableLayerPhysics(layerId: string): void {
      const layerStore = useLayerStore();
      const engine = this.getPhysicsEngine();
      engine.removeRigidBody(layerId);

      layerStore.updateLayerData(layerId, {
        physics: { physicsEnabled: false },
      });
      storeLogger.info("Physics disabled for layer:", layerId);
    },

    /**
     * Update physics body for a layer
     */
    updateLayerPhysicsConfig(
      layerId: string,
      updates: Partial<RigidBodyConfig>,
    ): void {
      const layerStore = useLayerStore();
      const layer = layerStore.getLayerById(layerId);
      if (!layer || !layer.data) return;

      if (!hasPhysicsData(layer.data)) return;
      const physicsData = layer.data.physics;
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      if (physicsData == null || typeof physicsData !== "object" || !("physicsEnabled" in physicsData) || !physicsData.physicsEnabled || !physicsData.rigidBody) return;

      const engine = this.getPhysicsEngine();
      engine.removeRigidBody(layerId);

      const newConfig: RigidBodyConfig = {
        ...physicsData.rigidBody,
        ...updates,
      };

      engine.addRigidBody(newConfig);

      layerStore.updateLayerData(layerId, {
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
    addForceField(force: ForceField): void {
      const projectStore = useProjectStore();
      const engine = this.getPhysicsEngine();
      const compId = projectStore.activeCompositionId;

      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy || []
      const fieldsRaw = compositionForceFields.get(compId);
      const fields = (fieldsRaw !== null && fieldsRaw !== undefined && Array.isArray(fieldsRaw)) ? fieldsRaw : [];
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
    removeForceField(forceId: string): void {
      const projectStore = useProjectStore();
      const engine = this.getPhysicsEngine();
      const compId = projectStore.activeCompositionId;

      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy || []
      const fieldsRaw = compositionForceFields.get(compId);
      const fields = (fieldsRaw !== null && fieldsRaw !== undefined && Array.isArray(fieldsRaw)) ? fieldsRaw : [];
      const newFields = fields.filter((f) => f.id !== forceId);

      compositionForceFields.set(compId, newFields);
      engine.setForceFields(newFields);
      storeLogger.info("Force field removed:", forceId);
    },

    /**
     * Set global gravity
     */
    setGravity(
      gravityX: number,
      gravityY: number,
    ): void {
      const projectStore = useProjectStore();
      const safeGravityX = Number.isFinite(gravityX) ? gravityX : 0;
      const safeGravityY = Number.isFinite(gravityY) ? gravityY : 0;

      const engine = this.getPhysicsEngine();
      const compId = projectStore.activeCompositionId;

      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy || []
      const fieldsRaw = compositionForceFields.get(compId);
      const fields = (fieldsRaw !== null && fieldsRaw !== undefined && Array.isArray(fieldsRaw)) ? fieldsRaw : [];
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
    stepPhysics(targetFrame: number): void {
      const engine = this.getPhysicsEngine();
      const state = engine.evaluateFrame(targetFrame);
      this._applyPhysicsStateToLayers(state);
    },

    /**
     * Evaluate physics at a specific frame (for scrubbing)
     */
    evaluatePhysicsAtFrame(targetFrame: number): void {
      const engine = this.getPhysicsEngine();
      const state = engine.evaluateFrame(targetFrame);
      this._applyPhysicsStateToLayers(state);
    },

    /**
     * Reset physics simulation to initial state
     */
    resetPhysicsSimulation(): void {
      const projectStore = useProjectStore();
      const engine = this.getPhysicsEngine();
      engine.clearCache();

      for (const key of compositionPhysicsStates.keys()) {
        if (key.startsWith(projectStore.activeCompositionId)) {
          compositionPhysicsStates.delete(key);
        }
      }

      const comp = projectStore.project.compositions[projectStore.activeCompositionId];
      if (!comp) return;

      for (const layer of comp.layers) {
        if (!layer.data || !hasPhysicsData(layer.data)) continue;
        const physicsData = layer.data.physics;
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
        if (physicsData != null && typeof physicsData === "object" && "physicsEnabled" in physicsData && physicsData.physicsEnabled && physicsData.rigidBody) {
          const initialPos = physicsData.rigidBody.position;
          // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
          const transform = layer.transform;
          if (transform != null && typeof transform === "object" && "position" in transform && transform.position != null && typeof transform.position === "object") {
            // Type proof: initialPos.x/y ∈ ℝ ∪ {undefined} → ℝ, z ∈ ℝ ∪ {undefined} → ℝ
            // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
            const initialXValue = (initialPos != null && typeof initialPos === "object" && "x" in initialPos && typeof initialPos.x === "number") ? initialPos.x : undefined;
            const initialX = isFiniteNumber(initialXValue) ? initialXValue : 0;
            const initialYValue = (initialPos != null && typeof initialPos === "object" && "y" in initialPos && typeof initialPos.y === "number") ? initialPos.y : undefined;
            const initialY = isFiniteNumber(initialYValue) ? initialYValue : 0;
            // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
            const positionValue = transform.position.value;
            const zValue = (positionValue != null && typeof positionValue === "object" && "z" in positionValue && typeof positionValue.z === "number") ? positionValue.z : undefined;
            const z = isFiniteNumber(zValue) ? zValue : 0;
            layer.transform.position.value = {
              x: initialX,
              y: initialY,
              z: z,
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
      state: PhysicsSimulationState,
    ): void {
      const projectStore = useProjectStore();
      const comp = projectStore.project.compositions[projectStore.activeCompositionId];
      if (!comp) return;

      for (const layer of comp.layers) {
        if (!layer.data || !hasPhysicsData(layer.data)) continue;
        const physicsData = layer.data.physics;
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
        if (physicsData == null || typeof physicsData !== "object" || !("physicsEnabled" in physicsData) || !physicsData.physicsEnabled) continue;

        const bodyState = state.rigidBodies.find((b) => b.id === layer.id);
        if (!bodyState) continue;

        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
        const transform = layer.transform;
        if (transform != null && typeof transform === "object" && "position" in transform && transform.position != null && typeof transform.position === "object" && "value" in transform.position) {
          const positionValue = transform.position.value;
          layer.transform.position.value = {
            x: bodyState.position.x,
            y: bodyState.position.y,
            // Type proof: z ∈ ℝ ∪ {undefined} → ℝ
            z: (() => {
              // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
              const zValue = (positionValue != null && typeof positionValue === "object" && "z" in positionValue && typeof positionValue.z === "number") ? positionValue.z : undefined;
              return isFiniteNumber(zValue) ? zValue : 0;
            })(),
          };
        }

        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
        if (transform != null && typeof transform === "object" && "rotation" in transform && transform.rotation != null && typeof transform.rotation === "object" && "value" in transform.rotation) {
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
      layerId: string,
      options: BakeOptions = {},
    ): Promise<BakeResult> {
      const layerStore = useLayerStore();
      const projectStore = useProjectStore();
      const keyframeStore = useKeyframeStore();
      const layer = layerStore.getLayerById(layerId);
      if (!layer) {
        throw new Error(`Layer not found: ${layerId}`);
      }

      const comp = projectStore.project.compositions[projectStore.activeCompositionId];
      if (!comp) {
        throw new Error("No active composition");
      }

      // Type proof: startFrame ∈ ℕ ∪ {undefined} → ℕ
      const startFrameValue = options.startFrame;
      const startFrame = isFiniteNumber(startFrameValue) && Number.isInteger(startFrameValue) && startFrameValue >= 0 ? startFrameValue : 0;
      // Type proof: endFrame ∈ ℕ ∪ {undefined} → ℕ
      const endFrameValue = options.endFrame;
      const endFrame = isFiniteNumber(endFrameValue) && Number.isInteger(endFrameValue) && endFrameValue >= 0 ? endFrameValue : comp.settings.frameCount - 1;
      // Type proof: sampleInterval is guaranteed finite and > 0 when condition is true
      const sampleIntervalValue = options.sampleInterval;
      const sampleInterval: number =
        Number.isFinite(sampleIntervalValue) && sampleIntervalValue !== undefined && sampleIntervalValue > 0
          ? (() => {
              assertDefined(sampleIntervalValue, "sampleInterval must be defined when finite and > 0");
              return sampleIntervalValue;
            })()
          : 1;

      const engine = this.getPhysicsEngine();
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
              // Type proof: z ∈ ℝ ∪ {undefined} → ℝ
              z: (() => {
                // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
                const transform = layer.transform;
                const position = (transform != null && typeof transform === "object" && "position" in transform && transform.position != null && typeof transform.position === "object" && "value" in transform.position && transform.position.value != null && typeof transform.position.value === "object") ? transform.position.value : undefined;
                const zValue = (position != null && "z" in position && typeof position.z === "number") ? position.z : undefined;
                return isFiniteNumber(zValue) ? zValue : 0;
              })(),
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
        keyframeStore.addKeyframe(layerId, "transform.position", kf.value, kf.frame);
      }

      for (const kf of rotationKeyframes) {
        keyframeStore.addKeyframe(layerId, "transform.rotation", kf.value, kf.frame);
      }

      this.disableLayerPhysics(layerId);

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
      options: BakeOptions = {},
    ): Promise<BakeResult[]> {
      const projectStore = useProjectStore();
      const comp = projectStore.project.compositions[projectStore.activeCompositionId];
      if (!comp) return [];

      const results: BakeResult[] = [];

      for (const layer of comp.layers) {
        if (!layer.data || !hasPhysicsData(layer.data)) continue;
        const physicsData = layer.data.physics;
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
        if (physicsData != null && typeof physicsData === "object" && "physicsEnabled" in physicsData && physicsData.physicsEnabled) {
          const result = await this.bakePhysicsToKeyframes(layer.id, options);
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
      layerId: string,
      options: {
        width: number;
        height: number;
        spacing?: number;
        pinnedTop?: boolean;
        pinnedCorners?: boolean;
      },
    ): void {
      const layerStore = useLayerStore();
      const layer = layerStore.getLayerById(layerId);
      if (!layer) return;

      const engine = this.getPhysicsEngine();

      // Type proof: position.x/y ∈ ℝ ∪ {undefined} → ℝ
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const transform = layer.transform;
      const position = (transform != null && typeof transform === "object" && "position" in transform && transform.position != null && typeof transform.position === "object" && "value" in transform.position && transform.position.value != null && typeof transform.position.value === "object") ? transform.position.value : undefined;
      const originXValue = (position != null && "x" in position && typeof position.x === "number") ? position.x : undefined;
      const originX = isFiniteNumber(originXValue) ? originXValue : 0;
      const originYValue = (position != null && "y" in position && typeof position.y === "number") ? position.y : undefined;
      const originY = isFiniteNumber(originYValue) ? originYValue : 0;
      const origin = {
        x: originX,
        y: originY,
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

      const physicsData: PhysicsLayerData = {
        physicsEnabled: true,
        cloth: clothConfig,
      };

      layerStore.updateLayerData(layerId, { physics: physicsData });

      storeLogger.info("Cloth created for layer:", layerId);
    },

    // ========================================================================
    // Ragdoll Simulation
    // ========================================================================

    /**
     * Create ragdoll for a pose layer
     */
    createRagdollForLayer(
      layerId: string,
      preset: "adult" | "child" | "cartoon" = "adult",
    ): void {
      const layerStore = useLayerStore();
      const layer = layerStore.getLayerById(layerId);
      if (!layer || layer.type !== "pose") {
        storeLogger.warn("Ragdoll requires a pose layer");
        return;
      }

      const engine = this.getPhysicsEngine();
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

      layerStore.updateLayerData(layerId, {
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
      layerId: string,
      group: number,
      mask: number = 0xffffffff,
    ): void {
      this.updateLayerPhysicsConfig(layerId, {
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
      _layerIdA: string,
      _layerIdB: string,
      _canCollide: boolean,
    ): void {
      storeLogger.warn("setLayersCanCollide not yet implemented");
    },
  },
});
