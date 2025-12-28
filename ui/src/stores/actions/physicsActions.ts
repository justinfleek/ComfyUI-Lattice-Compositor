/**
 * Physics Actions
 *
 * Store actions for Newton Physics Simulation integration.
 * Provides control over physics simulation, baking to keyframes,
 * and physics space configuration.
 */

import { storeLogger } from '@/utils/logger';
import {
  PhysicsEngine,
  createPhysicsEngine,
  createCircleBody,
  createBoxBody,
  createGravityForce,
  createClothConfig,
  createRagdollBuilder,
} from '@/services/physics';
import type {
  PhysicsSpaceConfig,
  RigidBodyConfig,
  SoftBodyConfig,
  ClothConfig,
  RagdollConfig,
  ForceField,
  PhysicsSimulationState,
  KeyframeExportOptions,
  ExportedKeyframes,
  PhysicsLayerData,
  PhysicsVec2,
} from '@/types/physics';
import type { Layer, Keyframe } from '@/types/project';

// ============================================================================
// STORE INTERFACE
// ============================================================================

export interface PhysicsStore {
  // State
  activeCompositionId: string;
  currentFrame: number;

  // Methods the store must provide
  project: {
    compositions: Record<string, {
      layers: Layer[];
      settings: {
        width: number;
        height: number;
        frameCount: number;
        fps: number;
      };
    }>;
  };

  // Layer access
  getLayerById(id: string): Layer | null | undefined;
  updateLayerData(layerId: string, data: Record<string, any>): void;
  // Signature must match compositorStore.addKeyframe
  addKeyframe<T>(layerId: string, propertyName: string, value: T, atFrame?: number): Keyframe<T> | null;
}

// ============================================================================
// PHYSICS ENGINE MANAGEMENT
// ============================================================================

/** Global physics engine instance */
let physicsEngine: PhysicsEngine | null = null;

/** Per-composition physics states for deterministic scrubbing */
const compositionPhysicsStates = new Map<string, PhysicsSimulationState>();

/**
 * Initialize physics engine for the current composition
 */
export function initializePhysicsEngine(
  store: PhysicsStore,
  config?: Partial<PhysicsSpaceConfig>
): PhysicsEngine {
  const comp = store.project.compositions[store.activeCompositionId];
  if (!comp) {
    throw new Error('No active composition');
  }

  // Create physics engine with composition-aware config
  const fullConfig: Partial<PhysicsSpaceConfig> = {
    ...config,
    // Use composition dimensions to set default gravity scale
    // (worldBounds is handled internally by the engine)
  };

  physicsEngine = createPhysicsEngine(fullConfig);
  storeLogger.info('Physics engine initialized for composition', store.activeCompositionId);
  return physicsEngine;
}

/**
 * Get or create physics engine
 */
export function getPhysicsEngine(store: PhysicsStore): PhysicsEngine {
  if (!physicsEngine) {
    return initializePhysicsEngine(store);
  }
  return physicsEngine;
}

/**
 * Dispose physics engine
 */
export function disposePhysicsEngine(): void {
  physicsEngine = null;
  compositionPhysicsStates.clear();
  storeLogger.info('Physics engine disposed');
}

// ============================================================================
// RIGID BODY MANAGEMENT
// ============================================================================

/**
 * Enable physics for a layer as a rigid body
 */
export function enableLayerPhysics(
  store: PhysicsStore,
  layerId: string,
  config: Partial<RigidBodyConfig> = {}
): void {
  const layer = store.getLayerById(layerId);
  if (!layer) {
    storeLogger.warn('Layer not found for physics:', layerId);
    return;
  }

  const engine = getPhysicsEngine(store);

  // Get layer position for initial body position
  const position = {
    x: layer.transform?.position?.value?.x ?? 0,
    y: layer.transform?.position?.value?.y ?? 0,
  };

  // Create rigid body config
  const bodyConfig = config.shape?.type === 'circle'
    ? createCircleBody(layerId, layerId, {
        position,
        radius: config.shape.radius ?? 50,
        mass: config.mass ?? 1,
        isStatic: config.type === 'static',
      })
    : createBoxBody(layerId, layerId, {
        position,
        width: config.shape?.width ?? 100,
        height: config.shape?.height ?? 100,
        mass: config.mass ?? 1,
        isStatic: config.type === 'static',
      });

  // Merge with any additional config
  const finalConfig: RigidBodyConfig = {
    ...bodyConfig,
    ...config,
    id: layerId,
    layerId,
  };

  // Add body to engine
  engine.addRigidBody(finalConfig);

  // Update layer data
  const physicsData: PhysicsLayerData = {
    physicsEnabled: true,
    rigidBody: finalConfig,
  };

  store.updateLayerData(layerId, { physics: physicsData });
  storeLogger.info('Physics enabled for layer:', layerId);
}

/**
 * Disable physics for a layer
 */
export function disableLayerPhysics(
  store: PhysicsStore,
  layerId: string
): void {
  const engine = getPhysicsEngine(store);
  engine.removeRigidBody(layerId);

  store.updateLayerData(layerId, {
    physics: { physicsEnabled: false },
  });
  storeLogger.info('Physics disabled for layer:', layerId);
}

/**
 * Update physics body for a layer
 */
export function updateLayerPhysicsConfig(
  store: PhysicsStore,
  layerId: string,
  updates: Partial<RigidBodyConfig>
): void {
  const layer = store.getLayerById(layerId);
  if (!layer) return;

  const physicsData = (layer.data as any)?.physics as PhysicsLayerData | undefined;
  if (!physicsData?.physicsEnabled || !physicsData.rigidBody) return;

  const engine = getPhysicsEngine(store);

  // Remove and re-add with new config
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
}

// ============================================================================
// FORCE FIELD MANAGEMENT
// ============================================================================

/** Track force fields locally */
const compositionForceFields = new Map<string, ForceField[]>();

/**
 * Add a force field to the physics simulation
 */
export function addForceField(
  store: PhysicsStore,
  force: ForceField
): void {
  const engine = getPhysicsEngine(store);
  const compId = store.activeCompositionId;

  // Get existing force fields for this composition
  const fields = compositionForceFields.get(compId) || [];
  const existingIndex = fields.findIndex(f => f.id === force.id);

  if (existingIndex >= 0) {
    fields[existingIndex] = force;
  } else {
    fields.push(force);
  }

  compositionForceFields.set(compId, fields);
  engine.setForceFields(fields);
  storeLogger.info('Force field added:', force.id);
}

/**
 * Remove a force field
 */
export function removeForceField(
  store: PhysicsStore,
  forceId: string
): void {
  const engine = getPhysicsEngine(store);
  const compId = store.activeCompositionId;

  const fields = compositionForceFields.get(compId) || [];
  const newFields = fields.filter(f => f.id !== forceId);

  compositionForceFields.set(compId, newFields);
  engine.setForceFields(newFields);
  storeLogger.info('Force field removed:', forceId);
}

/**
 * Set global gravity
 */
export function setGravity(
  store: PhysicsStore,
  gravityX: number,
  gravityY: number
): void {
  // Validate gravity values
  const safeGravityX = Number.isFinite(gravityX) ? gravityX : 0;
  const safeGravityY = Number.isFinite(gravityY) ? gravityY : 0;

  const engine = getPhysicsEngine(store);
  const compId = store.activeCompositionId;

  // Get existing force fields
  const fields = compositionForceFields.get(compId) || [];

  // Remove existing gravity force if any
  const newFields = fields.filter(f => f.id !== 'global-gravity');

  // Add new gravity force
  const gravityForce = createGravityForce('global-gravity', { x: safeGravityX, y: safeGravityY });
  newFields.push(gravityForce);

  compositionForceFields.set(compId, newFields);
  engine.setForceFields(newFields);

  storeLogger.info('Gravity set to:', gravityX, gravityY);
}

// ============================================================================
// SIMULATION CONTROL
// ============================================================================

/**
 * Step the physics simulation to a specific frame
 * Called during playback to advance physics state
 */
export function stepPhysics(
  store: PhysicsStore,
  targetFrame: number
): void {
  const engine = getPhysicsEngine(store);
  const state = engine.evaluateFrame(targetFrame);

  // Apply physics state back to layers
  applyPhysicsStateToLayers(store, state);
}

/**
 * Evaluate physics at a specific frame (for scrubbing)
 * Uses checkpoints for deterministic results (handled internally by engine)
 */
export function evaluatePhysicsAtFrame(
  store: PhysicsStore,
  targetFrame: number
): void {
  const engine = getPhysicsEngine(store);
  const state = engine.evaluateFrame(targetFrame);

  // Apply physics state to layers
  applyPhysicsStateToLayers(store, state);
}

/**
 * Reset physics simulation to initial state
 */
export function resetPhysicsSimulation(store: PhysicsStore): void {
  const engine = getPhysicsEngine(store);
  engine.clearCache();

  // Clear composition-specific states
  for (const key of compositionPhysicsStates.keys()) {
    if (key.startsWith(store.activeCompositionId)) {
      compositionPhysicsStates.delete(key);
    }
  }

  // Reset layers to initial positions
  const comp = store.project.compositions[store.activeCompositionId];
  if (!comp) return;

  for (const layer of comp.layers) {
    const physicsData = (layer.data as any)?.physics as PhysicsLayerData | undefined;
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

  storeLogger.info('Physics simulation reset');
}

/**
 * Apply physics state to layer transforms
 */
function applyPhysicsStateToLayers(store: PhysicsStore, state: PhysicsSimulationState): void {
  const comp = store.project.compositions[store.activeCompositionId];
  if (!comp) return;

  for (const layer of comp.layers) {
    const physicsData = (layer.data as any)?.physics as PhysicsLayerData | undefined;
    if (!physicsData?.physicsEnabled) continue;

    // Find the body state for this layer
    const bodyState = state.rigidBodies.find(b => b.id === layer.id);
    if (!bodyState) continue;

    // Update layer transform from physics state
    if (layer.transform?.position) {
      layer.transform.position.value = {
        x: bodyState.position.x,
        y: bodyState.position.y,
        z: layer.transform.position.value?.z ?? 0,
      };
    }

    if (layer.transform?.rotation) {
      // Convert radians to degrees
      layer.transform.rotation.value = bodyState.angle * (180 / Math.PI);
    }
  }
}

// ============================================================================
// BAKE TO KEYFRAMES
// ============================================================================

/** Internal keyframe structure for baking */
interface BakedKeyframe<T> {
  frame: number;
  value: T;
  interpolation: 'linear' | 'bezier';
}

/** Options for baking physics to keyframes */
export interface BakeOptions {
  startFrame?: number;
  endFrame?: number;
  sampleInterval?: number;
  simplify?: boolean;
}

/** Result of baking physics to keyframes */
export interface BakeResult {
  layerId: string;
  positionKeyframes: BakedKeyframe<{ x: number; y: number; z: number }>[];
  rotationKeyframes: BakedKeyframe<number>[];
}

/**
 * Bake physics simulation to keyframes
 * Creates position and rotation keyframes from simulation
 */
export async function bakePhysicsToKeyframes(
  store: PhysicsStore,
  layerId: string,
  options: BakeOptions = {}
): Promise<BakeResult> {
  const layer = store.getLayerById(layerId);
  if (!layer) {
    throw new Error(`Layer not found: ${layerId}`);
  }

  const comp = store.project.compositions[store.activeCompositionId];
  if (!comp) {
    throw new Error('No active composition');
  }

  const startFrame = options.startFrame ?? 0;
  const endFrame = options.endFrame ?? comp.settings.frameCount - 1;
  // Validate sampleInterval to prevent infinite loop (NaN causes frame += NaN = NaN)
  const sampleInterval: number = (Number.isFinite(options.sampleInterval) && options.sampleInterval! > 0)
    ? options.sampleInterval!
    : 1;

  const engine = getPhysicsEngine(store);

  // Clear cache to start fresh
  engine.clearCache();

  const positionKeyframes: BakedKeyframe<{ x: number; y: number; z: number }>[] = [];
  const rotationKeyframes: BakedKeyframe<number>[] = [];

  // Simulate and collect keyframes
  for (let frame = startFrame; frame <= endFrame; frame += sampleInterval) {
    const state = engine.evaluateFrame(frame);
    const bodyState = state.rigidBodies.find(b => b.id === layerId);

    if (bodyState) {
      positionKeyframes.push({
        frame,
        value: {
          x: bodyState.position.x,
          y: bodyState.position.y,
          z: layer.transform?.position?.value?.z ?? 0,
        },
        interpolation: 'linear',
      });

      rotationKeyframes.push({
        frame,
        value: bodyState.angle * (180 / Math.PI),
        interpolation: 'linear',
      });
    }
  }

  // Apply keyframes to layer (store should handle the Keyframe type conversion)
  for (const kf of positionKeyframes) {
    store.addKeyframe(layerId, 'transform.position', kf.value, kf.frame);
  }

  for (const kf of rotationKeyframes) {
    store.addKeyframe(layerId, 'transform.rotation', kf.value, kf.frame);
  }

  // Disable physics after baking
  disableLayerPhysics(store, layerId);

  storeLogger.info('Physics baked to keyframes:', layerId, {
    positionKeyframes: positionKeyframes.length,
    rotationKeyframes: rotationKeyframes.length,
  });

  return {
    layerId,
    positionKeyframes,
    rotationKeyframes,
  };
}

/**
 * Bake all physics-enabled layers to keyframes
 */
export async function bakeAllPhysicsToKeyframes(
  store: PhysicsStore,
  options: BakeOptions = {}
): Promise<BakeResult[]> {
  const comp = store.project.compositions[store.activeCompositionId];
  if (!comp) return [];

  const results: BakeResult[] = [];

  for (const layer of comp.layers) {
    const physicsData = (layer.data as any)?.physics as PhysicsLayerData | undefined;
    if (physicsData?.physicsEnabled) {
      const result = await bakePhysicsToKeyframes(store, layer.id, options);
      results.push(result);
    }
  }

  return results;
}

// ============================================================================
// CLOTH SIMULATION
// ============================================================================

/**
 * Create cloth simulation for a layer
 */
export function createClothForLayer(
  store: PhysicsStore,
  layerId: string,
  options: {
    width: number;
    height: number;
    spacing?: number;
    pinnedTop?: boolean;
    pinnedCorners?: boolean;
  }
): void {
  const layer = store.getLayerById(layerId);
  if (!layer) return;

  const engine = getPhysicsEngine(store);

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
      type: 'cloth',
      config: clothConfig,
    },
  });

  storeLogger.info('Cloth created for layer:', layerId);
}

// ============================================================================
// RAGDOLL SIMULATION
// ============================================================================

/**
 * Create ragdoll for a pose layer
 */
export function createRagdollForLayer(
  store: PhysicsStore,
  layerId: string,
  preset: 'adult' | 'child' | 'cartoon' = 'adult'
): void {
  const layer = store.getLayerById(layerId);
  if (!layer || layer.type !== 'pose') {
    storeLogger.warn('Ragdoll requires a pose layer');
    return;
  }

  const engine = getPhysicsEngine(store);
  const builder = createRagdollBuilder(layerId, layerId);

  // Build ragdoll based on preset - use builder pattern
  const ragdoll = builder.fromPreset(preset).build();

  // Add ragdoll's rigid bodies to engine, then register the ragdoll
  for (const bone of ragdoll.bones) {
    const bodyConfig: RigidBodyConfig = {
      id: `${ragdoll.id}_${bone.id}`,
      layerId: ragdoll.layerId,
      type: 'dynamic',
      mass: bone.mass,
      position: ragdoll.position,
      velocity: { x: 0, y: 0 },
      angle: ragdoll.rotation,
      angularVelocity: 0,
      shape: {
        type: 'capsule',
        length: bone.length,
        radius: bone.width / 2,
      },
      material: ragdoll.material,
      filter: ragdoll.filter,
      response: 'collide',
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

  storeLogger.info('Ragdoll created for pose layer:', layerId, preset);
}

// ============================================================================
// COLLISION CONFIGURATION
// ============================================================================

/**
 * Set collision group for a layer
 */
export function setLayerCollisionGroup(
  store: PhysicsStore,
  layerId: string,
  group: number,
  mask: number = 0xffffffff
): void {
  const layer = store.getLayerById(layerId);
  if (!layer) return;

  updateLayerPhysicsConfig(store, layerId, {
    filter: {
      category: 1 << (group - 1),
      mask,
      group: 0,
    },
  });

  storeLogger.info('Collision group set:', layerId, group);
}

/**
 * Enable/disable collision between two layers
 */
export function setLayersCanCollide(
  store: PhysicsStore,
  layerIdA: string,
  layerIdB: string,
  canCollide: boolean
): void {
  // For now, this would require more complex collision filtering
  // which can be added when the physics engine supports it
  storeLogger.warn('setLayersCanCollide not yet implemented');
}
