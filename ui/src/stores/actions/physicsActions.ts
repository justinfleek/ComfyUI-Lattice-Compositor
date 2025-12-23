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
} from '@/types/physics';
import type { Layer, Keyframe, AnimatableProperty } from '@/types/project';

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
  getLayerById(id: string): Layer | undefined;
  updateLayerData(layerId: string, data: Record<string, any>): void;
  addKeyframe<T>(layerId: string, property: string, frame: number, value: T): void;
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
    // Default to composition dimensions for world bounds
    worldBounds: config?.worldBounds ?? {
      minX: 0,
      minY: 0,
      maxX: comp.settings.width,
      maxY: comp.settings.height,
    },
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
    enabled: true,
    bodyId: layerId,
    type: 'rigid',
    config: finalConfig,
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
    physics: { enabled: false },
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
  if (!physicsData?.enabled) return;

  const engine = getPhysicsEngine(store);

  // Remove and re-add with new config
  engine.removeRigidBody(layerId);

  const newConfig: RigidBodyConfig = {
    ...physicsData.config,
    ...updates,
  } as RigidBodyConfig;

  engine.addRigidBody(newConfig);

  store.updateLayerData(layerId, {
    physics: {
      ...physicsData,
      config: newConfig,
    },
  });
}

// ============================================================================
// FORCE FIELD MANAGEMENT
// ============================================================================

/**
 * Add a force field to the physics simulation
 */
export function addForceField(
  store: PhysicsStore,
  force: ForceField
): void {
  const engine = getPhysicsEngine(store);
  engine.addForce(force);
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
  engine.removeForce(forceId);
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
  const engine = getPhysicsEngine(store);

  // Remove existing gravity force if any
  engine.removeForce('global-gravity');

  // Add new gravity force
  const gravityForce = createGravityForce('global-gravity', { x: gravityX, y: gravityY });
  engine.addForce(gravityForce);

  storeLogger.info('Gravity set to:', gravityX, gravityY);
}

// ============================================================================
// SIMULATION CONTROL
// ============================================================================

/**
 * Step the physics simulation
 * Called during playback to advance physics state
 */
export function stepPhysics(
  store: PhysicsStore,
  deltaTime: number
): void {
  const engine = getPhysicsEngine(store);
  engine.step(deltaTime);

  // Apply physics state back to layers
  applyPhysicsStateToLayers(store);
}

/**
 * Evaluate physics at a specific frame (for scrubbing)
 * Uses checkpoints for deterministic results
 */
export function evaluatePhysicsAtFrame(
  store: PhysicsStore,
  targetFrame: number
): void {
  const engine = getPhysicsEngine(store);
  const comp = store.project.compositions[store.activeCompositionId];
  if (!comp) return;

  const fps = comp.settings.fps;

  // Find nearest checkpoint and simulate forward
  const checkpointInterval = 30; // Checkpoint every 30 frames
  const nearestCheckpoint = Math.floor(targetFrame / checkpointInterval) * checkpointInterval;

  // Load checkpoint state if available
  const stateKey = `${store.activeCompositionId}-${nearestCheckpoint}`;
  const checkpointState = compositionPhysicsStates.get(stateKey);

  if (checkpointState && nearestCheckpoint > 0) {
    engine.loadState(checkpointState);
  } else if (nearestCheckpoint === 0) {
    engine.reset();
  }

  // Simulate from checkpoint to target frame
  const deltaTime = 1 / fps;
  for (let frame = nearestCheckpoint; frame < targetFrame; frame++) {
    engine.step(deltaTime);

    // Save checkpoint
    if (frame > 0 && frame % checkpointInterval === 0) {
      const key = `${store.activeCompositionId}-${frame}`;
      if (!compositionPhysicsStates.has(key)) {
        compositionPhysicsStates.set(key, engine.saveState());
      }
    }
  }

  // Apply physics state to layers
  applyPhysicsStateToLayers(store);
}

/**
 * Reset physics simulation to initial state
 */
export function resetPhysicsSimulation(store: PhysicsStore): void {
  const engine = getPhysicsEngine(store);
  engine.reset();

  // Clear composition-specific checkpoints
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
    if (physicsData?.enabled && physicsData.config) {
      const initialPos = physicsData.config.position;
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
 * Apply current physics state to layer transforms
 */
function applyPhysicsStateToLayers(store: PhysicsStore): void {
  const engine = getPhysicsEngine(store);
  const comp = store.project.compositions[store.activeCompositionId];
  if (!comp) return;

  for (const layer of comp.layers) {
    const physicsData = (layer.data as any)?.physics as PhysicsLayerData | undefined;
    if (!physicsData?.enabled) continue;

    const bodyState = engine.getRigidBodyState(layer.id);
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

/**
 * Bake physics simulation to keyframes
 * Creates position and rotation keyframes from simulation
 */
export async function bakePhysicsToKeyframes(
  store: PhysicsStore,
  layerId: string,
  options: KeyframeExportOptions = {}
): Promise<ExportedKeyframes> {
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
  const sampleInterval = options.sampleInterval ?? 1;
  const fps = comp.settings.fps;
  const deltaTime = 1 / fps;

  const engine = getPhysicsEngine(store);

  // Reset to beginning
  engine.reset();

  const positionKeyframes: Keyframe<{ x: number; y: number; z: number }>[] = [];
  const rotationKeyframes: Keyframe<number>[] = [];

  // Simulate and collect keyframes
  for (let frame = 0; frame <= endFrame; frame++) {
    engine.step(deltaTime);

    if (frame >= startFrame && frame % sampleInterval === 0) {
      const bodyState = engine.getRigidBodyState(layerId);
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
  }

  // Apply keyframes to layer
  if (layer.transform?.position) {
    layer.transform.position.animated = true;
    layer.transform.position.keyframes = positionKeyframes;
  }

  if (layer.transform?.rotation) {
    layer.transform.rotation.animated = true;
    layer.transform.rotation.keyframes = rotationKeyframes;
  }

  // Optionally simplify keyframes
  if (options.simplify) {
    // TODO: Implement keyframe simplification (remove redundant keyframes)
  }

  // Disable physics after baking
  disableLayerPhysics(store, layerId);

  storeLogger.info('Physics baked to keyframes:', layerId, {
    positionKeyframes: positionKeyframes.length,
    rotationKeyframes: rotationKeyframes.length,
  });

  return {
    layerId,
    properties: {
      'transform.position': positionKeyframes,
      'transform.rotation': rotationKeyframes,
    },
  };
}

/**
 * Bake all physics-enabled layers to keyframes
 */
export async function bakeAllPhysicsToKeyframes(
  store: PhysicsStore,
  options: KeyframeExportOptions = {}
): Promise<ExportedKeyframes[]> {
  const comp = store.project.compositions[store.activeCompositionId];
  if (!comp) return [];

  const results: ExportedKeyframes[] = [];

  for (const layer of comp.layers) {
    const physicsData = (layer.data as any)?.physics as PhysicsLayerData | undefined;
    if (physicsData?.enabled) {
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

  // Build ragdoll based on preset
  const ragdoll = builder.buildFromPreset(preset);

  // Add ragdoll to engine
  engine.addRagdoll(ragdoll);

  store.updateLayerData(layerId, {
    physics: {
      enabled: true,
      type: 'ragdoll',
      config: ragdoll,
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
