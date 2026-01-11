/**
 * Physics Actions - Rigid Body Management
 *
 * Enable, disable, and update physics for layers.
 */

import {
  createBoxBody,
  createCircleBody,
} from "@/services/physics";
import type { PhysicsLayerData, RigidBodyConfig } from "@/types/physics";
import { storeLogger } from "@/utils/logger";
import { getPhysicsEngine } from "./engine";
import type { PhysicsStore } from "./types";

// ============================================================================
// ENABLE/DISABLE
// ============================================================================

/**
 * Enable physics for a layer as a rigid body
 */
export function enableLayerPhysics(
  store: PhysicsStore,
  layerId: string,
  config: Partial<RigidBodyConfig> = {},
): void {
  const layer = store.getLayerById(layerId);
  if (!layer) {
    storeLogger.warn("Layer not found for physics:", layerId);
    return;
  }

  const engine = getPhysicsEngine(store);

  // Get layer position for initial body position
  const position = {
    x: layer.transform?.position?.value?.x ?? 0,
    y: layer.transform?.position?.value?.y ?? 0,
  };

  // Create rigid body config
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
  storeLogger.info("Physics enabled for layer:", layerId);
}

/**
 * Disable physics for a layer
 */
export function disableLayerPhysics(
  store: PhysicsStore,
  layerId: string,
): void {
  const engine = getPhysicsEngine(store);
  engine.removeRigidBody(layerId);

  store.updateLayerData(layerId, {
    physics: { physicsEnabled: false },
  });
  storeLogger.info("Physics disabled for layer:", layerId);
}

// ============================================================================
// UPDATE
// ============================================================================

/**
 * Update physics body for a layer
 */
export function updateLayerPhysicsConfig(
  store: PhysicsStore,
  layerId: string,
  updates: Partial<RigidBodyConfig>,
): void {
  const layer = store.getLayerById(layerId);
  if (!layer) return;

  const physicsData = (layer.data as unknown as Record<string, unknown>)?.physics as
    | PhysicsLayerData
    | undefined;
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
