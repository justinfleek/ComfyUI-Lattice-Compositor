/**
 * Physics Actions - Collision Configuration
 *
 * Set collision groups and filtering.
 */

import { storeLogger } from "@/utils/logger";
import { updateLayerPhysicsConfig } from "./rigidBody";
import type { PhysicsStore } from "./types";

// ============================================================================
// COLLISION GROUPS
// ============================================================================

/**
 * Set collision group for a layer
 */
export function setLayerCollisionGroup(
  store: PhysicsStore,
  layerId: string,
  group: number,
  mask: number = 0xffffffff,
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

  storeLogger.info("Collision group set:", layerId, group);
}

/**
 * Enable/disable collision between two layers
 */
export function setLayersCanCollide(
  _store: PhysicsStore,
  _layerIdA: string,
  _layerIdB: string,
  _canCollide: boolean,
): void {
  // For now, this would require more complex collision filtering
  // which can be added when the physics engine supports it
  storeLogger.warn("setLayersCanCollide not yet implemented");
}
