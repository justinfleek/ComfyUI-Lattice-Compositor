/**
 * Physics Actions - Cloth Simulation
 *
 * Create and configure cloth physics.
 */

import { createClothConfig } from "@/services/physics";
import { storeLogger } from "@/utils/logger";
import { getPhysicsEngine } from "./engine";
import type { PhysicsStore } from "./types";

// ============================================================================
// CLOTH CREATION
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
  },
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
      type: "cloth",
      config: clothConfig,
    },
  });

  storeLogger.info("Cloth created for layer:", layerId);
}
