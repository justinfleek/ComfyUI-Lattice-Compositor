/**
 * Physics Actions - Engine Management
 *
 * Initialize, get, and dispose the physics engine.
 */

import {
  createPhysicsEngine,
  type PhysicsEngine,
} from "@/services/physics";
import type { PhysicsSimulationState, PhysicsSpaceConfig } from "@/types/physics";
import { storeLogger } from "@/utils/logger";
import type { PhysicsStore } from "./types";

// ============================================================================
// PHYSICS ENGINE SINGLETON
// ============================================================================

/** Global physics engine instance */
let physicsEngine: PhysicsEngine | null = null;

/** Per-composition physics states for deterministic scrubbing */
export const compositionPhysicsStates = new Map<string, PhysicsSimulationState>();

// ============================================================================
// ENGINE LIFECYCLE
// ============================================================================

/**
 * Initialize physics engine for the current composition
 */
export function initializePhysicsEngine(
  store: PhysicsStore,
  config?: Partial<PhysicsSpaceConfig>,
): PhysicsEngine {
  const comp = store.project.compositions[store.activeCompositionId];
  if (!comp) {
    throw new Error("No active composition");
  }

  // Create physics engine with composition-aware config
  const fullConfig: Partial<PhysicsSpaceConfig> = {
    ...config,
    // Use composition dimensions to set default gravity scale
    // (worldBounds is handled internally by the engine)
  };

  physicsEngine = createPhysicsEngine(fullConfig);
  storeLogger.info(
    "Physics engine initialized for composition",
    store.activeCompositionId,
  );
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
  storeLogger.info("Physics engine disposed");
}
