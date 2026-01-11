/**
 * Physics Actions - Simulation Control
 *
 * Step, evaluate, and reset physics simulation.
 */

import type {
  PhysicsLayerData,
  PhysicsSimulationState,
} from "@/types/physics";
import { storeLogger } from "@/utils/logger";
import { getPhysicsEngine, compositionPhysicsStates } from "./engine";
import type { PhysicsStore } from "./types";

// ============================================================================
// SIMULATION STEPPING
// ============================================================================

/**
 * Step the physics simulation to a specific frame
 * Called during playback to advance physics state
 */
export function stepPhysics(store: PhysicsStore, targetFrame: number): void {
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
  targetFrame: number,
): void {
  const engine = getPhysicsEngine(store);
  const state = engine.evaluateFrame(targetFrame);

  // Apply physics state to layers
  applyPhysicsStateToLayers(store, state);
}

// ============================================================================
// SIMULATION RESET
// ============================================================================

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
}

// ============================================================================
// STATE APPLICATION
// ============================================================================

/**
 * Apply physics state to layer transforms
 */
function applyPhysicsStateToLayers(
  store: PhysicsStore,
  state: PhysicsSimulationState,
): void {
  const comp = store.project.compositions[store.activeCompositionId];
  if (!comp) return;

  for (const layer of comp.layers) {
    const physicsData = (layer.data as unknown as Record<string, unknown>)?.physics as
      | PhysicsLayerData
      | undefined;
    if (!physicsData?.physicsEnabled) continue;

    // Find the body state for this layer
    const bodyState = state.rigidBodies.find((b) => b.id === layer.id);
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
