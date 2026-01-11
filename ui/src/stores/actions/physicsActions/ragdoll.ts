/**
 * Physics Actions - Ragdoll Simulation
 *
 * Create ragdoll physics for pose layers.
 */

import { createRagdollBuilder } from "@/services/physics";
import type { RigidBodyConfig } from "@/types/physics";
import { storeLogger } from "@/utils/logger";
import { getPhysicsEngine } from "./engine";
import type { PhysicsStore } from "./types";

// ============================================================================
// RAGDOLL CREATION
// ============================================================================

/**
 * Create ragdoll for a pose layer
 */
export function createRagdollForLayer(
  store: PhysicsStore,
  layerId: string,
  preset: "adult" | "child" | "cartoon" = "adult",
): void {
  const layer = store.getLayerById(layerId);
  if (!layer || layer.type !== "pose") {
    storeLogger.warn("Ragdoll requires a pose layer");
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
}
