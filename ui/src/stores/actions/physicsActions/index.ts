/**
 * Physics Actions
 *
 * Store actions for Newton Physics Simulation integration.
 * Provides control over physics simulation, baking to keyframes,
 * and physics space configuration.
 *
 * MODULE STRUCTURE:
 * - types.ts: Store interface and baking types
 * - engine.ts: Physics engine management
 * - rigidBody.ts: Rigid body management
 * - forceFields.ts: Force field management
 * - simulation.ts: Simulation control
 * - bake.ts: Bake to keyframes
 * - cloth.ts: Cloth simulation
 * - ragdoll.ts: Ragdoll simulation
 * - collision.ts: Collision configuration
 */

// Types
export type {
  PhysicsStore,
  BakedKeyframe,
  BakeOptions,
  BakeResult,
} from "./types";

// Engine management
export {
  initializePhysicsEngine,
  getPhysicsEngine,
  disposePhysicsEngine,
} from "./engine";

// Rigid body management
export {
  enableLayerPhysics,
  disableLayerPhysics,
  updateLayerPhysicsConfig,
} from "./rigidBody";

// Force field management
export { addForceField, removeForceField, setGravity } from "./forceFields";

// Simulation control
export {
  stepPhysics,
  evaluatePhysicsAtFrame,
  resetPhysicsSimulation,
} from "./simulation";

// Bake to keyframes
export { bakePhysicsToKeyframes, bakeAllPhysicsToKeyframes } from "./bake";

// Cloth simulation
export { createClothForLayer } from "./cloth";

// Ragdoll simulation
export { createRagdollForLayer } from "./ragdoll";

// Collision configuration
export { setLayerCollisionGroup, setLayersCanCollide } from "./collision";
