/**
 * @module services/physics
 * @description Newton Physics Simulation module exports
 *
 * Complete physics engine for rigid bodies, soft bodies, cloth, and ragdolls.
 * All simulations are deterministic with checkpoint-based scrubbing support.
 */

// Re-export types
export type {
  AttractionForce,
  BlobJointConfig,
  BodyType,
  BuoyancyForce,
  // Cloth
  ClothConfig,
  ClothState,
  CollisionFilter,
  CollisionResponse,
  CollisionShape,
  ContactInfo,
  DistanceJointConfig,
  DragForce,
  ExplosionForce,
  ExportedKeyframes,
  ForceField,
  // Forces
  ForceType,
  GravityForce,
  HumanoidRagdollPreset,
  JointConfig,
  // Joints
  JointType,
  // Export
  KeyframeExportOptions,
  PhysicsCompositionData,
  // Layer integration
  PhysicsLayerData,
  PhysicsMaterial,
  PhysicsSimulationState,
  // Space configuration
  PhysicsSpaceConfig,
  // Core types
  PhysicsVec2,
  PistonJointConfig,
  PivotJointConfig,
  // Ragdoll
  RagdollBone,
  RagdollConfig,
  RagdollState,
  // Rigid body
  RigidBodyConfig,
  RigidBodyState,
  RopeJointConfig,
  ShapeType,
  SoftBodyConfig,
  SoftBodyState,
  SpringJointConfig,
  VerletConstraint,
  // Soft body
  VerletParticle,
  VortexForce,
  WeldJointConfig,
  WheelJointConfig,
  WindForce,
} from "@/types/physics";
// Re-export presets
export {
  DEFAULT_SPACE_CONFIG,
  HUMANOID_PRESETS,
  MATERIAL_PRESETS,
} from "@/types/physics";
// Joint constraint system
export { JointSystem } from "./JointSystem";
// Main physics engine
export { PhysicsEngine, PhysicsRandom, vec2 } from "./PhysicsEngine";
// Ragdoll builder
export {
  applyRagdollState,
  convertRagdollToPhysics,
  extractRagdollState,
  HUMANOID_BONES,
  RagdollBuilder,
} from "./RagdollBuilder";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                       // convenience // factory // functions
// ════════════════════════════════════════════════════════════════════════════

import type {
  ClothConfig,
  CollisionFilter,
  ForceField,
  PhysicsMaterial,
  PhysicsSpaceConfig,
  PhysicsVec2,
  RigidBodyConfig,
} from "@/types/physics";
import { MATERIAL_PRESETS } from "@/types/physics";
import { PhysicsEngine } from "./PhysicsEngine";
import { RagdollBuilder } from "./RagdollBuilder";
import { isFiniteNumber } from "@/utils/typeGuards";

/**
 * Create a new physics engine with default settings
 */
export function createPhysicsEngine(
  config?: Partial<PhysicsSpaceConfig>,
): PhysicsEngine {
  return new PhysicsEngine(config);
}

/**
 * Create a new ragdoll builder
 */
export function createRagdollBuilder(
  id: string,
  layerId: string,
): RagdollBuilder {
  return new RagdollBuilder(id, layerId);
}

/**
 * Create a simple circle rigid body config
 */
export function createCircleBody(
  id: string,
  layerId: string,
  options: {
    position: PhysicsVec2;
    radius: number;
    mass?: number;
    material?: PhysicsMaterial;
    isStatic?: boolean;
  },
): RigidBodyConfig {
  const defaultFilter: CollisionFilter = {
    category: 1,
    mask: 0xffffffff,
    group: 0,
  };

  // Type proof: mass ∈ number | undefined → number
  const mass = isFiniteNumber(options.mass) && options.mass > 0
    ? options.mass
    : 1;
  // Type proof: material ∈ PhysicsMaterial | undefined → PhysicsMaterial
  const material = options.material ? options.material : MATERIAL_PRESETS.default;

  return {
    id,
    layerId,
    type: options.isStatic ? "static" : "dynamic",
    mass,
    position: { ...options.position },
    velocity: { x: 0, y: 0 },
    angle: 0,
    angularVelocity: 0,
    shape: { type: "circle", radius: options.radius },
    material,
    filter: defaultFilter,
    response: "collide",
    linearDamping: 0.1,
    angularDamping: 0.1,
    canSleep: true,
    sleepThreshold: 10,
  };
}

/**
 * Create a simple box rigid body config
 */
export function createBoxBody(
  id: string,
  layerId: string,
  options: {
    position: PhysicsVec2;
    width: number;
    height: number;
    mass?: number;
    material?: PhysicsMaterial;
    isStatic?: boolean;
  },
): RigidBodyConfig {
  const defaultFilter: CollisionFilter = {
    category: 1,
    mask: 0xffffffff,
    group: 0,
  };

  // Type proof: mass ∈ number | undefined → number
  const mass = isFiniteNumber(options.mass) && options.mass > 0
    ? options.mass
    : 1;
  // Type proof: material ∈ PhysicsMaterial | undefined → PhysicsMaterial
  const material = options.material ? options.material : MATERIAL_PRESETS.default;

  return {
    id,
    layerId,
    type: options.isStatic ? "static" : "dynamic",
    mass,
    position: { ...options.position },
    velocity: { x: 0, y: 0 },
    angle: 0,
    angularVelocity: 0,
    shape: { type: "box", width: options.width, height: options.height },
    material,
    filter: defaultFilter,
    response: "collide",
    linearDamping: 0.1,
    angularDamping: 0.1,
    canSleep: true,
    sleepThreshold: 10,
  };
}

/**
 * Create a simple gravity force field
 */
export function createGravityForce(
  id: string,
  gravity: PhysicsVec2 = { x: 0, y: 980 },
): ForceField {
  return {
    id,
    type: "gravity",
    enabled: true,
    startFrame: 0,
    endFrame: -1,
    gravity: {
      id: `${id}-gravity`,
      name: "Gravity",
      type: "position" as const,
      value: { x: gravity.x, y: gravity.y, z: 0 },
      animated: false,
      keyframes: [],
    },
  } as ForceField;
}

/**
 * Create a cloth configuration
 */
export function createClothConfig(
  id: string,
  layerId: string,
  options: {
    origin: PhysicsVec2;
    width: number;
    height: number;
    spacing?: number;
    pinnedTop?: boolean;
    pinnedCorners?: boolean;
  },
): ClothConfig {
  // Type proof: spacing ∈ number | undefined → number
  const spacing = isFiniteNumber(options.spacing) && options.spacing > 0
    ? options.spacing
    : 10;
  const pinnedParticles: number[] = [];

  if (options.pinnedTop) {
    for (let x = 0; x < options.width; x++) {
      pinnedParticles.push(x); // Top row
    }
  } else if (options.pinnedCorners) {
    pinnedParticles.push(0); // Top-left
    pinnedParticles.push(options.width - 1); // Top-right
  }

  const defaultFilter: CollisionFilter = {
    category: 1,
    mask: 0xffffffff,
    group: 0,
  };

  return {
    id,
    layerId,
    width: options.width,
    height: options.height,
    spacing,
    origin: { ...options.origin },
    pinnedParticles,
    structuralStiffness: 0.8,
    shearStiffness: 0.5,
    bendStiffness: 0.3,
    iterations: 5,
    damping: 0.98,
    particleMass: 0.1,
    collisionRadius: spacing * 0.3,
    selfCollision: false,
    tearThreshold: 0,
    material: MATERIAL_PRESETS.default,
    filter: defaultFilter,
  };
}
