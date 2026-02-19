/**
 * @module services/physics/RagdollBuilder
 * @description Ragdoll creation and management system.
 *
 * Features:
 * - Humanoid ragdoll presets (adult, child, cartoon)
 * - Custom bone hierarchy
 * - Automatic joint generation with angle limits
 * - Integration with physics engine
 */

import type {
  CollisionFilter,
  HumanoidRagdollPreset,
  JointConfig,
  PhysicsMaterial,
  PhysicsVec2,
  PivotJointConfig,
  RagdollBone,
  RagdollConfig,
  RagdollState,
  RigidBodyConfig,
} from "@/types/physics";
import { HUMANOID_PRESETS, MATERIAL_PRESETS } from "@/types/physics";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                 // ragdoll // bone // names
// ═══════════════════════════════════════════════════════════════════════════

export const HUMANOID_BONES = {
  HEAD: "head",
  NECK: "neck",
  TORSO_UPPER: "torso_upper",
  TORSO_LOWER: "torso_lower",
  PELVIS: "pelvis",
  UPPER_ARM_L: "upper_arm_l",
  LOWER_ARM_L: "lower_arm_l",
  HAND_L: "hand_l",
  UPPER_ARM_R: "upper_arm_r",
  LOWER_ARM_R: "lower_arm_r",
  HAND_R: "hand_r",
  UPPER_LEG_L: "upper_leg_l",
  LOWER_LEG_L: "lower_leg_l",
  FOOT_L: "foot_l",
  UPPER_LEG_R: "upper_leg_r",
  LOWER_LEG_R: "lower_leg_r",
  FOOT_R: "foot_r",
} as const;

// ═══════════════════════════════════════════════════════════════════════════
//                                                       // ragdoll // builder
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Builder class for creating ragdolls
 */
export class RagdollBuilder {
  private id: string;
  private layerId: string;
  private position: PhysicsVec2;
  private rotation: number;
  private bones: RagdollBone[] = [];
  private material: PhysicsMaterial;
  private filter: CollisionFilter;
  private selfCollision: boolean = false;
  private damping: number = 0.1;

  constructor(id: string, layerId: string) {
    this.id = id;
    this.layerId = layerId;
    this.position = { x: 0, y: 0 };
    this.rotation = 0;
    this.material = { restitution: 0.2, friction: 0.5 };
    this.filter = { category: 1, mask: 0xffffffff, group: 0 };
  }

  /**
   * Set ragdoll position
   */
  setPosition(x: number, y: number): this {
    this.position = { x, y };
    return this;
  }

  /**
   * Set ragdoll rotation
   */
  setRotation(angle: number): this {
    this.rotation = angle;
    return this;
  }

  /**
   * Set material for all bones
   */
  setMaterial(material: PhysicsMaterial): this {
    this.material = material;
    return this;
  }

  /**
   * Set collision filter
   */
  setCollisionFilter(filter: CollisionFilter): this {
    this.filter = filter;
    return this;
  }

  /**
   * Enable/disable self collision
   */
  setSelfCollision(enabled: boolean): this {
    this.selfCollision = enabled;
    return this;
  }

  /**
   * Set damping
   */
  setDamping(damping: number): this {
    this.damping = damping;
    return this;
  }

  /**
   * Add a custom bone
   */
  addBone(bone: RagdollBone): this {
    this.bones.push(bone);
    return this;
  }

  /**
   * Create humanoid ragdoll from preset
   */
  fromPreset(presetName: keyof typeof HUMANOID_PRESETS): this {
    const preset = HUMANOID_PRESETS[presetName];
    if (!preset) {
      throw new Error(`Unknown ragdoll preset: ${presetName}`);
    }

    return this.fromCustomPreset(preset);
  }

  /**
   * Create humanoid ragdoll from custom preset
   */
  fromCustomPreset(preset: HumanoidRagdollPreset): this {
    const { scale, proportions, massDistribution } = preset;
    const p = proportions;
    const m = massDistribution;

    // Clear existing bones
    this.bones = [];

    // Pelvis (root)
    this.addBone({
      id: HUMANOID_BONES.PELVIS,
      name: "Pelvis",
      length: (p.hipWidth * scale) / 100,
      width: ((p.hipWidth * scale) / 100) * 0.5,
      mass: m.torso * 0.2,
      angleLimits: { min: -Math.PI * 0.1, max: Math.PI * 0.1 },
      jointStiffness: 0.8,
      jointDamping: 0.3,
    });

    // Torso Lower
    this.addBone({
      id: HUMANOID_BONES.TORSO_LOWER,
      name: "Lower Torso",
      parent: HUMANOID_BONES.PELVIS,
      length: ((p.torsoLength * scale) / 100) * 0.4,
      width: ((p.shoulderWidth * scale) / 100) * 0.6,
      mass: m.torso * 0.3,
      angleLimits: { min: -Math.PI * 0.15, max: Math.PI * 0.15 },
      jointStiffness: 0.7,
      jointDamping: 0.3,
    });

    // Torso Upper
    this.addBone({
      id: HUMANOID_BONES.TORSO_UPPER,
      name: "Upper Torso",
      parent: HUMANOID_BONES.TORSO_LOWER,
      length: ((p.torsoLength * scale) / 100) * 0.4,
      width: (p.shoulderWidth * scale) / 100,
      mass: m.torso * 0.4,
      angleLimits: { min: -Math.PI * 0.2, max: Math.PI * 0.2 },
      jointStiffness: 0.7,
      jointDamping: 0.3,
    });

    // Neck
    this.addBone({
      id: HUMANOID_BONES.NECK,
      name: "Neck",
      parent: HUMANOID_BONES.TORSO_UPPER,
      length: ((p.headSize * scale) / 100) * 0.3,
      width: ((p.headSize * scale) / 100) * 0.3,
      mass: m.head * 0.1,
      angleLimits: { min: -Math.PI * 0.25, max: Math.PI * 0.25 },
      jointStiffness: 0.5,
      jointDamping: 0.2,
    });

    // Head
    this.addBone({
      id: HUMANOID_BONES.HEAD,
      name: "Head",
      parent: HUMANOID_BONES.NECK,
      length: (p.headSize * scale) / 100,
      width: ((p.headSize * scale) / 100) * 0.8,
      mass: m.head * 0.9,
      angleLimits: { min: -Math.PI * 0.3, max: Math.PI * 0.3 },
      jointStiffness: 0.5,
      jointDamping: 0.2,
    });

    // Left Arm
    this.addBone({
      id: HUMANOID_BONES.UPPER_ARM_L,
      name: "Upper Arm Left",
      parent: HUMANOID_BONES.TORSO_UPPER,
      length: ((p.armLength * scale) / 100) * 0.45,
      width: ((p.armLength * scale) / 100) * 0.15,
      mass: m.upperArm,
      angleLimits: { min: -Math.PI * 0.9, max: Math.PI * 0.1 },
      jointStiffness: 0.4,
      jointDamping: 0.2,
    });

    this.addBone({
      id: HUMANOID_BONES.LOWER_ARM_L,
      name: "Lower Arm Left",
      parent: HUMANOID_BONES.UPPER_ARM_L,
      length: ((p.armLength * scale) / 100) * 0.4,
      width: ((p.armLength * scale) / 100) * 0.12,
      mass: m.lowerArm,
      angleLimits: { min: 0, max: Math.PI * 0.8 },
      jointStiffness: 0.4,
      jointDamping: 0.2,
    });

    this.addBone({
      id: HUMANOID_BONES.HAND_L,
      name: "Hand Left",
      parent: HUMANOID_BONES.LOWER_ARM_L,
      length: ((p.armLength * scale) / 100) * 0.15,
      width: ((p.armLength * scale) / 100) * 0.1,
      mass: m.hand,
      angleLimits: { min: -Math.PI * 0.3, max: Math.PI * 0.3 },
      jointStiffness: 0.3,
      jointDamping: 0.1,
    });

    // Right Arm
    this.addBone({
      id: HUMANOID_BONES.UPPER_ARM_R,
      name: "Upper Arm Right",
      parent: HUMANOID_BONES.TORSO_UPPER,
      length: ((p.armLength * scale) / 100) * 0.45,
      width: ((p.armLength * scale) / 100) * 0.15,
      mass: m.upperArm,
      angleLimits: { min: -Math.PI * 0.1, max: Math.PI * 0.9 },
      jointStiffness: 0.4,
      jointDamping: 0.2,
    });

    this.addBone({
      id: HUMANOID_BONES.LOWER_ARM_R,
      name: "Lower Arm Right",
      parent: HUMANOID_BONES.UPPER_ARM_R,
      length: ((p.armLength * scale) / 100) * 0.4,
      width: ((p.armLength * scale) / 100) * 0.12,
      mass: m.lowerArm,
      angleLimits: { min: -Math.PI * 0.8, max: 0 },
      jointStiffness: 0.4,
      jointDamping: 0.2,
    });

    this.addBone({
      id: HUMANOID_BONES.HAND_R,
      name: "Hand Right",
      parent: HUMANOID_BONES.LOWER_ARM_R,
      length: ((p.armLength * scale) / 100) * 0.15,
      width: ((p.armLength * scale) / 100) * 0.1,
      mass: m.hand,
      angleLimits: { min: -Math.PI * 0.3, max: Math.PI * 0.3 },
      jointStiffness: 0.3,
      jointDamping: 0.1,
    });

    // Left Leg
    this.addBone({
      id: HUMANOID_BONES.UPPER_LEG_L,
      name: "Upper Leg Left",
      parent: HUMANOID_BONES.PELVIS,
      length: ((p.legLength * scale) / 100) * 0.45,
      width: ((p.legLength * scale) / 100) * 0.15,
      mass: m.upperLeg,
      angleLimits: { min: -Math.PI * 0.3, max: Math.PI * 0.5 },
      jointStiffness: 0.5,
      jointDamping: 0.3,
    });

    this.addBone({
      id: HUMANOID_BONES.LOWER_LEG_L,
      name: "Lower Leg Left",
      parent: HUMANOID_BONES.UPPER_LEG_L,
      length: ((p.legLength * scale) / 100) * 0.4,
      width: ((p.legLength * scale) / 100) * 0.12,
      mass: m.lowerLeg,
      angleLimits: { min: -Math.PI * 0.7, max: 0 },
      jointStiffness: 0.5,
      jointDamping: 0.3,
    });

    this.addBone({
      id: HUMANOID_BONES.FOOT_L,
      name: "Foot Left",
      parent: HUMANOID_BONES.LOWER_LEG_L,
      length: ((p.legLength * scale) / 100) * 0.15,
      width: ((p.legLength * scale) / 100) * 0.08,
      mass: m.foot,
      angleLimits: { min: -Math.PI * 0.2, max: Math.PI * 0.3 },
      jointStiffness: 0.4,
      jointDamping: 0.2,
    });

    // Right Leg
    this.addBone({
      id: HUMANOID_BONES.UPPER_LEG_R,
      name: "Upper Leg Right",
      parent: HUMANOID_BONES.PELVIS,
      length: ((p.legLength * scale) / 100) * 0.45,
      width: ((p.legLength * scale) / 100) * 0.15,
      mass: m.upperLeg,
      angleLimits: { min: -Math.PI * 0.5, max: Math.PI * 0.3 },
      jointStiffness: 0.5,
      jointDamping: 0.3,
    });

    this.addBone({
      id: HUMANOID_BONES.LOWER_LEG_R,
      name: "Lower Leg Right",
      parent: HUMANOID_BONES.UPPER_LEG_R,
      length: ((p.legLength * scale) / 100) * 0.4,
      width: ((p.legLength * scale) / 100) * 0.12,
      mass: m.lowerLeg,
      angleLimits: { min: 0, max: Math.PI * 0.7 },
      jointStiffness: 0.5,
      jointDamping: 0.3,
    });

    this.addBone({
      id: HUMANOID_BONES.FOOT_R,
      name: "Foot Right",
      parent: HUMANOID_BONES.LOWER_LEG_R,
      length: ((p.legLength * scale) / 100) * 0.15,
      width: ((p.legLength * scale) / 100) * 0.08,
      mass: m.foot,
      angleLimits: { min: -Math.PI * 0.3, max: Math.PI * 0.2 },
      jointStiffness: 0.4,
      jointDamping: 0.2,
    });

    return this;
  }

  /**
   * Build the ragdoll configuration
   */
  build(): RagdollConfig {
    return {
      id: this.id,
      layerId: this.layerId,
      position: { ...this.position },
      rotation: this.rotation,
      bones: [...this.bones],
      material: { ...this.material },
      filter: { ...this.filter },
      selfCollision: this.selfCollision,
      damping: this.damping,
    };
  }
}

// ═══════════════════════════════════════════════════════════════════════════
//                                          // ragdoll // physics // converter
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Convert ragdoll config to rigid bodies and joints
 */
export function convertRagdollToPhysics(config: RagdollConfig): {
  bodies: RigidBodyConfig[];
  joints: JointConfig[];
} {
  const bodies: RigidBodyConfig[] = [];
  const joints: JointConfig[] = [];

  const boneMap = new Map<string, RagdollBone>();
  const bonePositions = new Map<string, PhysicsVec2>();
  const boneAngles = new Map<string, number>();

  // First pass: index bones
  for (const bone of config.bones) {
    boneMap.set(bone.id, bone);
  }

  // Calculate bone positions (recursive)
  function calculateBonePosition(bone: RagdollBone): {
    position: PhysicsVec2;
    angle: number;
  } {
    if (bonePositions.has(bone.id)) {
      return {
        position: bonePositions.get(bone.id)!,
        angle: boneAngles.get(bone.id)!,
      };
    }

    let position: PhysicsVec2;
    let angle: number;

    if (!bone.parent) {
      // Root bone
      position = { ...config.position };
      angle = config.rotation;
    } else {
      // Child bone - position at end of parent
      const parent = boneMap.get(bone.parent);
      if (!parent) {
        throw new Error(`Parent bone ${bone.parent} not found`);
      }

      const parentData = calculateBonePosition(parent);
      const parentEndOffset = {
        x: Math.cos(parentData.angle) * parent.length,
        y: Math.sin(parentData.angle) * parent.length,
      };

      position = {
        x: parentData.position.x + parentEndOffset.x,
        y: parentData.position.y + parentEndOffset.y,
      };
      angle = parentData.angle; // Inherit parent angle initially
    }

    bonePositions.set(bone.id, position);
    boneAngles.set(bone.id, angle);

    return { position, angle };
  }

  // Create rigid bodies for each bone
  for (const bone of config.bones) {
    const { position, angle } = calculateBonePosition(bone);

    // Body center is at middle of bone
    const centerOffset = {
      x: Math.cos(angle) * bone.length * 0.5,
      y: Math.sin(angle) * bone.length * 0.5,
    };

    const bodyId = `${config.id}_${bone.id}`;

    bodies.push({
      id: bodyId,
      layerId: config.layerId,
      type: "dynamic",
      mass: bone.mass,
      position: {
        x: position.x + centerOffset.x,
        y: position.y + centerOffset.y,
      },
      velocity: { x: 0, y: 0 },
      angle,
      angularVelocity: 0,
      shape: {
        type: "capsule",
        length: bone.length,
        radius: bone.width * 0.5,
      },
      material: { ...config.material },
      filter: config.selfCollision
        ? { ...config.filter }
        : { ...config.filter, group: -1 }, // Negative group = no self-collision
      response: "collide",
      linearDamping: config.damping,
      angularDamping: config.damping * 2,
      canSleep: true,
      sleepThreshold: 10,
    });
  }

  // Create joints between bones
  for (const bone of config.bones) {
    if (!bone.parent) continue;

    const parent = boneMap.get(bone.parent)!;
    const parentBodyId = `${config.id}_${parent.id}`;
    const childBodyId = `${config.id}_${bone.id}`;

    const jointId = `${config.id}_joint_${bone.id}`;

    // Pivot joint at connection point
    const joint: PivotJointConfig = {
      id: jointId,
      type: "pivot",
      bodyA: parentBodyId,
      bodyB: childBodyId,
      anchorA: {
        x: parent.length * 0.5, // End of parent
        y: 0,
      },
      anchorB: {
        x: -bone.length * 0.5, // Start of child
        y: 0,
      },
      collideConnected: config.selfCollision,
      limits: bone.angleLimits,
      motor: {
        enabled: bone.jointStiffness > 0,
        speed: 0,
        maxTorque: bone.jointStiffness * bone.mass * 100,
      },
    };

    joints.push(joint);
  }

  return { bodies, joints };
}

// ═══════════════════════════════════════════════════════════════════════════
//                                              // ragdoll // state // helpers
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Extract ragdoll state from physics bodies
 */
export function extractRagdollState(
  ragdollId: string,
  bones: RagdollBone[],
  getBodyState: (id: string) => {
    position: PhysicsVec2;
    velocity: PhysicsVec2;
    angle: number;
    angularVelocity: number;
  } | null,
): RagdollState {
  const boneStates = [];

  for (const bone of bones) {
    const bodyId = `${ragdollId}_${bone.id}`;
    const state = getBodyState(bodyId);

    if (state) {
      boneStates.push({
        id: bone.id,
        position: { ...state.position },
        angle: state.angle,
        velocity: { ...state.velocity },
        angularVelocity: state.angularVelocity,
      });
    }
  }

  return {
    id: ragdollId,
    bones: boneStates,
  };
}

/**
 * Apply ragdoll state to physics bodies
 */
export function applyRagdollState(
  state: RagdollState,
  setBodyState: (
    id: string,
    position: PhysicsVec2,
    velocity: PhysicsVec2,
    angle: number,
    angularVelocity: number,
  ) => void,
): void {
  for (const boneState of state.bones) {
    const bodyId = `${state.id}_${boneState.id}`;
    setBodyState(
      bodyId,
      boneState.position,
      boneState.velocity,
      boneState.angle,
      boneState.angularVelocity,
    );
  }
}

// ═══════════════════════════════════════════════════════════════════════════
//                                                                  // exports
// ═══════════════════════════════════════════════════════════════════════════

export { HUMANOID_PRESETS, MATERIAL_PRESETS };
