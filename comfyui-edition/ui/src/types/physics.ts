/**
 * @module types/physics
 * @description Complete type definitions for Newton Physics Simulation (Feature 05)
 *
 * Physics engine based on Verlet integration for soft bodies and
 * impulse-based rigid body dynamics. All simulations are deterministic
 * and support keyframe export for professional animation workflows.
 */

import type { AnimatableProperty } from "./animation";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                                     // enums
// ════════════════════════════════════════════════════════════════════════════

/**
 * Body type determines physics behavior
 */
export type BodyType =
  | "static" // Immovable, participates in collision
  | "dynamic" // Fully simulated with mass, velocity, forces
  | "kinematic" // User-controlled position, no forces, collides with dynamic
  | "dormant" // Dynamic that's asleep (optimized, wakes on collision)
  | "AEmatic" // Follows AE keyframes when present, dynamic otherwise
  | "dead"; // Removed from simulation, no collision

/**
 * Joint types for connecting bodies
 */
export type JointType =
  | "pivot" // Rotation around single point (pin joint)
  | "spring" // Springy connection with stiffness/damping
  | "distance" // Fixed distance constraint
  | "piston" // Slide along axis with limits
  | "wheel" // Motor-driven rotation
  | "weld" // Rigid connection (no relative movement)
  | "blob" // Soft blob-like connection
  | "rope"; // One-way constraint (max distance only)

/**
 * Force field types
 */
export type ForceType =
  | "gravity" // Directional constant force
  | "wind" // Directional force with turbulence
  | "attraction" // Point attractor/repeller
  | "explosion" // Radial impulse
  | "buoyancy" // Fluid buoyancy
  | "vortex" // Rotational force
  | "drag"; // Air/fluid resistance

/**
 * Collision shape types
 */
export type ShapeType =
  | "circle"
  | "box"
  | "polygon"
  | "capsule"
  | "convex" // Convex hull from points
  | "compound"; // Multiple shapes combined

/**
 * Collision response types
 */
export type CollisionResponse =
  | "collide" // Normal collision response
  | "sensor" // Detect but don't respond
  | "none"; // No collision detection

// ════════════════════════════════════════════════════════════════════════════
//                                                  // core // physics // types
// ════════════════════════════════════════════════════════════════════════════

/**
 * 2D vector for physics calculations
 */
export interface PhysicsVec2 {
  x: number;
  y: number;
}

/**
 * Physics material properties
 */
export interface PhysicsMaterial {
  /** Coefficient of restitution (bounciness) 0-1 */
  restitution: number;
  /** Friction coefficient 0-1+ */
  friction: number;
  /** Surface friction for rolling objects */
  surfaceVelocity?: PhysicsVec2;
}

/**
 * Collision shape definition
 */
export interface CollisionShape {
  type: ShapeType;

  // Circle
  radius?: number;

  // Box
  width?: number;
  height?: number;

  // Polygon / Convex
  vertices?: PhysicsVec2[];

  // Capsule
  length?: number;
  // radius shared with circle

  // Compound (multiple shapes)
  shapes?: CollisionShape[];

  /** Offset from body center */
  offset?: PhysicsVec2;

  /** Rotation offset in radians */
  rotation?: number;
}

/**
 * Collision filter for groups
 */
export interface CollisionFilter {
  /** Category bits (what this body is) */
  category: number;
  /** Mask bits (what this body collides with) */
  mask: number;
  /** Group index for special handling */
  group: number;
}

// ════════════════════════════════════════════════════════════════════════════
//                                                             // rigid // body
// ════════════════════════════════════════════════════════════════════════════

/**
 * Rigid body configuration
 */
export interface RigidBodyConfig {
  id: string;
  layerId: string; // Link to Lattice layer

  type: BodyType;

  // Physical properties
  mass: number;
  moment?: number; // Moment of inertia (auto-calculated if not set)

  // Position & velocity
  position: PhysicsVec2;
  velocity: PhysicsVec2;
  angle: number; // Rotation in radians
  angularVelocity: number;

  // Collision
  shape: CollisionShape;
  material: PhysicsMaterial;
  filter: CollisionFilter;
  response: CollisionResponse;

  // Damping
  linearDamping: number; // 0-1, velocity reduction per second
  angularDamping: number; // 0-1, rotation reduction per second

  // Constraints
  fixedRotation?: boolean; // Prevent rotation
  bullet?: boolean; // CCD for fast-moving objects

  // Sleep settings
  canSleep: boolean;
  sleepThreshold: number; // Velocity threshold for sleep
}

/**
 * Runtime rigid body state
 */
export interface RigidBodyState {
  id: string;
  position: PhysicsVec2;
  velocity: PhysicsVec2;
  angle: number;
  angularVelocity: number;
  isSleeping: boolean;
  contacts: ContactInfo[];
}

/**
 * Contact information from collision
 */
export interface ContactInfo {
  bodyA: string;
  bodyB: string;
  point: PhysicsVec2;
  normal: PhysicsVec2;
  depth: number;
  impulse: number;
}

// ════════════════════════════════════════════════════════════════════════════
//                                                                    // joints
// ════════════════════════════════════════════════════════════════════════════

/**
 * Base joint configuration
 */
export interface JointConfigBase {
  id: string;
  type: JointType;
  bodyA: string; // Body ID
  bodyB: string; // Body ID (or 'world' for ground)

  /** Local anchor on body A */
  anchorA: PhysicsVec2;
  /** Local anchor on body B */
  anchorB: PhysicsVec2;

  /** Collision between connected bodies */
  collideConnected: boolean;

  /** Breaking force (0 = unbreakable) */
  maxForce?: number;
}

/**
 * Pivot joint - rotation around single point
 */
export interface PivotJointConfig extends JointConfigBase {
  type: "pivot";
  /** Motor settings */
  motor?: {
    enabled: boolean;
    targetAngle?: number; // Target angle for servo mode
    speed: number; // Angular velocity
    maxTorque: number;
  };
  /** Angle limits in radians */
  limits?: {
    min: number;
    max: number;
  };
}

/**
 * Spring joint - springy connection
 */
export interface SpringJointConfig extends JointConfigBase {
  type: "spring";
  /** Rest length of spring */
  restLength: number;
  /** Spring stiffness (N/m) */
  stiffness: number;
  /** Damping coefficient */
  damping: number;
}

/**
 * Distance joint - fixed distance constraint
 */
export interface DistanceJointConfig extends JointConfigBase {
  type: "distance";
  /** Fixed distance between anchors */
  distance: number;
}

/**
 * Piston joint - slide along axis
 */
export interface PistonJointConfig extends JointConfigBase {
  type: "piston";
  /** Slide axis (local to bodyA) */
  axis: PhysicsVec2;
  /** Translation limits */
  limits?: {
    min: number;
    max: number;
  };
  /** Motor settings */
  motor?: {
    enabled: boolean;
    speed: number;
    maxForce: number;
  };
}

/**
 * Wheel joint - motor-driven rotation
 */
export interface WheelJointConfig extends JointConfigBase {
  type: "wheel";
  /** Suspension axis */
  axis: PhysicsVec2;
  /** Suspension frequency (Hz) */
  frequency: number;
  /** Suspension damping ratio */
  dampingRatio: number;
  /** Motor settings */
  motor?: {
    enabled: boolean;
    speed: number;
    maxTorque: number;
  };
}

/**
 * Weld joint - rigid connection
 */
export interface WeldJointConfig extends JointConfigBase {
  type: "weld";
  /** Reference angle between bodies */
  referenceAngle: number;
  /** Softness (0 = rigid, higher = softer) */
  frequency?: number;
  dampingRatio?: number;
}

/**
 * Blob joint - soft connection for deformable shapes
 */
export interface BlobJointConfig extends JointConfigBase {
  type: "blob";
  /** Softness factor */
  softness: number;
  /** Pressure (for internal volume) */
  pressure: number;
}

/**
 * Rope joint - maximum distance constraint
 */
export interface RopeJointConfig extends JointConfigBase {
  type: "rope";
  /** Maximum length */
  maxLength: number;
}

export type JointConfig =
  | PivotJointConfig
  | SpringJointConfig
  | DistanceJointConfig
  | PistonJointConfig
  | WheelJointConfig
  | WeldJointConfig
  | BlobJointConfig
  | RopeJointConfig;

// ════════════════════════════════════════════════════════════════════════════
//                                                                    // forces
// ════════════════════════════════════════════════════════════════════════════

/**
 * Base force field configuration
 */
export interface ForceFieldBase {
  id: string;
  type: ForceType;
  enabled: boolean;

  /** Bodies affected (empty = all) */
  affectedBodies?: string[];

  /** Start frame */
  startFrame: number;
  /** End frame (-1 = forever) */
  endFrame: number;
}

/**
 * Gravity force - constant directional
 */
export interface GravityForce extends ForceFieldBase {
  type: "gravity";
  /** Gravity vector (pixels/s²) */
  gravity: AnimatableProperty<PhysicsVec2>;
}

/**
 * Wind force - directional with turbulence
 */
export interface WindForce extends ForceFieldBase {
  type: "wind";
  /** Wind direction and strength */
  direction: AnimatableProperty<PhysicsVec2>;
  /** Turbulence strength */
  turbulence: AnimatableProperty<number>;
  /** Turbulence frequency */
  frequency: number;
  /** Noise seed for determinism */
  seed: number;
}

/**
 * Attraction force - point attractor/repeller
 */
export interface AttractionForce extends ForceFieldBase {
  type: "attraction";
  /** Attractor position */
  position: AnimatableProperty<PhysicsVec2>;
  /** Strength (negative = repel) */
  strength: AnimatableProperty<number>;
  /** Falloff radius (0 = infinite range) */
  radius: number;
  /** Falloff type */
  falloff: "linear" | "quadratic" | "constant";
}

/**
 * Explosion force - radial impulse
 */
export interface ExplosionForce extends ForceFieldBase {
  type: "explosion";
  /** Explosion center */
  position: PhysicsVec2;
  /** Impulse strength */
  strength: number;
  /** Effect radius */
  radius: number;
  /** Trigger frame */
  triggerFrame: number;
  /** Duration in frames (1 = instant) */
  duration: number;
}

/**
 * Buoyancy force - fluid simulation
 */
export interface BuoyancyForce extends ForceFieldBase {
  type: "buoyancy";
  /** Fluid surface Y level */
  surfaceLevel: AnimatableProperty<number>;
  /** Fluid density */
  density: number;
  /** Linear drag in fluid */
  linearDrag: number;
  /** Angular drag in fluid */
  angularDrag: number;
}

/**
 * Vortex force - rotational
 */
export interface VortexForce extends ForceFieldBase {
  type: "vortex";
  /** Center position */
  position: AnimatableProperty<PhysicsVec2>;
  /** Tangential strength */
  strength: AnimatableProperty<number>;
  /** Inward pull strength */
  inwardForce: number;
  /** Effect radius */
  radius: number;
}

/**
 * Drag force - air/fluid resistance
 */
export interface DragForce extends ForceFieldBase {
  type: "drag";
  /** Linear drag coefficient */
  linear: number;
  /** Quadratic drag coefficient */
  quadratic: number;
}

export type ForceField =
  | GravityForce
  | WindForce
  | AttractionForce
  | ExplosionForce
  | BuoyancyForce
  | VortexForce
  | DragForce;

// ════════════════════════════════════════════════════════════════════════════
//                                                              // soft // body
// ════════════════════════════════════════════════════════════════════════════

/**
 * Verlet particle for soft body simulation
 */
export interface VerletParticle {
  id: string;
  position: PhysicsVec2;
  previousPosition: PhysicsVec2;
  acceleration: PhysicsVec2;
  mass: number;
  pinned: boolean; // Fixed in place
  radius: number; // For collision
}

/**
 * Distance constraint between particles
 */
export interface VerletConstraint {
  id: string;
  particleA: string;
  particleB: string;
  restLength: number;
  stiffness: number; // 0-1, iterations needed for full constraint
  breakThreshold?: number; // Break if stretched beyond this
}

/**
 * Soft body configuration
 */
export interface SoftBodyConfig {
  id: string;
  layerId: string;

  /** Particles in the soft body */
  particles: VerletParticle[];

  /** Constraints connecting particles */
  constraints: VerletConstraint[];

  /** Constraint iterations per step (more = stiffer) */
  iterations: number;

  /** Pressure for closed soft bodies */
  pressure?: number;

  /** Collision radius scale */
  collisionScale: number;

  /** Self-collision enabled */
  selfCollision: boolean;

  /** Collision with rigid bodies */
  rigidCollision: boolean;

  /** Material for rigid body collision */
  material: PhysicsMaterial;

  /** Collision filter */
  filter: CollisionFilter;
}

/**
 * Runtime soft body state
 */
export interface SoftBodyState {
  id: string;
  particles: Array<{
    id: string;
    position: PhysicsVec2;
    velocity: PhysicsVec2;
  }>;
  brokenConstraints: string[];
}

// ════════════════════════════════════════════════════════════════════════════
//                                                       // cloth // simulation
// ════════════════════════════════════════════════════════════════════════════

/**
 * Cloth simulation configuration
 */
export interface ClothConfig {
  id: string;
  layerId: string;

  /** Grid dimensions */
  width: number; // Columns
  height: number; // Rows

  /** Spacing between particles */
  spacing: number;

  /** Top-left corner position */
  origin: PhysicsVec2;

  /** Pinned particle indices (fixed in place) */
  pinnedParticles: number[];

  /** Structural constraint stiffness */
  structuralStiffness: number;

  /** Shear constraint stiffness (diagonal) */
  shearStiffness: number;

  /** Bend constraint stiffness (skip one) */
  bendStiffness: number;

  /** Constraint iterations */
  iterations: number;

  /** Damping factor */
  damping: number;

  /** Mass per particle */
  particleMass: number;

  /** Collision radius per particle */
  collisionRadius: number;

  /** Self-collision enabled */
  selfCollision: boolean;

  /** Tear threshold (0 = no tearing) */
  tearThreshold: number;

  /** Material for rigid body collision */
  material: PhysicsMaterial;

  /** Collision filter */
  filter: CollisionFilter;
}

/**
 * Runtime cloth state
 */
export interface ClothState {
  id: string;
  /** Particle positions in row-major order */
  positions: PhysicsVec2[];
  /** Broken constraints (torn) */
  tornConstraints: Array<{
    row: number;
    col: number;
    type: "structural" | "shear" | "bend";
  }>;
}

// ════════════════════════════════════════════════════════════════════════════
//                                                                   // ragdoll
// ════════════════════════════════════════════════════════════════════════════

/**
 * Ragdoll bone definition
 */
export interface RagdollBone {
  id: string;
  name: string;

  /** Parent bone ID (null for root) */
  parent?: string;

  /** Bone length */
  length: number;

  /** Bone width (for collision shape) */
  width: number;

  /** Mass */
  mass: number;

  /** Joint angle limits (radians) */
  angleLimits: {
    min: number;
    max: number;
  };

  /** Joint stiffness */
  jointStiffness: number;

  /** Joint damping */
  jointDamping: number;
}

/**
 * Ragdoll configuration
 */
export interface RagdollConfig {
  id: string;
  layerId: string;

  /** Root position */
  position: PhysicsVec2;

  /** Root rotation */
  rotation: number;

  /** Bone hierarchy */
  bones: RagdollBone[];

  /** Material for collision */
  material: PhysicsMaterial;

  /** Collision filter */
  filter: CollisionFilter;

  /** Self-collision between bones */
  selfCollision: boolean;

  /** Global damping */
  damping: number;
}

/**
 * Humanoid ragdoll preset configuration
 */
export interface HumanoidRagdollPreset {
  name: string;

  /** Overall scale */
  scale: number;

  /** Body proportions */
  proportions: {
    headSize: number;
    torsoLength: number;
    armLength: number;
    legLength: number;
    shoulderWidth: number;
    hipWidth: number;
  };

  /** Mass distribution */
  massDistribution: {
    head: number;
    torso: number;
    upperArm: number;
    lowerArm: number;
    hand: number;
    upperLeg: number;
    lowerLeg: number;
    foot: number;
  };
}

/**
 * Runtime ragdoll state
 */
export interface RagdollState {
  id: string;
  bones: Array<{
    id: string;
    position: PhysicsVec2;
    angle: number;
    velocity: PhysicsVec2;
    angularVelocity: number;
  }>;
}

// ════════════════════════════════════════════════════════════════════════════
//                                                          // physics // space
// ════════════════════════════════════════════════════════════════════════════

/**
 * Physics space configuration
 */
export interface PhysicsSpaceConfig {
  /** Simulation time step (seconds) */
  timeStep: number;

  /** Velocity iterations for constraint solver */
  velocityIterations: number;

  /** Position iterations for constraint solver */
  positionIterations: number;

  /** Global gravity */
  gravity: PhysicsVec2;

  /** Sleep enabled */
  sleepEnabled: boolean;

  /** Sleep time threshold (seconds) */
  sleepTimeThreshold: number;

  /** Sleep velocity threshold */
  sleepVelocityThreshold: number;

  /** Collision slop (penetration allowance) */
  collisionSlop: number;

  /** Collision bias (position correction) */
  collisionBias: number;

  /** Deterministic mode (fixed timestep) */
  deterministic: boolean;

  /** Random seed for determinism */
  seed: number;
}

/**
 * Complete physics simulation state
 */
export interface PhysicsSimulationState {
  frame: number;
  rigidBodies: RigidBodyState[];
  softBodies: SoftBodyState[];
  cloths: ClothState[];
  ragdolls: RagdollState[];
  contacts: ContactInfo[];
}

/**
 * Keyframe export options
 */
export interface KeyframeExportOptions {
  /** Start frame */
  startFrame: number;

  /** End frame */
  endFrame: number;

  /** Frame step (1 = every frame) */
  frameStep: number;

  /** Properties to export */
  properties: Array<"position" | "rotation" | "scale">;

  /** Simplify keyframes (remove redundant) */
  simplify: boolean;

  /** Simplification tolerance */
  simplifyTolerance: number;

  /** Interpolation type for exported keyframes */
  interpolation: "linear" | "bezier";
}

/**
 * Exported keyframe data
 */
export interface ExportedKeyframes {
  layerId: string;
  property: string;
  keyframes: Array<{
    frame: number;
    value: number | PhysicsVec2;
    interpolation: "linear" | "bezier";
    inHandle?: PhysicsVec2;
    outHandle?: PhysicsVec2;
  }>;
}

// ════════════════════════════════════════════════════════════════════════════
//                                                      // layer // integration
// ════════════════════════════════════════════════════════════════════════════

/**
 * Physics layer data (extends layer.data)
 */
export interface PhysicsLayerData {
  physicsEnabled: boolean;

  /** Rigid body configuration */
  rigidBody?: RigidBodyConfig;

  /** Soft body configuration */
  softBody?: SoftBodyConfig;

  /** Cloth configuration */
  cloth?: ClothConfig;

  /** Ragdoll configuration */
  ragdoll?: RagdollConfig;

  /** Space configuration override (uses global if not set) */
  spaceConfig?: Partial<PhysicsSpaceConfig>;
}

/**
 * Physics composition data
 */
export interface PhysicsCompositionData {
  enabled: boolean;

  /** Global space configuration */
  spaceConfig: PhysicsSpaceConfig;

  /** Force fields */
  forceFields: ForceField[];

  /** Global collision groups */
  collisionGroups: Array<{
    name: string;
    category: number;
    collidesWithSelf: boolean;
  }>;

  /** Simulation cache (for scrubbing) */
  cached: boolean;
  cacheStartFrame: number;
  cacheEndFrame: number;
}

// ════════════════════════════════════════════════════════════════════════════
//                                                                   // presets
// ════════════════════════════════════════════════════════════════════════════

/**
 * Predefined humanoid ragdoll presets
 */
export const HUMANOID_PRESETS: Record<string, HumanoidRagdollPreset> = {
  adult: {
    name: "Adult Human",
    scale: 170,
    proportions: {
      headSize: 20,
      torsoLength: 50,
      armLength: 60,
      legLength: 80,
      shoulderWidth: 40,
      hipWidth: 30,
    },
    massDistribution: {
      head: 5,
      torso: 40,
      upperArm: 3,
      lowerArm: 2,
      hand: 1,
      upperLeg: 10,
      lowerLeg: 5,
      foot: 2,
    },
  },
  child: {
    name: "Child",
    scale: 100,
    proportions: {
      headSize: 18,
      torsoLength: 35,
      armLength: 40,
      legLength: 50,
      shoulderWidth: 25,
      hipWidth: 20,
    },
    massDistribution: {
      head: 8,
      torso: 35,
      upperArm: 3,
      lowerArm: 2,
      hand: 1,
      upperLeg: 8,
      lowerLeg: 4,
      foot: 2,
    },
  },
  cartoon: {
    name: "Cartoon Character",
    scale: 150,
    proportions: {
      headSize: 35,
      torsoLength: 40,
      armLength: 45,
      legLength: 55,
      shoulderWidth: 35,
      hipWidth: 25,
    },
    massDistribution: {
      head: 15,
      torso: 30,
      upperArm: 4,
      lowerArm: 3,
      hand: 2,
      upperLeg: 8,
      lowerLeg: 4,
      foot: 2,
    },
  },
};

/**
 * Default physics material presets
 */
export const MATERIAL_PRESETS: Record<string, PhysicsMaterial> = {
  default: { restitution: 0.3, friction: 0.5 },
  rubber: { restitution: 0.8, friction: 0.9 },
  ice: { restitution: 0.1, friction: 0.05 },
  metal: { restitution: 0.5, friction: 0.3 },
  wood: { restitution: 0.3, friction: 0.6 },
  stone: { restitution: 0.2, friction: 0.7 },
  bouncy: { restitution: 0.95, friction: 0.3 },
  sticky: { restitution: 0.0, friction: 1.0 },
};

/**
 * Default space configuration
 */
export const DEFAULT_SPACE_CONFIG: PhysicsSpaceConfig = {
  timeStep: 1 / 60,
  velocityIterations: 8,
  positionIterations: 3,
  gravity: { x: 0, y: 980 }, // Pixels per second squared (industry standard)
  sleepEnabled: true,
  sleepTimeThreshold: 0.5,
  sleepVelocityThreshold: 10,
  collisionSlop: 0.5,
  collisionBias: 0.1,
  deterministic: true,
  seed: 12345,
};
