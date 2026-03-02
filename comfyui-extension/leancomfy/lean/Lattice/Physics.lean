/-
  Lattice.Physics - Physics system types

  Main re-export module for physics types.

  Source: ui/src/types/physics.ts (991 lines)

  Module structure (to stay under 500 lines each):
  - Enums.lean: Body/Joint/Force/Shape type enumerations
  - Core.lean: PhysicsVec2, PhysicsMaterial, RigidBody, CollisionShape
  - Joints.lean: All joint configuration types
  - Forces.lean: All force field types
  - SoftBody.lean: Verlet particles, cloth, ragdoll
  - Space.lean: PhysicsSpaceConfig, simulation state, export
-/

import Lattice.Physics.Enums
import Lattice.Physics.Core
import Lattice.Physics.Joints
import Lattice.Physics.Forces
import Lattice.Physics.SoftBody
import Lattice.Physics.Space

namespace Lattice.Physics

-- Re-export all submodules
export Enums (
  BodyType
  JointType
  ForceType
  ShapeType
  CollisionResponse
  ForceFalloff
  ConstraintTornType
)

export Core (
  PhysicsVec2
  PhysicsMaterial
  CollisionShape
  CollisionFilter
  ContactInfo
  RigidBodyConfig
  RigidBodyState
  mkPhysicsVec2
  defaultMaterial
  rubberMaterial
  iceMaterial
)

export Joints (
  JointConfigBase
  MotorSettings
  AngleLimits
  TranslationLimits
  PivotJointConfig
  SpringJointConfig
  DistanceJointConfig
  PistonJointConfig
  PistonMotorSettings
  WheelJointConfig
  WeldJointConfig
  BlobJointConfig
  RopeJointConfig
  JointConfig
)

export Forces (
  ForceFieldBase
  GravityForce
  WindForce
  AttractionForce
  ExplosionForce
  BuoyancyForce
  VortexForce
  DragForce
  ForceField
)

export SoftBody (
  VerletParticle
  VerletConstraint
  SoftBodyConfig
  SoftBodyState
  ClothConfig
  ClothState
  TornConstraint
  RagdollBone
  RagdollConfig
  RagdollBoneState
  RagdollState
)

export Space (
  PhysicsSpaceConfig
  PhysicsSimulationState
  ExportableProperty
  ExportInterpolation
  KeyframeExportOptions
  ExportedKeyframeValue
  ExportedKeyframe
  ExportedKeyframes
  BodyProportions
  MassDistribution
  HumanoidRagdollPreset
  PhysicsLayerData
  CollisionGroup
  PhysicsCompositionData
  defaultSpaceConfig
  mkDefaultSpaceConfigWithGravity
)

end Lattice.Physics
