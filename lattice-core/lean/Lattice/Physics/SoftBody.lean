/-
  Lattice.Physics.SoftBody - Soft body, cloth, ragdoll types

  Part of Physics module. Max 500 lines.

  Source: ui/src/types/physics.ts (lines 479-738)
-/

import Lattice.Primitives
import Lattice.Physics.Enums
import Lattice.Physics.Core

namespace Lattice.Physics.SoftBody

open Lattice.Primitives
open Lattice.Physics.Enums
open Lattice.Physics.Core

/-! ## Verlet Particle -/

/-- Verlet particle for soft body simulation -/
structure VerletParticle where
  id : NonEmptyString
  position : PhysicsVec2
  previousPosition : PhysicsVec2
  acceleration : PhysicsVec2
  mass : Float
  pinned : Bool              -- Fixed in place
  radius : Float             -- For collision
  mass_positive : mass > 0
  mass_finite : mass.isFinite
  radius_ge_0 : radius ≥ 0
  radius_finite : radius.isFinite
  deriving Repr

/-! ## Verlet Constraint -/

/-- Distance constraint between particles -/
structure VerletConstraint where
  id : NonEmptyString
  particleA : NonEmptyString
  particleB : NonEmptyString
  restLength : Float
  stiffness : Float            -- 0-1, iterations needed for full constraint
  breakThreshold : Option Float -- Break if stretched beyond this
  restLength_ge_0 : restLength ≥ 0
  restLength_finite : restLength.isFinite
  stiffness_ge_0 : stiffness ≥ 0
  stiffness_le_1 : stiffness ≤ 1
  stiffness_finite : stiffness.isFinite
  deriving Repr

/-! ## Soft Body Config -/

/-- Soft body configuration -/
structure SoftBodyConfig where
  id : NonEmptyString
  layerId : NonEmptyString
  particles : Array VerletParticle
  constraints : Array VerletConstraint
  iterations : Nat           -- Constraint iterations per step (more = stiffer)
  pressure : Option Float    -- Pressure for closed soft bodies
  collisionScale : Float     -- Collision radius scale
  selfCollision : Bool       -- Self-collision enabled
  rigidCollision : Bool      -- Collision with rigid bodies
  material : PhysicsMaterial
  filter : CollisionFilter
  iterations_positive : iterations > 0
  collisionScale_positive : collisionScale > 0
  collisionScale_finite : collisionScale.isFinite
  deriving Repr

/-! ## Soft Body State -/

/-- Runtime soft body state -/
structure SoftBodyState where
  id : NonEmptyString
  particles : Array (NonEmptyString × PhysicsVec2 × PhysicsVec2)  -- (id, position, velocity)
  brokenConstraints : Array NonEmptyString
  deriving Repr

/-! ## Cloth Config -/

/-- Cloth simulation configuration -/
structure ClothConfig where
  id : NonEmptyString
  layerId : NonEmptyString
  width : Nat                -- Grid columns
  height : Nat               -- Grid rows
  spacing : Float            -- Spacing between particles
  origin : PhysicsVec2       -- Top-left corner position
  pinnedParticles : Array Nat -- Indices of fixed particles
  structuralStiffness : Float -- Structural constraint stiffness
  shearStiffness : Float      -- Shear constraint stiffness (diagonal)
  bendStiffness : Float       -- Bend constraint stiffness (skip one)
  iterations : Nat            -- Constraint iterations
  damping : Float             -- Damping factor
  particleMass : Float        -- Mass per particle
  collisionRadius : Float     -- Collision radius per particle
  selfCollision : Bool
  tearThreshold : Float       -- 0 = no tearing
  material : PhysicsMaterial
  filter : CollisionFilter
  width_positive : width > 0
  height_positive : height > 0
  spacing_positive : spacing > 0
  spacing_finite : spacing.isFinite
  structuralStiffness_ge_0 : structuralStiffness ≥ 0
  structuralStiffness_le_1 : structuralStiffness ≤ 1
  structuralStiffness_finite : structuralStiffness.isFinite
  shearStiffness_ge_0 : shearStiffness ≥ 0
  shearStiffness_le_1 : shearStiffness ≤ 1
  shearStiffness_finite : shearStiffness.isFinite
  bendStiffness_ge_0 : bendStiffness ≥ 0
  bendStiffness_le_1 : bendStiffness ≤ 1
  bendStiffness_finite : bendStiffness.isFinite
  iterations_positive : iterations > 0
  damping_ge_0 : damping ≥ 0
  damping_le_1 : damping ≤ 1
  damping_finite : damping.isFinite
  particleMass_positive : particleMass > 0
  particleMass_finite : particleMass.isFinite
  collisionRadius_ge_0 : collisionRadius ≥ 0
  collisionRadius_finite : collisionRadius.isFinite
  tearThreshold_ge_0 : tearThreshold ≥ 0
  tearThreshold_finite : tearThreshold.isFinite
  deriving Repr

/-! ## Torn Constraint -/

/-- Torn constraint record -/
structure TornConstraint where
  row : Nat
  col : Nat
  constraintType : ConstraintTornType
  deriving Repr

/-! ## Cloth State -/

/-- Runtime cloth state -/
structure ClothState where
  id : NonEmptyString
  positions : Array PhysicsVec2  -- Particle positions in row-major order
  tornConstraints : Array TornConstraint
  deriving Repr

/-! ## Ragdoll Bone -/

/-- Ragdoll bone definition -/
structure RagdollBone where
  id : NonEmptyString
  name : NonEmptyString
  parent : Option NonEmptyString  -- Parent bone ID (none for root)
  length : Float                  -- Bone length
  width : Float                   -- Bone width (for collision shape)
  mass : Float
  angleLimits : { min : Float // max : Float // min ≤ max }  -- Radians
  jointStiffness : Float
  jointDamping : Float
  length_positive : length > 0
  length_finite : length.isFinite
  width_positive : width > 0
  width_finite : width.isFinite
  mass_positive : mass > 0
  mass_finite : mass.isFinite
  jointStiffness_ge_0 : jointStiffness ≥ 0
  jointStiffness_finite : jointStiffness.isFinite
  jointDamping_ge_0 : jointDamping ≥ 0
  jointDamping_finite : jointDamping.isFinite
  deriving Repr

/-! ## Ragdoll Config -/

/-- Ragdoll configuration -/
structure RagdollConfig where
  id : NonEmptyString
  layerId : NonEmptyString
  position : PhysicsVec2         -- Root position
  rotation : Float               -- Root rotation
  bones : Array RagdollBone
  material : PhysicsMaterial
  filter : CollisionFilter
  selfCollision : Bool           -- Self-collision between bones
  damping : Float                -- Global damping
  rotation_finite : rotation.isFinite
  damping_ge_0 : damping ≥ 0
  damping_le_1 : damping ≤ 1
  damping_finite : damping.isFinite
  deriving Repr

/-! ## Ragdoll Bone State -/

/-- Runtime ragdoll bone state -/
structure RagdollBoneState where
  id : NonEmptyString
  position : PhysicsVec2
  angle : Float
  velocity : PhysicsVec2
  angularVelocity : Float
  angle_finite : angle.isFinite
  angularVelocity_finite : angularVelocity.isFinite
  deriving Repr

/-! ## Ragdoll State -/

/-- Runtime ragdoll state -/
structure RagdollState where
  id : NonEmptyString
  bones : Array RagdollBoneState
  deriving Repr

end Lattice.Physics.SoftBody
