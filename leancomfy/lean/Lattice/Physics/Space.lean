/-
  Lattice.Physics.Space - Physics space and simulation types

  Part of Physics module. Max 500 lines.

  Source: ui/src/types/physics.ts (lines 739-991)
-/

import Lattice.Primitives
import Lattice.Physics.Enums
import Lattice.Physics.Core
import Lattice.Physics.Forces
import Lattice.Physics.SoftBody

namespace Lattice.Physics.Space

open Lattice.Primitives
open Lattice.Physics.Enums
open Lattice.Physics.Core
open Lattice.Physics.Forces
open Lattice.Physics.SoftBody

/-! ## Physics Space Config -/

/-- Physics space configuration -/
structure PhysicsSpaceConfig where
  timeStep : Float                  -- Simulation time step (seconds)
  velocityIterations : Nat          -- Velocity iterations for constraint solver
  positionIterations : Nat          -- Position iterations for constraint solver
  gravity : PhysicsVec2             -- Global gravity
  sleepEnabled : Bool               -- Sleep enabled
  sleepTimeThreshold : Float        -- Sleep time threshold (seconds)
  sleepVelocityThreshold : Float    -- Sleep velocity threshold
  collisionSlop : Float             -- Collision slop (penetration allowance)
  collisionBias : Float             -- Collision bias (position correction)
  deterministic : Bool              -- Deterministic mode (fixed timestep)
  seed : Nat                        -- Random seed for determinism
  timeStep_positive : timeStep > 0
  timeStep_finite : timeStep.isFinite
  velocityIterations_positive : velocityIterations > 0
  positionIterations_positive : positionIterations > 0
  sleepTimeThreshold_ge_0 : sleepTimeThreshold ≥ 0
  sleepTimeThreshold_finite : sleepTimeThreshold.isFinite
  sleepVelocityThreshold_ge_0 : sleepVelocityThreshold ≥ 0
  sleepVelocityThreshold_finite : sleepVelocityThreshold.isFinite
  collisionSlop_ge_0 : collisionSlop ≥ 0
  collisionSlop_finite : collisionSlop.isFinite
  collisionBias_ge_0 : collisionBias ≥ 0
  collisionBias_le_1 : collisionBias ≤ 1
  collisionBias_finite : collisionBias.isFinite
  deriving Repr

/-! ## Physics Simulation State -/

/-- Complete physics simulation state -/
structure PhysicsSimulationState where
  frame : FrameNumber
  rigidBodies : Array RigidBodyState
  softBodies : Array SoftBodyState
  cloths : Array ClothState
  ragdolls : Array RagdollState
  contacts : Array ContactInfo
  deriving Repr

/-! ## Keyframe Export -/

/-- Exportable property types -/
inductive ExportableProperty where
  | position
  | rotation
  | scale
  deriving Repr, BEq, DecidableEq

/-- Export interpolation type -/
inductive ExportInterpolation where
  | linear
  | bezier
  deriving Repr, BEq, DecidableEq

/-- Keyframe export options -/
structure KeyframeExportOptions where
  startFrame : FrameNumber
  endFrame : FrameNumber
  frameStep : Nat                           -- 1 = every frame
  properties : Array ExportableProperty
  simplify : Bool                           -- Simplify keyframes (remove redundant)
  simplifyTolerance : Float                 -- Simplification tolerance
  interpolation : ExportInterpolation
  frameStep_positive : frameStep > 0
  simplifyTolerance_ge_0 : simplifyTolerance ≥ 0
  simplifyTolerance_finite : simplifyTolerance.isFinite
  deriving Repr

/-- Exported keyframe value -/
inductive ExportedKeyframeValue where
  | scalar : Float → ExportedKeyframeValue
  | vec2 : PhysicsVec2 → ExportedKeyframeValue
  deriving Repr

/-- Single exported keyframe -/
structure ExportedKeyframe where
  frame : FrameNumber
  value : ExportedKeyframeValue
  interpolation : ExportInterpolation
  inHandle : Option PhysicsVec2
  outHandle : Option PhysicsVec2
  deriving Repr

/-- Exported keyframes for a property -/
structure ExportedKeyframes where
  layerId : NonEmptyString
  property : NonEmptyString
  keyframes : Array ExportedKeyframe
  deriving Repr

/-! ## Humanoid Ragdoll Preset -/

/-- Body proportions for ragdoll preset -/
structure BodyProportions where
  headSize : Float
  torsoLength : Float
  armLength : Float
  legLength : Float
  shoulderWidth : Float
  hipWidth : Float
  headSize_positive : headSize > 0
  headSize_finite : headSize.isFinite
  torsoLength_positive : torsoLength > 0
  torsoLength_finite : torsoLength.isFinite
  armLength_positive : armLength > 0
  armLength_finite : armLength.isFinite
  legLength_positive : legLength > 0
  legLength_finite : legLength.isFinite
  shoulderWidth_positive : shoulderWidth > 0
  shoulderWidth_finite : shoulderWidth.isFinite
  hipWidth_positive : hipWidth > 0
  hipWidth_finite : hipWidth.isFinite
  deriving Repr

/-- Mass distribution for ragdoll preset -/
structure MassDistribution where
  head : Float
  torso : Float
  upperArm : Float
  lowerArm : Float
  hand : Float
  upperLeg : Float
  lowerLeg : Float
  foot : Float
  head_positive : head > 0
  head_finite : head.isFinite
  torso_positive : torso > 0
  torso_finite : torso.isFinite
  upperArm_positive : upperArm > 0
  upperArm_finite : upperArm.isFinite
  lowerArm_positive : lowerArm > 0
  lowerArm_finite : lowerArm.isFinite
  hand_positive : hand > 0
  hand_finite : hand.isFinite
  upperLeg_positive : upperLeg > 0
  upperLeg_finite : upperLeg.isFinite
  lowerLeg_positive : lowerLeg > 0
  lowerLeg_finite : lowerLeg.isFinite
  foot_positive : foot > 0
  foot_finite : foot.isFinite
  deriving Repr

/-- Humanoid ragdoll preset configuration -/
structure HumanoidRagdollPreset where
  name : NonEmptyString
  scale : Float                    -- Overall scale
  proportions : BodyProportions
  massDistribution : MassDistribution
  scale_positive : scale > 0
  scale_finite : scale.isFinite
  deriving Repr

/-! ## Layer Integration -/

/-- Physics layer data -/
structure PhysicsLayerData where
  physicsEnabled : Bool
  rigidBody : Option RigidBodyConfig
  softBody : Option SoftBodyConfig
  cloth : Option ClothConfig
  ragdoll : Option RagdollConfig
  spaceConfigOverride : Option PhysicsSpaceConfig  -- Uses global if not set
  deriving Repr

/-! ## Collision Group -/

/-- Collision group definition -/
structure CollisionGroup where
  name : NonEmptyString
  category : Nat
  collidesWithSelf : Bool
  deriving Repr

/-! ## Physics Composition Data -/

/-- Physics composition data -/
structure PhysicsCompositionData where
  enabled : Bool
  spaceConfig : PhysicsSpaceConfig
  forceFields : Array ForceField
  collisionGroups : Array CollisionGroup
  cached : Bool                    -- Simulation cache for scrubbing
  cacheStartFrame : FrameNumber
  cacheEndFrame : FrameNumber
  deriving Repr

/-! ## Default Values -/

/-- Default space configuration -/
def defaultSpaceConfig : PhysicsSpaceConfig :=
  { timeStep := 1.0 / 60.0
  , velocityIterations := 8
  , positionIterations := 3
  , gravity := PhysicsVec2.zero  -- Will set proper gravity below
  , sleepEnabled := true
  , sleepTimeThreshold := 0.5
  , sleepVelocityThreshold := 10.0
  , collisionSlop := 0.5
  , collisionBias := 0.1
  , deterministic := true
  , seed := 12345
  , timeStep_positive := by decide
  , timeStep_finite := by decide
  , velocityIterations_positive := by decide
  , positionIterations_positive := by decide
  , sleepTimeThreshold_ge_0 := by decide
  , sleepTimeThreshold_finite := by decide
  , sleepVelocityThreshold_ge_0 := by decide
  , sleepVelocityThreshold_finite := by decide
  , collisionSlop_ge_0 := by decide
  , collisionSlop_finite := by decide
  , collisionBias_ge_0 := by decide
  , collisionBias_le_1 := by decide
  , collisionBias_finite := by decide
  }

/-- Create physics space config with standard gravity (980 px/s²) -/
def mkDefaultSpaceConfigWithGravity (gravityY : Float) (h : gravityY.isFinite) : PhysicsSpaceConfig :=
  { defaultSpaceConfig with
    gravity := ⟨0, gravityY, by decide, h⟩
  }

end Lattice.Physics.Space
