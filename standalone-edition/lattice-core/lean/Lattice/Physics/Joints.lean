/-
  Lattice.Physics.Joints - Joint types for physics

  Part of Physics module. Max 500 lines.

  Source: ui/src/types/physics.ts (lines 204-350)
-/

import Lattice.Primitives
import Lattice.Physics.Enums
import Lattice.Physics.Core

namespace Lattice.Physics.Joints

open Lattice.Primitives
open Lattice.Physics.Enums
open Lattice.Physics.Core

/-! ## Base Joint Config -/

/-- Base joint configuration fields -/
structure JointConfigBase where
  id : NonEmptyString
  jointType : JointType
  bodyA : NonEmptyString        -- Body ID
  bodyB : NonEmptyString        -- Body ID (or 'world' for ground)
  anchorA : PhysicsVec2         -- Local anchor on body A
  anchorB : PhysicsVec2         -- Local anchor on body B
  collideConnected : Bool       -- Collision between connected bodies
  maxForce : Option Float       -- Breaking force (0 = unbreakable)
  deriving Repr

/-! ## Motor Settings -/

/-- Motor settings for joints -/
structure MotorSettings where
  enabled : Bool
  targetAngle : Option Float    -- Target angle for servo mode
  speed : Float                 -- Angular velocity
  maxTorque : Float
  speed_finite : speed.isFinite
  maxTorque_ge_0 : maxTorque ≥ 0
  maxTorque_finite : maxTorque.isFinite
  deriving Repr

/-! ## Angle Limits -/

/-- Angle limits for joints -/
structure AngleLimits where
  min : Float  -- Radians
  max : Float  -- Radians
  min_finite : min.isFinite
  max_finite : max.isFinite
  min_le_max : min ≤ max
  deriving Repr

/-! ## Translation Limits -/

/-- Translation limits for piston joints -/
structure TranslationLimits where
  min : Float
  max : Float
  min_finite : min.isFinite
  max_finite : max.isFinite
  min_le_max : min ≤ max
  deriving Repr

/-! ## Pivot Joint -/

/-- Pivot joint - rotation around single point -/
structure PivotJointConfig extends JointConfigBase where
  motor : Option MotorSettings
  limits : Option AngleLimits
  deriving Repr

/-! ## Spring Joint -/

/-- Spring joint - springy connection -/
structure SpringJointConfig extends JointConfigBase where
  restLength : Float      -- Rest length of spring
  stiffness : Float       -- Spring stiffness (N/m)
  damping : Float         -- Damping coefficient
  restLength_ge_0 : restLength ≥ 0
  restLength_finite : restLength.isFinite
  stiffness_ge_0 : stiffness ≥ 0
  stiffness_finite : stiffness.isFinite
  damping_ge_0 : damping ≥ 0
  damping_finite : damping.isFinite
  deriving Repr

/-! ## Distance Joint -/

/-- Distance joint - fixed distance constraint -/
structure DistanceJointConfig extends JointConfigBase where
  distance : Float  -- Fixed distance between anchors
  distance_ge_0 : distance ≥ 0
  distance_finite : distance.isFinite
  deriving Repr

/-! ## Piston Joint -/

/-- Piston motor settings -/
structure PistonMotorSettings where
  enabled : Bool
  speed : Float
  maxForce : Float
  speed_finite : speed.isFinite
  maxForce_ge_0 : maxForce ≥ 0
  maxForce_finite : maxForce.isFinite
  deriving Repr

/-- Piston joint - slide along axis -/
structure PistonJointConfig extends JointConfigBase where
  axis : PhysicsVec2         -- Slide axis (local to bodyA)
  limits : Option TranslationLimits
  motor : Option PistonMotorSettings
  deriving Repr

/-! ## Wheel Joint -/

/-- Wheel joint - motor-driven rotation -/
structure WheelJointConfig extends JointConfigBase where
  axis : PhysicsVec2         -- Suspension axis
  frequency : Float          -- Suspension frequency (Hz)
  dampingRatio : Float       -- Suspension damping ratio
  motor : Option MotorSettings
  frequency_positive : frequency > 0
  frequency_finite : frequency.isFinite
  dampingRatio_ge_0 : dampingRatio ≥ 0
  dampingRatio_finite : dampingRatio.isFinite
  deriving Repr

/-! ## Weld Joint -/

/-- Weld joint - rigid connection -/
structure WeldJointConfig extends JointConfigBase where
  referenceAngle : Float     -- Reference angle between bodies
  frequency : Option Float   -- Softness (0 = rigid, higher = softer)
  dampingRatio : Option Float
  referenceAngle_finite : referenceAngle.isFinite
  deriving Repr

/-! ## Blob Joint -/

/-- Blob joint - soft connection for deformable shapes -/
structure BlobJointConfig extends JointConfigBase where
  softness : Float  -- Softness factor
  pressure : Float  -- Pressure (for internal volume)
  softness_ge_0 : softness ≥ 0
  softness_finite : softness.isFinite
  pressure_finite : pressure.isFinite
  deriving Repr

/-! ## Rope Joint -/

/-- Rope joint - maximum distance constraint -/
structure RopeJointConfig extends JointConfigBase where
  maxLength : Float  -- Maximum length
  maxLength_positive : maxLength > 0
  maxLength_finite : maxLength.isFinite
  deriving Repr

/-! ## Joint Config Sum Type -/

/-- All joint configuration types -/
inductive JointConfig where
  | pivot : PivotJointConfig → JointConfig
  | spring : SpringJointConfig → JointConfig
  | distance : DistanceJointConfig → JointConfig
  | piston : PistonJointConfig → JointConfig
  | wheel : WheelJointConfig → JointConfig
  | weld : WeldJointConfig → JointConfig
  | blob : BlobJointConfig → JointConfig
  | rope : RopeJointConfig → JointConfig
  deriving Repr

/-! ## Joint Helpers -/

/-- Get joint ID from config -/
def JointConfig.id : JointConfig → NonEmptyString
  | pivot j => j.id
  | spring j => j.id
  | distance j => j.id
  | piston j => j.id
  | wheel j => j.id
  | weld j => j.id
  | blob j => j.id
  | rope j => j.id

/-- Get joint type from config -/
def JointConfig.jointType : JointConfig → JointType
  | pivot _ => JointType.pivot
  | spring _ => JointType.spring
  | distance _ => JointType.distance
  | piston _ => JointType.piston
  | wheel _ => JointType.wheel
  | weld _ => JointType.weld
  | blob _ => JointType.blob
  | rope _ => JointType.rope

end Lattice.Physics.Joints
