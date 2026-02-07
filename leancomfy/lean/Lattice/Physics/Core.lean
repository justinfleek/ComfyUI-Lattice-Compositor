/-
  Lattice.Physics.Core - Core physics types

  Part of Physics module. Max 500 lines.

  Source: ui/src/types/physics.ts (lines 72-200)
-/

import Lattice.Primitives
import Lattice.Physics.Enums

namespace Lattice.Physics.Core

open Lattice.Primitives
open Lattice.Physics.Enums

/-! ## Physics Vec2 -/

/-- 2D vector for physics calculations -/
structure PhysicsVec2 where
  x : Float
  y : Float
  x_finite : x.isFinite
  y_finite : y.isFinite
  deriving Repr

/-! ## Physics Material -/

/-- Physics material properties -/
structure PhysicsMaterial where
  restitution : Float  -- Coefficient of restitution (bounciness) 0-1
  friction : Float     -- Friction coefficient 0-1+
  surfaceVelocity : Option PhysicsVec2
  restitution_ge_0 : restitution ≥ 0
  restitution_le_1 : restitution ≤ 1
  restitution_finite : restitution.isFinite
  friction_ge_0 : friction ≥ 0
  friction_finite : friction.isFinite
  deriving Repr

/-! ## Collision Shape -/

/-- Collision shape definition -/
structure CollisionShape where
  shapeType : ShapeType
  radius : Option Float           -- Circle, capsule
  width : Option Float            -- Box
  height : Option Float           -- Box
  vertices : Option (Array PhysicsVec2)  -- Polygon, convex
  length : Option Float           -- Capsule
  shapes : Option (Array CollisionShape) -- Compound (deferred)
  offset : Option PhysicsVec2     -- Offset from body center
  rotation : Option Float         -- Rotation offset in radians
  deriving Repr

/-! ## Collision Filter -/

/-- Collision filter for groups -/
structure CollisionFilter where
  category : Nat  -- Category bits (what this body is)
  mask : Nat      -- Mask bits (what this body collides with)
  group : Nat     -- Group index for special handling
  deriving Repr

/-! ## Contact Info -/

/-- Contact information from collision -/
structure ContactInfo where
  bodyA : NonEmptyString
  bodyB : NonEmptyString
  point : PhysicsVec2
  normal : PhysicsVec2
  depth : Float
  impulse : Float
  depth_finite : depth.isFinite
  impulse_finite : impulse.isFinite
  deriving Repr

/-! ## Rigid Body Config -/

/-- Rigid body configuration -/
structure RigidBodyConfig where
  id : NonEmptyString
  layerId : NonEmptyString
  bodyType : BodyType
  mass : Float
  moment : Option Float          -- Moment of inertia (auto-calculated if not set)
  position : PhysicsVec2
  velocity : PhysicsVec2
  angle : Float                  -- Rotation in radians
  angularVelocity : Float
  shape : CollisionShape
  material : PhysicsMaterial
  filter : CollisionFilter
  response : CollisionResponse
  linearDamping : Float          -- 0-1, velocity reduction per second
  angularDamping : Float         -- 0-1, rotation reduction per second
  fixedRotation : Bool           -- Prevent rotation
  bullet : Bool                  -- CCD for fast-moving objects
  canSleep : Bool
  sleepThreshold : Float         -- Velocity threshold for sleep
  mass_positive : mass > 0
  mass_finite : mass.isFinite
  angle_finite : angle.isFinite
  angularVelocity_finite : angularVelocity.isFinite
  linearDamping_ge_0 : linearDamping ≥ 0
  linearDamping_le_1 : linearDamping ≤ 1
  linearDamping_finite : linearDamping.isFinite
  angularDamping_ge_0 : angularDamping ≥ 0
  angularDamping_le_1 : angularDamping ≤ 1
  angularDamping_finite : angularDamping.isFinite
  sleepThreshold_ge_0 : sleepThreshold ≥ 0
  sleepThreshold_finite : sleepThreshold.isFinite
  deriving Repr

/-! ## Rigid Body State -/

/-- Runtime rigid body state -/
structure RigidBodyState where
  id : NonEmptyString
  position : PhysicsVec2
  velocity : PhysicsVec2
  angle : Float
  angularVelocity : Float
  isSleeping : Bool
  contacts : Array ContactInfo
  angle_finite : angle.isFinite
  angularVelocity_finite : angularVelocity.isFinite
  deriving Repr

/-! ## Smart Constructors -/

/-- Create zero physics vector -/
def PhysicsVec2.zero : PhysicsVec2 :=
  ⟨0, 0, by decide, by decide⟩

/-- Create physics vector -/
def mkPhysicsVec2 (x y : Float) (hx : x.isFinite) (hy : y.isFinite) : PhysicsVec2 :=
  ⟨x, y, hx, hy⟩

/-! ## Default Materials -/

/-- Default physics material -/
def defaultMaterial : PhysicsMaterial :=
  { restitution := 0.3, friction := 0.5, surfaceVelocity := none,
    restitution_ge_0 := by decide, restitution_le_1 := by decide,
    restitution_finite := by decide, friction_ge_0 := by decide,
    friction_finite := by decide }

/-- Rubber material -/
def rubberMaterial : PhysicsMaterial :=
  { restitution := 0.8, friction := 0.9, surfaceVelocity := none,
    restitution_ge_0 := by decide, restitution_le_1 := by decide,
    restitution_finite := by decide, friction_ge_0 := by decide,
    friction_finite := by decide }

/-- Ice material -/
def iceMaterial : PhysicsMaterial :=
  { restitution := 0.1, friction := 0.05, surfaceVelocity := none,
    restitution_ge_0 := by decide, restitution_le_1 := by decide,
    restitution_finite := by decide, friction_ge_0 := by decide,
    friction_finite := by decide }

end Lattice.Physics.Core
