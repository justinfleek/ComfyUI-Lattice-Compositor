/-
  Lattice.Physics.Enums - Physics system enumerations

  Part of Physics module. Max 500 lines.

  Source: ui/src/types/physics.ts (lines 14-70)
-/

import Lattice.Primitives

namespace Lattice.Physics.Enums

open Lattice.Primitives

/-! ## Body Type -/

/-- Body type determines physics behavior -/
inductive BodyType where
  | static     -- Immovable, participates in collision
  | dynamic    -- Fully simulated with mass, velocity, forces
  | kinematic  -- User-controlled position, no forces, collides with dynamic
  | dormant    -- Dynamic that's asleep (optimized, wakes on collision)
  | aematic    -- Follows AE keyframes when present, dynamic otherwise
  | dead       -- Removed from simulation, no collision
  deriving Repr, BEq, DecidableEq

/-! ## Joint Type -/

/-- Joint types for connecting bodies -/
inductive JointType where
  | pivot    -- Rotation around single point (pin joint)
  | spring   -- Springy connection with stiffness/damping
  | distance -- Fixed distance constraint
  | piston   -- Slide along axis with limits
  | wheel    -- Motor-driven rotation
  | weld     -- Rigid connection (no relative movement)
  | blob     -- Soft blob-like connection
  | rope     -- One-way constraint (max distance only)
  deriving Repr, BEq, DecidableEq

/-! ## Force Type -/

/-- Force field types -/
inductive ForceType where
  | gravity    -- Directional constant force
  | wind       -- Directional force with turbulence
  | attraction -- Point attractor/repeller
  | explosion  -- Radial impulse
  | buoyancy   -- Fluid buoyancy
  | vortex     -- Rotational force
  | drag       -- Air/fluid resistance
  deriving Repr, BEq, DecidableEq

/-! ## Shape Type -/

/-- Collision shape types -/
inductive ShapeType where
  | circle
  | box
  | polygon
  | capsule
  | convex   -- Convex hull from points
  | compound -- Multiple shapes combined
  deriving Repr, BEq, DecidableEq

/-! ## Collision Response -/

/-- Collision response types -/
inductive CollisionResponse where
  | collide -- Normal collision response
  | sensor  -- Detect but don't respond
  | none    -- No collision detection
  deriving Repr, BEq, DecidableEq

/-! ## Falloff Type -/

/-- Force falloff types -/
inductive ForceFalloff where
  | linear
  | quadratic
  | constant
  deriving Repr, BEq, DecidableEq

/-! ## Constraint Type -/

/-- Constraint torn types for cloth -/
inductive ConstraintTornType where
  | structural
  | shear
  | bend
  deriving Repr, BEq, DecidableEq

end Lattice.Physics.Enums
