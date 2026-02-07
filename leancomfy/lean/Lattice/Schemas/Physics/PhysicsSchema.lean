/-
  Lattice.Schemas.Physics.PhysicsSchema

  Physics simulation type enums and core types.

  Source: ui/src/schemas/physics/physics-schema.ts
-/

namespace Lattice.Schemas.Physics.PhysicsSchema

--------------------------------------------------------------------------------
-- Body Type
--------------------------------------------------------------------------------

/-- Physics body type options -/
inductive BodyType where
  | static
  | dynamic
  | kinematic
  | dormant
  | AEmatic
  | dead
  deriving Repr, DecidableEq, Inhabited

def bodyTypeFromString : String → Option BodyType
  | "static" => some .static
  | "dynamic" => some .dynamic
  | "kinematic" => some .kinematic
  | "dormant" => some .dormant
  | "AEmatic" => some .AEmatic
  | "dead" => some .dead
  | _ => none

def bodyTypeToString : BodyType → String
  | .static => "static"
  | .dynamic => "dynamic"
  | .kinematic => "kinematic"
  | .dormant => "dormant"
  | .AEmatic => "AEmatic"
  | .dead => "dead"

--------------------------------------------------------------------------------
-- Joint Type
--------------------------------------------------------------------------------

/-- Physics joint type options -/
inductive JointType where
  | pivot
  | spring
  | distance
  | piston
  | wheel
  | weld
  | blob
  | rope
  deriving Repr, DecidableEq, Inhabited

def jointTypeFromString : String → Option JointType
  | "pivot" => some .pivot
  | "spring" => some .spring
  | "distance" => some .distance
  | "piston" => some .piston
  | "wheel" => some .wheel
  | "weld" => some .weld
  | "blob" => some .blob
  | "rope" => some .rope
  | _ => none

def jointTypeToString : JointType → String
  | .pivot => "pivot"
  | .spring => "spring"
  | .distance => "distance"
  | .piston => "piston"
  | .wheel => "wheel"
  | .weld => "weld"
  | .blob => "blob"
  | .rope => "rope"

--------------------------------------------------------------------------------
-- Force Type
--------------------------------------------------------------------------------

/-- Physics force type options -/
inductive ForceType where
  | gravity
  | wind
  | attraction
  | explosion
  | buoyancy
  | vortex
  | drag
  deriving Repr, DecidableEq, Inhabited

def forceTypeFromString : String → Option ForceType
  | "gravity" => some .gravity
  | "wind" => some .wind
  | "attraction" => some .attraction
  | "explosion" => some .explosion
  | "buoyancy" => some .buoyancy
  | "vortex" => some .vortex
  | "drag" => some .drag
  | _ => none

def forceTypeToString : ForceType → String
  | .gravity => "gravity"
  | .wind => "wind"
  | .attraction => "attraction"
  | .explosion => "explosion"
  | .buoyancy => "buoyancy"
  | .vortex => "vortex"
  | .drag => "drag"

--------------------------------------------------------------------------------
-- Shape Type
--------------------------------------------------------------------------------

/-- Collision shape type options -/
inductive ShapeType where
  | circle
  | box
  | polygon
  | capsule
  | convex
  | compound
  deriving Repr, DecidableEq, Inhabited

def shapeTypeFromString : String → Option ShapeType
  | "circle" => some .circle
  | "box" => some .box
  | "polygon" => some .polygon
  | "capsule" => some .capsule
  | "convex" => some .convex
  | "compound" => some .compound
  | _ => none

def shapeTypeToString : ShapeType → String
  | .circle => "circle"
  | .box => "box"
  | .polygon => "polygon"
  | .capsule => "capsule"
  | .convex => "convex"
  | .compound => "compound"

--------------------------------------------------------------------------------
-- Collision Response
--------------------------------------------------------------------------------

/-- Collision response options -/
inductive CollisionResponse where
  | collide
  | sensor
  | none
  deriving Repr, DecidableEq, Inhabited

def collisionResponseFromString : String → Option CollisionResponse
  | "collide" => some .collide
  | "sensor" => some .sensor
  | "none" => some .none
  | _ => Option.none

def collisionResponseToString : CollisionResponse → String
  | .collide => "collide"
  | .sensor => "sensor"
  | .none => "none"

--------------------------------------------------------------------------------
-- Physics Vec2
--------------------------------------------------------------------------------

/-- 2D vector for physics -/
structure PhysicsVec2 where
  x : Float
  y : Float
  deriving Repr, Inhabited

--------------------------------------------------------------------------------
-- Physics Material
--------------------------------------------------------------------------------

/-- Physics material properties -/
structure PhysicsMaterial where
  restitution : Float  -- 0-1
  friction : Float     -- >= 0
  surfaceVelocity : Option PhysicsVec2
  deriving Repr, Inhabited

--------------------------------------------------------------------------------
-- Collision Filter
--------------------------------------------------------------------------------

/-- Collision filtering -/
structure CollisionFilter where
  category : Nat       -- Max 32 categories
  mask : Nat           -- Bitmask
  group : Int          -- 16-bit signed range
  deriving Repr, Inhabited

end Lattice.Schemas.Physics.PhysicsSchema
