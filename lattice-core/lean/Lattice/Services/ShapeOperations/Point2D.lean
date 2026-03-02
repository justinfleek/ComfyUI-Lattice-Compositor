/-
  Lattice.Services.ShapeOperations.Point2D - 2D Point/Vector Operations

  Pure 2D vector math for shape operations:
  - Point arithmetic (add, subtract, scale)
  - Vector operations (dot, cross, normalize, perpendicular)
  - Rotation operations
  - Distance calculations

  Source: ui/src/services/shapeOperations.ts (utility functions)
-/

namespace Lattice.Services.ShapeOperations.Point2D

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

/-- 2D point or vector -/
structure Point2D where
  x : Float
  y : Float
  deriving Repr, Inhabited, BEq

/-- Default point at origin -/
def origin : Point2D := ⟨0, 0⟩

--------------------------------------------------------------------------------
-- Basic Arithmetic
--------------------------------------------------------------------------------

/-- Add two points/vectors -/
def add (a b : Point2D) : Point2D :=
  ⟨a.x + b.x, a.y + b.y⟩

/-- Subtract points (a - b) -/
def sub (a b : Point2D) : Point2D :=
  ⟨a.x - b.x, a.y - b.y⟩

/-- Scale a point by a scalar -/
def scale (p : Point2D) (s : Float) : Point2D :=
  ⟨p.x * s, p.y * s⟩

/-- Negate a vector -/
def neg (p : Point2D) : Point2D :=
  ⟨-p.x, -p.y⟩

/-- Component-wise multiplication -/
def mul (a b : Point2D) : Point2D :=
  ⟨a.x * b.x, a.y * b.y⟩

/-- Component-wise division -/
def div (a b : Point2D) : Point2D :=
  let bx := if b.x == 0 then 1 else b.x
  let by := if b.y == 0 then 1 else b.y
  ⟨a.x / bx, a.y / by⟩

--------------------------------------------------------------------------------
-- Vector Operations
--------------------------------------------------------------------------------

/-- Squared length of a vector (avoids sqrt) -/
def lengthSquared (p : Point2D) : Float :=
  p.x * p.x + p.y * p.y

/-- Length/magnitude of a vector -/
def length (p : Point2D) : Float :=
  Float.sqrt (lengthSquared p)

/-- Distance between two points -/
def distance (a b : Point2D) : Float :=
  length (sub b a)

/-- Squared distance between two points (avoids sqrt) -/
def distanceSquared (a b : Point2D) : Float :=
  lengthSquared (sub b a)

/-- Normalize a vector to unit length.
    Returns zero vector if input length is too small. -/
def normalize (p : Point2D) : Point2D :=
  let len := length p
  if len < 0.0001 then origin
  else scale p (1 / len)

/-- Dot product of two vectors -/
def dot (a b : Point2D) : Float :=
  a.x * b.x + a.y * b.y

/-- Cross product (2D returns scalar z-component) -/
def cross (a b : Point2D) : Float :=
  a.x * b.y - a.y * b.x

/-- Perpendicular vector (rotate 90° counter-clockwise) -/
def perpendicular (p : Point2D) : Point2D :=
  ⟨-p.y, p.x⟩

/-- Perpendicular vector (rotate 90° clockwise) -/
def perpendicularCW (p : Point2D) : Point2D :=
  ⟨p.y, -p.x⟩

--------------------------------------------------------------------------------
-- Rotation
--------------------------------------------------------------------------------

/-- Rotate point around origin by angle (radians) -/
def rotate (p : Point2D) (angle : Float) : Point2D :=
  let c := Float.cos angle
  let s := Float.sin angle
  ⟨p.x * c - p.y * s, p.x * s + p.y * c⟩

/-- Rotate point around a center by angle (radians) -/
def rotateAround (p center : Point2D) (angle : Float) : Point2D :=
  let translated := sub p center
  let rotated := rotate translated angle
  add rotated center

--------------------------------------------------------------------------------
-- Interpolation
--------------------------------------------------------------------------------

/-- Linear interpolation between two points -/
def lerp (a b : Point2D) (t : Float) : Point2D :=
  ⟨a.x + (b.x - a.x) * t, a.y + (b.y - a.y) * t⟩

/-- Clamp t to [0, 1] then lerp -/
def lerpClamped (a b : Point2D) (t : Float) : Point2D :=
  let tc := Float.max 0 (Float.min 1 t)
  lerp a b tc

--------------------------------------------------------------------------------
-- Projection and Reflection
--------------------------------------------------------------------------------

/-- Project point a onto vector b -/
def project (a b : Point2D) : Point2D :=
  let bLenSq := lengthSquared b
  if bLenSq < 0.0001 then origin
  else scale b (dot a b / bLenSq)

/-- Reflect vector a across normal n -/
def reflect (a n : Point2D) : Point2D :=
  let nNorm := normalize n
  sub a (scale nNorm (2 * dot a nNorm))

--------------------------------------------------------------------------------
-- Angle Operations
--------------------------------------------------------------------------------

/-- Angle of vector from positive x-axis (radians) -/
def angle (p : Point2D) : Float :=
  Float.atan2 p.y p.x

/-- Angle between two vectors (radians) -/
def angleBetween (a b : Point2D) : Float :=
  let d := dot (normalize a) (normalize b)
  let clamped := Float.max (-1) (Float.min 1 d)
  Float.acos clamped

/-- Create unit vector from angle (radians) -/
def fromAngle (angle : Float) : Point2D :=
  ⟨Float.cos angle, Float.sin angle⟩

--------------------------------------------------------------------------------
-- Clone/Copy
--------------------------------------------------------------------------------

/-- Clone a point -/
def clone (p : Point2D) : Point2D :=
  ⟨p.x, p.y⟩

--------------------------------------------------------------------------------
-- Comparison
--------------------------------------------------------------------------------

/-- Check if two points are approximately equal -/
def approxEqual (a b : Point2D) (epsilon : Float := 0.0001) : Bool :=
  Float.abs (a.x - b.x) < epsilon && Float.abs (a.y - b.y) < epsilon

/-- Check if point is approximately at origin -/
def isZero (p : Point2D) (epsilon : Float := 0.0001) : Bool :=
  lengthSquared p < epsilon * epsilon

--------------------------------------------------------------------------------
-- Operator Instances
--------------------------------------------------------------------------------

instance : Add Point2D where
  add := add

instance : Sub Point2D where
  sub := sub

instance : Neg Point2D where
  neg := neg

instance : HMul Point2D Float Point2D where
  hMul := scale

instance : HMul Float Point2D Point2D where
  hMul s p := scale p s

end Lattice.Services.ShapeOperations.Point2D
