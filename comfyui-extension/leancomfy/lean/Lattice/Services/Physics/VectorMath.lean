/-
  Lattice.Services.Physics.VectorMath - 2D Vector Math Operations

  Pure mathematical functions for 2D vector operations used in physics
  simulation. All operations are deterministic and side-effect free.

  Operations:
  - Basic: add, sub, scale, negate
  - Products: dot, cross (2D pseudo-cross)
  - Metrics: length, lengthSq, distance, distanceSq
  - Normalization and rotation
  - Interpolation: lerp

  Source: ui/src/services/physics/PhysicsEngine.ts
-/

namespace Lattice.Services.Physics.VectorMath

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

/-- 2D Vector for physics calculations -/
structure Vec2 where
  x : Float
  y : Float
  deriving Repr, Inhabited, BEq

--------------------------------------------------------------------------------
-- Constructors
--------------------------------------------------------------------------------

/-- Create a zero vector -/
def zero : Vec2 := { x := 0.0, y := 0.0 }

/-- Create a vector from components -/
def create (x y : Float) : Vec2 := { x := x, y := y }

/-- Clone a vector (identity, for API compatibility) -/
def clone (v : Vec2) : Vec2 := { x := v.x, y := v.y }

--------------------------------------------------------------------------------
-- Basic Operations
--------------------------------------------------------------------------------

/-- Vector addition -/
def add (a b : Vec2) : Vec2 :=
  { x := a.x + b.x, y := a.y + b.y }

/-- Vector subtraction -/
def sub (a b : Vec2) : Vec2 :=
  { x := a.x - b.x, y := a.y - b.y }

/-- Scalar multiplication -/
def scale (v : Vec2) (s : Float) : Vec2 :=
  { x := v.x * s, y := v.y * s }

/-- Vector negation -/
def negate (v : Vec2) : Vec2 :=
  { x := -v.x, y := -v.y }

--------------------------------------------------------------------------------
-- Products
--------------------------------------------------------------------------------

/-- Dot product of two vectors -/
def dot (a b : Vec2) : Float :=
  a.x * b.x + a.y * b.y

/-- 2D cross product (pseudo-cross, returns scalar).
    This is the Z component of the 3D cross product with z=0.
    Geometrically: |a| * |b| * sin(angle from a to b) -/
def cross (a b : Vec2) : Float :=
  a.x * b.y - a.y * b.x

--------------------------------------------------------------------------------
-- Metrics
--------------------------------------------------------------------------------

/-- Squared length of a vector (avoids sqrt) -/
def lengthSq (v : Vec2) : Float :=
  v.x * v.x + v.y * v.y

/-- Length (magnitude) of a vector -/
def length (v : Vec2) : Float :=
  Float.sqrt (lengthSq v)

/-- Squared distance between two points (avoids sqrt) -/
def distanceSq (a b : Vec2) : Float :=
  lengthSq (sub b a)

/-- Distance between two points -/
def distance (a b : Vec2) : Float :=
  length (sub b a)

--------------------------------------------------------------------------------
-- Normalization
--------------------------------------------------------------------------------

/-- Normalize a vector to unit length.
    Returns zero vector if input has zero length. -/
def normalize (v : Vec2) : Vec2 :=
  let len := length v
  if len < 0.0001 then
    zero
  else
    { x := v.x / len, y := v.y / len }

--------------------------------------------------------------------------------
-- Perpendicular and Rotation
--------------------------------------------------------------------------------

/-- Get perpendicular vector (90 degrees counter-clockwise).
    For (x, y), returns (-y, x). -/
def perpendicular (v : Vec2) : Vec2 :=
  { x := -v.y, y := v.x }

/-- Rotate vector by angle (in radians).

    Uses rotation matrix:
    [cos θ  -sin θ] [x]
    [sin θ   cos θ] [y]
-/
def rotate (v : Vec2) (angle : Float) : Vec2 :=
  let c := Float.cos angle
  let s := Float.sin angle
  { x := v.x * c - v.y * s
  , y := v.x * s + v.y * c }

--------------------------------------------------------------------------------
-- Interpolation
--------------------------------------------------------------------------------

/-- Linear interpolation between two vectors.

    @param a Start vector (t=0)
    @param b End vector (t=1)
    @param t Interpolation parameter (0 to 1)
    @return Interpolated vector: a + (b - a) * t -/
def lerp (a b : Vec2) (t : Float) : Vec2 :=
  { x := a.x + (b.x - a.x) * t
  , y := a.y + (b.y - a.y) * t }

--------------------------------------------------------------------------------
-- Projection
--------------------------------------------------------------------------------

/-- Project vector a onto vector b.

    @return Component of a in the direction of b -/
def project (a b : Vec2) : Vec2 :=
  let bLenSq := lengthSq b
  if bLenSq < 0.0001 then
    zero
  else
    let scalar := dot a b / bLenSq
    scale b scalar

/-- Reflect vector v off a surface with normal n.

    @param v Incoming vector
    @param n Surface normal (should be normalized)
    @return Reflected vector -/
def reflect (v n : Vec2) : Vec2 :=
  let dotVN := dot v n
  sub v (scale n (2.0 * dotVN))

--------------------------------------------------------------------------------
-- Angle Operations
--------------------------------------------------------------------------------

/-- Get angle of vector from positive x-axis (in radians).
    Returns 0 for zero vector. -/
def angle (v : Vec2) : Float :=
  Float.atan2 v.y v.x

/-- Get angle between two vectors (in radians).
    Returns 0 if either vector has zero length. -/
def angleBetween (a b : Vec2) : Float :=
  let lenA := length a
  let lenB := length b
  if lenA < 0.0001 || lenB < 0.0001 then
    0.0
  else
    let cosAngle := dot a b / (lenA * lenB)
    -- Clamp to [-1, 1] to handle floating point errors
    let clamped := Float.max (-1.0) (Float.min 1.0 cosAngle)
    Float.acos clamped

end Lattice.Services.Physics.VectorMath
