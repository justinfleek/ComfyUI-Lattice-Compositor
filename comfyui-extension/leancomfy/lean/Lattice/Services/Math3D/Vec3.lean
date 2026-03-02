/-
  Lattice.Services.Math3D.Vec3 - 3D Vector operations

  Pure math functions for 3D vector manipulation.

  Source: ui/src/services/math3d.ts
-/

namespace Lattice.Services.Math3D.Vec3

--------------------------------------------------------------------------------
-- Vec3 Type
--------------------------------------------------------------------------------

/-- 3D Vector -/
structure Vec3 where
  x : Float
  y : Float
  z : Float
  deriving Repr, Inhabited

instance : BEq Vec3 where
  beq a b := a.x == b.x && a.y == b.y && a.z == b.z

--------------------------------------------------------------------------------
-- Constructors
--------------------------------------------------------------------------------

/-- Create a Vec3 -/
def vec3 (x y z : Float) : Vec3 := ⟨x, y, z⟩

/-- Zero vector -/
def zero : Vec3 := ⟨0.0, 0.0, 0.0⟩

/-- Unit vectors -/
def unitX : Vec3 := ⟨1.0, 0.0, 0.0⟩
def unitY : Vec3 := ⟨0.0, 1.0, 0.0⟩
def unitZ : Vec3 := ⟨0.0, 0.0, 1.0⟩

--------------------------------------------------------------------------------
-- Basic Operations
--------------------------------------------------------------------------------

/-- Vector addition -/
def add (a b : Vec3) : Vec3 :=
  ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

instance : Add Vec3 where
  add := add

/-- Vector subtraction -/
def sub (a b : Vec3) : Vec3 :=
  ⟨a.x - b.x, a.y - b.y, a.z - b.z⟩

instance : Sub Vec3 where
  sub := sub

/-- Scalar multiplication -/
def scale (v : Vec3) (s : Float) : Vec3 :=
  ⟨v.x * s, v.y * s, v.z * s⟩

instance : HMul Vec3 Float Vec3 where
  hMul := scale

/-- Negation -/
def neg (v : Vec3) : Vec3 :=
  ⟨-v.x, -v.y, -v.z⟩

instance : Neg Vec3 where
  neg := neg

--------------------------------------------------------------------------------
-- Vector Products
--------------------------------------------------------------------------------

/-- Dot product -/
def dot (a b : Vec3) : Float :=
  a.x * b.x + a.y * b.y + a.z * b.z

/-- Cross product -/
def cross (a b : Vec3) : Vec3 :=
  ⟨a.y * b.z - a.z * b.y,
   a.z * b.x - a.x * b.z,
   a.x * b.y - a.y * b.x⟩

/-- Component-wise multiplication (Hadamard product) -/
def mul (a b : Vec3) : Vec3 :=
  ⟨a.x * b.x, a.y * b.y, a.z * b.z⟩

/-- Component-wise division -/
def div (a b : Vec3) : Vec3 :=
  ⟨a.x / b.x, a.y / b.y, a.z / b.z⟩

--------------------------------------------------------------------------------
-- Length and Distance
--------------------------------------------------------------------------------

/-- Squared length (avoids sqrt) -/
def lengthSq (v : Vec3) : Float :=
  v.x * v.x + v.y * v.y + v.z * v.z

/-- Vector length -/
def length (v : Vec3) : Float :=
  Float.sqrt (lengthSq v)

/-- Squared distance between two points -/
def distanceSq (a b : Vec3) : Float :=
  lengthSq (sub a b)

/-- Distance between two points -/
def distance (a b : Vec3) : Float :=
  length (sub a b)

--------------------------------------------------------------------------------
-- Normalization
--------------------------------------------------------------------------------

/-- Result type for normalization (handles zero vector case) -/
inductive NormalizeResult where
  | success (v : Vec3)
  | zeroVector
  deriving Repr

/-- Normalize vector (returns NormalizeResult to handle zero case) -/
def normalizeSafe (v : Vec3) : NormalizeResult :=
  let len := length v
  if len == 0.0 then .zeroVector
  else .success ⟨v.x / len, v.y / len, v.z / len⟩

/-- Normalize vector (returns zero for zero vector - matches TypeScript behavior) -/
def normalize (v : Vec3) : Vec3 :=
  let len := length v
  if len == 0.0 then zero
  else ⟨v.x / len, v.y / len, v.z / len⟩

/-- Check if vector is normalized (unit length) -/
def isNormalized (v : Vec3) (tolerance : Float := 0.0001) : Bool :=
  let lenSq := lengthSq v
  Float.abs (lenSq - 1.0) < tolerance

--------------------------------------------------------------------------------
-- Interpolation
--------------------------------------------------------------------------------

/-- Linear interpolation -/
def lerp (a b : Vec3) (t : Float) : Vec3 :=
  ⟨a.x + (b.x - a.x) * t,
   a.y + (b.y - a.y) * t,
   a.z + (b.z - a.z) * t⟩

/-- Spherical linear interpolation (for normalized vectors) -/
def slerp (a b : Vec3) (t : Float) : Vec3 :=
  let d := dot a b
  -- Clamp to avoid acos domain errors
  let d' := Float.max (-1.0) (Float.min 1.0 d)
  let theta := Float.acos d'
  if Float.abs theta < 0.0001 then
    -- Vectors are nearly parallel, use lerp
    normalize (lerp a b t)
  else
    let sinTheta := Float.sin theta
    let s0 := Float.sin ((1.0 - t) * theta) / sinTheta
    let s1 := Float.sin (t * theta) / sinTheta
    ⟨a.x * s0 + b.x * s1,
     a.y * s0 + b.y * s1,
     a.z * s0 + b.z * s1⟩

--------------------------------------------------------------------------------
-- Component Operations
--------------------------------------------------------------------------------

/-- Get minimum component value -/
def minComponent (v : Vec3) : Float :=
  Float.min v.x (Float.min v.y v.z)

/-- Get maximum component value -/
def maxComponent (v : Vec3) : Float :=
  Float.max v.x (Float.max v.y v.z)

/-- Component-wise min of two vectors -/
def min (a b : Vec3) : Vec3 :=
  ⟨Float.min a.x b.x, Float.min a.y b.y, Float.min a.z b.z⟩

/-- Component-wise max of two vectors -/
def max (a b : Vec3) : Vec3 :=
  ⟨Float.max a.x b.x, Float.max a.y b.y, Float.max a.z b.z⟩

/-- Component-wise absolute value -/
def abs (v : Vec3) : Vec3 :=
  ⟨Float.abs v.x, Float.abs v.y, Float.abs v.z⟩

/-- Clamp each component to range -/
def clamp (v : Vec3) (lo hi : Vec3) : Vec3 :=
  ⟨Float.max lo.x (Float.min hi.x v.x),
   Float.max lo.y (Float.min hi.y v.y),
   Float.max lo.z (Float.min hi.z v.z)⟩

--------------------------------------------------------------------------------
-- Projection and Reflection
--------------------------------------------------------------------------------

/-- Project vector a onto vector b -/
def project (a b : Vec3) : Vec3 :=
  let bLenSq := lengthSq b
  if bLenSq == 0.0 then zero
  else scale b (dot a b / bLenSq)

/-- Reflect vector v around normal n (n should be normalized) -/
def reflect (v n : Vec3) : Vec3 :=
  sub v (scale n (2.0 * dot v n))

/-- Compute the angle between two vectors (in radians) -/
def angle (a b : Vec3) : Float :=
  let lenA := length a
  let lenB := length b
  if lenA == 0.0 || lenB == 0.0 then 0.0
  else
    let d := dot a b / (lenA * lenB)
    Float.acos (Float.max (-1.0) (Float.min 1.0 d))

--------------------------------------------------------------------------------
-- Conversion
--------------------------------------------------------------------------------

/-- Convert to array [x, y, z] -/
def toArray (v : Vec3) : Array Float :=
  #[v.x, v.y, v.z]

/-- Create from array (returns zero if array too short) -/
def fromArray (arr : Array Float) : Vec3 :=
  match arr.get? 0, arr.get? 1, arr.get? 2 with
  | some x, some y, some z => ⟨x, y, z⟩
  | _, _, _ => zero

end Lattice.Services.Math3D.Vec3
