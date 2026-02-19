/-
  Lattice.Services.Expressions.VectorMath - Vector math for expressions

  Vector operations for expression evaluation.
  Includes add, sub, mul, div, normalize, dot, cross, length, clamp.

  Source: ui/src/services/expressions/vectorMath.ts
-/

namespace Lattice.Services.Expressions.VectorMath

--------------------------------------------------------------------------------
-- Helper Functions
--------------------------------------------------------------------------------

/-- Safe finite number check -/
def isFinite (x : Float) : Bool :=
  x.isFinite

/-- Get value or default if not finite -/
def finiteOr (x : Float) (default : Float) : Float :=
  if x.isFinite then x else default

/-- Array get with default -/
def getOr (arr : Array Float) (i : Nat) (default : Float) : Float :=
  match arr.get? i with
  | some x => finiteOr x default
  | none => default

--------------------------------------------------------------------------------
-- Vector Addition
--------------------------------------------------------------------------------

/-- Vector addition: add(vec1, vec2)
    Pads shorter vector with zeros -/
def vectorAdd (a b : Array Float) : Array Float :=
  let maxLen := Nat.max a.size b.size
  Array.range maxLen |>.map fun i =>
    getOr a i 0 + getOr b i 0

--------------------------------------------------------------------------------
-- Vector Subtraction
--------------------------------------------------------------------------------

/-- Vector subtraction: sub(vec1, vec2) -/
def vectorSub (a b : Array Float) : Array Float :=
  let maxLen := Nat.max a.size b.size
  Array.range maxLen |>.map fun i =>
    getOr a i 0 - getOr b i 0

--------------------------------------------------------------------------------
-- Vector Multiplication
--------------------------------------------------------------------------------

/-- Scalar-vector multiplication -/
def scalarMulVec (s : Float) (v : Array Float) : Array Float :=
  v.map (· * s)

/-- Vector-scalar multiplication -/
def vecMulScalar (v : Array Float) (s : Float) : Array Float :=
  v.map (· * s)

/-- Component-wise vector multiplication -/
def vecMulVec (a b : Array Float) : Array Float :=
  let maxLen := Nat.max a.size b.size
  Array.range maxLen |>.map fun i =>
    getOr a i 0 * getOr b i 0

--------------------------------------------------------------------------------
-- Vector Division
--------------------------------------------------------------------------------

/-- Safe division (returns num if denom is 0) -/
def safeDiv (num denom : Float) : Float :=
  if denom == 0 then num else num / denom

/-- Scalar-vector division -/
def scalarDivVec (s : Float) (v : Array Float) : Array Float :=
  v.map fun x => safeDiv s (if x == 0 then 1 else x)

/-- Vector-scalar division -/
def vecDivScalar (v : Array Float) (s : Float) : Array Float :=
  let divisor := if s == 0 then 1 else s
  v.map (· / divisor)

/-- Component-wise vector division -/
def vecDivVec (a b : Array Float) : Array Float :=
  let maxLen := Nat.max a.size b.size
  Array.range maxLen |>.map fun i =>
    let aVal := getOr a i 0
    let bVal := getOr b i 1  -- Default to 1 to avoid division by zero
    aVal / bVal

--------------------------------------------------------------------------------
-- Vector Normalization
--------------------------------------------------------------------------------

/-- Calculate vector length/magnitude -/
def magnitude (v : Array Float) : Float :=
  let sumSq := v.foldl (fun acc x => acc + x * x) 0
  Float.sqrt sumSq

/-- Normalize vector to unit length -/
def vectorNormalize (v : Array Float) : Array Float :=
  let len := magnitude v
  if len == 0 then v.map (fun _ => 0)
  else v.map (· / len)

--------------------------------------------------------------------------------
-- Dot Product
--------------------------------------------------------------------------------

/-- Dot product of two vectors -/
def vectorDot (a b : Array Float) : Float :=
  let minLen := Nat.min a.size b.size
  let pairs := Array.range minLen |>.map fun i =>
    getOr a i 0 * getOr b i 0
  pairs.foldl (· + ·) 0

--------------------------------------------------------------------------------
-- Cross Product
--------------------------------------------------------------------------------

/-- Cross product of two 3D vectors -/
def vectorCross (a b : Array Float) : Array Float :=
  let ax := getOr a 0 0
  let ay := getOr a 1 0
  let az := getOr a 2 0
  let bx := getOr b 0 0
  let by := getOr b 1 0
  let bz := getOr b 2 0
  #[ay * bz - az * by, az * bx - ax * bz, ax * by - ay * bx]

--------------------------------------------------------------------------------
-- Vector Length / Distance
--------------------------------------------------------------------------------

/-- Vector magnitude (length of single vector) -/
def vectorMagnitude (v : Array Float) : Float :=
  magnitude v

/-- Distance between two points -/
def vectorDistance (a b : Array Float) : Float :=
  let maxLen := Nat.max a.size b.size
  let sumSq := Array.range maxLen |>.foldl (fun acc i =>
    let diff := getOr a i 0 - getOr b i 0
    acc + diff * diff) 0
  Float.sqrt sumSq

--------------------------------------------------------------------------------
-- Clamp
--------------------------------------------------------------------------------

/-- Clamp scalar value -/
def clampScalar (v minVal maxVal : Float) : Float :=
  Float.max minVal (Float.min maxVal v)

/-- Clamp vector with scalar bounds -/
def vectorClampScalar (v : Array Float) (minVal maxVal : Float) : Array Float :=
  v.map fun x => clampScalar x minVal maxVal

/-- Clamp vector with vector bounds -/
def vectorClampVec (v minBounds maxBounds : Array Float) : Array Float :=
  v.mapIdx fun i x =>
    let minVal := match minBounds.get? i with
      | some m => if m.isFinite then m else -Float.inf
      | none => -Float.inf
    let maxVal := match maxBounds.get? i with
      | some m => if m.isFinite then m else Float.inf
      | none => Float.inf
    clampScalar x minVal maxVal

--------------------------------------------------------------------------------
-- Noise
--------------------------------------------------------------------------------

/-- 1D noise (Perlin-like) -/
def noise1D (x : Float) : Float :=
  let n := Float.sin (x * 12.9898) * 43758.5453
  (n - Float.floor n) * 2 - 1

/-- Multi-dimensional noise (up to 3D) -/
def noise (v : Array Float) : Float :=
  let x := getOr v 0 0
  let y := getOr v 1 0
  let z := getOr v 2 0
  let n := Float.sin (x * 12.9898 + y * 78.233 + z * 37.719) * 43758.5453
  (n - Float.floor n) * 2 - 1

--------------------------------------------------------------------------------
-- Degree Trigonometry
--------------------------------------------------------------------------------

/-- Convert degrees to radians -/
def degToRad (deg : Float) : Float :=
  deg * Float.pi / 180

/-- Convert radians to degrees -/
def radToDeg (rad : Float) : Float :=
  rad * 180 / Float.pi

/-- Sine in degrees -/
def sinDeg (deg : Float) : Float :=
  Float.sin (degToRad deg)

/-- Cosine in degrees -/
def cosDeg (deg : Float) : Float :=
  Float.cos (degToRad deg)

/-- Tangent in degrees -/
def tanDeg (deg : Float) : Float :=
  Float.tan (degToRad deg)

/-- Arc sine returning degrees -/
def asinDeg (x : Float) : Float :=
  radToDeg (Float.asin x)

/-- Arc cosine returning degrees -/
def acosDeg (x : Float) : Float :=
  radToDeg (Float.acos x)

/-- Arc tangent returning degrees -/
def atanDeg (x : Float) : Float :=
  radToDeg (Float.atan x)

/-- Two-argument arc tangent returning degrees -/
def atan2Deg (y x : Float) : Float :=
  radToDeg (Float.atan2 y x)

end Lattice.Services.Expressions.VectorMath
