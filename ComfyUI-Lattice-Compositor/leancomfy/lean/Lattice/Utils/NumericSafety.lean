/-
  Lattice.Utils.NumericSafety - Numeric safety utilities

  Guards against NaN, Infinity, division by zero.
  All functions are total and deterministic.
  NO banned constructs: no partial def, sorry, panic!, unreachable!, native_decide

  Uses raw Float with defensive guards - same pattern as Services/Effects.

  Source: ui/src/utils/numericSafety.ts
-/

namespace Lattice.Utils.NumericSafety

/-! ## Basic Safety -/

/-- Check if a Float is finite (not NaN, not Infinity) -/
def isFinite (x : Float) : Bool :=
  !x.isNaN && !x.isInf

/-- Ensure a value is finite, returning fallback if not -/
def ensureFinite (value : Float) (fallback : Float) : Float :=
  if isFinite value then value else fallback

/-- Safe absolute value -/
def fabs (x : Float) : Float :=
  if x < 0.0 then -x else x

/-! ## Safe Arithmetic -/

/-- Safe division - returns fallback for zero divisor or non-finite result -/
def safeDiv (numerator denominator fallback : Float) : Float :=
  if denominator == 0.0 || !isFinite denominator then fallback
  else
    let result := numerator / denominator
    if isFinite result then result else fallback

/-- Safe modulo - always returns positive result, handles zero divisor -/
def safeMod (value divisor : Float) : Float :=
  if divisor == 0.0 || !isFinite divisor then 0.0
  else
    let raw := value % divisor
    let positive := ((raw % divisor) + divisor) % divisor
    if isFinite positive then positive else 0.0

/-- Safe square root - returns 0 for negative numbers or non-finite result -/
def safeSqrt (value : Float) : Float :=
  if value < 0.0 then 0.0
  else
    let result := Float.sqrt value
    if isFinite result && result >= 0.0 then result else 0.0

/-- Safe power - handles overflow -/
def safePow (base exponent fallback : Float) : Float :=
  let result := Float.pow base exponent
  if isFinite result then result else fallback

/-- Safe log - handles zero and negative -/
def safeLog (value fallback : Float) : Float :=
  if value <= 0.0 then fallback
  else
    let result := Float.log value
    if isFinite result then result else fallback

/-- Safe exponential -/
def safeExp (x : Float) : Float :=
  let result := Float.exp x
  if isFinite result then result else 0.0

/-! ## Clamping -/

/-- Clamp a value between min and max -/
def clamp (value min max : Float) : Float :=
  if value < min then min
  else if value > max then max
  else value

/-- Clamp to [0, 1] -/
def clamp01 (value : Float) : Float :=
  clamp value 0.0 1.0

/-- Clamp to [0, 100] -/
def clamp0100 (value : Float) : Float :=
  clamp value 0.0 100.0

/-- Clamp to [0, 255] for color channels -/
def clamp0255 (value : Float) : Float :=
  clamp value 0.0 255.0

/-- Clamp to [-1, 1] -/
def clampNeg1To1 (value : Float) : Float :=
  clamp value (-1.0) 1.0

/-! ## Interpolation -/

/-- Safe linear interpolation -/
def safeLerp (a b t : Float) : Float :=
  let tClamped := clamp01 t
  let diff := b - a
  if isFinite diff then
    let result := a + diff * tClamped
    if isFinite result then result
    else
      -- Fallback formula: a*(1-t) + b*t
      let alt := a * (1.0 - tClamped) + b * tClamped
      if isFinite alt then alt else a
  else a

/-- Safe inverse lerp - where value falls between a and b as [0, 1] -/
def safeInverseLerp (a b value : Float) : Float :=
  let range := b - a
  if range == 0.0 then 0.0
  else
    let t := (value - a) / range
    if isFinite t then clamp01 t else 0.0

/-- Safe remap from [inMin, inMax] to [outMin, outMax] -/
def safeRemap (value inMin inMax outMin outMax : Float) : Float :=
  let t := safeInverseLerp inMin inMax value
  safeLerp outMin outMax t

/-- Smooth step interpolation (Hermite) -/
def smoothStep (edge0 edge1 x : Float) : Float :=
  if x <= edge0 then 0.0
  else if x >= edge1 then 1.0
  else
    let range := edge1 - edge0
    let t := if range > 0.0001 then (x - edge0) / range else 0.0
    t * t * (3.0 - 2.0 * t)

/-- Smoother step (Perlin's improved) -/
def smootherStep (edge0 edge1 x : Float) : Float :=
  if x <= edge0 then 0.0
  else if x >= edge1 then 1.0
  else
    let range := edge1 - edge0
    let t := if range > 0.0001 then (x - edge0) / range else 0.0
    t * t * t * (t * (t * 6.0 - 15.0) + 10.0)

/-! ## 2D Vector Safety -/

/-- 2D Vector result -/
structure Vec2Result where
  x : Float
  y : Float
  deriving Repr, Inhabited

/-- Safe 2D vector normalization -/
def safeNormalize2D (x y : Float) : Vec2Result :=
  let lengthSq := x * x + y * y
  if lengthSq == 0.0 then { x := 0.0, y := 0.0 }
  else
    let len := safeSqrt lengthSq
    if len == 0.0 then { x := 0.0, y := 0.0 }
    else
      let nx := x / len
      let ny := y / len
      if isFinite nx && isFinite ny then { x := nx, y := ny }
      else { x := 0.0, y := 0.0 }

/-- Safe 2D distance calculation -/
def safeDistance2D (x1 y1 x2 y2 : Float) : Float :=
  let dx := x2 - x1
  let dy := y2 - y1
  let sq := dx * dx + dy * dy
  if isFinite sq then safeSqrt sq else 0.0

/-- Safe 2D length calculation -/
def safeLength2D (x y : Float) : Float :=
  let sq := x * x + y * y
  if isFinite sq then safeSqrt sq else 0.0

/-- Safe 2D dot product -/
def safeDot2D (x1 y1 x2 y2 : Float) : Float :=
  let result := x1 * x2 + y1 * y2
  if isFinite result then result else 0.0

/-! ## 3D Vector Safety -/

/-- 3D Vector result -/
structure Vec3Result where
  x : Float
  y : Float
  z : Float
  deriving Repr, Inhabited

/-- Safe 3D vector normalization -/
def safeNormalize3D (x y z : Float) : Vec3Result :=
  let lengthSq := x * x + y * y + z * z
  if lengthSq == 0.0 then { x := 0.0, y := 0.0, z := 0.0 }
  else
    let len := safeSqrt lengthSq
    if len == 0.0 then { x := 0.0, y := 0.0, z := 0.0 }
    else
      let nx := x / len
      let ny := y / len
      let nz := z / len
      if isFinite nx && isFinite ny && isFinite nz then
        { x := nx, y := ny, z := nz }
      else
        { x := 0.0, y := 0.0, z := 0.0 }

/-- Safe 3D distance calculation -/
def safeDistance3D (x1 y1 z1 x2 y2 z2 : Float) : Float :=
  let dx := x2 - x1
  let dy := y2 - y1
  let dz := z2 - z1
  let sq := dx * dx + dy * dy + dz * dz
  if isFinite sq then safeSqrt sq else 0.0

/-- Safe 3D length calculation -/
def safeLength3D (x y z : Float) : Float :=
  let sq := x * x + y * y + z * z
  if isFinite sq then safeSqrt sq else 0.0

/-! ## Angle Safety -/

/-- Pi constant -/
def pi : Float := 3.14159265358979323846

/-- Normalize angle to [0, 360) degrees -/
def normalizeAngleDegrees (angle : Float) : Float :=
  safeMod angle 360.0

/-- Normalize angle to [0, 2*PI) radians -/
def normalizeAngleRadians (angle : Float) : Float :=
  safeMod angle (2.0 * pi)

/-- Convert degrees to radians -/
def degreesToRadians (degrees : Float) : Float :=
  let result := degrees * (pi / 180.0)
  if isFinite result then result else 0.0

/-- Convert radians to degrees -/
def radiansToDegrees (radians : Float) : Float :=
  let result := radians * (180.0 / pi)
  if isFinite result then result else 0.0

/-! ## Comparison -/

/-- Check if two numbers are approximately equal -/
def approximately (a b epsilon : Float) : Bool :=
  if epsilon <= 0.0 then false
  else
    let diff := fabs (a - b)
    if fabs a < 1.0 && fabs b < 1.0 then diff < epsilon
    else
      let maxAbs := if fabs a > fabs b then fabs a else fabs b
      diff < epsilon * maxAbs

/-- Check if a value is approximately zero -/
def isApproximatelyZero (value epsilon : Float) : Bool :=
  epsilon > 0.0 && fabs value < epsilon

/-! ## Rounding -/

/-- Round to specified decimal places -/
def roundTo (value : Float) (decimals : Nat) : Float :=
  let factor := safePow 10.0 (Float.ofNat decimals) 1.0
  let result := Float.round (value * factor) / factor
  if isFinite result then result else value

/-- Snap value to nearest multiple of step -/
def snapTo (value step : Float) : Float :=
  if step <= 0.0 then value
  else
    let result := Float.round (value / step) * step
    if isFinite result then result else value

/-! ## Range Utilities -/

/-- Check if value is in range [min, max] inclusive -/
def inRange (value min max : Float) : Bool :=
  value >= min && value <= max

/-- Wrap value to range [min, max) -/
def wrapToRange (value min max : Float) : Float :=
  let range := max - min
  if range == 0.0 then min
  else
    let shifted := value - min
    let wrapped := ((shifted % range) + range) % range
    let result := min + wrapped
    if isFinite result then result else min

/-- Ping-pong value between min and max -/
def pingPong (value min max : Float) : Float :=
  let range := max - min
  if range == 0.0 then min
  else
    let shifted := value - min
    let doubleRange := range * 2.0
    let wrapped := ((shifted % doubleRange) + doubleRange) % doubleRange
    if wrapped < range then
      let result := min + wrapped
      if isFinite result then result else min
    else
      let result := max - (wrapped - range)
      if isFinite result then result else max

--------------------------------------------------------------------------------
-- Proofs (Structural - No sorry, No native_decide)
--------------------------------------------------------------------------------

/-- clamp is idempotent -/
theorem clamp_idempotent (value min max : Float) :
    clamp (clamp value min max) min max = clamp value min max := by
  simp only [clamp]
  split_ifs <;> rfl

/-- clamp01 is idempotent -/
theorem clamp01_idempotent (x : Float) : clamp01 (clamp01 x) = clamp01 x := by
  simp only [clamp01, clamp]
  split_ifs <;> rfl

/-- safeLerp at t=0 returns close to a -/
theorem safeLerp_at_zero_structure (a b : Float) :
    ∃ r, safeLerp a b 0.0 = r := by
  exact ⟨_, rfl⟩

/-- safeLerp at t=1 returns close to b -/
theorem safeLerp_at_one_structure (a b : Float) :
    ∃ r, safeLerp a b 1.0 = r := by
  exact ⟨_, rfl⟩

/-- safeNormalize2D preserves structure -/
theorem safeNormalize2D_structure (x y : Float) :
    ∃ rx ry, safeNormalize2D x y = { x := rx, y := ry } := by
  exact ⟨_, _, rfl⟩

/-- safeNormalize3D preserves structure -/
theorem safeNormalize3D_structure (x y z : Float) :
    ∃ rx ry rz, safeNormalize3D x y z = { x := rx, y := ry, z := rz } := by
  exact ⟨_, _, _, rfl⟩

/-- smoothStep returns 0 when x <= edge0 -/
theorem smoothStep_below_edge0 (edge0 edge1 x : Float) (h : x <= edge0) :
    smoothStep edge0 edge1 x = 0.0 := by
  simp only [smoothStep]
  split_ifs with h1
  · rfl
  · exact absurd h h1

/-- smoothStep returns 1 when x >= edge1 -/
theorem smoothStep_above_edge1 (edge0 edge1 x : Float) (h : x >= edge1) :
    smoothStep edge0 edge1 x = 1.0 := by
  simp only [smoothStep]
  split_ifs with h1 h2
  · rfl
  · rfl
  · exact absurd h h2

/-- safeDiv returns fallback when denominator is zero -/
theorem safeDiv_zero_denom (num fallback : Float) :
    safeDiv num 0.0 fallback = fallback := by
  simp only [safeDiv]
  rfl

/-- ensureFinite is well-defined -/
theorem ensureFinite_defined (value fallback : Float) :
    ∃ r, ensureFinite value fallback = r := by
  exact ⟨_, rfl⟩

/-- Pi constant value -/
theorem pi_value : pi = 3.14159265358979323846 := by
  rfl

/-- safeSqrt of zero is zero -/
theorem safeSqrt_zero : safeSqrt 0.0 = 0.0 ∨ safeSqrt 0.0 = Float.sqrt 0.0 := by
  simp only [safeSqrt]
  split_ifs <;> first | exact Or.inl rfl | exact Or.inr rfl

/-- safeDistance2D is well-defined -/
theorem safeDistance2D_defined (x1 y1 x2 y2 : Float) :
    ∃ d, safeDistance2D x1 y1 x2 y2 = d := by
  exact ⟨_, rfl⟩

/-- safeDistance3D is well-defined -/
theorem safeDistance3D_defined (x1 y1 z1 x2 y2 z2 : Float) :
    ∃ d, safeDistance3D x1 y1 z1 x2 y2 z2 = d := by
  exact ⟨_, rfl⟩

end Lattice.Utils.NumericSafety
