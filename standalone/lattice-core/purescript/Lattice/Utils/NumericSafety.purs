-- | Lattice.Utils.NumericSafety - Numeric safety with total functions
-- |
-- | Guards against NaN, Infinity, division by zero.
-- | All functions are total and safe.
-- |
-- | Source: lattice-core/lean/Lattice/Utils/NumericSafety.lean

module Lattice.Utils.NumericSafety
  ( ensureFinite
  , requireFinite
  , safeDivide
  , safeMod
  , safeSqrt
  , safePow
  , safeLog
  , clamp
  , clamp01
  , clamp0100
  , clamp0255
  , clampNeg1To1
  , safeLerp
  , safeInverseLerp
  , safeRemap
  , smoothStep
  , smootherStep
  , safeNormalize2D
  , safeDistance2D
  , safeLength2D
  , safeDot2D
  , safeNormalize3D
  , safeDistance3D
  , safeLength3D
  , normalizeAngleDegrees
  , normalizeAngleRadians
  , degreesToRadians
  , radiansToDegrees
  , approximately
  , isApproximatelyZero
  , roundTo
  , snapTo
  , inRange
  , wrapToRange
  , pingPong
  ) where

import Prelude
import Data.Int (floor, round, toNumber)
import Data.Number (isFinite, isNaN, nan, pow, sqrt, log, pi, abs) as Number
import Lattice.Primitives (FiniteFloat(..), mkFiniteFloat, unFiniteFloat, UnitFloat(..), mkUnitFloat, unUnitFloat, NonNegativeFloat(..), mkNonNegativeFloat, unNonNegativeFloat, PositiveFloat(..), unPositiveFloat, Vec2, Vec3)

--------------------------------------------------------------------------------
-- Basic Safety
--------------------------------------------------------------------------------

-- | Check if a Number is finite (not NaN or Infinity)
isFiniteNumber :: Number -> Boolean
isFiniteNumber x = Number.isFinite x && not (Number.isNaN x)

-- | Ensure a value is finite, returning fallback if not
ensureFinite :: Number -> FiniteFloat -> FiniteFloat
ensureFinite value fallback =
  if isFiniteNumber value then FiniteFloat value
  else fallback

-- | Require a value to be finite (caller guarantees)
requireFinite :: Number -> FiniteFloat
requireFinite value =
  if isFiniteNumber value then FiniteFloat value
  else FiniteFloat 0.0

--------------------------------------------------------------------------------
-- Safe Arithmetic
--------------------------------------------------------------------------------

-- | Safe division - returns fallback for zero divisor or infinite result
safeDivide :: FiniteFloat -> FiniteFloat -> FiniteFloat -> FiniteFloat
safeDivide (FiniteFloat n) (FiniteFloat d) fallback =
  let result = n / d
  in if d == 0.0 then fallback
     else if isFiniteNumber result then FiniteFloat result
     else fallback

-- | Safe modulo - always returns non-negative result, handles zero divisor
safeMod :: FiniteFloat -> FiniteFloat -> FiniteFloat
safeMod value (FiniteFloat d) =
  if d == 0.0 then FiniteFloat 0.0
  else
    let raw = modFloat' (unFiniteFloat value) d
        positive = modFloat' (modFloat' raw d + d) d
    in if isFiniteNumber positive then FiniteFloat positive
       else FiniteFloat 0.0

-- | Helper for float modulo (operates on raw Numbers)
modFloat' :: Number -> Number -> Number
modFloat' a b = a - b * toNumber (floor (a / b))

-- | Safe square root - returns 0 for negative numbers
safeSqrt :: FiniteFloat -> NonNegativeFloat
safeSqrt (FiniteFloat v) =
  let result = Number.sqrt v
  in if v < 0.0 then NonNegativeFloat 0.0
     else if isFiniteNumber result && result >= 0.0 then NonNegativeFloat result
     else NonNegativeFloat 0.0

-- | Safe power - handles overflow
safePow :: FiniteFloat -> FiniteFloat -> FiniteFloat -> FiniteFloat
safePow (FiniteFloat b) (FiniteFloat e) fallback =
  let result = Number.pow b e
  in if isFiniteNumber result then FiniteFloat result
     else fallback

-- | Safe log - handles zero and negative
safeLog :: FiniteFloat -> FiniteFloat -> FiniteFloat
safeLog (FiniteFloat v) fallback =
  let result = Number.log v
  in if v <= 0.0 then fallback
     else if isFiniteNumber result then FiniteFloat result
     else fallback

--------------------------------------------------------------------------------
-- Clamping
--------------------------------------------------------------------------------

-- | Clamp a value between min and max
clamp :: FiniteFloat -> FiniteFloat -> FiniteFloat -> FiniteFloat
clamp value minVal maxVal =
  if value < minVal then minVal
  else if value > maxVal then maxVal
  else value

-- | Clamp to [0, 1] - returns UnitFloat
clamp01 :: FiniteFloat -> UnitFloat
clamp01 (FiniteFloat v) = UnitFloat (max 0.0 (min 1.0 v))

-- | Clamp to [0, 100]
clamp0100 :: FiniteFloat -> FiniteFloat
clamp0100 value = clamp value (FiniteFloat 0.0) (FiniteFloat 100.0)

-- | Clamp to [0, 255] for color channels
clamp0255 :: FiniteFloat -> FiniteFloat
clamp0255 value = clamp value (FiniteFloat 0.0) (FiniteFloat 255.0)

-- | Clamp to [-1, 1]
clampNeg1To1 :: FiniteFloat -> FiniteFloat
clampNeg1To1 value = clamp value (FiniteFloat (0.0 - 1.0)) (FiniteFloat 1.0)

--------------------------------------------------------------------------------
-- Interpolation
--------------------------------------------------------------------------------

-- | Safe linear interpolation with clamped t
safeLerp :: FiniteFloat -> FiniteFloat -> UnitFloat -> FiniteFloat
safeLerp (FiniteFloat a) (FiniteFloat b) (UnitFloat t) =
  let diff = b - a
      result = a + diff * t
      alt = a * (1.0 - t) + b * t
  in if isFiniteNumber result then FiniteFloat result
     else if isFiniteNumber alt then FiniteFloat alt
     else FiniteFloat a

-- | Safe inverse lerp - where value falls between a and b as [0, 1]
safeInverseLerp :: FiniteFloat -> FiniteFloat -> FiniteFloat -> UnitFloat
safeInverseLerp (FiniteFloat a) (FiniteFloat b) (FiniteFloat v) =
  let range' = b - a
      t = (v - a) / range'
  in if range' == 0.0 then UnitFloat 0.0
     else UnitFloat (max 0.0 (min 1.0 t))

-- | Safe remap from [inMin, inMax] to [outMin, outMax]
safeRemap :: FiniteFloat -> FiniteFloat -> FiniteFloat -> FiniteFloat -> FiniteFloat -> FiniteFloat
safeRemap value inMin inMax outMin outMax =
  let t = safeInverseLerp inMin inMax value
  in safeLerp outMin outMax t

-- | Smooth step interpolation (Hermite)
smoothStep :: FiniteFloat -> FiniteFloat -> UnitFloat -> FiniteFloat
smoothStep a b (UnitFloat t) =
  let smooth = UnitFloat (t * t * (3.0 - 2.0 * t))
  in safeLerp a b smooth

-- | Smoother step (Perlin's improved)
smootherStep :: FiniteFloat -> FiniteFloat -> UnitFloat -> FiniteFloat
smootherStep a b (UnitFloat t) =
  let smooth = UnitFloat (t * t * t * (t * (t * 6.0 - 15.0) + 10.0))
  in safeLerp a b smooth

--------------------------------------------------------------------------------
-- 2D Vector Safety
--------------------------------------------------------------------------------

-- | Safe 2D vector normalization
safeNormalize2D :: FiniteFloat -> FiniteFloat -> Vec2
safeNormalize2D (FiniteFloat x) (FiniteFloat y) =
  let zero = { x: FiniteFloat 0.0, y: FiniteFloat 0.0 }
      lengthSq = x * x + y * y
      len = Number.sqrt lengthSq
      nx = x / len
      ny = y / len
  in if lengthSq == 0.0 then zero
     else if len == 0.0 then zero
     else if isFiniteNumber nx && isFiniteNumber ny then { x: FiniteFloat nx, y: FiniteFloat ny }
     else zero

-- | Safe 2D distance calculation
safeDistance2D :: FiniteFloat -> FiniteFloat -> FiniteFloat -> FiniteFloat -> NonNegativeFloat
safeDistance2D (FiniteFloat x1) (FiniteFloat y1) (FiniteFloat x2) (FiniteFloat y2) =
  let dx = x2 - x1
      dy = y2 - y1
  in safeSqrt (FiniteFloat (dx * dx + dy * dy))

-- | Safe 2D length calculation
safeLength2D :: FiniteFloat -> FiniteFloat -> NonNegativeFloat
safeLength2D (FiniteFloat x) (FiniteFloat y) = safeSqrt (FiniteFloat (x * x + y * y))

-- | Safe 2D dot product
safeDot2D :: FiniteFloat -> FiniteFloat -> FiniteFloat -> FiniteFloat -> FiniteFloat
safeDot2D (FiniteFloat x1) (FiniteFloat y1) (FiniteFloat x2) (FiniteFloat y2) =
  let result = x1 * x2 + y1 * y2
  in if isFiniteNumber result then FiniteFloat result
     else FiniteFloat 0.0

--------------------------------------------------------------------------------
-- 3D Vector Safety
--------------------------------------------------------------------------------

-- | Safe 3D vector normalization
safeNormalize3D :: FiniteFloat -> FiniteFloat -> FiniteFloat -> Vec3
safeNormalize3D (FiniteFloat x) (FiniteFloat y) (FiniteFloat z) =
  let zero = { x: FiniteFloat 0.0, y: FiniteFloat 0.0, z: FiniteFloat 0.0 }
      lengthSq = x * x + y * y + z * z
      len = Number.sqrt lengthSq
      nx = x / len
      ny = y / len
      nz = z / len
  in if lengthSq == 0.0 then zero
     else if len == 0.0 then zero
     else if isFiniteNumber nx && isFiniteNumber ny && isFiniteNumber nz then { x: FiniteFloat nx, y: FiniteFloat ny, z: FiniteFloat nz }
     else zero

-- | Safe 3D distance calculation
safeDistance3D :: FiniteFloat -> FiniteFloat -> FiniteFloat -> FiniteFloat -> FiniteFloat -> FiniteFloat -> NonNegativeFloat
safeDistance3D (FiniteFloat x1) (FiniteFloat y1) (FiniteFloat z1) (FiniteFloat x2) (FiniteFloat y2) (FiniteFloat z2) =
  let dx = x2 - x1
      dy = y2 - y1
      dz = z2 - z1
  in safeSqrt (FiniteFloat (dx * dx + dy * dy + dz * dz))

-- | Safe 3D length calculation
safeLength3D :: FiniteFloat -> FiniteFloat -> FiniteFloat -> NonNegativeFloat
safeLength3D (FiniteFloat x) (FiniteFloat y) (FiniteFloat z) = safeSqrt (FiniteFloat (x * x + y * y + z * z))

--------------------------------------------------------------------------------
-- Angle Safety
--------------------------------------------------------------------------------

-- | Normalize angle to [0, 360) degrees
normalizeAngleDegrees :: FiniteFloat -> FiniteFloat
normalizeAngleDegrees angle = safeMod angle (FiniteFloat 360.0)

-- | Normalize angle to [0, 2*PI) radians
normalizeAngleRadians :: FiniteFloat -> FiniteFloat
normalizeAngleRadians angle = safeMod angle (FiniteFloat (Number.pi * 2.0))

-- | Convert degrees to radians
degreesToRadians :: FiniteFloat -> FiniteFloat
degreesToRadians (FiniteFloat d) =
  let result = d * (Number.pi / 180.0)
  in if isFiniteNumber result then FiniteFloat result
     else FiniteFloat 0.0

-- | Convert radians to degrees
radiansToDegrees :: FiniteFloat -> FiniteFloat
radiansToDegrees (FiniteFloat r) =
  let result = r * (180.0 / Number.pi)
  in if isFiniteNumber result then FiniteFloat result
     else FiniteFloat 0.0

--------------------------------------------------------------------------------
-- Comparison
--------------------------------------------------------------------------------

-- | Check if two numbers are approximately equal
approximately :: FiniteFloat -> FiniteFloat -> PositiveFloat -> Boolean
approximately (FiniteFloat a) (FiniteFloat b) (PositiveFloat eps) =
  let diff = Number.abs (a - b)
      maxAbs = max (Number.abs a) (Number.abs b)
  in if Number.abs a < 1.0 && Number.abs b < 1.0 then diff < eps
     else diff < eps * maxAbs

-- | Check if a value is approximately zero
isApproximatelyZero :: FiniteFloat -> PositiveFloat -> Boolean
isApproximatelyZero (FiniteFloat v) (PositiveFloat eps) = Number.abs v < eps

--------------------------------------------------------------------------------
-- Rounding
--------------------------------------------------------------------------------

-- | Round to specified decimal places
roundTo :: FiniteFloat -> Int -> FiniteFloat
roundTo (FiniteFloat v) decimals =
  let factor = Number.pow 10.0 (toNumber decimals)
      result = toNumber (round (v * factor)) / factor
  in if isFiniteNumber result then FiniteFloat result
     else FiniteFloat v

-- | Snap value to nearest multiple of step
snapTo :: FiniteFloat -> PositiveFloat -> FiniteFloat
snapTo (FiniteFloat v) (PositiveFloat s) =
  let result = toNumber (round (v / s)) * s
  in if isFiniteNumber result then FiniteFloat result
     else FiniteFloat v

--------------------------------------------------------------------------------
-- Range Utilities
--------------------------------------------------------------------------------

-- | Check if value is in range [min, max] inclusive
inRange :: FiniteFloat -> FiniteFloat -> FiniteFloat -> Boolean
inRange value minVal maxVal = value >= minVal && value <= maxVal

-- | Wrap value to range [min, max)
wrapToRange :: FiniteFloat -> FiniteFloat -> FiniteFloat -> FiniteFloat
wrapToRange (FiniteFloat v) (FiniteFloat minV) (FiniteFloat maxV) =
  let range' = maxV - minV
      shifted = v - minV
      wrapped = modFloat' (modFloat' shifted range' + range') range'
      result = minV + wrapped
  in if range' == 0.0 then FiniteFloat minV
     else if isFiniteNumber result then FiniteFloat result
     else FiniteFloat minV

-- | Ping-pong value between min and max
pingPong :: FiniteFloat -> FiniteFloat -> FiniteFloat -> FiniteFloat
pingPong (FiniteFloat v) (FiniteFloat minV) (FiniteFloat maxV) =
  let range' = maxV - minV
      shifted = v - minV
      doubleRange = range' + range'
      wrapped = modFloat' (modFloat' shifted doubleRange + doubleRange) doubleRange
      resultUp = minV + wrapped
      resultDown = maxV - (wrapped - range')
  in if range' == 0.0 then FiniteFloat minV
     else if wrapped < range' then
       if isFiniteNumber resultUp then FiniteFloat resultUp else FiniteFloat minV
     else
       if isFiniteNumber resultDown then FiniteFloat resultDown else FiniteFloat minV
