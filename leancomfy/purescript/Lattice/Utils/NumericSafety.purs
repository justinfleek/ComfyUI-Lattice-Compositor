-- | Lattice.Utils.NumericSafety - Numeric safety with total functions
-- |
-- | Guards against NaN, Infinity, division by zero.
-- | All functions are total and safe.
-- |
-- | Source: leancomfy/lean/Lattice/Utils/NumericSafety.lean

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
import Lattice.Primitives (FiniteFloat, UnitFloat, NonNegativeFloat, PositiveFloat, Vec2, Vec3)

--------------------------------------------------------------------------------
-- Basic Safety
--------------------------------------------------------------------------------

-- | Check if a Number is finite (not NaN or Infinity)
isFiniteNumber :: Number -> Boolean
isFiniteNumber x = Number.isFinite x && not (Number.isNaN x)

-- | Ensure a value is finite, returning fallback if not
ensureFinite :: Number -> FiniteFloat -> FiniteFloat
ensureFinite value fallback
  | isFiniteNumber value = value
  | otherwise = fallback

-- | Require a value to be finite (caller guarantees)
requireFinite :: Number -> FiniteFloat
requireFinite value
  | isFiniteNumber value = value
  | otherwise = 0.0

--------------------------------------------------------------------------------
-- Safe Arithmetic
--------------------------------------------------------------------------------

-- | Safe division - returns fallback for zero divisor or infinite result
safeDivide :: FiniteFloat -> FiniteFloat -> FiniteFloat -> FiniteFloat
safeDivide num denom fallback
  | denom == 0.0 = fallback
  | isFiniteNumber result = result
  | otherwise = fallback
  where result = num / denom

-- | Safe modulo - always returns non-negative result, handles zero divisor
safeMod :: FiniteFloat -> FiniteFloat -> FiniteFloat
safeMod value divisor
  | divisor == 0.0 = 0.0
  | isFiniteNumber positive = positive
  | otherwise = 0.0
  where
    raw = modFloat value divisor
    positive = modFloat (modFloat raw divisor + divisor) divisor

-- | Helper for float modulo
modFloat :: Number -> Number -> Number
modFloat a b = a - b * toNumber (floor (a / b))

-- | Safe square root - returns 0 for negative numbers
safeSqrt :: FiniteFloat -> NonNegativeFloat
safeSqrt value
  | value < 0.0 = 0.0
  | isFiniteNumber result && result >= 0.0 = result
  | otherwise = 0.0
  where result = Number.sqrt value

-- | Safe power - handles overflow
safePow :: FiniteFloat -> FiniteFloat -> FiniteFloat -> FiniteFloat
safePow base exponent fallback
  | isFiniteNumber result = result
  | otherwise = fallback
  where result = Number.pow base exponent

-- | Safe log - handles zero and negative
safeLog :: FiniteFloat -> FiniteFloat -> FiniteFloat
safeLog value fallback
  | value <= 0.0 = fallback
  | isFiniteNumber result = result
  | otherwise = fallback
  where result = Number.log value

--------------------------------------------------------------------------------
-- Clamping
--------------------------------------------------------------------------------

-- | Clamp a value between min and max
clamp :: FiniteFloat -> FiniteFloat -> FiniteFloat -> FiniteFloat
clamp value minVal maxVal
  | value < minVal = minVal
  | value > maxVal = maxVal
  | otherwise = value

-- | Clamp to [0, 1] - returns UnitFloat
clamp01 :: FiniteFloat -> UnitFloat
clamp01 value = max 0.0 (min 1.0 value)

-- | Clamp to [0, 100]
clamp0100 :: FiniteFloat -> FiniteFloat
clamp0100 value = clamp value 0.0 100.0

-- | Clamp to [0, 255] for color channels
clamp0255 :: FiniteFloat -> FiniteFloat
clamp0255 value = clamp value 0.0 255.0

-- | Clamp to [-1, 1]
clampNeg1To1 :: FiniteFloat -> FiniteFloat
clampNeg1To1 value = clamp value (-1.0) 1.0

--------------------------------------------------------------------------------
-- Interpolation
--------------------------------------------------------------------------------

-- | Safe linear interpolation with clamped t
safeLerp :: FiniteFloat -> FiniteFloat -> UnitFloat -> FiniteFloat
safeLerp a b t
  | isFiniteNumber result = result
  | isFiniteNumber alt = alt
  | otherwise = a
  where
    diff = b - a
    result = a + diff * t
    alt = a * (1.0 - t) + b * t

-- | Safe inverse lerp - where value falls between a and b as [0, 1]
safeInverseLerp :: FiniteFloat -> FiniteFloat -> FiniteFloat -> UnitFloat
safeInverseLerp a b value
  | range == 0.0 = 0.0
  | otherwise = clamp01 t
  where
    range = b - a
    t = (value - a) / range

-- | Safe remap from [inMin, inMax] to [outMin, outMax]
safeRemap :: FiniteFloat -> FiniteFloat -> FiniteFloat -> FiniteFloat -> FiniteFloat -> FiniteFloat
safeRemap value inMin inMax outMin outMax =
  safeLerp outMin outMax t
  where t = safeInverseLerp inMin inMax value

-- | Smooth step interpolation (Hermite)
smoothStep :: FiniteFloat -> FiniteFloat -> UnitFloat -> FiniteFloat
smoothStep a b t =
  safeLerp a b smooth
  where smooth = t * t * (3.0 - 2.0 * t)

-- | Smoother step (Perlin's improved)
smootherStep :: FiniteFloat -> FiniteFloat -> UnitFloat -> FiniteFloat
smootherStep a b t =
  safeLerp a b smooth
  where smooth = t * t * t * (t * (t * 6.0 - 15.0) + 10.0)

--------------------------------------------------------------------------------
-- 2D Vector Safety
--------------------------------------------------------------------------------

-- | Safe 2D vector normalization
safeNormalize2D :: FiniteFloat -> FiniteFloat -> Vec2
safeNormalize2D x y
  | lengthSq == 0.0 = { x: 0.0, y: 0.0 }
  | len == 0.0 = { x: 0.0, y: 0.0 }
  | isFiniteNumber nx && isFiniteNumber ny = { x: nx, y: ny }
  | otherwise = { x: 0.0, y: 0.0 }
  where
    lengthSq = x * x + y * y
    len = Number.sqrt lengthSq
    nx = x / len
    ny = y / len

-- | Safe 2D distance calculation
safeDistance2D :: FiniteFloat -> FiniteFloat -> FiniteFloat -> FiniteFloat -> NonNegativeFloat
safeDistance2D x1 y1 x2 y2 =
  safeSqrt (dx * dx + dy * dy)
  where
    dx = x2 - x1
    dy = y2 - y1

-- | Safe 2D length calculation
safeLength2D :: FiniteFloat -> FiniteFloat -> NonNegativeFloat
safeLength2D x y = safeSqrt (x * x + y * y)

-- | Safe 2D dot product
safeDot2D :: FiniteFloat -> FiniteFloat -> FiniteFloat -> FiniteFloat -> FiniteFloat
safeDot2D x1 y1 x2 y2
  | isFiniteNumber result = result
  | otherwise = 0.0
  where result = x1 * x2 + y1 * y2

--------------------------------------------------------------------------------
-- 3D Vector Safety
--------------------------------------------------------------------------------

-- | Safe 3D vector normalization
safeNormalize3D :: FiniteFloat -> FiniteFloat -> FiniteFloat -> Vec3
safeNormalize3D x y z
  | lengthSq == 0.0 = zero
  | len == 0.0 = zero
  | isFiniteNumber nx && isFiniteNumber ny && isFiniteNumber nz = { x: nx, y: ny, z: nz }
  | otherwise = zero
  where
    zero = { x: 0.0, y: 0.0, z: 0.0 }
    lengthSq = x * x + y * y + z * z
    len = Number.sqrt lengthSq
    nx = x / len
    ny = y / len
    nz = z / len

-- | Safe 3D distance calculation
safeDistance3D :: FiniteFloat -> FiniteFloat -> FiniteFloat -> FiniteFloat -> FiniteFloat -> FiniteFloat -> NonNegativeFloat
safeDistance3D x1 y1 z1 x2 y2 z2 =
  safeSqrt (dx * dx + dy * dy + dz * dz)
  where
    dx = x2 - x1
    dy = y2 - y1
    dz = z2 - z1

-- | Safe 3D length calculation
safeLength3D :: FiniteFloat -> FiniteFloat -> FiniteFloat -> NonNegativeFloat
safeLength3D x y z = safeSqrt (x * x + y * y + z * z)

--------------------------------------------------------------------------------
-- Angle Safety
--------------------------------------------------------------------------------

-- | Normalize angle to [0, 360) degrees
normalizeAngleDegrees :: FiniteFloat -> FiniteFloat
normalizeAngleDegrees angle = safeMod angle 360.0

-- | Normalize angle to [0, 2*PI) radians
normalizeAngleRadians :: FiniteFloat -> FiniteFloat
normalizeAngleRadians angle = safeMod angle (Number.pi * 2.0)

-- | Convert degrees to radians
degreesToRadians :: FiniteFloat -> FiniteFloat
degreesToRadians degrees
  | isFiniteNumber result = result
  | otherwise = 0.0
  where result = degrees * (Number.pi / 180.0)

-- | Convert radians to degrees
radiansToDegrees :: FiniteFloat -> FiniteFloat
radiansToDegrees radians
  | isFiniteNumber result = result
  | otherwise = 0.0
  where result = radians * (180.0 / Number.pi)

--------------------------------------------------------------------------------
-- Comparison
--------------------------------------------------------------------------------

-- | Check if two numbers are approximately equal
approximately :: FiniteFloat -> FiniteFloat -> PositiveFloat -> Boolean
approximately a b epsilon
  | Number.abs a < 1.0 && Number.abs b < 1.0 = diff < epsilon
  | otherwise = diff < epsilon * maxAbs
  where
    diff = Number.abs (a - b)
    maxAbs = max (Number.abs a) (Number.abs b)

-- | Check if a value is approximately zero
isApproximatelyZero :: FiniteFloat -> PositiveFloat -> Boolean
isApproximatelyZero value epsilon = Number.abs value < epsilon

--------------------------------------------------------------------------------
-- Rounding
--------------------------------------------------------------------------------

-- | Round to specified decimal places
roundTo :: FiniteFloat -> Int -> FiniteFloat
roundTo value decimals
  | isFiniteNumber result = result
  | otherwise = value
  where
    factor = Number.pow 10.0 (toNumber decimals)
    result = toNumber (round (value * factor)) / factor

-- | Snap value to nearest multiple of step
snapTo :: FiniteFloat -> PositiveFloat -> FiniteFloat
snapTo value step
  | isFiniteNumber result = result
  | otherwise = value
  where
    result = toNumber (round (value / step)) * step

--------------------------------------------------------------------------------
-- Range Utilities
--------------------------------------------------------------------------------

-- | Check if value is in range [min, max] inclusive
inRange :: FiniteFloat -> FiniteFloat -> FiniteFloat -> Boolean
inRange value minVal maxVal = value >= minVal && value <= maxVal

-- | Wrap value to range [min, max)
wrapToRange :: FiniteFloat -> FiniteFloat -> FiniteFloat -> FiniteFloat
wrapToRange value minVal maxVal
  | range == 0.0 = minVal
  | isFiniteNumber (minVal + wrapped) = minVal + wrapped
  | otherwise = minVal
  where
    range = maxVal - minVal
    shifted = value - minVal
    wrapped = modFloat (modFloat shifted range + range) range

-- | Ping-pong value between min and max
pingPong :: FiniteFloat -> FiniteFloat -> FiniteFloat -> FiniteFloat
pingPong value minVal maxVal
  | range == 0.0 = minVal
  | wrapped < range = safeResult (minVal + wrapped)
  | otherwise = safeResult (maxVal - (wrapped - range))
  where
    range = maxVal - minVal
    shifted = value - minVal
    doubleRange = range * 2.0
    wrapped = modFloat (modFloat shifted doubleRange + doubleRange) doubleRange
    safeResult r
      | isFiniteNumber r = r
      | otherwise = minVal
