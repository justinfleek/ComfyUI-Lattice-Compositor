{-# LANGUAGE StrictData #-}

{-|
Module      : Lattice.Utils.NumericSafety
Description : Numeric safety with total functions
Copyright   : (c) Lattice, 2026
License     : MIT

Guards against NaN, Infinity, division by zero.
All functions are total and proven safe.

Source: leancomfy/lean/Lattice/Utils/NumericSafety.lean
-}

module Lattice.Utils.NumericSafety
  ( -- * Basic Safety
    ensureFinite
  , requireFinite
    -- * Safe Arithmetic
  , safeDivide
  , safeMod
  , safeSqrt
  , safePow
  , safeLog
    -- * Clamping
  , clamp
  , clamp01
  , clamp0100
  , clamp0255
  , clampNeg1To1
    -- * Interpolation
  , safeLerp
  , safeInverseLerp
  , safeRemap
  , smoothStep
  , smootherStep
    -- * 2D Vector Safety
  , safeNormalize2D
  , safeDistance2D
  , safeLength2D
  , safeDot2D
    -- * 3D Vector Safety
  , safeNormalize3D
  , safeDistance3D
  , safeLength3D
    -- * Angle Safety
  , normalizeAngleDegrees
  , normalizeAngleRadians
  , degreesToRadians
  , radiansToDegrees
    -- * Comparison
  , approximately
  , isApproximatelyZero
    -- * Rounding
  , roundTo
  , snapTo
    -- * Range Utilities
  , inRange
  , wrapToRange
  , pingPong
  ) where

import Lattice.Primitives

--------------------------------------------------------------------------------
-- Basic Safety
--------------------------------------------------------------------------------

-- | Check if a Double is finite (not NaN or Infinity)
isFiniteDouble :: Double -> Bool
isFiniteDouble x = not (isNaN x) && not (isInfinite x)

-- | Ensure a value is finite, returning fallback if not
ensureFinite :: Double -> FiniteFloat -> FiniteFloat
ensureFinite value fallback
  | isFiniteDouble value = FiniteFloat value
  | otherwise = fallback

-- | Require a value to be finite (caller guarantees)
requireFinite :: Double -> FiniteFloat
requireFinite value
  | isFiniteDouble value = FiniteFloat value
  | otherwise = FiniteFloat 0  -- Safe fallback

--------------------------------------------------------------------------------
-- Safe Arithmetic
--------------------------------------------------------------------------------

-- | Safe division - returns fallback for zero divisor or infinite result
safeDivide :: FiniteFloat -> FiniteFloat -> FiniteFloat -> FiniteFloat
safeDivide (FiniteFloat num) (FiniteFloat denom) fallback
  | denom == 0 = fallback
  | isFiniteDouble result = FiniteFloat result
  | otherwise = fallback
  where result = num / denom

-- | Safe modulo - always returns non-negative result, handles zero divisor
safeMod :: FiniteFloat -> FiniteFloat -> FiniteFloat
safeMod (FiniteFloat value) (FiniteFloat divisor)
  | divisor == 0 = FiniteFloat 0
  | isFiniteDouble positive = FiniteFloat positive
  | otherwise = FiniteFloat 0
  where
    raw = value `mod'` divisor
    positive = ((raw `mod'` divisor) + divisor) `mod'` divisor
    mod' a b = a - b * fromIntegral (floor (a / b) :: Int)

-- | Safe square root - returns 0 for negative numbers
safeSqrt :: FiniteFloat -> NonNegativeFloat
safeSqrt (FiniteFloat value)
  | value < 0 = NonNegativeFloat 0
  | isFiniteDouble result && result >= 0 = NonNegativeFloat result
  | otherwise = NonNegativeFloat 0
  where result = sqrt value

-- | Safe power - handles overflow
safePow :: FiniteFloat -> FiniteFloat -> FiniteFloat -> FiniteFloat
safePow (FiniteFloat base) (FiniteFloat exponent) fallback
  | isFiniteDouble result = FiniteFloat result
  | otherwise = fallback
  where result = base ** exponent

-- | Safe log - handles zero and negative
safeLog :: FiniteFloat -> FiniteFloat -> FiniteFloat
safeLog (FiniteFloat value) fallback
  | value <= 0 = fallback
  | isFiniteDouble result = FiniteFloat result
  | otherwise = fallback
  where result = log value

--------------------------------------------------------------------------------
-- Clamping
--------------------------------------------------------------------------------

-- | Clamp a value between min and max
clamp :: FiniteFloat -> FiniteFloat -> FiniteFloat -> FiniteFloat
clamp (FiniteFloat value) (FiniteFloat minVal) (FiniteFloat maxVal)
  | value < minVal = FiniteFloat minVal
  | value > maxVal = FiniteFloat maxVal
  | otherwise = FiniteFloat value

-- | Clamp to [0, 1] - returns UnitFloat
clamp01 :: FiniteFloat -> UnitFloat
clamp01 (FiniteFloat value) = UnitFloat clamped
  where clamped = max 0 (min 1 value)

-- | Clamp to [0, 100]
clamp0100 :: FiniteFloat -> FiniteFloat
clamp0100 value = clamp value (FiniteFloat 0) (FiniteFloat 100)

-- | Clamp to [0, 255] for color channels
clamp0255 :: FiniteFloat -> FiniteFloat
clamp0255 value = clamp value (FiniteFloat 0) (FiniteFloat 255)

-- | Clamp to [-1, 1]
clampNeg1To1 :: FiniteFloat -> FiniteFloat
clampNeg1To1 value = clamp value (FiniteFloat (-1)) (FiniteFloat 1)

--------------------------------------------------------------------------------
-- Interpolation
--------------------------------------------------------------------------------

-- | Safe linear interpolation with clamped t
safeLerp :: FiniteFloat -> FiniteFloat -> UnitFloat -> FiniteFloat
safeLerp (FiniteFloat a) (FiniteFloat b) (UnitFloat t)
  | isFiniteDouble result = FiniteFloat result
  | isFiniteDouble alt = FiniteFloat alt
  | otherwise = FiniteFloat a
  where
    diff = b - a
    result = a + diff * t
    alt = a * (1 - t) + b * t

-- | Safe inverse lerp - where value falls between a and b as [0, 1]
safeInverseLerp :: FiniteFloat -> FiniteFloat -> FiniteFloat -> UnitFloat
safeInverseLerp (FiniteFloat a) (FiniteFloat b) (FiniteFloat value)
  | range == 0 = UnitFloat 0
  | otherwise = clamp01 (FiniteFloat t)
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
smoothStep a b (UnitFloat t) =
  safeLerp a b (UnitFloat smooth)
  where smooth = t * t * (3 - 2 * t)

-- | Smoother step (Perlin's improved)
smootherStep :: FiniteFloat -> FiniteFloat -> UnitFloat -> FiniteFloat
smootherStep a b (UnitFloat t) =
  safeLerp a b (UnitFloat smooth)
  where smooth = t * t * t * (t * (t * 6 - 15) + 10)

--------------------------------------------------------------------------------
-- 2D Vector Safety
--------------------------------------------------------------------------------

-- | Safe 2D vector normalization
safeNormalize2D :: FiniteFloat -> FiniteFloat -> (FiniteFloat, FiniteFloat)
safeNormalize2D (FiniteFloat x) (FiniteFloat y)
  | lengthSq == 0 = (FiniteFloat 0, FiniteFloat 0)
  | len == 0 = (FiniteFloat 0, FiniteFloat 0)
  | isFiniteDouble nx && isFiniteDouble ny = (FiniteFloat nx, FiniteFloat ny)
  | otherwise = (FiniteFloat 0, FiniteFloat 0)
  where
    lengthSq = x * x + y * y
    len = sqrt lengthSq
    nx = x / len
    ny = y / len

-- | Safe 2D distance calculation
safeDistance2D :: FiniteFloat -> FiniteFloat -> FiniteFloat -> FiniteFloat -> NonNegativeFloat
safeDistance2D (FiniteFloat x1) (FiniteFloat y1) (FiniteFloat x2) (FiniteFloat y2) =
  safeSqrt (FiniteFloat (dx * dx + dy * dy))
  where
    dx = x2 - x1
    dy = y2 - y1

-- | Safe 2D length calculation
safeLength2D :: FiniteFloat -> FiniteFloat -> NonNegativeFloat
safeLength2D (FiniteFloat x) (FiniteFloat y) =
  safeSqrt (FiniteFloat (x * x + y * y))

-- | Safe 2D dot product
safeDot2D :: FiniteFloat -> FiniteFloat -> FiniteFloat -> FiniteFloat -> FiniteFloat
safeDot2D (FiniteFloat x1) (FiniteFloat y1) (FiniteFloat x2) (FiniteFloat y2)
  | isFiniteDouble result = FiniteFloat result
  | otherwise = FiniteFloat 0
  where result = x1 * x2 + y1 * y2

--------------------------------------------------------------------------------
-- 3D Vector Safety
--------------------------------------------------------------------------------

-- | Safe 3D vector normalization
safeNormalize3D :: FiniteFloat -> FiniteFloat -> FiniteFloat -> (FiniteFloat, FiniteFloat, FiniteFloat)
safeNormalize3D (FiniteFloat x) (FiniteFloat y) (FiniteFloat z)
  | lengthSq == 0 = zero
  | len == 0 = zero
  | isFiniteDouble nx && isFiniteDouble ny && isFiniteDouble nz = (FiniteFloat nx, FiniteFloat ny, FiniteFloat nz)
  | otherwise = zero
  where
    zero = (FiniteFloat 0, FiniteFloat 0, FiniteFloat 0)
    lengthSq = x * x + y * y + z * z
    len = sqrt lengthSq
    nx = x / len
    ny = y / len
    nz = z / len

-- | Safe 3D distance calculation
safeDistance3D :: FiniteFloat -> FiniteFloat -> FiniteFloat -> FiniteFloat -> FiniteFloat -> FiniteFloat -> NonNegativeFloat
safeDistance3D (FiniteFloat x1) (FiniteFloat y1) (FiniteFloat z1) (FiniteFloat x2) (FiniteFloat y2) (FiniteFloat z2) =
  safeSqrt (FiniteFloat (dx * dx + dy * dy + dz * dz))
  where
    dx = x2 - x1
    dy = y2 - y1
    dz = z2 - z1

-- | Safe 3D length calculation
safeLength3D :: FiniteFloat -> FiniteFloat -> FiniteFloat -> NonNegativeFloat
safeLength3D (FiniteFloat x) (FiniteFloat y) (FiniteFloat z) =
  safeSqrt (FiniteFloat (x * x + y * y + z * z))

--------------------------------------------------------------------------------
-- Angle Safety
--------------------------------------------------------------------------------

-- | Normalize angle to [0, 360) degrees
normalizeAngleDegrees :: FiniteFloat -> FiniteFloat
normalizeAngleDegrees angle = safeMod angle (FiniteFloat 360)

-- | Normalize angle to [0, 2*PI) radians
normalizeAngleRadians :: FiniteFloat -> FiniteFloat
normalizeAngleRadians angle = safeMod angle (FiniteFloat (pi * 2))

-- | Convert degrees to radians
degreesToRadians :: FiniteFloat -> FiniteFloat
degreesToRadians (FiniteFloat degrees)
  | isFiniteDouble result = FiniteFloat result
  | otherwise = FiniteFloat 0
  where result = degrees * (pi / 180)

-- | Convert radians to degrees
radiansToDegrees :: FiniteFloat -> FiniteFloat
radiansToDegrees (FiniteFloat radians)
  | isFiniteDouble result = FiniteFloat result
  | otherwise = FiniteFloat 0
  where result = radians * (180 / pi)

--------------------------------------------------------------------------------
-- Comparison
--------------------------------------------------------------------------------

-- | Check if two numbers are approximately equal
approximately :: FiniteFloat -> FiniteFloat -> PositiveFloat -> Bool
approximately (FiniteFloat a) (FiniteFloat b) (PositiveFloat epsilon)
  | abs a < 1 && abs b < 1 = diff < epsilon
  | otherwise = diff < epsilon * maxAbs
  where
    diff = abs (a - b)
    maxAbs = max (abs a) (abs b)

-- | Check if a value is approximately zero
isApproximatelyZero :: FiniteFloat -> PositiveFloat -> Bool
isApproximatelyZero (FiniteFloat value) (PositiveFloat epsilon) =
  abs value < epsilon

--------------------------------------------------------------------------------
-- Rounding
--------------------------------------------------------------------------------

-- | Round to specified decimal places
roundTo :: FiniteFloat -> Int -> FiniteFloat
roundTo (FiniteFloat value) decimals
  | isFiniteDouble result = FiniteFloat result
  | otherwise = FiniteFloat value
  where
    factor = 10 ** fromIntegral decimals
    result = fromIntegral (round (value * factor) :: Int) / factor

-- | Snap value to nearest multiple of step
snapTo :: FiniteFloat -> PositiveFloat -> FiniteFloat
snapTo (FiniteFloat value) (PositiveFloat step)
  | isFiniteDouble result = FiniteFloat result
  | otherwise = FiniteFloat value
  where
    result = fromIntegral (round (value / step) :: Int) * step

--------------------------------------------------------------------------------
-- Range Utilities
--------------------------------------------------------------------------------

-- | Check if value is in range [min, max] inclusive
inRange :: FiniteFloat -> FiniteFloat -> FiniteFloat -> Bool
inRange (FiniteFloat value) (FiniteFloat minVal) (FiniteFloat maxVal) =
  value >= minVal && value <= maxVal

-- | Wrap value to range [min, max)
wrapToRange :: FiniteFloat -> FiniteFloat -> FiniteFloat -> FiniteFloat
wrapToRange (FiniteFloat value) (FiniteFloat minVal) (FiniteFloat maxVal)
  | range == 0 = FiniteFloat minVal
  | isFiniteDouble (minVal + wrapped) = FiniteFloat (minVal + wrapped)
  | otherwise = FiniteFloat minVal
  where
    range = maxVal - minVal
    shifted = value - minVal
    wrapped = ((shifted `mod'` range) + range) `mod'` range
    mod' a b = a - b * fromIntegral (floor (a / b) :: Int)

-- | Ping-pong value between min and max
pingPong :: FiniteFloat -> FiniteFloat -> FiniteFloat -> FiniteFloat
pingPong (FiniteFloat value) (FiniteFloat minVal) (FiniteFloat maxVal)
  | range == 0 = FiniteFloat minVal
  | wrapped < range = safeResult (minVal + wrapped)
  | otherwise = safeResult (maxVal - (wrapped - range))
  where
    range = maxVal - minVal
    shifted = value - minVal
    doubleRange = range * 2
    wrapped = ((shifted `mod'` doubleRange) + doubleRange) `mod'` doubleRange
    mod' a b = a - b * fromIntegral (floor (a / b) :: Int)
    safeResult r
      | isFiniteDouble r = FiniteFloat r
      | otherwise = FiniteFloat minVal
