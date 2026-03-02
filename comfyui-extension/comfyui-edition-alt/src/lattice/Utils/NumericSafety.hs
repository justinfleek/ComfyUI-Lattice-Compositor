-- |
-- Module      : Lattice.Utils.NumericSafety
-- Description : Numeric safety utilities - guards against NaN, Infinity, division by zero
-- 
-- Migrated from ui/src/utils/numericSafety.ts
-- Pure functions for safe numeric operations
-- Use these in hot paths: interpolation, transforms, physics, particles
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.Utils.NumericSafety
  ( -- Basic safety
    ensureFinite
  , requireFinite
  -- Safe arithmetic
  , safeDivide
  , safeMod
  , safeSqrt
  , safePow
  , safeLog
  -- Clamping
  , clamp
  , clamp01
  , clamp0100
  , clamp0255
  , clampNeg1To1
  -- Interpolation
  , safeLerp
  , safeLerpUnclamped
  , safeInverseLerp
  , safeRemap
  , smoothStep
  , smootherStep
  -- 2D vector safety
  , safeNormalize2D
  , safeDistance2D
  , safeLength2D
  , safeDot2D
  -- 3D vector safety
  , safeNormalize3D
  , safeDistance3D
  , safeLength3D
  -- Angle safety
  , normalizeAngleDegrees
  , normalizeAngleRadians
  , normalizeAngleDegreesSymmetric
  , normalizeAngleRadiansSymmetric
  , degreesToRadians
  , radiansToDegrees
  , shortestAngleDifferenceDegrees
  , lerpAngleDegrees
  -- Comparison
  , approximately
  , isApproximatelyZero
  -- Rounding
  , roundTo
  , floorTo
  , ceilTo
  , snapTo
  -- Range utilities
  , inRange
  , wrapToRange
  , pingPong
  , isFinite
  , validateFinite
  ) where

import Data.Text (Text)
import qualified Data.Text as T

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                           // basic // safety
-- ════════════════════════════════════════════════════════════════════════════

-- | Finite number check (not NaN, not ±Infinity). Re-exported for modules that cannot use Data.Float.
isFinite :: Double -> Bool
isFinite x = not (isNaN x) && not (isInfinite x)

-- | Alias for isFinite (used by LayerData and validation modules).
validateFinite :: Double -> Bool
validateFinite = isFinite

-- | Ensure a value is a finite number, returning fallback if not
ensureFinite :: Double -> Double -> Double
ensureFinite value fallback
  | isFinite value = value
  | otherwise = fallback

-- | Require a value to be a finite number, throwing if not
-- Note: In Haskell, we return Either instead of throwing
requireFinite :: Double -> Text -> Either Text Double
requireFinite value name
  | isNaN value = Left (name <> " must not be NaN")
  | not (isFinite value) = Left (name <> " must be finite, got " <> T.pack (show value))
  | otherwise = Right value

-- ════════════════════════════════════════════════════════════════════════════
--                                                        // safe // arithmetic
-- ════════════════════════════════════════════════════════════════════════════

-- | Safe division - returns fallback instead of Infinity or NaN
safeDivide :: Double -> Double -> Double -> Double
safeDivide numerator denominator fallback
  | denominator == 0 = fallback
  | otherwise = let result = numerator / denominator
                in if isFinite result then result else fallback

-- | Safe modulo - always returns positive result, handles zero divisor
-- Unlike Haskell's mod, this always returns a positive value (like JavaScript %)
safeMod :: Double -> Double -> Double
safeMod value divisor
  | divisor == 0 = 0
  | otherwise = let jsMod = value - fromIntegral (floor (value / divisor)) * divisor
                    result = if jsMod < 0 then jsMod + abs divisor else jsMod
                in if isFinite result then result else 0

-- | Safe square root - returns 0 for negative numbers instead of NaN
safeSqrt :: Double -> Double
safeSqrt value
  | value < 0 = 0
  | not (isFinite value) = 0
  | otherwise = sqrt value

-- | Safe power - handles edge cases
safePow :: Double -> Double -> Double -> Double
safePow base exponent fallback =
  let result = base ** exponent
  in if isFinite result then result else fallback

-- | Safe log - handles zero and negative numbers
safeLog :: Double -> Double -> Double
safeLog value fallback
  | value <= 0 = fallback
  | otherwise = let result = log value
                in if isFinite result then result else fallback

-- ════════════════════════════════════════════════════════════════════════════
--                                                                  // clamping
-- ════════════════════════════════════════════════════════════════════════════

-- | Clamp a value between min and max
clamp :: Double -> Double -> Double -> Double
clamp value min max
  | isNaN value = min
  | value < min = min
  | value > max = max
  | otherwise = value

-- | Clamp a value to [0, 1] range
clamp01 :: Double -> Double
clamp01 value = clamp value 0 1

-- | Clamp a value to [0, 100] range (for percentages)
clamp0100 :: Double -> Double
clamp0100 value = clamp value 0 100

-- | Clamp a value to [0, 255] range (for color channels)
clamp0255 :: Double -> Double
clamp0255 value = clamp value 0 255

-- | Clamp a value to [-1, 1] range
clampNeg1To1 :: Double -> Double
clampNeg1To1 value = clamp value (-1) 1

-- ════════════════════════════════════════════════════════════════════════════
--                                                             // interpolation
-- ════════════════════════════════════════════════════════════════════════════

-- | Safe linear interpolation - clamps t to [0, 1] and ensures finite result
safeLerp :: Double -> Double -> Double -> Double
safeLerp a b t =
  let safeA = ensureFinite a 0
      safeB = ensureFinite b 0
      safeT = clamp01 (ensureFinite t 0)
      diff = safeB - safeA
  in if isFinite diff
       then safeA + diff * safeT
       else let result = safeA * (1 - safeT) + safeB * safeT
            in ensureFinite result safeA

-- | Unclamped lerp - allows t outside [0, 1] but still ensures finite result
safeLerpUnclamped :: Double -> Double -> Double -> Double
safeLerpUnclamped a b t =
  let safeA = ensureFinite a 0
      safeB = ensureFinite b 0
      safeT = ensureFinite t 0
      diff = safeB - safeA
  in if isFinite diff
       then let result = safeA + diff * safeT
            in ensureFinite result safeA
       else let result = safeA * (1 - safeT) + safeB * safeT
            in ensureFinite result safeA

-- | Safe inverse lerp - returns where value falls between a and b as [0, 1]
safeInverseLerp :: Double -> Double -> Double -> Double
safeInverseLerp a b value =
  let safeA = ensureFinite a 0
      safeB = ensureFinite b 0
      safeValue = ensureFinite value 0
      range = safeB - safeA
  in if range == 0
       then 0
       else clamp01 ((safeValue - safeA) / range)

-- | Safe remap - remaps value from [inMin, inMax] to [outMin, outMax]
safeRemap :: Double -> Double -> Double -> Double -> Double -> Double
safeRemap value inMin inMax outMin outMax =
  let t = safeInverseLerp inMin inMax value
  in safeLerp outMin outMax t

-- | Smooth step interpolation - smooth Hermite interpolation
smoothStep :: Double -> Double -> Double -> Double
smoothStep a b t =
  let safeT = clamp01 (ensureFinite t 0)
      smooth = safeT * safeT * (3 - 2 * safeT)
  in safeLerp a b smooth

-- | Smoother step - Ken Perlin's improved smooth step
smootherStep :: Double -> Double -> Double -> Double
smootherStep a b t =
  let safeT = clamp01 (ensureFinite t 0)
      smooth = safeT * safeT * safeT * (safeT * (safeT * 6 - 15) + 10)
  in safeLerp a b smooth

-- ════════════════════════════════════════════════════════════════════════════
-- 2D VECTOR SAFETY
-- ════════════════════════════════════════════════════════════════════════════

-- | Safe 2D vector normalization - returns zero vector for zero-length input
safeNormalize2D :: Double -> Double -> (Double, Double)
safeNormalize2D x y =
  let safeX = ensureFinite x 0
      safeY = ensureFinite y 0
      lengthSq = safeX * safeX + safeY * safeY
  in if lengthSq == 0
       then (0, 0)
       else let length = sqrt lengthSq
            in if length == 0
                 then (0, 0)
                 else (safeX / length, safeY / length)

-- | Safe 2D distance calculation
safeDistance2D :: Double -> Double -> Double -> Double -> Double
safeDistance2D x1 y1 x2 y2 =
  let dx = ensureFinite x2 0 - ensureFinite x1 0
      dy = ensureFinite y2 0 - ensureFinite y1 0
  in safeSqrt (dx * dx + dy * dy)

-- | Safe 2D length calculation
safeLength2D :: Double -> Double -> Double
safeLength2D x y =
  let safeX = ensureFinite x 0
      safeY = ensureFinite y 0
  in safeSqrt (safeX * safeX + safeY * safeY)

-- | Safe 2D dot product
safeDot2D :: Double -> Double -> Double -> Double -> Double
safeDot2D x1 y1 x2 y2 =
  let result = ensureFinite x1 0 * ensureFinite x2 0 +
               ensureFinite y1 0 * ensureFinite y2 0
  in ensureFinite result 0

-- ════════════════════════════════════════════════════════════════════════════
-- 3D VECTOR SAFETY
-- ════════════════════════════════════════════════════════════════════════════

-- | Safe 3D vector normalization
safeNormalize3D :: Double -> Double -> Double -> (Double, Double, Double)
safeNormalize3D x y z =
  let safeX = ensureFinite x 0
      safeY = ensureFinite y 0
      safeZ = ensureFinite z 0
      lengthSq = safeX * safeX + safeY * safeY + safeZ * safeZ
  in if lengthSq == 0
       then (0, 0, 0)
       else let length = sqrt lengthSq
            in if length == 0
                 then (0, 0, 0)
                 else (safeX / length, safeY / length, safeZ / length)

-- | Safe 3D distance calculation
safeDistance3D :: Double -> Double -> Double -> Double -> Double -> Double -> Double
safeDistance3D x1 y1 z1 x2 y2 z2 =
  let dx = ensureFinite x2 0 - ensureFinite x1 0
      dy = ensureFinite y2 0 - ensureFinite y1 0
      dz = ensureFinite z2 0 - ensureFinite z1 0
  in safeSqrt (dx * dx + dy * dy + dz * dz)

-- | Safe 3D length calculation
safeLength3D :: Double -> Double -> Double -> Double
safeLength3D x y z =
  let safeX = ensureFinite x 0
      safeY = ensureFinite y 0
      safeZ = ensureFinite z 0
  in safeSqrt (safeX * safeX + safeY * safeY + safeZ * safeZ)

-- ════════════════════════════════════════════════════════════════════════════
--                                                           // angle // safety
-- ════════════════════════════════════════════════════════════════════════════

-- | Normalize angle to [0, 360) degrees
normalizeAngleDegrees :: Double -> Double
normalizeAngleDegrees angle =
  let safe = ensureFinite angle 0
  in safeMod safe 360

-- | Normalize angle to [0, 2*PI) radians
normalizeAngleRadians :: Double -> Double
normalizeAngleRadians angle =
  let safe = ensureFinite angle 0
  in safeMod safe (2 * pi)

-- | Normalize angle to [-180, 180) degrees
normalizeAngleDegreesSymmetric :: Double -> Double
normalizeAngleDegreesSymmetric angle =
  let normalized = normalizeAngleDegrees angle
  in if normalized > 180 then normalized - 360 else normalized

-- | Normalize angle to [-PI, PI) radians
normalizeAngleRadiansSymmetric :: Double -> Double
normalizeAngleRadiansSymmetric angle =
  let normalized = normalizeAngleRadians angle
  in if normalized > pi then normalized - 2 * pi else normalized

-- | Convert degrees to radians safely
degreesToRadians :: Double -> Double
degreesToRadians degrees = ensureFinite degrees 0 * (pi / 180)

-- | Convert radians to degrees safely
radiansToDegrees :: Double -> Double
radiansToDegrees radians = ensureFinite radians 0 * (180 / pi)

-- | Shortest angular distance between two angles in degrees
shortestAngleDifferenceDegrees :: Double -> Double -> Double
shortestAngleDifferenceDegrees from to =
  normalizeAngleDegreesSymmetric (to - from)

-- | Lerp between angles using shortest path (degrees)
lerpAngleDegrees :: Double -> Double -> Double -> Double
lerpAngleDegrees from to t =
  let diff = shortestAngleDifferenceDegrees from to
  in normalizeAngleDegrees (from + diff * clamp01 (ensureFinite t 0))

-- ════════════════════════════════════════════════════════════════════════════
--                                                                // comparison
-- ════════════════════════════════════════════════════════════════════════════

-- | Check if two numbers are approximately equal
approximately :: Double -> Double -> Double -> Bool
approximately a b epsilon =
  let safeA = ensureFinite a 0
      safeB = ensureFinite b 0
      diff = abs (safeA - safeB)
  in if abs safeA < 1 && abs safeB < 1
       then diff < epsilon
       else let maxAbs = max (abs safeA) (abs safeB)
            in diff < epsilon * maxAbs

-- | Check if a value is approximately zero
isApproximatelyZero :: Double -> Double -> Bool
isApproximatelyZero value epsilon = abs (ensureFinite value 0) < epsilon

-- ════════════════════════════════════════════════════════════════════════════
--                                                                  // rounding
-- ════════════════════════════════════════════════════════════════════════════

-- | Round to specified decimal places
roundTo :: Double -> Int -> Double
roundTo value decimals =
  let safe = ensureFinite value 0
      factor = 10 ** fromIntegral (max 0 decimals)
  in fromIntegral (round (safe * factor)) / factor

-- | Floor to specified decimal places
floorTo :: Double -> Int -> Double
floorTo value decimals =
  let safe = ensureFinite value 0
      factor = 10 ** fromIntegral (max 0 decimals)
  in fromIntegral (floor (safe * factor)) / factor

-- | Ceil to specified decimal places
ceilTo :: Double -> Int -> Double
ceilTo value decimals =
  let safe = ensureFinite value 0
      factor = 10 ** fromIntegral (max 0 decimals)
  in fromIntegral (ceiling (safe * factor)) / factor

-- | Snap value to nearest multiple of step
snapTo :: Double -> Double -> Double
snapTo value step
  | step == 0 = ensureFinite value 0
  | otherwise = let safe = ensureFinite value 0
                    safeStep = ensureFinite step 1
                in fromIntegral (round (safe / safeStep)) * safeStep

-- ════════════════════════════════════════════════════════════════════════════
--                                                        // range // utilities
-- ════════════════════════════════════════════════════════════════════════════

-- | Check if value is in range [min, max] inclusive
inRange :: Double -> Double -> Double -> Bool
inRange value min max =
  let safe = ensureFinite value (min - 1)  -- Default outside range
  in safe >= min && safe <= max

-- | Wrap value to range [min, max)
wrapToRange :: Double -> Double -> Double -> Double
wrapToRange value min max =
  let safe = ensureFinite value min
      range = max - min
  in if range == 0
       then min
       else min + safeMod (safe - min) range

-- | Ping-pong value between min and max
pingPong :: Double -> Double -> Double -> Double
pingPong value min max =
  let safe = ensureFinite value min
      range = max - min
  in if range == 0
       then min
       else let wrapped = safeMod (safe - min) (range * 2)
            in if wrapped < range
                 then min + wrapped
                 else max - (wrapped - range)
