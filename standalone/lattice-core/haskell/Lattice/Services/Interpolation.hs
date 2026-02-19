{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}

{-|
Module      : Lattice.Services.Interpolation
Description : Pure interpolation functions
Copyright   : (c) Lattice, 2026
License     : MIT

Pure math functions for keyframe interpolation.
Handles bezier curves, linear interpolation, and color blending.

Source: ui/src/services/interpolation.ts (pure math portions)
-}

module Lattice.Services.Interpolation
  ( -- * Types
    Vec2(..)
  , Vec3(..)
  , Color(..)
  , EasingPreset(..)
    -- * Linear Interpolation
  , lerp, safeLerp, lerpVec2, lerpVec3, lerpColor
    -- * Bezier Curves
  , bezierPoint, bezierDerivative, solveBezierX, cubicBezierEasing
    -- * Color
  , colorFromHex6, normalizeHex, colorToHex
    -- * Easing Presets
  , easeLinear, easeIn, easeOut, easeInOut, easeOutBack
  , applyEasingPreset
    -- * Keyframe Search
  , findKeyframeIndex
  ) where

import GHC.Generics (Generic)
import Data.Char (digitToInt, intToDigit, isHexDigit, toLower)
import Data.Vector (Vector)
import qualified Data.Vector as V
import Text.Printf (printf)

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | 2D vector
data Vec2 = Vec2
  { vec2X :: Double
  , vec2Y :: Double
  } deriving stock (Eq, Show, Generic)

-- | 3D vector
data Vec3 = Vec3
  { vec3X :: Double
  , vec3Y :: Double
  , vec3Z :: Double
  } deriving stock (Eq, Show, Generic)

-- | RGB color with components 0-255
data Color = Color
  { colorR :: Double
  , colorG :: Double
  , colorB :: Double
  , colorA :: Double  -- Alpha, 0-255
  } deriving stock (Eq, Show, Generic)

-- | Easing preset with normalized 0-1 control points
data EasingPreset = EasingPreset
  { epOutX :: Double
  , epOutY :: Double
  , epInX :: Double
  , epInY :: Double
  } deriving stock (Eq, Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Linear Interpolation
-- ────────────────────────────────────────────────────────────────────────────

-- | Linear interpolation between two numbers
lerp :: Double -> Double -> Double -> Double
lerp a b t = a + (b - a) * t

-- | Safe linear interpolation (handles extreme values)
safeLerp :: Double -> Double -> Double -> Double
safeLerp a b t =
  let result = lerp a b t
  in if isNaN result || isInfinite result
     then if t < 0.5 then a else b
     else result

-- | Interpolate Vec2
lerpVec2 :: Vec2 -> Vec2 -> Double -> Vec2
lerpVec2 a b t = Vec2 (safeLerp (vec2X a) (vec2X b) t)
                      (safeLerp (vec2Y a) (vec2Y b) t)

-- | Interpolate Vec3
lerpVec3 :: Vec3 -> Vec3 -> Double -> Vec3
lerpVec3 a b t = Vec3 (safeLerp (vec3X a) (vec3X b) t)
                      (safeLerp (vec3Y a) (vec3Y b) t)
                      (safeLerp (vec3Z a) (vec3Z b) t)

-- | Interpolate between two colors
lerpColor :: Color -> Color -> Double -> Color
lerpColor c1 c2 t = Color
  (fromIntegral (round (safeLerp (colorR c1) (colorR c2) t) :: Int))
  (fromIntegral (round (safeLerp (colorG c1) (colorG c2) t) :: Int))
  (fromIntegral (round (safeLerp (colorB c1) (colorB c2) t) :: Int))
  (fromIntegral (round (safeLerp (colorA c1) (colorA c2) t) :: Int))

-- ────────────────────────────────────────────────────────────────────────────
-- Bezier Curve Math
-- ────────────────────────────────────────────────────────────────────────────

-- | Cubic bezier point calculation
bezierPoint :: Double -> Double -> Double -> Double -> Double -> Double
bezierPoint t p0 p1 p2 p3 =
  let mt = 1 - t
  in mt * mt * mt * p0 +
     3 * mt * mt * t * p1 +
     3 * mt * t * t * p2 +
     t * t * t * p3

-- | Cubic bezier derivative
bezierDerivative :: Double -> Double -> Double -> Double -> Double -> Double
bezierDerivative t p0 p1 p2 p3 =
  let mt = 1 - t
  in 3 * mt * mt * (p1 - p0) +
     6 * mt * t * (p2 - p1) +
     3 * t * t * (p3 - p2)

-- | Find t for given x using Newton-Raphson iteration
solveBezierX :: Double -> Double -> Double -> Int -> Double
solveBezierX x x1 x2 maxIter = go x maxIter
  where
    epsilon = 1e-6
    go guessT 0 = guessT
    go guessT n =
      let currentX = bezierPoint guessT 0 x1 x2 1
          err = currentX - x
      in if abs err < epsilon then guessT
         else let slope = bezierDerivative guessT 0 x1 x2 1
              in if abs slope < epsilon then guessT
                 else let newT = guessT - err / slope
                          clampedT = max 0 (min 1 newT)
                      in go clampedT (n - 1)

-- | Cubic bezier easing
cubicBezierEasing :: Double -> Double -> Double -> Double -> Double -> Double
cubicBezierEasing t x1 y1 x2 y2 =
  let solvedT = solveBezierX t x1 x2 8
  in bezierPoint solvedT 0 y1 y2 1

-- ────────────────────────────────────────────────────────────────────────────
-- Color Parsing
-- ────────────────────────────────────────────────────────────────────────────

-- | Parse hex digit to number
hexDigitToInt :: Char -> Int
hexDigitToInt c
  | isHexDigit c = digitToInt (toLower c)
  | otherwise = 0

-- | Parse two hex chars to byte value
parseHexByte :: Char -> Char -> Double
parseHexByte h1 h2 =
  fromIntegral (hexDigitToInt h1 * 16 + hexDigitToInt h2)

-- | Create color from 6+ digit hex string (without #)
colorFromHex6 :: String -> Color
colorFromHex6 s
  | length s < 6 = Color 0 0 0 255
  | otherwise =
      let r = parseHexByte (s !! 0) (s !! 1)
          g = parseHexByte (s !! 2) (s !! 3)
          b = parseHexByte (s !! 4) (s !! 5)
          a = if length s >= 8
              then parseHexByte (s !! 6) (s !! 7)
              else 255
      in Color r g b a

-- | Expand 3/4 char hex to 6/8 char
expandShortHex :: String -> String
expandShortHex [r, g, b] = [r, r, g, g, b, b]
expandShortHex [r, g, b, a] = [r, r, g, g, b, b, a, a]
expandShortHex s = s

-- | Normalize hex color string
normalizeHex :: String -> String
normalizeHex hex =
  let s = if take 1 hex == "#" then drop 1 hex else hex
  in if length s == 3 || length s == 4
     then expandShortHex s
     else s

-- | Convert color to hex string
colorToHex :: Color -> Bool -> String
colorToHex (Color r g b a) includeAlpha =
  let clamp' x = max 0 (min 255 (round x :: Int))
      rgb = printf "#%02x%02x%02x" (clamp' r) (clamp' g) (clamp' b)
  in if includeAlpha
     then rgb ++ printf "%02x" (clamp' a)
     else rgb

-- ────────────────────────────────────────────────────────────────────────────
-- Easing Presets
-- ────────────────────────────────────────────────────────────────────────────

-- | Linear easing
easeLinear :: EasingPreset
easeLinear = EasingPreset 0.33 0.33 0.33 0.33

-- | Ease in (slow start)
easeIn :: EasingPreset
easeIn = EasingPreset 0.42 0 0.33 0.33

-- | Ease out (slow end)
easeOut :: EasingPreset
easeOut = EasingPreset 0.33 0.33 0.58 1

-- | Ease in-out
easeInOut :: EasingPreset
easeInOut = EasingPreset 0.42 0 0.58 1

-- | Ease out with overshoot
easeOutBack :: EasingPreset
easeOutBack = EasingPreset 0.33 0.33 0.34 1.56

-- | Apply easing preset to a ratio (0-1)
applyEasingPreset :: Double -> EasingPreset -> Double
applyEasingPreset ratio preset =
  let t = max 0 (min 1 ratio)
      x1 = epOutX preset
      y1 = epOutY preset
      x2 = 1 - epInX preset
      y2 = 1 - epInY preset
  in cubicBezierEasing t x1 y1 x2 y2

-- ────────────────────────────────────────────────────────────────────────────
-- Binary Search for Keyframes
-- ────────────────────────────────────────────────────────────────────────────

-- | Binary search to find index where arr[i] <= value < arr[i+1]
findKeyframeIndex :: Vector Double -> Double -> Int
findKeyframeIndex frames frame
  | V.length frames < 2 = 0
  | otherwise = binarySearch 0 (V.length frames - 2)
  where
    binarySearch low high
      | low > high = min low (V.length frames - 2)
      | otherwise =
          let mid = (low + high) `div` 2
              midFrame = frames V.! mid
              nextFrame = frames V.! (mid + 1)
          in if frame >= midFrame && frame <= nextFrame
             then mid
             else if frame < midFrame
             then if mid == 0 then 0 else binarySearch low (mid - 1)
             else binarySearch (mid + 1) high
