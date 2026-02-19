-- | Lattice.Services.Expressions.VectorMath - Vector math for expressions
-- |
-- | Vector operations for expression evaluation.
-- | Includes add, sub, mul, div, normalize, dot, cross, length, clamp.
-- |
-- | Source: ui/src/services/expressions/vectorMath.ts

module Lattice.Services.Expressions.VectorMath
  ( -- * Vector Operations
    vectorAdd, vectorSub
  , scalarMulVec, vecMulScalar, vecMulVec
  , scalarDivVec, vecDivScalar, vecDivVec
  , vectorNormalize
  , vectorDot, vectorCross
  , vectorMagnitude, vectorDistance
  , vectorClampScalar, vectorClampVec
    -- * Noise
  , noise1D, noise
    -- * Degree Trigonometry
  , degToRad, radToDeg
  , sinDeg, cosDeg, tanDeg
  , asinDeg, acosDeg, atanDeg, atan2Deg
    -- * Helpers
  , finiteOr, getOr, safeDiv, clampScalar
  ) where

import Prelude
import Data.Array (length, (!!), (..), mapWithIndex)
import Data.Array as Array
import Data.Foldable (foldl)
import Data.Int (floor, toNumber)
import Data.Maybe (Maybe(..), fromMaybe)
import Global (isNaN, isFinite) as Global
import Math (acos, asin, atan, atan2, cos, pi, sin, sqrt, tan) as Math

-- ────────────────────────────────────────────────────────────────────────────
-- Helper Functions
-- ────────────────────────────────────────────────────────────────────────────

-- | Check if finite
isFiniteNum :: Number -> Boolean
isFiniteNum x = Global.isFinite x && not (Global.isNaN x)

-- | Get value or default if not finite
finiteOr :: Number -> Number -> Number
finiteOr x def = if isFiniteNum x then x else def

-- | Array get with default
getOr :: Array Number -> Int -> Number -> Number
getOr arr i def = case arr !! i of
  Just x -> finiteOr x def
  Nothing -> def

-- ────────────────────────────────────────────────────────────────────────────
-- Vector Addition
-- ────────────────────────────────────────────────────────────────────────────

-- | Vector addition: add(vec1, vec2)
vectorAdd :: Array Number -> Array Number -> Array Number
vectorAdd a b =
  let maxLen = max (length a) (length b)
  in map (\i -> getOr a i 0.0 + getOr b i 0.0) (0 .. (maxLen - 1))

-- ────────────────────────────────────────────────────────────────────────────
-- Vector Subtraction
-- ────────────────────────────────────────────────────────────────────────────

-- | Vector subtraction: sub(vec1, vec2)
vectorSub :: Array Number -> Array Number -> Array Number
vectorSub a b =
  let maxLen = max (length a) (length b)
  in map (\i -> getOr a i 0.0 - getOr b i 0.0) (0 .. (maxLen - 1))

-- ────────────────────────────────────────────────────────────────────────────
-- Vector Multiplication
-- ────────────────────────────────────────────────────────────────────────────

-- | Scalar-vector multiplication
scalarMulVec :: Number -> Array Number -> Array Number
scalarMulVec s = map (_ * s)

-- | Vector-scalar multiplication
vecMulScalar :: Array Number -> Number -> Array Number
vecMulScalar v s = map (_ * s) v

-- | Component-wise vector multiplication
vecMulVec :: Array Number -> Array Number -> Array Number
vecMulVec a b =
  let maxLen = max (length a) (length b)
  in map (\i -> getOr a i 0.0 * getOr b i 0.0) (0 .. (maxLen - 1))

-- ────────────────────────────────────────────────────────────────────────────
-- Vector Division
-- ────────────────────────────────────────────────────────────────────────────

-- | Safe division (returns num if denom is 0)
safeDiv :: Number -> Number -> Number
safeDiv num denom = if denom == 0.0 then num else num / denom

-- | Scalar-vector division
scalarDivVec :: Number -> Array Number -> Array Number
scalarDivVec s = map \x -> safeDiv s (if x == 0.0 then 1.0 else x)

-- | Vector-scalar division
vecDivScalar :: Array Number -> Number -> Array Number
vecDivScalar v s =
  let divisor = if s == 0.0 then 1.0 else s
  in map (_ / divisor) v

-- | Component-wise vector division
vecDivVec :: Array Number -> Array Number -> Array Number
vecDivVec a b =
  let maxLen = max (length a) (length b)
  in map (\i ->
       let aVal = getOr a i 0.0
           bVal = getOr b i 1.0  -- Default to 1 to avoid division by zero
       in aVal / bVal) (0 .. (maxLen - 1))

-- ────────────────────────────────────────────────────────────────────────────
-- Vector Normalization
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate vector magnitude
magnitude :: Array Number -> Number
magnitude v = Math.sqrt (foldl (\acc x -> acc + x * x) 0.0 v)

-- | Normalize vector to unit length
vectorNormalize :: Array Number -> Array Number
vectorNormalize v =
  let len = magnitude v
  in if len == 0.0 then map (const 0.0) v
     else map (_ / len) v

-- ────────────────────────────────────────────────────────────────────────────
-- Dot Product
-- ────────────────────────────────────────────────────────────────────────────

-- | Dot product of two vectors
vectorDot :: Array Number -> Array Number -> Number
vectorDot a b =
  let minLen = min (length a) (length b)
  in foldl (+) 0.0 (map (\i -> getOr a i 0.0 * getOr b i 0.0) (0 .. (minLen - 1)))

-- ────────────────────────────────────────────────────────────────────────────
-- Cross Product
-- ────────────────────────────────────────────────────────────────────────────

-- | Cross product of two 3D vectors
vectorCross :: Array Number -> Array Number -> Array Number
vectorCross a b =
  let ax = getOr a 0 0.0
      ay = getOr a 1 0.0
      az = getOr a 2 0.0
      bx = getOr b 0 0.0
      by = getOr b 1 0.0
      bz = getOr b 2 0.0
  in [ay * bz - az * by, az * bx - ax * bz, ax * by - ay * bx]

-- ────────────────────────────────────────────────────────────────────────────
-- Vector Length / Distance
-- ────────────────────────────────────────────────────────────────────────────

-- | Vector magnitude (length of single vector)
vectorMagnitude :: Array Number -> Number
vectorMagnitude = magnitude

-- | Distance between two points
vectorDistance :: Array Number -> Array Number -> Number
vectorDistance a b =
  let maxLen = max (length a) (length b)
      sumSq = foldl (\acc i ->
                let diff = getOr a i 0.0 - getOr b i 0.0
                in acc + diff * diff) 0.0 (0 .. (maxLen - 1))
  in Math.sqrt sumSq

-- ────────────────────────────────────────────────────────────────────────────
-- Clamp
-- ────────────────────────────────────────────────────────────────────────────

-- | Clamp scalar value
clampScalar :: Number -> Number -> Number -> Number
clampScalar v minVal maxVal = max minVal (min maxVal v)

-- | Clamp vector with scalar bounds
vectorClampScalar :: Array Number -> Number -> Number -> Array Number
vectorClampScalar v minVal maxVal = map (\x -> clampScalar x minVal maxVal) v

-- | Clamp vector with vector bounds
vectorClampVec :: Array Number -> Array Number -> Array Number -> Array Number
vectorClampVec v minBounds maxBounds =
  mapWithIndex (\i x ->
    let minVal = case minBounds !! i of
                   Just m -> if isFiniteNum m then m else (-1.0 / 0.0)
                   Nothing -> (-1.0 / 0.0)
        maxVal = case maxBounds !! i of
                   Just m -> if isFiniteNum m then m else (1.0 / 0.0)
                   Nothing -> (1.0 / 0.0)
    in clampScalar x minVal maxVal) v

-- ────────────────────────────────────────────────────────────────────────────
-- Noise
-- ────────────────────────────────────────────────────────────────────────────

-- | 1D noise (Perlin-like)
noise1D :: Number -> Number
noise1D x =
  let n = Math.sin (x * 12.9898) * 43758.5453
  in (n - toNumber (floor n)) * 2.0 - 1.0

-- | Multi-dimensional noise (up to 3D)
noise :: Array Number -> Number
noise v =
  let x = getOr v 0 0.0
      y = getOr v 1 0.0
      z = getOr v 2 0.0
      n = Math.sin (x * 12.9898 + y * 78.233 + z * 37.719) * 43758.5453
  in (n - toNumber (floor n)) * 2.0 - 1.0

-- ────────────────────────────────────────────────────────────────────────────
-- Degree Trigonometry
-- ────────────────────────────────────────────────────────────────────────────

-- | Convert degrees to radians
degToRad :: Number -> Number
degToRad deg = deg * Math.pi / 180.0

-- | Convert radians to degrees
radToDeg :: Number -> Number
radToDeg rad = rad * 180.0 / Math.pi

-- | Sine in degrees
sinDeg :: Number -> Number
sinDeg = Math.sin <<< degToRad

-- | Cosine in degrees
cosDeg :: Number -> Number
cosDeg = Math.cos <<< degToRad

-- | Tangent in degrees
tanDeg :: Number -> Number
tanDeg = Math.tan <<< degToRad

-- | Arc sine returning degrees
asinDeg :: Number -> Number
asinDeg = radToDeg <<< Math.asin

-- | Arc cosine returning degrees
acosDeg :: Number -> Number
acosDeg = radToDeg <<< Math.acos

-- | Arc tangent returning degrees
atanDeg :: Number -> Number
atanDeg = radToDeg <<< Math.atan

-- | Two-argument arc tangent returning degrees
atan2Deg :: Number -> Number -> Number
atan2Deg y x = radToDeg (Math.atan2 y x)
