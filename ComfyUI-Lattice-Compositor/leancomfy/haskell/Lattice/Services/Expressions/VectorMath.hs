{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Lattice.Services.Expressions.VectorMath
Description : Vector math for expressions
Copyright   : (c) Lattice, 2026
License     : MIT

Vector operations for expression evaluation.
Includes add, sub, mul, div, normalize, dot, cross, length, clamp.

Source: ui/src/services/expressions/vectorMath.ts
-}

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

import Data.Vector (Vector)
import qualified Data.Vector as V

--------------------------------------------------------------------------------
-- Helper Functions
--------------------------------------------------------------------------------

-- | Check if finite
isFiniteNum :: Double -> Bool
isFiniteNum x = not (isNaN x || isInfinite x)

-- | Get value or default if not finite
finiteOr :: Double -> Double -> Double
finiteOr x def = if isFiniteNum x then x else def

-- | Array get with default
getOr :: Vector Double -> Int -> Double -> Double
getOr arr i def = case arr V.!? i of
  Just x -> finiteOr x def
  Nothing -> def

--------------------------------------------------------------------------------
-- Vector Addition
--------------------------------------------------------------------------------

-- | Vector addition: add(vec1, vec2)
vectorAdd :: Vector Double -> Vector Double -> Vector Double
vectorAdd a b =
  let maxLen = max (V.length a) (V.length b)
  in V.generate maxLen $ \i ->
       getOr a i 0 + getOr b i 0

--------------------------------------------------------------------------------
-- Vector Subtraction
--------------------------------------------------------------------------------

-- | Vector subtraction: sub(vec1, vec2)
vectorSub :: Vector Double -> Vector Double -> Vector Double
vectorSub a b =
  let maxLen = max (V.length a) (V.length b)
  in V.generate maxLen $ \i ->
       getOr a i 0 - getOr b i 0

--------------------------------------------------------------------------------
-- Vector Multiplication
--------------------------------------------------------------------------------

-- | Scalar-vector multiplication
scalarMulVec :: Double -> Vector Double -> Vector Double
scalarMulVec s = V.map (* s)

-- | Vector-scalar multiplication
vecMulScalar :: Vector Double -> Double -> Vector Double
vecMulScalar v s = V.map (* s) v

-- | Component-wise vector multiplication
vecMulVec :: Vector Double -> Vector Double -> Vector Double
vecMulVec a b =
  let maxLen = max (V.length a) (V.length b)
  in V.generate maxLen $ \i ->
       getOr a i 0 * getOr b i 0

--------------------------------------------------------------------------------
-- Vector Division
--------------------------------------------------------------------------------

-- | Safe division (returns num if denom is 0)
safeDiv :: Double -> Double -> Double
safeDiv num denom = if denom == 0 then num else num / denom

-- | Scalar-vector division
scalarDivVec :: Double -> Vector Double -> Vector Double
scalarDivVec s = V.map $ \x -> safeDiv s (if x == 0 then 1 else x)

-- | Vector-scalar division
vecDivScalar :: Vector Double -> Double -> Vector Double
vecDivScalar v s =
  let divisor = if s == 0 then 1 else s
  in V.map (/ divisor) v

-- | Component-wise vector division
vecDivVec :: Vector Double -> Vector Double -> Vector Double
vecDivVec a b =
  let maxLen = max (V.length a) (V.length b)
  in V.generate maxLen $ \i ->
       let aVal = getOr a i 0
           bVal = getOr b i 1  -- Default to 1 to avoid division by zero
       in aVal / bVal

--------------------------------------------------------------------------------
-- Vector Normalization
--------------------------------------------------------------------------------

-- | Calculate vector magnitude
magnitude :: Vector Double -> Double
magnitude v = sqrt $ V.foldl' (\acc x -> acc + x * x) 0 v

-- | Normalize vector to unit length
vectorNormalize :: Vector Double -> Vector Double
vectorNormalize v =
  let len = magnitude v
  in if len == 0 then V.map (const 0) v
     else V.map (/ len) v

--------------------------------------------------------------------------------
-- Dot Product
--------------------------------------------------------------------------------

-- | Dot product of two vectors
vectorDot :: Vector Double -> Vector Double -> Double
vectorDot a b =
  let minLen = min (V.length a) (V.length b)
  in V.sum $ V.generate minLen $ \i ->
       getOr a i 0 * getOr b i 0

--------------------------------------------------------------------------------
-- Cross Product
--------------------------------------------------------------------------------

-- | Cross product of two 3D vectors
vectorCross :: Vector Double -> Vector Double -> Vector Double
vectorCross a b =
  let ax = getOr a 0 0
      ay = getOr a 1 0
      az = getOr a 2 0
      bx = getOr b 0 0
      by = getOr b 1 0
      bz = getOr b 2 0
  in V.fromList [ay * bz - az * by, az * bx - ax * bz, ax * by - ay * bx]

--------------------------------------------------------------------------------
-- Vector Length / Distance
--------------------------------------------------------------------------------

-- | Vector magnitude (length of single vector)
vectorMagnitude :: Vector Double -> Double
vectorMagnitude = magnitude

-- | Distance between two points
vectorDistance :: Vector Double -> Vector Double -> Double
vectorDistance a b =
  let maxLen = max (V.length a) (V.length b)
      sumSq = V.foldl' (\acc i ->
                let diff = getOr a i 0 - getOr b i 0
                in acc + diff * diff) 0 (V.enumFromN 0 maxLen)
  in sqrt sumSq

--------------------------------------------------------------------------------
-- Clamp
--------------------------------------------------------------------------------

-- | Clamp scalar value
clampScalar :: Double -> Double -> Double -> Double
clampScalar v minVal maxVal = max minVal (min maxVal v)

-- | Clamp vector with scalar bounds
vectorClampScalar :: Vector Double -> Double -> Double -> Vector Double
vectorClampScalar v minVal maxVal = V.map (\x -> clampScalar x minVal maxVal) v

-- | Clamp vector with vector bounds
vectorClampVec :: Vector Double -> Vector Double -> Vector Double -> Vector Double
vectorClampVec v minBounds maxBounds =
  V.imap (\i x ->
    let minVal = case minBounds V.!? i of
                   Just m -> if isFiniteNum m then m else (-1/0)
                   Nothing -> (-1/0)
        maxVal = case maxBounds V.!? i of
                   Just m -> if isFiniteNum m then m else (1/0)
                   Nothing -> (1/0)
    in clampScalar x minVal maxVal) v

--------------------------------------------------------------------------------
-- Noise
--------------------------------------------------------------------------------

-- | 1D noise (Perlin-like)
noise1D :: Double -> Double
noise1D x =
  let n = sin (x * 12.9898) * 43758.5453
  in (n - fromIntegral (floor n :: Int)) * 2 - 1

-- | Multi-dimensional noise (up to 3D)
noise :: Vector Double -> Double
noise v =
  let x = getOr v 0 0
      y = getOr v 1 0
      z = getOr v 2 0
      n = sin (x * 12.9898 + y * 78.233 + z * 37.719) * 43758.5453
  in (n - fromIntegral (floor n :: Int)) * 2 - 1

--------------------------------------------------------------------------------
-- Degree Trigonometry
--------------------------------------------------------------------------------

-- | Convert degrees to radians
degToRad :: Double -> Double
degToRad deg = deg * pi / 180

-- | Convert radians to degrees
radToDeg :: Double -> Double
radToDeg rad = rad * 180 / pi

-- | Sine in degrees
sinDeg :: Double -> Double
sinDeg = sin . degToRad

-- | Cosine in degrees
cosDeg :: Double -> Double
cosDeg = cos . degToRad

-- | Tangent in degrees
tanDeg :: Double -> Double
tanDeg = tan . degToRad

-- | Arc sine returning degrees
asinDeg :: Double -> Double
asinDeg = radToDeg . asin

-- | Arc cosine returning degrees
acosDeg :: Double -> Double
acosDeg = radToDeg . acos

-- | Arc tangent returning degrees
atanDeg :: Double -> Double
atanDeg = radToDeg . atan

-- | Two-argument arc tangent returning degrees
atan2Deg :: Double -> Double -> Double
atan2Deg y x = radToDeg (atan2 y x)
