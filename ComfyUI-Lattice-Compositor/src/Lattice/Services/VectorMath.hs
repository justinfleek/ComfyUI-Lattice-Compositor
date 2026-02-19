-- |
-- Module      : Lattice.Services.VectorMath
-- Description : Pure vector math functions for expression evaluation
-- 
-- Migrated from ui/src/services/expressions/vectorMath.ts
-- Pure vector operations: add, sub, mul, div, normalize, dot, cross, length, clampD
-- Also includes noise function and degree-based trigonometry helpers
--

module Lattice.Services.VectorMath
  ( -- Vector operations
    vectorAdd
  , vectorSub
  , vectorMul
  , vectorDiv
  , vectorNormalize
  , vectorDot
  , vectorCross
  , vectorLength
  , vectorClamp
  -- Noise function
  , noise
  -- Degree-based trigonometry
  , degreeSin
  , degreeCos
  , degreeTan
  , degreeAsin
  , degreeAcos
  , degreeAtan
  , degreeAtan2
  ) where

import Lattice.Utils.NumericSafety (isFinite)
import Lattice.Utils.NumericSafety
  ( ensureFiniteD
  , safeSqrtD
  )
import Lattice.Utils.ArrayUtils
  ( safeArrayGet
  )

-- ============================================================================
-- VECTOR OPERATIONS
-- ============================================================================

-- | Get array element safely, defaulting to 0 if out of bounds or invalid
safeGet :: [Double] -> Int -> Double
safeGet arr idx =
  let val = safeArrayGet arr idx 0.0
  in if isFinite val then val else 0.0

-- | Vector addition
-- Pure function: same inputs → same outputs
vectorAdd :: [Double] -> [Double] -> [Double]
vectorAdd a b =
  let maxLen = max (length a) (length b)
  in [safeGet a i + safeGet b i | i <- [0 .. maxLen - 1]]

-- | Vector subtraction
-- Pure function: same inputs → same outputs
vectorSub :: [Double] -> [Double] -> [Double]
vectorSub a b =
  let maxLen = max (length a) (length b)
  in [safeGet a i - safeGet b i | i <- [0 .. maxLen - 1]]

-- | Vector multiplication (component-wise or scalar)
-- Pure function: same inputs → same outputs
vectorMul :: Either Double [Double] -> Either Double [Double] -> [Double]
vectorMul (Left scalar) (Right vec) = map (* scalar) vec
vectorMul (Right vec) (Left scalar) = map (* scalar) vec
vectorMul (Right a) (Right b) =
  let maxLen = max (length a) (length b)
  in [safeGet a i * safeGet b i | i <- [0 .. maxLen - 1]]
vectorMul _ _ = [0.0]

-- | Vector division (component-wise or scalar)
-- Pure function: same inputs → same outputs
vectorDiv :: Either Double [Double] -> Either Double [Double] -> [Double]
vectorDiv (Left scalar) (Right vec) = map (\v -> scalar / if v /= 0 then v else 1.0) vec
vectorDiv (Right vec) (Left scalar) = map (\v -> v / if scalar /= 0 then scalar else 1.0) vec
vectorDiv (Right a) (Right b) =
  let maxLen = max (length a) (length b)
  in [safeGet a i / if safeGet b i /= 0 then safeGet b i else 1.0 | i <- [0 .. maxLen - 1]]
vectorDiv _ _ = [0.0]

-- | Normalize vector to unit length
-- Pure function: same inputs → same outputs
vectorNormalize :: [Double] -> [Double]
vectorNormalize vec
  | null vec = vec
  | otherwise =
      let len = safeSqrtD (sum (map (\v -> v * v) vec)) 0.0
      in if len == 0 then map (const 0.0) vec else map (/ len) vec

-- | Dot product of two vectors
-- Pure function: same inputs → same outputs
vectorDot :: [Double] -> [Double] -> Double
vectorDot a b =
  let maxLen = min (length a) (length b)
  in sum [safeGet a i * safeGet b i | i <- [0 .. maxLen - 1]]

-- | Cross product of two 3D vectors
-- Pure function: same inputs → same outputs
vectorCross :: [Double] -> [Double] -> [Double]
vectorCross a b =
  let ax = safeGet a 0
      ay = safeGet a 1
      az = safeGet a 2
      bx = safeGet b 0
      by = safeGet b 1
      bz = safeGet b 2
  in [ay * bz - az * by, az * bx - ax * bz, ax * by - ay * bx]

-- | Calculate vector length/magnitude or distance between two points
-- Pure function: same inputs → same outputs
vectorLength :: [Double] -> Maybe [Double] -> Double
vectorLength a Nothing = safeSqrtD (sum (map (\v -> v * v) a)) 0.0
vectorLength a (Just b) =
  let maxLen = max (length a) (length b)
      sumSq = sum [let diff = safeGet a i - safeGet b i in diff * diff | i <- [0 .. maxLen - 1]]
  in safeSqrtD sumSq 0.0

-- | Clamp vector components
-- Pure function: same inputs → same outputs
vectorClamp :: [Double] -> Either Double [Double] -> Either Double [Double] -> [Double]
vectorClamp vec (Left minVal) (Left maxVal) =
  map (\v -> max minVal (min maxVal v)) vec
vectorClamp vec (Left minVal) (Right maxArr) =
  zipWith (\v maxV -> max minVal (min maxV v)) vec (maxArr ++ repeat (1/0))
vectorClamp vec (Right minArr) (Left maxVal) =
  zipWith (\v minV -> max minV (min maxVal v)) vec (minArr ++ repeat (-1/0))
vectorClamp vec (Right minArr) (Right maxArr) =
  zipWith3 (\v minV maxV -> max minV (min maxV v)) vec
    (minArr ++ repeat (-1/0))
    (maxArr ++ repeat (1/0))

-- ============================================================================
-- NOISE FUNCTION
-- ============================================================================

-- | Noise function (Perlin-like) for expressions
-- Pure function: deterministic pseudo-random based on input
-- Uses deterministic hash function, not true randomness
noise :: Either Double [Double] -> Double
noise (Left val) =
  let x = sin (val * 12.9898) * 43758.5453
  in (x - fromIntegral (floor x)) * 2 - 1
noise (Right vec) =
  let x = safeGet vec 0
      y = safeGet vec 1
      z = safeGet vec 2
      n = sin (x * 12.9898 + y * 78.233 + z * 37.719) * 43758.5453
  in (n - fromIntegral (floor n)) * 2 - 1

-- ============================================================================
-- DEGREE-BASED TRIGONOMETRY
-- ============================================================================

-- | Convert degrees to radians
degreesToRadians :: Double -> Double
degreesToRadians deg = deg * pi / 180.0

-- | Convert radians to degrees
radiansToDegrees :: Double -> Double
radiansToDegrees rad = rad * 180.0 / pi

-- | Sine with degree input
degreeSin :: Double -> Double
degreeSin = sin . degreesToRadians

-- | Cosine with degree input
degreeCos :: Double -> Double
degreeCos = cos . degreesToRadians

-- | Tangent with degree input
degreeTan :: Double -> Double
degreeTan = tan . degreesToRadians

-- | Arc sine with degree output
degreeAsin :: Double -> Double
degreeAsin = radiansToDegrees . asin

-- | Arc cosine with degree output
degreeAcos :: Double -> Double
degreeAcos = radiansToDegrees . acos

-- | Arc tangent with degree output
degreeAtan :: Double -> Double
degreeAtan = radiansToDegrees . atan

-- | Arc tangent 2 with degree output
degreeAtan2 :: Double -> Double -> Double
degreeAtan2 y x = radiansToDegrees (atan2 y x)
