{-# LANGUAGE StrictData #-}

{-|
Module      : Lattice.Utils.ArrayUtils
Description : Array utility functions
Copyright   : (c) Lattice, 2026
License     : MIT

Common array operations used throughout the codebase.
All functions handle edge cases safely.

Source: leancomfy/lean/Lattice/Utils/ArrayUtils.lean
-}

module Lattice.Utils.ArrayUtils
  ( -- * Basic Operations
    clamp
  , lerp
  , mapRange
    -- * Array Statistics
  , mean
  , maxList
  , minList
  , normalize
    -- * Safe Versions
  , clampFinite
  , lerpFinite
  , mapRangeFinite
  , meanFinite
  , normalizeFinite
    -- * Additional Utilities
  , sumList
  , productList
  , variance
  , stdDev
  , countWhere
  , findIndex'
  , unique
  , zipWith'
  , range
  ) where

import Data.List (nub)
import Data.Vector (Vector)
import qualified Data.Vector as V
import Lattice.Primitives

--------------------------------------------------------------------------------
-- Helper
--------------------------------------------------------------------------------

-- | Check if Double is finite
isFiniteDouble :: Double -> Bool
isFiniteDouble x = not (isNaN x) && not (isInfinite x)

--------------------------------------------------------------------------------
-- Basic Operations
--------------------------------------------------------------------------------

-- | Clamp a value to a range
clamp :: Double -> Double -> Double -> Double
clamp minVal maxVal value = max minVal (min maxVal value)

-- | Linear interpolation between two values
lerp :: Double -> Double -> Double -> Double
lerp a b t = a + (b - a) * t

-- | Map a value from one range to another
mapRange :: Double -> Double -> Double -> Double -> Double -> Double
mapRange value inMin inMax outMin outMax
  | range' == 0 = outMin
  | otherwise = outMin + normalized * (outMax - outMin)
  where
    range' = inMax - inMin
    normalized = (value - inMin) / range'

--------------------------------------------------------------------------------
-- Array Statistics
--------------------------------------------------------------------------------

-- | Calculate the mean of a vector
mean :: Vector Double -> Double
mean values
  | V.null values = 0
  | otherwise = V.sum values / fromIntegral (V.length values)

-- | Find maximum value in vector
maxList :: Double -> Vector Double -> Double
maxList def values
  | V.null values = def
  | otherwise = V.maximum values

-- | Find minimum value in vector
minList :: Double -> Vector Double -> Double
minList def values
  | V.null values = def
  | otherwise = V.minimum values

-- | Normalize a vector to [0, 1] range
normalize :: Vector Double -> Maybe Double -> Vector Double
normalize values maxValueOpt =
  let maxVal = case maxValueOpt of
        Just m -> m
        Nothing -> maxList 0 values
      safeMax = if isFiniteDouble maxVal && maxVal > 0 then maxVal else 0.0001
  in V.map (/ safeMax) values

--------------------------------------------------------------------------------
-- Safe Versions with Refined Types
--------------------------------------------------------------------------------

-- | Clamp a finite value to a range
clampFinite :: FiniteFloat -> FiniteFloat -> FiniteFloat -> FiniteFloat
clampFinite (FiniteFloat minVal) (FiniteFloat maxVal) (FiniteFloat value)
  | value < minVal = FiniteFloat minVal
  | value > maxVal = FiniteFloat maxVal
  | otherwise = FiniteFloat value

-- | Linear interpolation with finite floats and unit t
lerpFinite :: FiniteFloat -> FiniteFloat -> UnitFloat -> FiniteFloat
lerpFinite (FiniteFloat a) (FiniteFloat b) (UnitFloat t)
  | isFiniteDouble result = FiniteFloat result
  | otherwise = FiniteFloat a
  where result = a + (b - a) * t

-- | Map a finite value from one range to another
mapRangeFinite :: FiniteFloat -> FiniteFloat -> FiniteFloat -> FiniteFloat -> FiniteFloat -> FiniteFloat
mapRangeFinite (FiniteFloat value) (FiniteFloat inMin) (FiniteFloat inMax) (FiniteFloat outMin) (FiniteFloat outMax)
  | range' == 0 = FiniteFloat outMin
  | isFiniteDouble result = FiniteFloat result
  | otherwise = FiniteFloat outMin
  where
    range' = inMax - inMin
    normalized = (value - inMin) / range'
    result = outMin + normalized * (outMax - outMin)

-- | Calculate the mean of finite floats
meanFinite :: Vector FiniteFloat -> FiniteFloat
meanFinite values
  | V.null values = FiniteFloat 0
  | isFiniteDouble result = FiniteFloat result
  | otherwise = FiniteFloat 0
  where
    sumVal = V.sum $ V.map (\(FiniteFloat x) -> x) values
    result = sumVal / fromIntegral (V.length values)

-- | Normalize finite float vector to [0, 1]
normalizeFinite :: Vector FiniteFloat -> Vector UnitFloat
normalizeFinite values =
  let maxVal = V.maximum $ V.map (\(FiniteFloat x) -> x) values
      safeMax = if maxVal > 0 then maxVal else 0.0001
  in V.map (\(FiniteFloat x) -> UnitFloat $ max 0 (min 1 (x / safeMax))) values

--------------------------------------------------------------------------------
-- Additional Utilities
--------------------------------------------------------------------------------

-- | Sum of a vector
sumList :: Vector Double -> Double
sumList = V.sum

-- | Product of a vector
productList :: Vector Double -> Double
productList = V.product

-- | Variance of a vector
variance :: Vector Double -> Double
variance values
  | V.null values = 0
  | otherwise = mean $ V.map (\v -> (v - m) * (v - m)) values
  where m = mean values

-- | Standard deviation of a vector
stdDev :: Vector Double -> Double
stdDev = sqrt . variance

-- | Count items satisfying predicate
countWhere :: (a -> Bool) -> Vector a -> Int
countWhere pred' = V.length . V.filter pred'

-- | Find index of first item satisfying predicate
findIndex' :: (a -> Bool) -> Vector a -> Maybe Int
findIndex' = V.findIndex

-- | Remove duplicates (keeps first occurrence)
unique :: Eq a => [a] -> [a]
unique = nub

-- | Zip two vectors with function
zipWith' :: (a -> b -> c) -> Vector a -> Vector b -> Vector c
zipWith' = V.zipWith

-- | Create range of integers
range :: Int -> Int -> [Int]
range start endVal
  | start >= endVal = []
  | otherwise = [start .. endVal - 1]
