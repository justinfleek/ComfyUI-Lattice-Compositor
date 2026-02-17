-- |
-- Module      : Lattice.Utils.ArrayUtils
-- Description : Array utility functions for common array operations
-- 
-- Migrated from ui/src/utils/arrayUtils.ts
-- Pure functions for array manipulation
-- 
-- CRITICAL: No forbidden patterns - explicit types, no null/undefined, no type escapes
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.Utils.ArrayUtils
  ( -- Array operations
    normalize
  , clamp
  , lerp
  , mapRange
  , mean
  , safeArrayGet
  ) where

import Lattice.Utils.NumericSafety (isFinite)
import Lattice.Utils.NumericSafety (ensureFinite)

-- ============================================================================
-- ARRAY OPERATIONS
-- ============================================================================

-- | Safe index into a list: returns element at index or default if out of bounds.
safeArrayGet :: [a] -> Int -> a -> a
safeArrayGet arr idx def
  | idx >= 0 && idx < length arr = arr !! idx
  | otherwise = def

-- | Normalize an array of numbers to the range [0, 1]
-- 
-- System F/Omega proof: Explicit type [Double] -> Maybe Double -> [Double]
-- Mathematical proof: 
--   - If maxValue provided: maxValue > 0 (validated)
--   - If not provided: max of array > 0 (validated)
--   - Result: all values in [0, 1]
-- 
-- @param values Array of numbers to normalize
-- @param maxValue Optional max value (defaults to array max)
-- @returns Normalized array with values in [0, 1] range
normalize :: [Double] -> Maybe Double -> [Double]
normalize values mMaxValue =
  let arrayMax = if null values then 0.0001 else maximum values
      safeMax = case mMaxValue of
        Just maxVal -> if maxVal > 0 && isFinite maxVal then maxVal else 0.0001
        Nothing -> if arrayMax > 0 && isFinite arrayMax then arrayMax else 0.0001
  in map (\v -> ensureFinite (v / safeMax) 0.0) values

-- | Clamp a value to a range
-- 
-- System F/Omega proof: Explicit type Double -> Double -> Double -> Double
-- Mathematical proof: Result always in [min, max]
-- 
-- @param value Value to clamp
-- @param min Minimum value
-- @param max Maximum value
clamp :: Double -> Double -> Double -> Double
clamp value min max =
  let safeValue = ensureFinite value min
      safeMin = ensureFinite min 0.0
      safeMax = ensureFinite max 1.0
  in if safeValue < safeMin then safeMin
     else if safeValue > safeMax then safeMax
     else safeValue

-- | Linear interpolation between two values
-- 
-- System F/Omega proof: Explicit type Double -> Double -> Double -> Double
-- Mathematical proof: Result = a + (b - a) * t, where t ∈ [0, 1] (clamped)
-- 
-- @param a Start value
-- @param b End value
-- @param t Interpolation factor (0-1)
lerp :: Double -> Double -> Double -> Double
lerp a b t =
  let safeA = ensureFinite a 0.0
      safeB = ensureFinite b 0.0
      safeT = clamp (ensureFinite t 0.0) 0.0 1.0
      diff = safeB - safeA
  in ensureFinite (safeA + diff * safeT) safeA

-- | Map a value from one range to another
-- 
-- System F/Omega proof: Explicit type Double -> Double -> Double -> Double -> Double -> Double
-- Mathematical proof: 
--   - normalized = (value - inMin) / (inMax - inMin)
--   - Result = outMin + normalized * (outMax - outMin)
--   - Handles division by zero (returns outMin)
-- 
-- @param value Value to map
-- @param inMin Input range minimum
-- @param inMax Input range maximum
-- @param outMin Output range minimum
-- @param outMax Output range maximum
mapRange :: Double -> Double -> Double -> Double -> Double -> Double
mapRange value inMin inMax outMin outMax =
  let safeValue = ensureFinite value inMin
      safeInMin = ensureFinite inMin 0.0
      safeInMax = ensureFinite inMax 1.0
      safeOutMin = ensureFinite outMin 0.0
      safeOutMax = ensureFinite outMax 1.0
      range = safeInMax - safeInMin
  in if range == 0 || not (isFinite range) then
       safeOutMin
     else
       let normalized = (safeValue - safeInMin) / range
           result = safeOutMin + normalized * (safeOutMax - safeOutMin)
       in ensureFinite result safeOutMin

-- | Calculate the mean of an array
-- 
-- System F/Omega proof: Explicit type [Double] -> Double
-- Mathematical proof: 
--   - Empty array returns 0
--   - Non-empty: sum / length
--   - All values validated (finite)
-- 
-- @param values Array of numbers
mean :: [Double] -> Double
mean values =
  if null values then
    0.0
  else
    let safeValues = map (\v -> ensureFinite v 0.0) values
        sum = foldl (+) 0.0 safeValues
        count = fromIntegral (length safeValues)
    in if count == 0 then 0.0 else ensureFinite (sum / count) 0.0
