-- | Lattice.Utils.ArrayUtils - Array utility functions
-- |
-- | Common array operations used throughout the codebase.
-- | All functions handle edge cases safely.
-- |
-- | Source: leancomfy/lean/Lattice/Utils/ArrayUtils.lean

module Lattice.Utils.ArrayUtils
  ( clamp
  , lerp
  , mapRange
  , mean
  , maxArray
  , minArray
  , normalize
  , clampFinite
  , lerpFinite
  , mapRangeFinite
  , meanFinite
  , normalizeFinite
  , sumArray
  , productArray
  , variance
  , stdDev
  , countWhere
  , findIndex'
  , unique
  , zipWith'
  , range
  ) where

import Prelude
import Data.Array (filter, foldl, length, nub, null, zip, (..))
import Data.Array as Array
import Data.Int (toNumber)
import Data.Maybe (Maybe(..))
import Data.Number (isFinite, sqrt) as Number
import Data.Tuple (Tuple(..))
import Lattice.Primitives (FiniteFloat, UnitFloat)

--------------------------------------------------------------------------------
-- Basic Operations
--------------------------------------------------------------------------------

-- | Clamp a value to a range
clamp :: Number -> Number -> Number -> Number
clamp minVal maxVal value = max minVal (min maxVal value)

-- | Linear interpolation between two values
lerp :: Number -> Number -> Number -> Number
lerp a b t = a + (b - a) * t

-- | Map a value from one range to another
mapRange :: Number -> Number -> Number -> Number -> Number -> Number
mapRange value inMin inMax outMin outMax
  | range' == 0.0 = outMin
  | otherwise = outMin + normalized * (outMax - outMin)
  where
    range' = inMax - inMin
    normalized = (value - inMin) / range'

--------------------------------------------------------------------------------
-- Array Statistics
--------------------------------------------------------------------------------

-- | Calculate the mean of an array
mean :: Array Number -> Number
mean values
  | null values = 0.0
  | otherwise = sumArray values / toNumber (length values)

-- | Find maximum value in array
maxArray :: Number -> Array Number -> Number
maxArray def values
  | null values = def
  | otherwise = foldl max def values

-- | Find minimum value in array
minArray :: Number -> Array Number -> Number
minArray def values
  | null values = def
  | otherwise = foldl min def values

-- | Normalize an array to [0, 1] range
normalize :: Array Number -> Maybe Number -> Array Number
normalize values maxValueOpt =
  let maxVal = case maxValueOpt of
        Just m -> m
        Nothing -> maxArray 0.0 values
      safeMax = if Number.isFinite maxVal && maxVal > 0.0 then maxVal else 0.0001
  in map (_ / safeMax) values

--------------------------------------------------------------------------------
-- Safe Versions with Refined Types
--------------------------------------------------------------------------------

-- | Check if Number is finite
isFiniteNumber :: Number -> Boolean
isFiniteNumber x = Number.isFinite x

-- | Clamp a finite value to a range
clampFinite :: FiniteFloat -> FiniteFloat -> FiniteFloat -> FiniteFloat
clampFinite minVal maxVal value
  | value < minVal = minVal
  | value > maxVal = maxVal
  | otherwise = value

-- | Linear interpolation with finite floats and unit t
lerpFinite :: FiniteFloat -> FiniteFloat -> UnitFloat -> FiniteFloat
lerpFinite a b t
  | isFiniteNumber result = result
  | otherwise = a
  where result = a + (b - a) * t

-- | Map a finite value from one range to another
mapRangeFinite :: FiniteFloat -> FiniteFloat -> FiniteFloat -> FiniteFloat -> FiniteFloat -> FiniteFloat
mapRangeFinite value inMin inMax outMin outMax
  | range' == 0.0 = outMin
  | isFiniteNumber result = result
  | otherwise = outMin
  where
    range' = inMax - inMin
    normalized = (value - inMin) / range'
    result = outMin + normalized * (outMax - outMin)

-- | Calculate the mean of finite floats
meanFinite :: Array FiniteFloat -> FiniteFloat
meanFinite values
  | null values = 0.0
  | isFiniteNumber result = result
  | otherwise = 0.0
  where
    sumVal = foldl (+) 0.0 values
    result = sumVal / toNumber (length values)

-- | Normalize finite float array to [0, 1]
normalizeFinite :: Array FiniteFloat -> Array UnitFloat
normalizeFinite values =
  let maxVal = foldl max 0.0 values
      safeMax = if maxVal > 0.0 then maxVal else 0.0001
  in map (\x -> max 0.0 (min 1.0 (x / safeMax))) values

--------------------------------------------------------------------------------
-- Additional Utilities
--------------------------------------------------------------------------------

-- | Sum of an array
sumArray :: Array Number -> Number
sumArray = foldl (+) 0.0

-- | Product of an array
productArray :: Array Number -> Number
productArray = foldl (*) 1.0

-- | Variance of an array
variance :: Array Number -> Number
variance values
  | null values = 0.0
  | otherwise = mean $ map (\v -> (v - m) * (v - m)) values
  where m = mean values

-- | Standard deviation of an array
stdDev :: Array Number -> Number
stdDev = Number.sqrt <<< variance

-- | Count items satisfying predicate
countWhere :: forall a. (a -> Boolean) -> Array a -> Int
countWhere pred = length <<< filter pred

-- | Find index of first item satisfying predicate
findIndex' :: forall a. (a -> Boolean) -> Array a -> Maybe Int
findIndex' = Array.findIndex

-- | Remove duplicates (keeps first occurrence)
unique :: forall a. Eq a => Array a -> Array a
unique = nub

-- | Zip two arrays with function
zipWith' :: forall a b c. (a -> b -> c) -> Array a -> Array b -> Array c
zipWith' f xs ys = map (\(Tuple a b) -> f a b) (zip xs ys)

-- | Create range of integers
range :: Int -> Int -> Array Int
range start endVal
  | start >= endVal = []
  | otherwise = start .. (endVal - 1)
