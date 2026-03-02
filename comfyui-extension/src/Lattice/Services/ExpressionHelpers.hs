-- |
-- Module      : Lattice.Services.ExpressionHelpers
-- Description : Pure expression helper functions for value operations
-- 
-- Migrated from ui/src/services/expressions/expressionHelpers.ts
-- Pure utility functions for value arithmetic, interpolation, and easing
--

module Lattice.Services.ExpressionHelpers
  ( -- Value operations
    subtractValues
  , addValues
  , scaleValue
  , lerpValues
  -- Value type
  , Value(..)
  ) where

import Lattice.Utils.NumericSafety (isFinite)
import Lattice.Utils.NumericSafety (safeLerpD)
import Lattice.Utils.ArrayUtils (safeArrayGet)

-- ============================================================================
-- VALUE TYPE
-- ============================================================================

-- | Expression value: either a number or an array of numbers
data Value
  = ValueNumber Double
  | ValueArray [Double]
  deriving (Eq, Show)

-- | Convert number to Value
numberToValue :: Double -> Value
numberToValue = ValueNumber

-- | Convert array to Value
arrayToValue :: [Double] -> Value
arrayToValue = ValueArray

-- | Extract number from Value (defaults to 0 if array)
valueToNumber :: Value -> Double
valueToNumber (ValueNumber n) = n
valueToNumber (ValueArray _) = 0.0

-- | Extract array from Value (defaults to single-element array if number)
valueToArray :: Value -> [Double]
valueToArray (ValueNumber n) = [n]
valueToArray (ValueArray arr) = arr

-- ============================================================================
-- VALUE OPERATIONS
-- ============================================================================

-- | Subtract two values (numbers or arrays)
-- Pure function: same inputs → same outputs
subtractValues :: Value -> Value -> Value
subtractValues (ValueNumber a) (ValueNumber b) = ValueNumber (a - b)
subtractValues (ValueArray a) (ValueArray b) =
  let maxLen = max (length a) (length b)
      safeGet arr idx =
        let v = safeArrayGet arr idx 0.0
        in if isFinite v then v else 0.0
  in ValueArray [safeGet a i - safeGet b i | i <- [0 .. maxLen - 1]]
subtractValues _ _ = ValueNumber 0.0

-- | Add two values (numbers or arrays)
-- Pure function: same inputs → same outputs
addValues :: Value -> Value -> Value
addValues (ValueNumber a) (ValueNumber b) = ValueNumber (a + b)
addValues (ValueArray a) (ValueArray b) =
  let maxLen = max (length a) (length b)
      safeGet arr idx =
        let v = safeArrayGet arr idx 0.0
        in if isFinite v then v else 0.0
  in ValueArray [safeGet a i + safeGet b i | i <- [0 .. maxLen - 1]]
addValues (ValueNumber a) _ = ValueNumber a
addValues _ (ValueNumber b) = ValueNumber b

-- | Scale a value by a scalar
-- Pure function: same inputs → same outputs
scaleValue :: Value -> Double -> Value
scaleValue (ValueNumber v) s = ValueNumber (v * s)
scaleValue (ValueArray arr) s = ValueArray (map (* s) arr)

-- | Linear interpolation between two values
-- Pure function: same inputs → same outputs
lerpValues :: Value -> Value -> Double -> Value
lerpValues (ValueNumber a) (ValueNumber b) t = ValueNumber (safeLerpD a b t)
lerpValues (ValueArray a) (ValueArray b) t =
  let maxLen = max (length a) (length b)
      safeGet arr idx =
        let v = safeArrayGet arr idx 0.0
        in if isFinite v then v else 0.0
      lerpPair aVal bVal = safeLerpD aVal bVal t
  in ValueArray [lerpPair (safeGet a i) (safeGet b i) | i <- [0 .. maxLen - 1]]
lerpValues (ValueNumber a) _ _ = ValueNumber a
lerpValues _ (ValueNumber b) _ = ValueNumber b
