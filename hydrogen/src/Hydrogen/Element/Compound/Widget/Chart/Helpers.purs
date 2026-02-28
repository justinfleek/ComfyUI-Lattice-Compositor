-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // element // widget // chart // helpers
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Chart Helpers — Pure utilities for chart rendering.
-- |
-- | **No FFI. Pure PureScript.**
-- |
-- | Math functions from Hydrogen.Math.Core (Taylor series implementations).
-- | Array utilities from Data.Array.
-- | All helpers use bounded fallbacks — no Infinity or NaN escapes.

module Hydrogen.Element.Compound.Widget.Chart.Helpers
  ( -- * Array Operations
    mapPoints
  , arrayMin
  , arrayMax
  , sumArray
  
  -- * Re-exports from standard library
  , module ReExports
  ) where

import Prelude
  ( (+)
  , (<)
  , (>)
  )

import Data.Array (foldl, index, mapWithIndex, replicate, take) as ReExports
import Data.Array (foldl, index, mapWithIndex)
import Data.Maybe (Maybe(Just, Nothing))
import Data.Int (toNumber) as ReExports
import Hydrogen.Element.Compound.Widget.Chart.Types (DataPoint)
import Hydrogen.Math.Core (cos, sin) as ReExports

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // array operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Map data points to extract a value.
mapPoints :: (DataPoint -> Number) -> Array DataPoint -> Array Number
mapPoints f points = mapWithIndex (\_ p -> f p) points

-- | Get minimum value from array.
-- |
-- | Returns 0.0 for empty arrays (bounded fallback, no Infinity).
-- | Uses first element as initial accumulator to avoid unbounded values.
arrayMin :: Array Number -> Number
arrayMin arr = case index arr 0 of
  Nothing -> 0.0  -- Empty array fallback
  Just first -> foldl min' first arr
  where
    min' :: Number -> Number -> Number
    min' a b = if a < b then a else b

-- | Get maximum value from array.
-- |
-- | Returns 0.0 for empty arrays (bounded fallback, no Infinity).
-- | Uses first element as initial accumulator to avoid unbounded values.
arrayMax :: Array Number -> Number
arrayMax arr = case index arr 0 of
  Nothing -> 0.0  -- Empty array fallback
  Just first -> foldl max' first arr
  where
    max' :: Number -> Number -> Number
    max' a b = if a > b then a else b

-- | Sum an array of numbers.
sumArray :: Array Number -> Number
sumArray arr = foldl (\acc n -> acc + n) 0.0 arr
