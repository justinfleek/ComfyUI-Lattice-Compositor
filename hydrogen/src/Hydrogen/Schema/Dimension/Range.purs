-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // dimension // range
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Range — Min and Max bounds for a value.
-- |
-- | **WHY RANGE?**
-- | Range represents a bounded interval:
-- | - Minimum value (inclusive)
-- | - Maximum value (inclusive)
-- |
-- | **Use cases:**
-- | - Slider bounds (min: 0, max: 100)
-- | - Input validation (age: 0-120)
-- | - Animation keyframe times
-- | - Responsive breakpoint ranges
-- | - Value constraints
-- |
-- | **Invariant:**
-- | min <= max (enforced by constructors via normalization)

module Hydrogen.Schema.Dimension.Range
  ( -- * Types
    Range(Range)
  
  -- * Constructors
  , range
  , rangeFromRecord
  , rangeUnit
  , rangePercent
  , rangePositive
  , rangeSingleton
  
  -- * Accessors
  , minVal
  , maxVal
  , toRecord
  
  -- * Operations
  , span
  , midpoint
  , contains
  , containsRange
  , clamp
  , normalize
  , lerp
  , expand
  , contract
  , shift
  , scale
  , union
  , intersection
  
  -- * Predicates
  , isEmpty
  , isSingleton
  , overlaps
  , isEqual
  
  -- * Mapping
  , mapToRange
  , mapFromRange
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , (&&)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (<=)
  , (>)
  , (>=)
  , (==)
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // range
-- ═════════════════════════════════════════════════════════════════════════════

-- | Range with minimum and maximum values.
-- |
-- | Invariant: min <= max (normalized by constructors).
data Range = Range Number Number

derive instance eqRange :: Eq Range
derive instance ordRange :: Ord Range

instance showRange :: Show Range where
  show (Range minV maxV) = "Range(" <> show minV <> " .. " <> show maxV <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a Range from min and max values.
-- |
-- | Values are normalized so min <= max.
-- |
-- | ```purescript
-- | range 0.0 100.0  -- 0 to 100
-- | range 100.0 0.0  -- normalized to 0 to 100
-- | ```
range :: Number -> Number -> Range
range a b =
  if a <= b
    then Range a b
    else Range b a

-- | Create from a record.
rangeFromRecord :: { min :: Number, max :: Number } -> Range
rangeFromRecord { min: minV, max: maxV } = range minV maxV

-- | Unit range (0.0 to 1.0).
rangeUnit :: Range
rangeUnit = Range 0.0 1.0

-- | Percentage range (0.0 to 100.0).
rangePercent :: Range
rangePercent = Range 0.0 100.0

-- | Positive range (0.0 to infinity represented as large number).
rangePositive :: Range
rangePositive = Range 0.0 1.0e308

-- | Singleton range (min = max).
rangeSingleton :: Number -> Range
rangeSingleton n = Range n n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get minimum value.
minVal :: Range -> Number
minVal (Range minV _) = minV

-- | Get maximum value.
maxVal :: Range -> Number
maxVal (Range _ maxV) = maxV

-- | Convert to record.
toRecord :: Range -> { min :: Number, max :: Number }
toRecord (Range minV maxV) = { min: minV, max: maxV }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate span (max - min).
span :: Range -> Number
span (Range minV maxV) = maxV - minV

-- | Calculate midpoint.
midpoint :: Range -> Number
midpoint (Range minV maxV) = (minV + maxV) / 2.0

-- | Check if value is within range (inclusive).
contains :: Number -> Range -> Boolean
contains val (Range minV maxV) = val >= minV && val <= maxV

-- | Check if this range fully contains another range.
containsRange :: Range -> Range -> Boolean
containsRange (Range innerMin innerMax) (Range outerMin outerMax) =
  innerMin >= outerMin && innerMax <= outerMax

-- | Clamp value to range bounds.
clamp :: Number -> Range -> Number
clamp val (Range minV maxV)
  | val < minV = minV
  | val > maxV = maxV
  | otherwise = val

-- | Normalize a value from this range to 0-1.
-- |
-- | ```purescript
-- | normalize 50.0 (range 0.0 100.0)  -- 0.5
-- | normalize 25.0 (range 0.0 100.0)  -- 0.25
-- | ```
normalize :: Number -> Range -> Number
normalize val (Range minV maxV) =
  let s = maxV - minV
  in if s == 0.0 then 0.0 else (val - minV) / s

-- | Linear interpolation within range.
-- |
-- | `lerp 0.0 range` = min
-- | `lerp 1.0 range` = max
-- | `lerp 0.5 range` = midpoint
lerp :: Number -> Range -> Number
lerp t (Range minV maxV) =
  let t' = clamp01 t
  in minV + (maxV - minV) * t'

-- | Expand range by amount on both ends.
expand :: Number -> Range -> Range
expand amount (Range minV maxV) = Range (minV - amount) (maxV + amount)

-- | Contract range by amount on both ends.
-- |
-- | Clamped so min doesn't exceed max.
contract :: Number -> Range -> Range
contract amount (Range minV maxV) =
  let newMin = minV + amount
      newMax = maxV - amount
  in if newMin > newMax
     then let mid = (minV + maxV) / 2.0 in Range mid mid
     else Range newMin newMax

-- | Shift range by offset.
shift :: Number -> Range -> Range
shift offset (Range minV maxV) = Range (minV + offset) (maxV + offset)

-- | Scale range from its midpoint.
scale :: Number -> Range -> Range
scale factor (Range minV maxV) =
  let mid = (minV + maxV) / 2.0
      halfSpan = (maxV - minV) / 2.0 * factor
  in Range (mid - halfSpan) (mid + halfSpan)

-- | Calculate union of two ranges (smallest range containing both).
union :: Range -> Range -> Range
union (Range min1 max1) (Range min2 max2) =
  Range (minNum min1 min2) (maxNum max1 max2)

-- | Calculate intersection of two ranges.
-- |
-- | Returns Nothing if ranges don't overlap.
intersection :: Range -> Range -> Maybe Range
intersection (Range min1 max1) (Range min2 max2) =
  let newMin = maxNum min1 min2
      newMax = minNum max1 max2
  in if newMin <= newMax
     then Just (Range newMin newMax)
     else Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if range has zero span (min == max after floating point tolerance).
isEmpty :: Range -> Boolean
isEmpty (Range minV maxV) = minV == maxV

-- | Check if range is a singleton (same as isEmpty for continuous ranges).
isSingleton :: Range -> Boolean
isSingleton = isEmpty

-- | Check if two ranges overlap.
overlaps :: Range -> Range -> Boolean
overlaps (Range min1 max1) (Range min2 max2) =
  min1 <= max2 && max1 >= min2

-- | Check if two ranges are equal.
isEqual :: Range -> Range -> Boolean
isEqual (Range min1 max1) (Range min2 max2) =
  min1 == min2 && max1 == max2

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // mapping
-- ═════════════════════════════════════════════════════════════════════════════

-- | Map a value from source range to target range.
-- |
-- | ```purescript
-- | mapToRange (range 0.0 100.0) (range 0.0 255.0) 50.0  -- 127.5
-- | ```
mapToRange :: Range -> Range -> Number -> Number
mapToRange from to val =
  let normalized = normalize val from
  in lerp normalized to

-- | Map a normalized value (0-1) to this range.
-- |
-- | Same as `lerp` but with argument order suitable for piping.
mapFromRange :: Range -> Number -> Number
mapFromRange r t = lerp t r

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // internal
-- ═════════════════════════════════════════════════════════════════════════════

-- | Maximum of two numbers
maxNum :: Number -> Number -> Number
maxNum a b
  | a >= b = a
  | otherwise = b

-- | Minimum of two numbers
minNum :: Number -> Number -> Number
minNum a b
  | a <= b = a
  | otherwise = b

-- | Clamp to 0.0-1.0
clamp01 :: Number -> Number
clamp01 n
  | n < 0.0 = 0.0
  | n <= 1.0 = n
  | otherwise = 1.0
