-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // elevation // zindex
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Z-Index atoms — stacking order in the z-axis.
-- |
-- | ## CSS Stacking Context
-- |
-- | Z-index only has meaning within a stacking context. Elements with
-- | `position: static` (the default) do not participate in z-index ordering.
-- |
-- | A new stacking context is created by:
-- | - `position: relative/absolute/fixed/sticky` with `z-index` other than `auto`
-- | - `opacity` less than 1
-- | - `transform`, `filter`, `perspective`, etc.
-- | - `isolation: isolate`
-- |
-- | ## Value Range
-- |
-- | CSS z-index accepts any integer. In practice:
-- | - Browsers clamp to approximately ±2147483647 (32-bit signed int)
-- | - Values beyond ±9999 are rarely needed
-- | - Negative values place elements behind the default layer
-- |
-- | ## Concrete Values
-- |
-- | This module provides a typed wrapper around integers. BrandSchema can
-- | define semantic z-index scales (e.g., `modal`, `dropdown`, `tooltip`)
-- | by assigning concrete ZIndex values.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Elevation.ZIndex as ZIndex
-- |
-- | -- Create z-index values
-- | dropdownZ :: ZIndex.ZIndex
-- | dropdownZ = ZIndex.z 100
-- |
-- | -- Auto (default stacking)
-- | defaultZ :: ZIndex.ZIndex
-- | defaultZ = ZIndex.auto
-- |
-- | -- Convert to CSS
-- | css = ZIndex.toLegacyCss dropdownZ  -- "100"
-- | ```

module Hydrogen.Schema.Elevation.ZIndex
  ( -- * Core Types
    ZIndex(..)
  , IsolationMode(..)
  
  -- * ZIndex Constructors
  , z
  , auto
  , negative
  
  -- * IsolationMode Constructors
  , isolate
  , autoIsolation
  
  -- * Operations
  , above
  , below
  , increment
  , decrement
  
  -- * Conversion (Legacy string generation, NOT FFI)
  , toLegacyCss
  , isolationToLegacyCss
  , toInt
  
  -- * Predicates
  , isAuto
  , isNegative
  , isPositive
  , isIsolated
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , compare
  , negate
  , (+)
  , (-)
  , (<)
  , (>)
  )

import Data.Ordering (Ordering(LT, GT, EQ))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // core types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Z-index value for CSS stacking order
-- |
-- | Either a concrete integer or `auto` (browser default).
data ZIndex
  = ZIndexAuto
  | ZIndexValue Int

derive instance eqZIndex :: Eq ZIndex

-- | Isolation mode for stacking context creation.
-- |
-- | CSS `isolation` property controls whether an element creates a new
-- | stacking context. This is useful for containing z-index values
-- | within a subtree.
-- |
-- | - `isolate`: Creates a new stacking context (like z-index: 0 but
-- |   without requiring position: relative)
-- | - `auto`: Inherits stacking context from parent (default)
data IsolationMode
  = Isolate
  | IsolationAuto

derive instance eqIsolationMode :: Eq IsolationMode

instance ordZIndex :: Ord ZIndex where
  compare ZIndexAuto ZIndexAuto = EQ
  compare ZIndexAuto (ZIndexValue _) = LT  -- auto < any explicit value
  compare (ZIndexValue _) ZIndexAuto = GT
  compare (ZIndexValue a) (ZIndexValue b) = compare a b

instance showZIndex :: Show ZIndex where
  show = toLegacyCss

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a z-index from an integer
z :: Int -> ZIndex
z = ZIndexValue

-- | Auto z-index (default browser stacking)
-- |
-- | Element participates in normal document flow stacking.
auto :: ZIndex
auto = ZIndexAuto

-- | Create a negative z-index
-- |
-- | Places element behind the default stacking layer.
negative :: Int -> ZIndex
negative n = ZIndexValue (negate (abs n))
  where
    abs x = if x < 0 then negate x else x

-- | Create isolation mode that forces a new stacking context
isolate :: IsolationMode
isolate = Isolate

-- | Auto isolation (inherit from parent, default)
autoIsolation :: IsolationMode
autoIsolation = IsolationAuto

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a z-index above another
-- |
-- | Returns value + 1, or 1 if auto.
above :: ZIndex -> ZIndex
above ZIndexAuto = ZIndexValue 1
above (ZIndexValue n) = ZIndexValue (n + 1)

-- | Create a z-index below another
-- |
-- | Returns value - 1, or -1 if auto.
below :: ZIndex -> ZIndex
below ZIndexAuto = ZIndexValue (-1)
below (ZIndexValue n) = ZIndexValue (n - 1)

-- | Increment z-index by a specific amount
increment :: Int -> ZIndex -> ZIndex
increment _ ZIndexAuto = ZIndexAuto
increment delta (ZIndexValue n) = ZIndexValue (n + delta)

-- | Decrement z-index by a specific amount
decrement :: Int -> ZIndex -> ZIndex
decrement delta = increment (negate delta)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert to legacy CSS string.
-- |
-- | NOT an FFI boundary - pure string generation.
toLegacyCss :: ZIndex -> String
toLegacyCss ZIndexAuto = "auto"
toLegacyCss (ZIndexValue n) = show n

-- | Convert isolation mode to CSS string.
-- |
-- | NOT an FFI boundary - pure string generation.
isolationToLegacyCss :: IsolationMode -> String
isolationToLegacyCss Isolate = "isolate"
isolationToLegacyCss IsolationAuto = "auto"

-- | Extract integer value (Nothing for auto)
toInt :: ZIndex -> Int
toInt ZIndexAuto = 0
toInt (ZIndexValue n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if z-index is auto
isAuto :: ZIndex -> Boolean
isAuto ZIndexAuto = true
isAuto _ = false

-- | Check if z-index is negative
isNegative :: ZIndex -> Boolean
isNegative ZIndexAuto = false
isNegative (ZIndexValue n) = n < 0

-- | Check if z-index is positive
isPositive :: ZIndex -> Boolean
isPositive ZIndexAuto = false
isPositive (ZIndexValue n) = n > 0

-- | Check if isolation mode creates a stacking context
isIsolated :: IsolationMode -> Boolean
isIsolated Isolate = true
isIsolated IsolationAuto = false
