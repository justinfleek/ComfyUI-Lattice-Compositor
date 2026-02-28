-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // schema // temporal // microsecond
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Microsecond — Bounded microsecond duration atom (0 to 999999).
-- |
-- | Represents sub-second precision at the microsecond level.
-- | Used for high-precision timing, physics simulations, and temporal queries.
-- |
-- | One second = 1,000,000 microseconds.

module Hydrogen.Schema.Temporal.Microsecond
  ( Microsecond
  , microsecond
  , unsafeMicrosecond
  , unwrap
  , toInt
  , toNumber
  , toNanoseconds
  , toMilliseconds
  , fromNanoseconds
  , fromMilliseconds
  , bounds
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , (/)
  , (*)
  , (<>)
  , (<)
  , (>)
  )

import Data.Int (toNumber) as Int
import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // microsecond
-- ═════════════════════════════════════════════════════════════════════════════

-- | Microsecond duration (0 to 999999)
-- |
-- | Bounded by construction. Invalid microsecond values cannot exist.
-- | Upper bound is one second minus one microsecond.
newtype Microsecond = Microsecond Int

derive instance eqMicrosecond :: Eq Microsecond
derive instance ordMicrosecond :: Ord Microsecond

instance showMicrosecond :: Show Microsecond where
  show (Microsecond us) = "(Microsecond " <> show us <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a Microsecond, clamping to valid range 0-999999
-- |
-- | ```purescript
-- | microsecond 500       -- Microsecond 500
-- | microsecond (-100)    -- Microsecond 0 (clamped)
-- | microsecond 2000000   -- Microsecond 999999 (clamped)
-- | ```
microsecond :: Int -> Microsecond
microsecond us
  | us < 0 = Microsecond 0
  | us > 999999 = Microsecond 999999
  | otherwise = Microsecond us

-- | Create a Microsecond without bounds checking
-- |
-- | Use only when you know the value is valid (0-999999).
unsafeMicrosecond :: Int -> Microsecond
unsafeMicrosecond = Microsecond

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract raw Int from Microsecond
unwrap :: Microsecond -> Int
unwrap (Microsecond us) = us

-- | Alias for unwrap
toInt :: Microsecond -> Int
toInt = unwrap

-- | Convert to Number for calculations
toNumber :: Microsecond -> Number
toNumber (Microsecond us) = Int.toNumber us

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // conversions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert to nanoseconds
-- |
-- | 1 microsecond = 1000 nanoseconds
-- | ```purescript
-- | toNanoseconds (microsecond 5)  -- 5000
-- | ```
toNanoseconds :: Microsecond -> Int
toNanoseconds (Microsecond us) = us * 1000

-- | Convert to milliseconds (truncates)
-- |
-- | 1 millisecond = 1000 microseconds
-- | ```purescript
-- | toMilliseconds (microsecond 5500)  -- 5
-- | ```
toMilliseconds :: Microsecond -> Int
toMilliseconds (Microsecond us) = us / 1000

-- | Create from nanoseconds (truncates)
-- |
-- | Clamps to valid microsecond range.
-- | ```purescript
-- | fromNanoseconds 5000  -- Microsecond 5
-- | ```
fromNanoseconds :: Int -> Microsecond
fromNanoseconds ns = microsecond (ns / 1000)

-- | Create from milliseconds
-- |
-- | Clamps to valid microsecond range.
-- | ```purescript
-- | fromMilliseconds 500  -- Microsecond 500000
-- | ```
fromMilliseconds :: Int -> Microsecond
fromMilliseconds ms = microsecond (ms * 1000)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds for Microsecond
-- |
-- | Min: 0
-- | Max: 999999 (one second minus one microsecond)
bounds :: Bounded.IntBounds
bounds = Bounded.intBounds 0 999999 "microsecond" 
  "Microsecond duration (0 to 999999, one second = 1 million us)"
