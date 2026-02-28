-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                               // hydrogen // schema // temporal // nanosecond
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Nanosecond — Bounded nanosecond duration atom (0 to 999999999).
-- |
-- | Represents sub-second precision at the nanosecond level.
-- | Used for high-precision timing, physics simulations, and temporal queries.
-- |
-- | One second = 1,000,000,000 nanoseconds.

module Hydrogen.Schema.Temporal.Nanosecond
  ( Nanosecond
  , nanosecond
  , unsafeNanosecond
  , unwrap
  , toInt
  , toNumber
  , toMicroseconds
  , toMilliseconds
  , fromMicroseconds
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
--                                                                 // nanosecond
-- ═════════════════════════════════════════════════════════════════════════════

-- | Nanosecond duration (0 to 999999999)
-- |
-- | Bounded by construction. Invalid nanosecond values cannot exist.
-- | Upper bound is one second minus one nanosecond.
newtype Nanosecond = Nanosecond Int

derive instance eqNanosecond :: Eq Nanosecond
derive instance ordNanosecond :: Ord Nanosecond

instance showNanosecond :: Show Nanosecond where
  show (Nanosecond ns) = "(Nanosecond " <> show ns <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a Nanosecond, clamping to valid range 0-999999999
-- |
-- | ```purescript
-- | nanosecond 500       -- Nanosecond 500
-- | nanosecond (-100)    -- Nanosecond 0 (clamped)
-- | nanosecond 2000000000 -- Nanosecond 999999999 (clamped)
-- | ```
nanosecond :: Int -> Nanosecond
nanosecond ns
  | ns < 0 = Nanosecond 0
  | ns > 999999999 = Nanosecond 999999999
  | otherwise = Nanosecond ns

-- | Create a Nanosecond without bounds checking
-- |
-- | Use only when you know the value is valid (0-999999999).
unsafeNanosecond :: Int -> Nanosecond
unsafeNanosecond = Nanosecond

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract raw Int from Nanosecond
unwrap :: Nanosecond -> Int
unwrap (Nanosecond ns) = ns

-- | Alias for unwrap
toInt :: Nanosecond -> Int
toInt = unwrap

-- | Convert to Number for calculations
toNumber :: Nanosecond -> Number
toNumber (Nanosecond ns) = Int.toNumber ns

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // conversions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert to microseconds (truncates)
-- |
-- | 1 microsecond = 1000 nanoseconds
-- | ```purescript
-- | toMicroseconds (nanosecond 5500)  -- 5
-- | ```
toMicroseconds :: Nanosecond -> Int
toMicroseconds (Nanosecond ns) = ns / 1000

-- | Convert to milliseconds (truncates)
-- |
-- | 1 millisecond = 1000000 nanoseconds
-- | ```purescript
-- | toMilliseconds (nanosecond 5500000)  -- 5
-- | ```
toMilliseconds :: Nanosecond -> Int
toMilliseconds (Nanosecond ns) = ns / 1000000

-- | Create from microseconds
-- |
-- | Clamps to valid nanosecond range.
-- | ```purescript
-- | fromMicroseconds 500  -- Nanosecond 500000
-- | ```
fromMicroseconds :: Int -> Nanosecond
fromMicroseconds us = nanosecond (us * 1000)

-- | Create from milliseconds
-- |
-- | Clamps to valid nanosecond range.
-- | ```purescript
-- | fromMilliseconds 500  -- Nanosecond 500000000
-- | ```
fromMilliseconds :: Int -> Nanosecond
fromMilliseconds ms = nanosecond (ms * 1000000)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds for Nanosecond
-- |
-- | Min: 0
-- | Max: 999999999 (one second minus one nanosecond)
bounds :: Bounded.IntBounds
bounds = Bounded.intBounds 0 999999999 "nanosecond" 
  "Nanosecond duration (0 to 999999999, one second = 1 billion ns)"
