-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // temporal // minute
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Minute — Bounded minute atom (0-59).
-- |
-- | Represents the minute component within an hour.

module Hydrogen.Schema.Temporal.Minute
  ( Minute
  , minute
  , unsafeMinute
  , unwrap
  , toInt
  , toLegacyCss
  , bounds
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , (<>)
  , (<)
  , (>)
  )

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // minute
-- ═════════════════════════════════════════════════════════════════════════════

-- | Minute within hour (0-59)
-- |
-- | Bounded by construction. Invalid minutes cannot exist.
newtype Minute = Minute Int

derive instance eqMinute :: Eq Minute
derive instance ordMinute :: Ord Minute

instance showMinute :: Show Minute where
  show (Minute m) = padZero m

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a Minute, clamping to valid range 0-59
minute :: Int -> Minute
minute m
  | m < 0 = Minute 0
  | m > 59 = Minute 59
  | otherwise = Minute m

-- | Create a Minute without bounds checking
-- |
-- | Use only when you know the value is valid (0-59).
unsafeMinute :: Int -> Minute
unsafeMinute = Minute

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract raw Int from Minute
unwrap :: Minute -> Int
unwrap (Minute m) = m

-- | Alias for unwrap
toInt :: Minute -> Int
toInt = unwrap

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // formatting
-- ═════════════════════════════════════════════════════════════════════════════

-- | Format for CSS for legacy system interop.
-- |
-- | **NOTE:** Hydrogen renders via WebGPU, NOT CSS. This function exists only
-- | for exporting to legacy systems that require CSS format.
toLegacyCss :: Minute -> String
toLegacyCss (Minute m) = show m

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pad number to 2 digits with leading zero
padZero :: Int -> String
padZero n
  | n < 10 = "0" <> show n
  | otherwise = show n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds for Minute
-- |
-- | Min: 0
-- | Max: 59
bounds :: Bounded.IntBounds
bounds = Bounded.intBounds 0 59 "minute" "Minute within hour (0-59)"
