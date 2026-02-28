-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // schema // temporal // hour
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Hour — Bounded hour-of-day atom (0-23).
-- |
-- | Represents the hour component of wall-clock time.
-- | 0 = midnight, 12 = noon, 23 = 11 PM.

module Hydrogen.Schema.Temporal.Hour
  ( Hour
  , hour
  , unsafeHour
  , unwrap
  , toInt
  , to12Hour
  , isAM
  , isPM
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
  , (-)
  , (>=)
  , (==)
  )

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // hour
-- ═════════════════════════════════════════════════════════════════════════════

-- | Hour of day (0-23)
-- |
-- | Bounded by construction. Invalid hours cannot exist.
newtype Hour = Hour Int

derive instance eqHour :: Eq Hour
derive instance ordHour :: Ord Hour

instance showHour :: Show Hour where
  show (Hour h) = padZero h

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create an Hour, clamping to valid range 0-23
hour :: Int -> Hour
hour h
  | h < 0 = Hour 0
  | h > 23 = Hour 23
  | otherwise = Hour h

-- | Create an Hour without bounds checking
-- |
-- | Use only when you know the value is valid (0-23).
unsafeHour :: Int -> Hour
unsafeHour = Hour

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract raw Int from Hour
unwrap :: Hour -> Int
unwrap (Hour h) = h

-- | Alias for unwrap
toInt :: Hour -> Int
toInt = unwrap

-- | Convert to 12-hour format (1-12)
to12Hour :: Hour -> Int
to12Hour (Hour h)
  | h == 0 = 12
  | h > 12 = h - 12
  | otherwise = h

-- | Check if hour is AM (before noon)
isAM :: Hour -> Boolean
isAM (Hour h) = h < 12

-- | Check if hour is PM (noon or after)
isPM :: Hour -> Boolean
isPM (Hour h) = h >= 12

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // formatting
-- ═════════════════════════════════════════════════════════════════════════════

-- | Format for CSS for legacy system interop.
-- |
-- | **NOTE:** Hydrogen renders via WebGPU, NOT CSS. This function exists only
-- | for exporting to legacy systems that require CSS format.
toLegacyCss :: Hour -> String
toLegacyCss (Hour h) = show h

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

-- | Bounds for Hour
-- |
-- | Min: 0 (midnight)
-- | Max: 23 (11 PM)
bounds :: Bounded.IntBounds
bounds = Bounded.intBounds 0 23 "hour" "Hour of day (0-23)"
