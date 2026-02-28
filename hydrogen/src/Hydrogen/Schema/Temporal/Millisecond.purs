-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // schema // temporal // millisecond
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Millisecond — Bounded millisecond-of-second atom (0-999).
-- |
-- | Represents the sub-second component of wall-clock time.
-- | Used for precise timing in scheduling, animations, and temporal queries.

module Hydrogen.Schema.Temporal.Millisecond
  ( Millisecond
  , millisecond
  , unsafeMillisecond
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
--                                                                // millisecond
-- ═════════════════════════════════════════════════════════════════════════════

-- | Millisecond within second (0-999)
-- |
-- | Bounded by construction. Invalid milliseconds cannot exist.
newtype Millisecond = Millisecond Int

derive instance eqMillisecond :: Eq Millisecond
derive instance ordMillisecond :: Ord Millisecond

instance showMillisecond :: Show Millisecond where
  show (Millisecond ms) = padZero3 ms

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a Millisecond, clamping to valid range 0-999
millisecond :: Int -> Millisecond
millisecond ms
  | ms < 0 = Millisecond 0
  | ms > 999 = Millisecond 999
  | otherwise = Millisecond ms

-- | Create a Millisecond without bounds checking
-- |
-- | Use only when you know the value is valid (0-999).
unsafeMillisecond :: Int -> Millisecond
unsafeMillisecond = Millisecond

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract raw Int from Millisecond
unwrap :: Millisecond -> Int
unwrap (Millisecond ms) = ms

-- | Alias for unwrap
toInt :: Millisecond -> Int
toInt = unwrap

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // formatting
-- ═════════════════════════════════════════════════════════════════════════════

-- | Format for CSS for legacy system interop.
-- |
-- | **NOTE:** Hydrogen renders via WebGPU, NOT CSS. This function exists only
-- | for exporting to legacy systems that require CSS format.
-- |
-- | Returns value in milliseconds: "250ms"
toLegacyCss :: Millisecond -> String
toLegacyCss (Millisecond ms) = show ms <> "ms"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pad number to 3 digits with leading zeros
padZero3 :: Int -> String
padZero3 n
  | n < 10 = "00" <> show n
  | n < 100 = "0" <> show n
  | otherwise = show n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds for Millisecond
-- |
-- | Min: 0
-- | Max: 999
bounds :: Bounded.IntBounds
bounds = Bounded.intBounds 0 999 "millisecond" "Millisecond within second (0-999)"
