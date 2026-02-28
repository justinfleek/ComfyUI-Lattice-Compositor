-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // temporal // second
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Second — Bounded second atom (0-59).
-- |
-- | Represents the second component within a minute.
-- |
-- | Note: Leap seconds (60) are not supported. They are a display/formatting
-- | concern handled at the application level.

module Hydrogen.Schema.Temporal.Second
  ( Second
  , second
  , unsafeSecond
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
--                                                                     // second
-- ═════════════════════════════════════════════════════════════════════════════

-- | Second within minute (0-59)
-- |
-- | Bounded by construction. Invalid seconds cannot exist.
-- | Leap seconds are not supported at the type level.
newtype Second = Second Int

derive instance eqSecond :: Eq Second
derive instance ordSecond :: Ord Second

instance showSecond :: Show Second where
  show (Second s) = padZero s

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a Second, clamping to valid range 0-59
second :: Int -> Second
second s
  | s < 0 = Second 0
  | s > 59 = Second 59
  | otherwise = Second s

-- | Create a Second without bounds checking
-- |
-- | Use only when you know the value is valid (0-59).
unsafeSecond :: Int -> Second
unsafeSecond = Second

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract raw Int from Second
unwrap :: Second -> Int
unwrap (Second s) = s

-- | Alias for unwrap
toInt :: Second -> Int
toInt = unwrap

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // formatting
-- ═════════════════════════════════════════════════════════════════════════════

-- | Format for CSS for legacy system interop.
-- |
-- | **NOTE:** Hydrogen renders via WebGPU, NOT CSS. This function exists only
-- | for exporting to legacy systems that require CSS format.
toLegacyCss :: Second -> String
toLegacyCss (Second s) = show s

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

-- | Bounds for Second
-- |
-- | Min: 0
-- | Max: 59
bounds :: Bounded.IntBounds
bounds = Bounded.intBounds 0 59 "second" "Second within minute (0-59)"
