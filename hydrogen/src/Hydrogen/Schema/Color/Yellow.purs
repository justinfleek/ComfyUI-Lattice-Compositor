-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // schema // color // yellow
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Yellow - yellow ink percentage for CMYK printing.
-- |
-- | Measured as a percentage from 0 to 100:
-- | - **0%**: No yellow ink
-- | - **50%**: Half coverage
-- | - **100%**: Full yellow ink coverage
-- |
-- | Part of the CMYK subtractive color model used in printing.
-- | Yellow absorbs blue light, allowing red and green to reflect.

module Hydrogen.Schema.Color.Yellow
  ( Yellow
  , yellow
  , unsafeYellow
  , unwrap
  , scale
  , increase
  , decrease
  , bounds
  , toNumber
  , toUnitInterval
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (+)
  , (-)
  , (*)
  , (/)
  , (<>)
  )

import Data.Int (round, toNumber) as Int
import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // yellow
-- ═════════════════════════════════════════════════════════════════════════════

-- | Yellow ink percentage (0-100)
-- |
-- | Represents yellow ink coverage in CMYK printing. 0% = no yellow, 100% = full coverage.
newtype Yellow = Yellow Int

derive instance eqYellow :: Eq Yellow
derive instance ordYellow :: Ord Yellow

instance showYellow :: Show Yellow where
  show (Yellow y) = show y <> "%"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a yellow value, clamping to 0-100
yellow :: Int -> Yellow
yellow n = Yellow (Bounded.clampInt 0 100 n)

-- | Create a yellow value without clamping
-- |
-- | Use only when you know the value is valid.
unsafeYellow :: Int -> Yellow
unsafeYellow = Yellow

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Scale yellow by a factor (0.0 to 2.0 typical)
scale :: Number -> Yellow -> Yellow
scale factor (Yellow y) = 
  yellow (Int.round (Int.toNumber y * factor))

-- | Increase yellow by percentage points
increase :: Int -> Yellow -> Yellow
increase amount (Yellow y) = yellow (y + amount)

-- | Decrease yellow by percentage points
decrease :: Int -> Yellow -> Yellow
decrease amount (Yellow y) = yellow (y - amount)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Int value
unwrap :: Yellow -> Int
unwrap (Yellow y) = y

-- | Convert to Number for calculations
toNumber :: Yellow -> Number
toNumber (Yellow y) = Int.toNumber y

-- | Convert to unit interval (0.0-1.0)
toUnitInterval :: Yellow -> Number
toUnitInterval (Yellow y) = Int.toNumber y / 100.0

-- | Bounds documentation for this type
bounds :: Bounded.IntBounds
bounds = Bounded.intBounds 0 100 "yellow" "Yellow ink percentage"
