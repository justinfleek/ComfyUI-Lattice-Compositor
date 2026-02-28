-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // schema // color // cyan
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Cyan - cyan ink percentage for CMYK printing.
-- |
-- | Measured as a percentage from 0 to 100:
-- | - **0%**: No cyan ink
-- | - **50%**: Half coverage
-- | - **100%**: Full cyan ink coverage
-- |
-- | Part of the CMYK subtractive color model used in printing.
-- | Cyan absorbs red light, allowing green and blue to reflect.

module Hydrogen.Schema.Color.Cyan
  ( Cyan
  , cyan
  , unsafeCyan
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
--                                                                       // cyan
-- ═════════════════════════════════════════════════════════════════════════════

-- | Cyan ink percentage (0-100)
-- |
-- | Represents cyan ink coverage in CMYK printing. 0% = no cyan, 100% = full coverage.
newtype Cyan = Cyan Int

derive instance eqCyan :: Eq Cyan
derive instance ordCyan :: Ord Cyan

instance showCyan :: Show Cyan where
  show (Cyan c) = show c <> "%"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a cyan value, clamping to 0-100
cyan :: Int -> Cyan
cyan n = Cyan (Bounded.clampInt 0 100 n)

-- | Create a cyan value without clamping
-- |
-- | Use only when you know the value is valid.
unsafeCyan :: Int -> Cyan
unsafeCyan = Cyan

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Scale cyan by a factor (0.0 to 2.0 typical)
scale :: Number -> Cyan -> Cyan
scale factor (Cyan c) = 
  cyan (Int.round (Int.toNumber c * factor))

-- | Increase cyan by percentage points
increase :: Int -> Cyan -> Cyan
increase amount (Cyan c) = cyan (c + amount)

-- | Decrease cyan by percentage points
decrease :: Int -> Cyan -> Cyan
decrease amount (Cyan c) = cyan (c - amount)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Int value
unwrap :: Cyan -> Int
unwrap (Cyan c) = c

-- | Convert to Number for calculations
toNumber :: Cyan -> Number
toNumber (Cyan c) = Int.toNumber c

-- | Convert to unit interval (0.0-1.0)
toUnitInterval :: Cyan -> Number
toUnitInterval (Cyan c) = Int.toNumber c / 100.0

-- | Bounds documentation for this type
bounds :: Bounded.IntBounds
bounds = Bounded.intBounds 0 100 "cyan" "Cyan ink percentage"
