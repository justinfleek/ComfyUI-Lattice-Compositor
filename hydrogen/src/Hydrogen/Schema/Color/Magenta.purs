-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // schema // color // magenta
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Magenta - magenta ink percentage for CMYK printing.
-- |
-- | Measured as a percentage from 0 to 100:
-- | - **0%**: No magenta ink
-- | - **50%**: Half coverage
-- | - **100%**: Full magenta ink coverage
-- |
-- | Part of the CMYK subtractive color model used in printing.
-- | Magenta absorbs green light, allowing red and blue to reflect.

module Hydrogen.Schema.Color.Magenta
  ( Magenta
  , magenta
  , unsafeMagenta
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
--                                                                    // magenta
-- ═════════════════════════════════════════════════════════════════════════════

-- | Magenta ink percentage (0-100)
-- |
-- | Represents magenta ink coverage in CMYK printing. 0% = no magenta, 100% = full coverage.
newtype Magenta = Magenta Int

derive instance eqMagenta :: Eq Magenta
derive instance ordMagenta :: Ord Magenta

instance showMagenta :: Show Magenta where
  show (Magenta m) = show m <> "%"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a magenta value, clamping to 0-100
magenta :: Int -> Magenta
magenta n = Magenta (Bounded.clampInt 0 100 n)

-- | Create a magenta value without clamping
-- |
-- | Use only when you know the value is valid.
unsafeMagenta :: Int -> Magenta
unsafeMagenta = Magenta

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Scale magenta by a factor (0.0 to 2.0 typical)
scale :: Number -> Magenta -> Magenta
scale factor (Magenta m) = 
  magenta (Int.round (Int.toNumber m * factor))

-- | Increase magenta by percentage points
increase :: Int -> Magenta -> Magenta
increase amount (Magenta m) = magenta (m + amount)

-- | Decrease magenta by percentage points
decrease :: Int -> Magenta -> Magenta
decrease amount (Magenta m) = magenta (m - amount)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Int value
unwrap :: Magenta -> Int
unwrap (Magenta m) = m

-- | Convert to Number for calculations
toNumber :: Magenta -> Number
toNumber (Magenta m) = Int.toNumber m

-- | Convert to unit interval (0.0-1.0)
toUnitInterval :: Magenta -> Number
toUnitInterval (Magenta m) = Int.toNumber m / 100.0

-- | Bounds documentation for this type
bounds :: Bounded.IntBounds
bounds = Bounded.intBounds 0 100 "magenta" "Magenta ink percentage"
