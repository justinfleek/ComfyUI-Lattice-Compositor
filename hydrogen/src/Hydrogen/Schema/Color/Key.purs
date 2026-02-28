-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // schema // color // key
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Key (Black) - black ink percentage for CMYK printing.
-- |
-- | Measured as a percentage from 0 to 100:
-- | - **0%**: No black ink (color built from CMY only)
-- | - **50%**: Half black coverage
-- | - **100%**: Full black ink coverage (rich black)
-- |
-- | The "K" in CMYK. Black ink is used because:
-- | 1. Pure black (100% CMY) wastes ink and doesn't look truly black
-- | 2. Black ink is cheaper than mixing three colors
-- | 3. Text and fine details need true black, not composite
-- |
-- | Named "Key" historically from printing plates where the black plate
-- | was the "key plate" that other colors were registered to.

module Hydrogen.Schema.Color.Key
  ( Key
  , key
  , unsafeKey
  , unwrap
  , scale
  , increase
  , decrease
  , bounds
  , toNumber
  , toUnitInterval
  , isRichBlack
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
  , (>)
  , (<>)
  )

import Data.Int (round, toNumber) as Int
import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                        // key
-- ═════════════════════════════════════════════════════════════════════════════

-- | Key (black) ink percentage (0-100)
-- |
-- | Represents black ink coverage in CMYK printing. 0% = no black, 100% = full coverage.
-- | The fourth channel in CMYK, added to improve print quality and reduce ink costs.
newtype Key = Key Int

derive instance eqKey :: Eq Key
derive instance ordKey :: Ord Key

instance showKey :: Show Key where
  show (Key k) = show k <> "%"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a key (black) value, clamping to 0-100
key :: Int -> Key
key n = Key (Bounded.clampInt 0 100 n)

-- | Create a key value without clamping
-- |
-- | Use only when you know the value is valid.
unsafeKey :: Int -> Key
unsafeKey = Key

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Scale key by a factor (0.0 to 2.0 typical)
scale :: Number -> Key -> Key
scale factor (Key k) = 
  key (Int.round (Int.toNumber k * factor))

-- | Increase key by percentage points
increase :: Int -> Key -> Key
increase amount (Key k) = key (k + amount)

-- | Decrease key by percentage points
decrease :: Int -> Key -> Key
decrease amount (Key k) = key (k - amount)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if this is "rich black" (K > 80%)
-- |
-- | Rich blacks combine high K with some CMY for deeper, richer blacks.
-- | Common in print for backgrounds and large black areas.
isRichBlack :: Key -> Boolean
isRichBlack (Key k) = k > 80

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Int value
unwrap :: Key -> Int
unwrap (Key k) = k

-- | Convert to Number for calculations
toNumber :: Key -> Number
toNumber (Key k) = Int.toNumber k

-- | Convert to unit interval (0.0-1.0)
toUnitInterval :: Key -> Number
toUnitInterval (Key k) = Int.toNumber k / 100.0

-- | Bounds documentation for this type
bounds :: Bounded.IntBounds
bounds = Bounded.intBounds 0 100 "key" "Black (Key) ink percentage"
