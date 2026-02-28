-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // schema // color // hwb
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | HWB - Hue, Whiteness, Blackness (CSS Color Level 4).
-- |
-- | **MORE INTUITIVE THAN HSL:**
-- | Instead of saturation and lightness, HWB uses:
-- | - How much white is mixed in (whiteness)
-- | - How much black is mixed in (blackness)
-- |
-- | **Components:**
-- | - **H**: Hue, 0-360 degrees (color wheel position)
-- | - **W**: Whiteness, 0-100% (amount of white mixed in)
-- | - **B**: Blackness, 0-100% (amount of black mixed in)
-- |
-- | **Use cases:**
-- | - CSS4 hwb() function
-- | - More intuitive color picking for designers
-- | - "Make it lighter" = increase whiteness
-- | - "Make it darker" = increase blackness
-- |
-- | **CSS Example:**
-- | hwb(120deg 20% 10%) - green with 20% white, 10% black

module Hydrogen.Schema.Color.HWB
  ( -- * Types
    HWB
  , Whiteness
  , Blackness
  
  -- * Constructors
  , hwb
  , hwbFromRecord
  , whiteness
  , blackness
  
  -- * Accessors
  , hue
  , getWhiteness
  , getBlackness
  , unwrapWhiteness
  , unwrapBlackness
  , hwbToRecord
  , toRecord
  
  -- * Operations
  , rotateHue
  , increaseWhiteness
  , increaseBlackness
  
  -- * CSS Output (Legacy string generation, NOT FFI)
  , toLegacyCss
  ) where

import Prelude

import Hydrogen.Schema.Bounded as Bounded
import Hydrogen.Schema.Color.Hue (Hue)
import Hydrogen.Schema.Color.Hue as Hue

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // atoms
-- ═════════════════════════════════════════════════════════════════════════════

-- | Whiteness component: 0-100%
newtype Whiteness = Whiteness Int

derive instance eqWhiteness :: Eq Whiteness
derive instance ordWhiteness :: Ord Whiteness

instance showWhiteness :: Show Whiteness where
  show (Whiteness w) = show w <> "%"

-- | Create whiteness value (clamped 0-100)
whiteness :: Int -> Whiteness
whiteness n = Whiteness (Bounded.clampInt 0 100 n)

unwrapWhiteness :: Whiteness -> Int
unwrapWhiteness (Whiteness w) = w

-- | Blackness component: 0-100%
newtype Blackness = Blackness Int

derive instance eqBlackness :: Eq Blackness
derive instance ordBlackness :: Ord Blackness

instance showBlackness :: Show Blackness where
  show (Blackness b) = show b <> "%"

-- | Create blackness value (clamped 0-100)
blackness :: Int -> Blackness
blackness n = Blackness (Bounded.clampInt 0 100 n)

unwrapBlackness :: Blackness -> Int
unwrapBlackness (Blackness b) = b

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // molecule
-- ═════════════════════════════════════════════════════════════════════════════

-- | HWB color - composition of Hue, Whiteness, Blackness
newtype HWB = HWB
  { h :: Hue
  , w :: Whiteness
  , b :: Blackness
  }

derive instance eqHWB :: Eq HWB
derive instance ordHWB :: Ord HWB

instance showHWB :: Show HWB where
  show = toLegacyCss

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create HWB color
hwb :: Int -> Int -> Int -> HWB
hwb h w b = HWB
  { h: Hue.hue h
  , w: whiteness w
  , b: blackness b
  }

-- | Create from record
hwbFromRecord :: { h :: Int, w :: Int, b :: Int } -> HWB
hwbFromRecord { h, w, b } = hwb h w b

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract hue
hue :: HWB -> Hue
hue (HWB c) = c.h

-- | Extract whiteness
getWhiteness :: HWB -> Whiteness
getWhiteness (HWB c) = c.w

-- | Extract blackness
getBlackness :: HWB -> Blackness
getBlackness (HWB c) = c.b

-- | Convert to record
hwbToRecord :: HWB -> { h :: Int, w :: Int, b :: Int }
hwbToRecord (HWB c) =
  { h: Hue.unwrap c.h
  , w: unwrapWhiteness c.w
  , b: unwrapBlackness c.b
  }

-- | Alias for hwbToRecord
toRecord :: HWB -> { h :: Int, w :: Int, b :: Int }
toRecord = hwbToRecord

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Rotate hue by degrees
rotateHue :: Int -> HWB -> HWB
rotateHue degrees (HWB c) = HWB c { h = Hue.rotate degrees c.h }

-- | Increase whiteness (make lighter)
increaseWhiteness :: Int -> HWB -> HWB
increaseWhiteness amount (HWB c) = HWB c { w = whiteness (unwrapWhiteness c.w + amount) }

-- | Increase blackness (make darker)
increaseBlackness :: Int -> HWB -> HWB
increaseBlackness amount (HWB c) = HWB c { b = blackness (unwrapBlackness c.b + amount) }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // css output
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert to legacy CSS hwb() function string.
-- |
-- | This generates a CSS-compatible string for use with legacy rendering.
-- | NOT an FFI boundary - pure string generation.
toLegacyCss :: HWB -> String
toLegacyCss (HWB c) = 
  "hwb(" <> show (Hue.unwrap c.h) <> "deg " 
         <> show (unwrapWhiteness c.w) <> "% " 
         <> show (unwrapBlackness c.b) <> "%)"
