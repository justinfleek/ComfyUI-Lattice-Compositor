-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // schema // color // cmyk
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | CMYK color molecule - composition of Cyan, Magenta, Yellow, Key atoms.
-- |
-- | CMYK is the subtractive color model used in color printing:
-- | - **Cyan**: Absorbs red light (0-100%)
-- | - **Magenta**: Absorbs green light (0-100%)
-- | - **Yellow**: Absorbs blue light (0-100%)
-- | - **Key (Black)**: True black ink (0-100%)
-- |
-- | ## Subtractive Color Mixing
-- |
-- | Unlike RGB (additive - light-based), CMYK is subtractive (ink/pigment-based):
-- | ```
-- | Cyan + Magenta        = Blue
-- | Magenta + Yellow      = Red
-- | Yellow + Cyan         = Green
-- | Cyan + Magenta + Yellow = Dark Brown (not true black - that's why K exists)
-- | ```
-- |
-- | ## Print Applications
-- |
-- | CMYK is essential for:
-- | - Print-on-demand products (t-shirts, mugs, posters)
-- | - Professional printing (brochures, business cards)
-- | - Color accuracy preview ("will this RGB color print correctly?")
-- | - Gamut warnings ("this bright green can't be printed in CMYK")

module Hydrogen.Schema.Color.CMYK
  ( -- * Types
    CMYK
  
  -- * Constructors
  , cmyk
  , cmykFromRecord
  , cmykFromComponents
  
  -- * Accessors
  , cyan
  , magenta
  , yellow
  , key
  , cmykToRecord
  
  -- * CSS Output
  , cmykToCss
  
  -- * Conversion
  , rgbToCmyk
  , cmykToRgb
  ) where

import Prelude (class Eq, class Ord, class Show, show, (<>), (/), (*), (-), (>=))

import Data.Int (round, toNumber) as Int
import Hydrogen.Schema.Color.Cyan as C
import Hydrogen.Schema.Color.Magenta as M
import Hydrogen.Schema.Color.Yellow as Y
import Hydrogen.Schema.Color.Key as K
import Hydrogen.Schema.Color.RGB as RGB
import Hydrogen.Schema.Color.Channel as Ch
import Hydrogen.Math.Core as Math

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // cmyk
-- ═════════════════════════════════════════════════════════════════════════════

-- | CMYK color value — a molecule composed of four ink percentage atoms.
-- |
-- | This is a lawful composition: if Cyan, Magenta, Yellow, and Key are each
-- | correct (0-100, clamped), then CMYK is correct by construction.
newtype CMYK = CMYK
  { cyan :: C.Cyan
  , magenta :: M.Magenta
  , yellow :: Y.Yellow
  , key :: K.Key
  }

derive instance eqCMYK :: Eq CMYK
derive instance ordCMYK :: Ord CMYK

instance showCMYK :: Show CMYK where
  show = cmykToCss

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a CMYK color from raw percentage values.
-- |
-- | All values are ink percentages (0-100):
-- | ```purescript
-- | cmyk 0 100 100 0    -- Red (no cyan, full magenta+yellow)
-- | cmyk 100 0 0 0      -- Cyan
-- | cmyk 0 0 0 100      -- Pure black
-- | cmyk 50 40 40 100   -- Rich black (black + some color)
-- | ```
cmyk :: Int -> Int -> Int -> Int -> CMYK
cmyk c m y k = CMYK
  { cyan: C.cyan c
  , magenta: M.magenta m
  , yellow: Y.yellow y
  , key: K.key k
  }

-- | Create from a record of raw values.
cmykFromRecord :: { c :: Int, m :: Int, y :: Int, k :: Int } -> CMYK
cmykFromRecord { c, m, y, k } = cmyk c m y k

-- | Create from already-validated atoms.
-- |
-- | Use when you already have valid Cyan, Magenta, Yellow, Key values.
cmykFromComponents :: C.Cyan -> M.Magenta -> Y.Yellow -> K.Key -> CMYK
cmykFromComponents c m y k = CMYK { cyan: c, magenta: m, yellow: y, key: k }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the cyan component.
cyan :: CMYK -> C.Cyan
cyan (CMYK c) = c.cyan

-- | Extract the magenta component.
magenta :: CMYK -> M.Magenta
magenta (CMYK c) = c.magenta

-- | Extract the yellow component.
yellow :: CMYK -> Y.Yellow
yellow (CMYK c) = c.yellow

-- | Extract the key (black) component.
key :: CMYK -> K.Key
key (CMYK c) = c.key

-- | Convert to a record of raw Int values.
-- |
-- | Useful for interop with other systems or JSON serialization.
cmykToRecord :: CMYK -> { c :: Int, m :: Int, y :: Int, k :: Int }
cmykToRecord (CMYK c) =
  { c: C.unwrap c.cyan
  , m: M.unwrap c.magenta
  , y: Y.unwrap c.yellow
  , k: K.unwrap c.key
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // css output
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert to CSS device-cmyk() function string.
-- |
-- | Uses CSS Color Level 4 device-cmyk() syntax:
-- | ```purescript
-- | cmykToCss (cmyk 0 100 100 0)  -- "device-cmyk(0%, 100%, 100%, 0%)"
-- | ```
cmykToCss :: CMYK -> String
cmykToCss (CMYK c) =
  "device-cmyk(" 
  <> show (C.unwrap c.cyan) <> "%"
  <> ", " <> show (M.unwrap c.magenta) <> "%"
  <> ", " <> show (Y.unwrap c.yellow) <> "%"
  <> ", " <> show (K.unwrap c.key) <> "%)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert RGB to CMYK.
-- |
-- | This is an approximation - actual conversion depends on color profiles,
-- | ink characteristics, and paper type. For print-accurate conversion,
-- | use ICC color profiles.
-- |
-- | Algorithm:
-- | 1. Normalize RGB to 0.0-1.0
-- | 2. Calculate K = 1 - max(R, G, B)
-- | 3. If K = 1 (black), C=M=Y=0
-- | 4. Otherwise: C = (1-R-K)/(1-K), M = (1-G-K)/(1-K), Y = (1-B-K)/(1-K)
-- |
-- | ```purescript
-- | rgbToCmyk (RGB.rgb 255 0 0)  -- Red → CMYK(0, 100, 100, 0)
-- | rgbToCmyk (RGB.rgb 0 0 0)    -- Black → CMYK(0, 0, 0, 100)
-- | ```
rgbToCmyk :: RGB.RGB -> CMYK
rgbToCmyk rgb =
  let
    r = Int.toNumber (Ch.unwrap (RGB.red rgb)) / 255.0
    g = Int.toNumber (Ch.unwrap (RGB.green rgb)) / 255.0
    b = Int.toNumber (Ch.unwrap (RGB.blue rgb)) / 255.0
    
    k = 1.0 - Math.max (Math.max r g) b
    
    -- If completely black, CMY are all 0
    result = if k >= 1.0
      then { c: 0.0, m: 0.0, y: 0.0, k: 1.0 }
      else
        { c: (1.0 - r - k) / (1.0 - k)
        , m: (1.0 - g - k) / (1.0 - k)
        , y: (1.0 - b - k) / (1.0 - k)
        , k: k
        }
  in
    cmyk
      (Int.round (result.c * 100.0))
      (Int.round (result.m * 100.0))
      (Int.round (result.y * 100.0))
      (Int.round (result.k * 100.0))

-- | Convert CMYK to RGB.
-- |
-- | This is an approximation - actual conversion depends on color profiles,
-- | ink characteristics, and paper type. For accurate conversion, use ICC
-- | color profiles.
-- |
-- | Algorithm:
-- | 1. Normalize CMYK to 0.0-1.0
-- | 2. R = 255 × (1-C) × (1-K)
-- | 3. G = 255 × (1-M) × (1-K)
-- | 4. B = 255 × (1-Y) × (1-K)
-- |
-- | ```purescript
-- | cmykToRgb (cmyk 0 100 100 0)  -- CMYK Red → RGB(255, 0, 0)
-- | ```
cmykToRgb :: CMYK -> RGB.RGB
cmykToRgb (CMYK c) =
  let
    cVal = C.toUnitInterval c.cyan
    mVal = M.toUnitInterval c.magenta
    yVal = Y.toUnitInterval c.yellow
    kVal = K.toUnitInterval c.key
    
    r = 255.0 * (1.0 - cVal) * (1.0 - kVal)
    g = 255.0 * (1.0 - mVal) * (1.0 - kVal)
    b = 255.0 * (1.0 - yVal) * (1.0 - kVal)
  in
    RGB.rgb
      (Int.round r)
      (Int.round g)
      (Int.round b)
