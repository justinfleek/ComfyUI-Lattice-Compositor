-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // schema // color // hsl
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | HSL color molecule - composition of Hue, Saturation, Lightness atoms.
-- |
-- | HSL (Hue, Saturation, Lightness) is a cylindrical color space that
-- | separates color identity (hue) from color properties (saturation, lightness).
-- | This makes it intuitive for color manipulation:
-- |
-- | - **Hue**: Position on the color wheel (0-359°)
-- | - **Saturation**: Color intensity/purity (0-100%)
-- | - **Lightness**: Light/dark level (0-100%)
-- |
-- | ## Color Wheel Reference
-- |
-- | ```
-- |   0°/360° = Red
-- |      60°  = Yellow
-- |     120°  = Green
-- |     180°  = Cyan
-- |     240°  = Blue
-- |     300°  = Magenta
-- | ```
-- |
-- | ## Lightness Behavior
-- |
-- | - At L=0%, any hue is black
-- | - At L=50%, colors are most vivid
-- | - At L=100%, any hue is white

module Hydrogen.Schema.Color.HSL
  ( -- * Types
    HSL
  
  -- * Constructors
  , hsl
  , hslFromRecord
  , fromRecord
  , fromComponents
  
  -- * Accessors
  , hue
  , saturation
  , lightness
  , hslToRecord
  , toRecord
  
  -- * Operations (HSL-space, NOT perceptually uniform)
  , rotateHue
  , complement
  , increaseLightness
  , decreaseLightness
  , increaseSaturation
  , decreaseSaturation
  , grayscale
  
  -- * CSS Output (Legacy string generation, NOT FFI)
  , toLegacyCss
  
  -- * Interop
  , fromLegacy
  , toLegacy
  ) where

import Prelude

import Hydrogen.Schema.Color.Hue as Hue
import Hydrogen.Schema.Color.Saturation as Sat
import Hydrogen.Schema.Color.Lightness as Light

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                        // hsl
-- ═════════════════════════════════════════════════════════════════════════════

-- | HSL color value - a molecule composed of three atoms.
-- |
-- | This is a lawful composition: if Hue, Saturation, and Lightness are each
-- | correct (valid bounds, proper semantics), then HSL is correct by construction.
newtype HSL = HSL
  { hue :: Hue.Hue
  , saturation :: Sat.Saturation
  , lightness :: Light.Lightness
  }

derive instance eqHSL :: Eq HSL
derive instance ordHSL :: Ord HSL

instance showHSL :: Show HSL where
  show = toLegacyCss

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create an HSL color from raw values.
-- |
-- | Values are normalized by the underlying atoms:
-- | - Hue clamps to 0-359 (use `rotate` for wrapping behavior)
-- | - Saturation clamps to 0-100
-- | - Lightness clamps to 0-100
-- |
-- | ```purescript
-- | hsl 210 80 50  -- Ocean blue
-- | hsl 0 100 50   -- Pure red
-- | hsl 120 100 25 -- Dark green
-- | ```
hsl :: Int -> Int -> Int -> HSL
hsl h s l = HSL
  { hue: Hue.hue h
  , saturation: Sat.saturation s
  , lightness: Light.lightness l
  }

-- | Create from a record of raw values.
-- | **Explicitly named for backend persistence** - no conflicts with other color spaces.
hslFromRecord :: { h :: Int, s :: Int, l :: Int } -> HSL
hslFromRecord { h, s, l } = hsl h s l

-- | Generic alias for hslFromRecord
fromRecord :: { h :: Int, s :: Int, l :: Int } -> HSL
fromRecord = hslFromRecord

-- | Create from already-validated atoms.
-- |
-- | Use when you already have valid Hue, Saturation, Lightness values.
fromComponents :: Hue.Hue -> Sat.Saturation -> Light.Lightness -> HSL
fromComponents h s l = HSL { hue: h, saturation: s, lightness: l }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the hue component.
hue :: HSL -> Hue.Hue
hue (HSL c) = c.hue

-- | Extract the saturation component.
saturation :: HSL -> Sat.Saturation
saturation (HSL c) = c.saturation

-- | Extract the lightness component.
lightness :: HSL -> Light.Lightness
lightness (HSL c) = c.lightness

-- | Convert to a record of raw Int values.
-- |
-- | Useful for interop with other systems or JSON serialization.
-- | **Explicitly named for backend persistence** - no conflicts with other color spaces.
hslToRecord :: HSL -> { h :: Int, s :: Int, l :: Int }
hslToRecord (HSL c) =
  { h: Hue.unwrap c.hue
  , s: Sat.unwrap c.saturation
  , l: Light.unwrap c.lightness
  }

-- | Generic alias for hslToRecord
toRecord :: HSL -> { h :: Int, s :: Int, l :: Int }
toRecord = hslToRecord

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- ═════════════════════════════════════════════════════════════════════════════
--                                               // operations // explicit names
-- ═════════════════════════════════════════════════════════════════════════════

-- | Rotate hue by degrees (wraps around the color wheel).
-- |
-- | **Semantically explicit name:** `rotateHue` makes clear this operates on hue angle.
-- |
-- | ```purescript
-- | rotateHue 120 (hsl 0 100 50)   -- Red → Green
-- | rotateHue (-60) (hsl 60 100 50) -- Yellow → Red
-- | ```
rotateHue :: Int -> HSL -> HSL
rotateHue degrees (HSL c) = HSL
  { hue: Hue.rotate degrees c.hue
  , saturation: c.saturation
  , lightness: c.lightness
  }

-- | Get the complementary color (opposite on color wheel).
-- |
-- | ```purescript
-- | complement (hsl 0 100 50)   -- Red → Cyan (180°)
-- | complement (hsl 60 100 50)  -- Yellow → Blue (240°)
-- | ```
complement :: HSL -> HSL
complement = rotateHue 180

-- | Increase HSL lightness by percentage points.
-- |
-- | **WARNING:** HSL lightness is NOT perceptually uniform. For accurate "looks 10% lighter"
-- | operations, convert to LAB via Conversion module and use `LAB.increaseLuminance`.
-- |
-- | ```purescript
-- | increaseLightness 20 (hsl 0 100 50)  -- L: 50 → 70 (HSL space, not perceptual)
-- | ```
increaseLightness :: Int -> HSL -> HSL
increaseLightness amount (HSL c) = HSL
  { hue: c.hue
  , saturation: c.saturation
  , lightness: Light.lighten amount c.lightness
  }

-- | Decrease HSL lightness by percentage points.
-- |
-- | **WARNING:** HSL lightness is NOT perceptually uniform. For accurate "looks 10% darker"
-- | operations, convert to LAB via Conversion module and use `LAB.decreaseLuminance`.
-- |
-- | ```purescript
-- | decreaseLightness 20 (hsl 0 100 50)  -- L: 50 → 30 (HSL space, not perceptual)
-- | ```
decreaseLightness :: Int -> HSL -> HSL
decreaseLightness amount (HSL c) = HSL
  { hue: c.hue
  , saturation: c.saturation
  , lightness: Light.darken amount c.lightness
  }

-- | Increase HSL saturation by percentage points.
-- |
-- | **NOTE:** HSL saturation differs from LCH chroma. For perceptually uniform saturation
-- | adjustments, use LCH.increaseChroma.
-- |
-- | ```purescript
-- | increaseSaturation 20 (hsl 0 50 50)  -- S: 50 → 70
-- | ```
increaseSaturation :: Int -> HSL -> HSL
increaseSaturation amount (HSL c) = HSL
  { hue: c.hue
  , saturation: Sat.increase amount c.saturation
  , lightness: c.lightness
  }

-- | Decrease HSL saturation by percentage points.
-- |
-- | **NOTE:** HSL saturation differs from LCH chroma. For perceptually uniform saturation
-- | adjustments, use LCH.decreaseChroma.
-- |
-- | ```purescript
-- | decreaseSaturation 20 (hsl 0 100 50)  -- S: 100 → 80
-- | ```
decreaseSaturation :: Int -> HSL -> HSL
decreaseSaturation amount (HSL c) = HSL
  { hue: c.hue
  , saturation: Sat.decrease amount c.saturation
  , lightness: c.lightness
  }



-- | Convert to grayscale (saturation = 0).
-- |
-- | Preserves hue information (can be re-saturated later).
grayscale :: HSL -> HSL
grayscale (HSL c) = HSL
  { hue: c.hue
  , saturation: Sat.saturation 0
  , lightness: c.lightness
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // css output
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert to legacy CSS hsl() function string.
-- |
-- | This generates a CSS-compatible string for use with legacy rendering.
-- | NOT an FFI boundary - pure string generation.
-- |
-- | ```purescript
-- | toLegacyCss (hsl 210 80 50)  -- "hsl(210, 80%, 50%)"
-- | ```
toLegacyCss :: HSL -> String
toLegacyCss (HSL c) =
  "hsl(" <> show (Hue.unwrap c.hue) 
  <> ", " <> show (Sat.unwrap c.saturation) <> "%"
  <> ", " <> show (Light.unwrap c.lightness) <> "%)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // interop
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert from legacy Value.purs HSL record.
-- |
-- | For migration from `Hydrogen.Schema.Color.Value.HSL` to this module.
fromLegacy :: { h :: Int, s :: Int, l :: Int } -> HSL
fromLegacy = fromRecord

-- | Convert to legacy Value.purs HSL record.
-- |
-- | For interop with code still using `Hydrogen.Schema.Color.Value`.
toLegacy :: HSL -> { h :: Int, s :: Int, l :: Int }
toLegacy = toRecord
