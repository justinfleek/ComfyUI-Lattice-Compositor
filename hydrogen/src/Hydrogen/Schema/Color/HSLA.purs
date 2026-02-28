-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // schema // color // hsla
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | HSLA color molecule - HSL with alpha transparency.
-- |
-- | HSLA extends HSL with an opacity channel, allowing for transparent colors
-- | in the cylindrical color space.
-- |
-- | - **Hue**: Position on the color wheel (0-359°)
-- | - **Saturation**: Color intensity/purity (0-100%)
-- | - **Lightness**: Light/dark level (0-100%)
-- | - **Alpha**: Opacity (0-100%): 0% = transparent, 100% = opaque
-- |
-- | Like HSL, this space is intuitive for color manipulation while supporting
-- | transparency for UI effects, overlays, and compositing.

module Hydrogen.Schema.Color.HSLA
  ( -- * Types
    HSLA
  
  -- * Constructors
  , hsla
  , hslaFromRecord
  , hslaFromComponents
  
  -- * Accessors
  , hue
  , saturation
  , lightness
  , alpha
  , hslaToRecord
  
  -- * Operations
  , rotate
  , complement
  , lighten
  , darken
  , saturate
  , desaturate
  , grayscale
  , fadeIn
  , fadeOut
  , opacify
  , transparentize
  
  -- * CSS Output
  , hslaToCss
  
  -- * Conversion
  , toHSLA
  , fromHSLA
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  )

import Hydrogen.Schema.Color.Hue as Hue
import Hydrogen.Schema.Color.Saturation as Sat
import Hydrogen.Schema.Color.Lightness as Light
import Hydrogen.Schema.Color.Opacity as Op
import Hydrogen.Schema.Color.HSL as HSL

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // hsla
-- ═════════════════════════════════════════════════════════════════════════════

-- | HSLA color value — HSL with an alpha channel.
-- |
-- | Alpha is an Opacity (0-100%): 0% = fully transparent, 100% = fully opaque.
-- | This matches the pattern of other percentage-based atoms in the Schema.
newtype HSLA = HSLA
  { hue :: Hue.Hue
  , saturation :: Sat.Saturation
  , lightness :: Light.Lightness
  , alpha :: Op.Opacity
  }

derive instance eqHSLA :: Eq HSLA
derive instance ordHSLA :: Ord HSLA

instance showHSLA :: Show HSLA where
  show = hslaToCss

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create an HSLA color from raw values.
-- |
-- | - Hue: 0-359 (wraps)
-- | - Saturation: 0-100 (percentage)
-- | - Lightness: 0-100 (percentage)
-- | - Alpha: 0-100 (percentage): 0 = transparent, 100 = opaque
-- |
-- | ```purescript
-- | hsla 210 80 50 100  -- Ocean blue, fully opaque
-- | hsla 0 100 50 50    -- Red, half transparent
-- | hsla 120 100 25 0   -- Dark green, fully transparent
-- | ```
hsla :: Int -> Int -> Int -> Int -> HSLA
hsla h s l a = HSLA
  { hue: Hue.hue h
  , saturation: Sat.saturation s
  , lightness: Light.lightness l
  , alpha: Op.opacity a
  }

-- | Create an HSLA color from a record.
-- |
-- | Alpha is a percentage (0-100).
hslaFromRecord :: { h :: Int, s :: Int, l :: Int, a :: Int } -> HSLA
hslaFromRecord { h, s, l, a } = hsla h s l a

-- | Create from already-validated components.
-- |
-- | Use when you already have valid Hue, Saturation, Lightness, Opacity atoms.
hslaFromComponents :: Hue.Hue -> Sat.Saturation -> Light.Lightness -> Op.Opacity -> HSLA
hslaFromComponents h s l a = HSLA { hue: h, saturation: s, lightness: l, alpha: a }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the hue component.
hue :: HSLA -> Hue.Hue
hue (HSLA c) = c.hue

-- | Extract the saturation component.
saturation :: HSLA -> Sat.Saturation
saturation (HSLA c) = c.saturation

-- | Extract the lightness component.
lightness :: HSLA -> Light.Lightness
lightness (HSLA c) = c.lightness

-- | Extract the alpha (opacity).
alpha :: HSLA -> Op.Opacity
alpha (HSLA c) = c.alpha

-- | Convert HSLA to a record of raw Int values.
-- |
-- | All values are percentages (0-100) except hue (0-359).
hslaToRecord :: HSLA -> { h :: Int, s :: Int, l :: Int, a :: Int }
hslaToRecord (HSLA c) =
  { h: Hue.unwrap c.hue
  , s: Sat.unwrap c.saturation
  , l: Light.unwrap c.lightness
  , a: Op.unwrap c.alpha
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Rotate hue by degrees (wraps around the color wheel).
-- |
-- | Preserves alpha.
-- |
-- | ```purescript
-- | rotate 120 (hsla 0 100 50 50)   -- Red → Green (half transparent)
-- | rotate (-60) (hsla 60 100 50 100) -- Yellow → Red (opaque)
-- | ```
rotate :: Int -> HSLA -> HSLA
rotate degrees (HSLA c) = HSLA
  { hue: Hue.rotate degrees c.hue
  , saturation: c.saturation
  , lightness: c.lightness
  , alpha: c.alpha
  }

-- | Get the complementary color (opposite on color wheel).
-- |
-- | Preserves alpha.
-- |
-- | ```purescript
-- | complement (hsla 0 100 50 50)   -- Red → Cyan (180°), half transparent
-- | complement (hsla 60 100 50 100)  -- Yellow → Blue (240°), opaque
-- | ```
complement :: HSLA -> HSLA
complement = rotate 180

-- | Increase lightness by percentage points.
-- |
-- | Preserves alpha.
-- |
-- | ```purescript
-- | lighten 20 (hsla 0 100 50 50)  -- L: 50 → 70, alpha unchanged
-- | ```
lighten :: Int -> HSLA -> HSLA
lighten amount (HSLA c) = HSLA
  { hue: c.hue
  , saturation: c.saturation
  , lightness: Light.lighten amount c.lightness
  , alpha: c.alpha
  }

-- | Decrease lightness by percentage points.
-- |
-- | Preserves alpha.
-- |
-- | ```purescript
-- | darken 20 (hsla 0 100 50 50)  -- L: 50 → 30, alpha unchanged
-- | ```
darken :: Int -> HSLA -> HSLA
darken amount (HSLA c) = HSLA
  { hue: c.hue
  , saturation: c.saturation
  , lightness: Light.darken amount c.lightness
  , alpha: c.alpha
  }

-- | Increase saturation by percentage points.
-- |
-- | Preserves alpha.
-- |
-- | ```purescript
-- | saturate 20 (hsla 0 50 50 50)  -- S: 50 → 70, alpha unchanged
-- | ```
saturate :: Int -> HSLA -> HSLA
saturate amount (HSLA c) = HSLA
  { hue: c.hue
  , saturation: Sat.increase amount c.saturation
  , lightness: c.lightness
  , alpha: c.alpha
  }

-- | Decrease saturation by percentage points.
-- |
-- | Preserves alpha.
-- |
-- | ```purescript
-- | desaturate 20 (hsla 0 100 50 50)  -- S: 100 → 80, alpha unchanged
-- | ```
desaturate :: Int -> HSLA -> HSLA
desaturate amount (HSLA c) = HSLA
  { hue: c.hue
  , saturation: Sat.decrease amount c.saturation
  , lightness: c.lightness
  , alpha: c.alpha
  }

-- | Convert to grayscale (saturation = 0).
-- |
-- | Preserves hue information (can be re-saturated later) and alpha.
-- |
-- | ```purescript
-- | grayscale (hsla 0 100 50 50)  -- Gray, half transparent
-- | ```
grayscale :: HSLA -> HSLA
grayscale (HSLA c) = HSLA
  { hue: c.hue
  , saturation: Sat.saturation 0
  , lightness: c.lightness
  , alpha: c.alpha
  }

-- | Increase opacity by percentage points (make more opaque).
-- |
-- | Alias for `opacify` - makes color less transparent.
-- |
-- | ```purescript
-- | fadeIn 20 (hsla 0 100 50 30)  -- Alpha: 30 → 50
-- | ```
fadeIn :: Int -> HSLA -> HSLA
fadeIn amount (HSLA c) = HSLA
  { hue: c.hue
  , saturation: c.saturation
  , lightness: c.lightness
  , alpha: Op.increase amount c.alpha
  }

-- | Decrease opacity by percentage points (make more transparent).
-- |
-- | Alias for `transparentize` - makes color more transparent.
-- |
-- | ```purescript
-- | fadeOut 20 (hsla 0 100 50 50)  -- Alpha: 50 → 30
-- | ```
fadeOut :: Int -> HSLA -> HSLA
fadeOut amount (HSLA c) = HSLA
  { hue: c.hue
  , saturation: c.saturation
  , lightness: c.lightness
  , alpha: Op.decrease amount c.alpha
  }

-- | Increase opacity by percentage points (make more opaque).
-- |
-- | Same as `fadeIn` - provided for semantic clarity in different contexts.
opacify :: Int -> HSLA -> HSLA
opacify = fadeIn

-- | Decrease opacity by percentage points (make more transparent).
-- |
-- | Same as `fadeOut` - provided for semantic clarity in different contexts.
transparentize :: Int -> HSLA -> HSLA
transparentize = fadeOut

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // css output
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert to CSS hsla() function string.
-- |
-- | CSS expects alpha as 0.0-1.0, so we use Opacity.toUnitInterval.
-- |
-- | ```purescript
-- | hslaToCss (hsla 210 80 50 100)  -- "hsla(210, 80%, 50%, 1.0)"
-- | hslaToCss (hsla 0 100 50 50)    -- "hsla(0, 100%, 50%, 0.5)"
-- | ```
hslaToCss :: HSLA -> String
hslaToCss (HSLA c) =
  let a' = Op.toUnitInterval c.alpha
  in "hsla(" <> show (Hue.unwrap c.hue)
  <> ", " <> show (Sat.unwrap c.saturation) <> "%"
  <> ", " <> show (Light.unwrap c.lightness) <> "%"
  <> ", " <> show a' <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert HSL to HSLA with full opacity (100%).
toHSLA :: HSL.HSL -> HSLA
toHSLA hsl = HSLA
  { hue: HSL.hue hsl
  , saturation: HSL.saturation hsl
  , lightness: HSL.lightness hsl
  , alpha: Op.opacity 100
  }

-- | Convert HSLA to HSL (drops alpha).
fromHSLA :: HSLA -> HSL.HSL
fromHSLA (HSLA c) = HSL.fromComponents c.hue c.saturation c.lightness
