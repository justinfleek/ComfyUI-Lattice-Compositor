-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // schema // color // srgb
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | sRGB color molecule — RGB with sRGB gamma curve.
-- |
-- | sRGB is the **web standard color space**. All web browsers, CSS colors,
-- | and HTML rendering assumes sRGB unless explicitly specified otherwise.
-- |
-- | ## Difference from RGB
-- |
-- | - **RGB**: Generic additive color, device-dependent
-- | - **sRGB**: Standardized color space with specific gamma curve (~2.2)
-- |
-- | sRGB defines:
-- | - Standard primaries (specific red, green, blue wavelengths)
-- | - Standard white point (D65 - daylight)
-- | - Standard gamma transfer function (piece-wise, not pure 2.2)
-- |
-- | ## Guaranteed Properties
-- |
-- | - Values 0-255 are always in-gamut (by definition)
-- | - Same values produce same colors across compliant displays
-- | - Direct CSS output without conversion
-- | - Compatible with all web standards
-- |
-- | ## When to Use
-- |
-- | - Web rendering (always)
-- | - CSS output
-- | - HTML/SVG colors
-- | - Default color space for UI
-- |
-- | For wide-gamut or color-accurate work, see DisplayP3, AdobeRGB, ProPhotoRGB.

module Hydrogen.Schema.Color.SRGB
  ( -- * Types
    SRGB
  , SRGBA
  
  -- * SRGB Constructors
  , srgb
  , srgbFromRecord
  , srgbFromChannels
  , srgbFromRGB
  
  -- * SRGB Accessors
  , red
  , green
  , blue
  , srgbToRecord
  
  -- * SRGB Operations
  , invert
  , blend
  , add
  , multiply
  , screen
  
  -- * SRGB Legacy CSS Output (for interop with legacy systems)
  , srgbToLegacyCss
  , srgbToHex
  , srgbToRGB
  
  -- * SRGBA Constructors
  , srgba
  , srgbaFromRecord
  
  -- * SRGBA Accessors
  , alpha
  , srgbaToRecord
  
  -- * SRGBA Output
  , srgbaToCss
  
  -- * Conversion
  , toSRGBA
  , fromSRGBA
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  )

import Data.Int as Int
import Hydrogen.Schema.Color.Channel as Ch
import Hydrogen.Schema.Color.Opacity as Op
import Hydrogen.Schema.Color.RGB as RGB

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // srgb
-- ═════════════════════════════════════════════════════════════════════════════

-- | sRGB color value — web standard RGB with gamma curve.
-- |
-- | This is a newtype wrapper around RGB that tags it as specifically sRGB.
-- | The gamma encoding is implicit in the representation (0-255 are gamma-encoded).
newtype SRGB = SRGB RGB.RGB

derive newtype instance eqSRGB :: Eq SRGB
derive newtype instance ordSRGB :: Ord SRGB

instance showSRGB :: Show SRGB where
  show = srgbToLegacyCss

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create an sRGB color from raw channel values.
-- |
-- | Values are clamped to 0-255 by the underlying Channel atoms.
-- |
-- | ```purescript
-- | srgb 255 128 0    -- Orange in web standard sRGB
-- | srgb 0 0 0        -- Black
-- | srgb 255 255 255  -- White
-- | ```
srgb :: Int -> Int -> Int -> SRGB
srgb r g b = SRGB (RGB.rgb r g b)

-- | Create from a record of raw values.
srgbFromRecord :: { r :: Int, g :: Int, b :: Int } -> SRGB
srgbFromRecord { r, g, b } = srgb r g b

-- | Create from already-validated Channel atoms.
srgbFromChannels :: Ch.Channel -> Ch.Channel -> Ch.Channel -> SRGB
srgbFromChannels r g b = SRGB (RGB.rgbFromChannels r g b)

-- | Create sRGB from generic RGB (assumes RGB is already sRGB-encoded).
srgbFromRGB :: RGB.RGB -> SRGB
srgbFromRGB = SRGB

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the red channel.
red :: SRGB -> Ch.Channel
red (SRGB rgb) = RGB.red rgb

-- | Extract the green channel.
green :: SRGB -> Ch.Channel
green (SRGB rgb) = RGB.green rgb

-- | Extract the blue channel.
blue :: SRGB -> Ch.Channel
blue (SRGB rgb) = RGB.blue rgb

-- | Convert to record.
srgbToRecord :: SRGB -> { r :: Ch.Channel, g :: Ch.Channel, b :: Ch.Channel }
srgbToRecord (SRGB rgb) = 
  { r: RGB.red rgb
  , g: RGB.green rgb
  , b: RGB.blue rgb
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Invert an sRGB color.
invert :: SRGB -> SRGB
invert (SRGB rgb) = SRGB (RGB.invert rgb)

-- | Blend two sRGB colors.
blend :: Number -> SRGB -> SRGB -> SRGB
blend t (SRGB a) (SRGB b) = SRGB (RGB.blend t a b)

-- | Add two sRGB colors (clamps to 255).
add :: SRGB -> SRGB -> SRGB
add (SRGB a) (SRGB b) = SRGB (RGB.add a b)

-- | Multiply two sRGB colors.
multiply :: SRGB -> SRGB -> SRGB
multiply (SRGB a) (SRGB b) = SRGB (RGB.multiply a b)

-- | Screen blend mode.
screen :: SRGB -> SRGB -> SRGB
screen (SRGB a) (SRGB b) = SRGB (RGB.screen a b)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // output
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert to CSS rgb() string.
-- | Convert to CSS string for legacy system interop.
-- |
-- | **NOTE:** Hydrogen renders via WebGPU, NOT CSS. This function exists only
-- | for exporting to legacy systems that require CSS format.
-- |
-- | ```purescript
-- | srgbToLegacyCss (srgb 255 128 0)  -- "rgb(255, 128, 0)"
-- | ```
srgbToLegacyCss :: SRGB -> String
srgbToLegacyCss (SRGB rgb) = RGB.rgbToLegacyCss rgb

-- | Convert to hex string.
-- |
-- | ```purescript
-- | srgbToHex (srgb 255 128 0)  -- "#ff8000"
-- | ```
srgbToHex :: SRGB -> String
srgbToHex (SRGB rgb) = RGB.rgbToHex rgb

-- | Convert back to generic RGB.
srgbToRGB :: SRGB -> RGB.RGB
srgbToRGB (SRGB rgb) = rgb

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // srgba
-- ═════════════════════════════════════════════════════════════════════════════

-- | sRGBA — sRGB with alpha channel.
newtype SRGBA = SRGBA { color :: SRGB, alpha :: Op.Opacity }

derive instance eqSRGBA :: Eq SRGBA

instance showSRGBA :: Show SRGBA where
  show = srgbaToCss

-- | Create an sRGBA color.
-- |
-- | Alpha is specified as a Number (0.0-1.0) and converted to Opacity (0-100).
srgba :: Int -> Int -> Int -> Number -> SRGBA
srgba r g b a = SRGBA
  { color: srgb r g b
  , alpha: Op.fromUnitInterval a
  }

-- | Create from record.
srgbaFromRecord :: { r :: Int, g :: Int, b :: Int, a :: Number } -> SRGBA
srgbaFromRecord { r, g, b, a } = srgba r g b a

-- | Extract alpha channel.
alpha :: SRGBA -> Op.Opacity
alpha (SRGBA c) = c.alpha

-- | Convert to record.
srgbaToRecord :: SRGBA -> { r :: Ch.Channel, g :: Ch.Channel, b :: Ch.Channel, a :: Op.Opacity }
srgbaToRecord (SRGBA c) =
  let rgb = srgbToRecord c.color
  in { r: rgb.r, g: rgb.g, b: rgb.b, a: c.alpha }

-- | Convert to CSS rgba() string.
-- |
-- | ```purescript
-- | srgbaToCss (srgba 255 128 0 0.5)  -- "rgba(255, 128, 0, 0.5)"
-- | ```
srgbaToCss :: SRGBA -> String
srgbaToCss (SRGBA c) =
  let rgb = srgbToRecord c.color
      r = show (Ch.unwrap rgb.r)
      g = show (Ch.unwrap rgb.g)
      b = show (Ch.unwrap rgb.b)
      a = show (Op.unwrap c.alpha)
  in "rgba(" <> r <> ", " <> g <> ", " <> b <> ", " <> a <> ")"

-- | Add alpha to sRGB (creates SRGBA).
toSRGBA :: SRGB -> Op.Opacity -> SRGBA
toSRGBA color alpha' = SRGBA { color, alpha: alpha' }

-- | Remove alpha from SRGBA (drops alpha channel).
fromSRGBA :: SRGBA -> SRGB
fromSRGBA (SRGBA c) = c.color
