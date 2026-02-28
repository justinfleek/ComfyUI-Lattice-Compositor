-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // color // linear-rgb
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | LinearRGB — Linear-light RGB molecule for color math.
-- |
-- | **WHY LINEAR RGB MATTERS:**
-- | sRGB applies a nonlinear "gamma" encoding to compress highlight detail.
-- | This encoding is perceptually motivated but mathematically problematic:
-- | - Blending in sRGB produces incorrect results
-- | - Light calculations require linear values
-- | - Color transformations need linear input
-- |
-- | **The sRGB Transfer Function:**
-- | Linear → sRGB (gamma encoding):
-- |   if linear ≤ 0.0031308:
-- |     srgb = 12.92 × linear
-- |   else:
-- |     srgb = 1.055 × linear^(1/2.4) - 0.055
-- |
-- | sRGB → Linear (gamma decoding):
-- |   if srgb ≤ 0.04045:
-- |     linear = srgb / 12.92
-- |   else:
-- |     linear = ((srgb + 0.055) / 1.055)^2.4
-- |
-- | **When to use LinearRGB:**
-- | - Blending/compositing operations
-- | - Lighting calculations
-- | - Color space conversions (through XYZ)
-- | - Any additive color math
-- |
-- | **When to use sRGB:**
-- | - Display output
-- | - Storage (8-bit images)
-- | - CSS/web colors

module Hydrogen.Schema.Color.LinearRGB
  ( -- * Types
    LinearChannel
  , LinearRGB
  , LinearRGBA
  
  -- * LinearChannel Constructors
  , linearChannel
  , linearChannelSafe
  , unwrapLinearChannel
  
  -- * LinearRGB Constructors
  , linearRGB
  , linearRGBFromRecord
  
  -- * LinearRGB Accessors
  , linearRed
  , linearGreen
  , linearBlue
  , linearRGBToRecord
  
  -- * LinearRGBA Constructors
  , linearRGBA
  , linearRGBAFromRecord
  
  -- * LinearRGBA Accessors
  , linearAlpha
  , linearRGBAToRecord
  
  -- * sRGB Conversion
  , fromSRGB
  , toSRGB
  , fromSRGBA
  , toSRGBA
  
  -- * Operations (in linear space)
  , blend
  , add
  , scale
  , multiply
  , luminance
  
  -- * Comparison
  , isBlack
  , isWhite
  , isEqual
  , isNotEqual
  , isGray
  , isInSDRRange
  , isHDR
  , isBrighterThan
  , isDarkerThan
  
  -- * Channel Operations
  , linearChannelBlend
  , linearChannelScale
  , linearChannelAdd
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , (&&)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (<=)
  , (>)
  , (>=)
  , (==)
  , (/=)
  , (||)
  , (<>)
  )

import Data.Int (round, toNumber)
import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Math.Core as Math
import Hydrogen.Schema.Bounded as Bounded
import Hydrogen.Schema.Color.RGB (RGB, rgb, rgbToRecord) as RGB
import Hydrogen.Schema.Color.RGB (RGBA, rgba, rgbaToRecord) as RGBA
import Hydrogen.Schema.Color.Opacity (Opacity, opacity, toUnitInterval, fromUnitInterval) as Op

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // linear channel
-- ═════════════════════════════════════════════════════════════════════════════

-- | Linear-light channel value (0.0-1.0, can exceed for HDR)
-- |
-- | Represents physical light intensity before gamma encoding.
-- | Values are clamped to >= 0.0 (negative light is impossible).
-- | Values > 1.0 are allowed for HDR content.
newtype LinearChannel = LinearChannel Number

derive instance eqLinearChannel :: Eq LinearChannel
derive instance ordLinearChannel :: Ord LinearChannel

instance showLinearChannel :: Show LinearChannel where
  show (LinearChannel n) = show n

-- | Create a linear channel value (clamped to >= 0.0)
linearChannel :: Number -> LinearChannel
linearChannel n = LinearChannel (Bounded.clampNumberMin 0.0 n)

-- | Create a linear channel with validation (must be >= 0.0)
linearChannelSafe :: Number -> Maybe LinearChannel
linearChannelSafe n
  | n >= 0.0 = Just (LinearChannel n)
  | otherwise = Nothing

-- | Extract raw value
unwrapLinearChannel :: LinearChannel -> Number
unwrapLinearChannel (LinearChannel n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // linear channel operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Blend two linear channels (correct in linear space)
linearChannelBlend :: Number -> LinearChannel -> LinearChannel -> LinearChannel
linearChannelBlend weight (LinearChannel a) (LinearChannel b) =
  let w = Bounded.clampNumber 0.0 1.0 weight
  in linearChannel (a * (1.0 - w) + b * w)

-- | Scale a linear channel
linearChannelScale :: Number -> LinearChannel -> LinearChannel
linearChannelScale factor (LinearChannel n) = linearChannel (n * factor)

-- | Add two linear channels
linearChannelAdd :: LinearChannel -> LinearChannel -> LinearChannel
linearChannelAdd (LinearChannel a) (LinearChannel b) = linearChannel (a + b)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // linear rgb
-- ═════════════════════════════════════════════════════════════════════════════

-- | Linear RGB color (pre-gamma, for math operations)
-- |
-- | All channels are in linear light space.
newtype LinearRGB = LinearRGB
  { r :: LinearChannel
  , g :: LinearChannel
  , b :: LinearChannel
  }

derive instance eqLinearRGB :: Eq LinearRGB
derive instance ordLinearRGB :: Ord LinearRGB

instance showLinearRGB :: Show LinearRGB where
  show (LinearRGB c) = "LinearRGB(" <> show c.r <> ", " 
    <> show c.g <> ", " <> show c.b <> ")"

-- | Create LinearRGB from raw values
linearRGB :: Number -> Number -> Number -> LinearRGB
linearRGB r g b = LinearRGB
  { r: linearChannel r
  , g: linearChannel g
  , b: linearChannel b
  }

-- | Create from record
linearRGBFromRecord :: { r :: Number, g :: Number, b :: Number } -> LinearRGB
linearRGBFromRecord rec = linearRGB rec.r rec.g rec.b

-- | Get red channel
linearRed :: LinearRGB -> LinearChannel
linearRed (LinearRGB c) = c.r

-- | Get green channel
linearGreen :: LinearRGB -> LinearChannel
linearGreen (LinearRGB c) = c.g

-- | Get blue channel
linearBlue :: LinearRGB -> LinearChannel
linearBlue (LinearRGB c) = c.b

-- | Convert to record
linearRGBToRecord :: LinearRGB -> { r :: Number, g :: Number, b :: Number }
linearRGBToRecord (LinearRGB c) =
  { r: unwrapLinearChannel c.r
  , g: unwrapLinearChannel c.g
  , b: unwrapLinearChannel c.b
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // linear rgba
-- ═════════════════════════════════════════════════════════════════════════════

-- | Linear RGBA color (pre-gamma with alpha)
newtype LinearRGBA = LinearRGBA
  { r :: LinearChannel
  , g :: LinearChannel
  , b :: LinearChannel
  , a :: Op.Opacity
  }

derive instance eqLinearRGBA :: Eq LinearRGBA
derive instance ordLinearRGBA :: Ord LinearRGBA

instance showLinearRGBA :: Show LinearRGBA where
  show (LinearRGBA c) = "LinearRGBA(" <> show c.r <> ", " 
    <> show c.g <> ", " <> show c.b <> ", " 
    <> show (Op.toUnitInterval c.a) <> ")"

-- | Create LinearRGBA from raw values
linearRGBA :: Number -> Number -> Number -> Number -> LinearRGBA
linearRGBA r g b a = LinearRGBA
  { r: linearChannel r
  , g: linearChannel g
  , b: linearChannel b
  , a: Op.fromUnitInterval a
  }

-- | Create from record
linearRGBAFromRecord :: { r :: Number, g :: Number, b :: Number, a :: Number } -> LinearRGBA
linearRGBAFromRecord rec = linearRGBA rec.r rec.g rec.b rec.a

-- | Get alpha
linearAlpha :: LinearRGBA -> Op.Opacity
linearAlpha (LinearRGBA c) = c.a

-- | Convert to record
linearRGBAToRecord :: LinearRGBA -> { r :: Number, g :: Number, b :: Number, a :: Number }
linearRGBAToRecord (LinearRGBA c) =
  { r: unwrapLinearChannel c.r
  , g: unwrapLinearChannel c.g
  , b: unwrapLinearChannel c.b
  , a: Op.toUnitInterval c.a
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // srgb conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert sRGB (gamma-encoded) to LinearRGB
-- |
-- | Applies the sRGB EOTF (Electro-Optical Transfer Function).
fromSRGB :: RGB.RGB -> LinearRGB
fromSRGB srgbColor =
  let rec = RGB.rgbToRecord srgbColor
  in LinearRGB
    { r: linearChannel (srgbToLinearChannel (toNumber rec.r / 255.0))
    , g: linearChannel (srgbToLinearChannel (toNumber rec.g / 255.0))
    , b: linearChannel (srgbToLinearChannel (toNumber rec.b / 255.0))
    }

-- | Convert LinearRGB to sRGB (gamma-encoded)
-- |
-- | Applies the sRGB OETF (Opto-Electronic Transfer Function).
toSRGB :: LinearRGB -> RGB.RGB
toSRGB (LinearRGB c) =
  let r = linearToSrgbChannel (unwrapLinearChannel c.r)
      g = linearToSrgbChannel (unwrapLinearChannel c.g)
      b = linearToSrgbChannel (unwrapLinearChannel c.b)
  in RGB.rgb 
    (round (Bounded.clampNumber 0.0 255.0 (r * 255.0)))
    (round (Bounded.clampNumber 0.0 255.0 (g * 255.0)))
    (round (Bounded.clampNumber 0.0 255.0 (b * 255.0)))

-- | Convert sRGBA to LinearRGBA
fromSRGBA :: RGBA.RGBA -> LinearRGBA
fromSRGBA srgbaColor =
  let rec = RGBA.rgbaToRecord srgbaColor
  in LinearRGBA
    { r: linearChannel (srgbToLinearChannel (toNumber rec.r / 255.0))
    , g: linearChannel (srgbToLinearChannel (toNumber rec.g / 255.0))
    , b: linearChannel (srgbToLinearChannel (toNumber rec.b / 255.0))
    , a: Op.opacity rec.a
    }

-- | Convert LinearRGBA to sRGBA
toSRGBA :: LinearRGBA -> RGBA.RGBA
toSRGBA (LinearRGBA c) =
  let r = linearToSrgbChannel (unwrapLinearChannel c.r)
      g = linearToSrgbChannel (unwrapLinearChannel c.g)
      b = linearToSrgbChannel (unwrapLinearChannel c.b)
  in RGBA.rgba 
    (round (Bounded.clampNumber 0.0 255.0 (r * 255.0)))
    (round (Bounded.clampNumber 0.0 255.0 (g * 255.0)))
    (round (Bounded.clampNumber 0.0 255.0 (b * 255.0)))
    (round (Op.toUnitInterval c.a * 100.0))

-- | sRGB to linear channel conversion (EOTF)
srgbToLinearChannel :: Number -> Number
srgbToLinearChannel srgb
  | srgb <= 0.04045 = srgb / 12.92
  | otherwise = Math.pow ((srgb + 0.055) / 1.055) 2.4

-- | Linear to sRGB channel conversion (OETF)
linearToSrgbChannel :: Number -> Number
linearToSrgbChannel lin
  | lin <= 0.0031308 = lin * 12.92
  | otherwise = 1.055 * Math.pow lin (1.0 / 2.4) - 0.055

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Blend two LinearRGB colors (correct in linear space!)
-- |
-- | This is the CORRECT way to blend colors. Blending in sRGB space
-- | produces incorrect results (the "middle gray" problem).
blend :: Number -> LinearRGB -> LinearRGB -> LinearRGB
blend weight (LinearRGB a) (LinearRGB b) =
  let w = Bounded.clampNumber 0.0 1.0 weight
  in LinearRGB
    { r: linearChannelBlend w a.r b.r
    , g: linearChannelBlend w a.g b.g
    , b: linearChannelBlend w a.b b.b
    }

-- | Add two linear colors (light mixing)
add :: LinearRGB -> LinearRGB -> LinearRGB
add (LinearRGB a) (LinearRGB b) = LinearRGB
  { r: linearChannelAdd a.r b.r
  , g: linearChannelAdd a.g b.g
  , b: linearChannelAdd a.b b.b
  }

-- | Scale a linear color by a factor
scale :: Number -> LinearRGB -> LinearRGB
scale factor (LinearRGB c) = LinearRGB
  { r: linearChannelScale factor c.r
  , g: linearChannelScale factor c.g
  , b: linearChannelScale factor c.b
  }

-- | Multiply two linear colors (component-wise)
multiply :: LinearRGB -> LinearRGB -> LinearRGB
multiply (LinearRGB a) (LinearRGB b) = LinearRGB
  { r: linearChannel (unwrapLinearChannel a.r * unwrapLinearChannel b.r)
  , g: linearChannel (unwrapLinearChannel a.g * unwrapLinearChannel b.g)
  , b: linearChannel (unwrapLinearChannel a.b * unwrapLinearChannel b.b)
  }

-- | Calculate relative luminance (Y in XYZ)
-- |
-- | Uses Rec. 709 luma coefficients.
-- | This is only correct for linear values!
luminance :: LinearRGB -> Number
luminance (LinearRGB c) =
  0.2126 * unwrapLinearChannel c.r +
  0.7152 * unwrapLinearChannel c.g +
  0.0722 * unwrapLinearChannel c.b

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // comparison
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if color is black (all channels zero)
isBlack :: LinearRGB -> Boolean
isBlack (LinearRGB c) =
  unwrapLinearChannel c.r == 0.0 &&
  unwrapLinearChannel c.g == 0.0 &&
  unwrapLinearChannel c.b == 0.0

-- | Check if color is white (all channels 1.0)
isWhite :: LinearRGB -> Boolean
isWhite (LinearRGB c) =
  unwrapLinearChannel c.r == 1.0 &&
  unwrapLinearChannel c.g == 1.0 &&
  unwrapLinearChannel c.b == 1.0

-- | Check if two colors are equal
isEqual :: LinearRGB -> LinearRGB -> Boolean
isEqual (LinearRGB a) (LinearRGB b) =
  unwrapLinearChannel a.r == unwrapLinearChannel b.r &&
  unwrapLinearChannel a.g == unwrapLinearChannel b.g &&
  unwrapLinearChannel a.b == unwrapLinearChannel b.b

-- | Check if color is gray (all channels equal)
isGray :: LinearRGB -> Boolean
isGray (LinearRGB c) =
  let r = unwrapLinearChannel c.r
      g = unwrapLinearChannel c.g
      b = unwrapLinearChannel c.b
  in r == g && g == b

-- | Check if two colors are NOT equal
isNotEqual :: LinearRGB -> LinearRGB -> Boolean
isNotEqual a b = 
  let recA = linearRGBToRecord a
      recB = linearRGBToRecord b
  in recA.r /= recB.r || recA.g /= recB.g || recA.b /= recB.b

-- | Check if color is within SDR range (all channels <= 1.0)
isInSDRRange :: LinearRGB -> Boolean
isInSDRRange (LinearRGB c) =
  unwrapLinearChannel c.r <= 1.0 &&
  unwrapLinearChannel c.g <= 1.0 &&
  unwrapLinearChannel c.b <= 1.0

-- | Check if color is HDR (any channel > 1.0)
isHDR :: LinearRGB -> Boolean
isHDR (LinearRGB c) =
  unwrapLinearChannel c.r > 1.0 ||
  unwrapLinearChannel c.g > 1.0 ||
  unwrapLinearChannel c.b > 1.0

-- | Check if first color is brighter than second (by luminance)
isBrighterThan :: LinearRGB -> LinearRGB -> Boolean
isBrighterThan a b = luminance a > luminance b

-- | Check if first color is darker than second (by luminance)
isDarkerThan :: LinearRGB -> LinearRGB -> Boolean
isDarkerThan a b = luminance a < luminance b
