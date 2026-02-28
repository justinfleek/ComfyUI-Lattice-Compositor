-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // color // properties
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Color properties - measurable characteristics.
-- |
-- | Perceptual properties for color analysis:
-- | - **Colorfulness**: How vivid/chromatic a color appears
-- | - **Brightness**: Simple average RGB brightness
-- | - **Perceived Lightness**: L* from CIELAB (perceptually uniform)

module Hydrogen.Schema.Color.Properties
  ( -- * Colorfulness
    colorfulness
  , chroma
  
  -- * Brightness
  , brightness
  , value
  
  -- * Perceived Lightness
  , perceivedLightness
  , labLightness
  ) where

import Prelude
  ( (+)
  , (-)
  , (*)
  , (/)
  , (>)
  )

import Data.Int (toNumber)
import Hydrogen.Math.Core as Math
import Hydrogen.Schema.Color.HSL as HSL
import Hydrogen.Schema.Color.RGB as RGB
import Hydrogen.Schema.Color.Saturation as Sat
import Hydrogen.Schema.Color.Lightness as Light
import Hydrogen.Schema.Color.Channel as Ch
import Hydrogen.Schema.Color.Contrast (luminanceRGB)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // colorfulness
-- ═════════════════════════════════════════════════════════════════════════════

-- | Perceived colorfulness (chroma relative to lightness)
-- |
-- | A measure of how vivid a color appears. Highly saturated colors
-- | at mid-lightness have maximum colorfulness.
colorfulness :: HSL.HSL -> Number
colorfulness color =
  let s = Sat.unwrap (HSL.saturation color)
      l = Light.unwrap (HSL.lightness color)
  in toNumber s * (1.0 - Math.abs (toNumber l / 50.0 - 1.0))

-- | Chroma - saturation normalized to 0-1 range
chroma :: HSL.HSL -> Number
chroma color =
  let s = Sat.unwrap (HSL.saturation color)
  in toNumber s / 100.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // brightness
-- ═════════════════════════════════════════════════════════════════════════════

-- | Simple brightness (average of RGB channels)
-- |
-- | Returns 0-1 range. This is a naive measure; use perceivedLightness
-- | for perceptually accurate results.
brightness :: RGB.RGB -> Number
brightness color =
  let r = Ch.unwrap (RGB.red color)
      g = Ch.unwrap (RGB.green color)
      b = Ch.unwrap (RGB.blue color)
  in toNumber (r + g + b) / 3.0 / 255.0

-- | HSV Value (maximum of RGB channels)
-- |
-- | The "V" in HSV color space.
value :: RGB.RGB -> Number
value color =
  let r = Ch.unwrap (RGB.red color)
      g = Ch.unwrap (RGB.green color)
      b = Ch.unwrap (RGB.blue color)
  in Math.max (Math.max (toNumber r) (toNumber g)) (toNumber b) / 255.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // perceived lightness
-- ═════════════════════════════════════════════════════════════════════════════

-- | Perceived lightness (L* from CIELAB)
-- |
-- | This is perceptually uniform: a change of 10 L* units looks like
-- | the same lightness difference regardless of the starting point.
-- |
-- | Returns 0-100 range.
perceivedLightness :: RGB.RGB -> Number
perceivedLightness color =
  let y = luminanceRGB color
  in if y > 0.008856
     then 116.0 * Math.cbrt y - 16.0
     else 903.3 * y

-- | Alias for perceivedLightness (CIELAB terminology)
labLightness :: RGB.RGB -> Number
labLightness = perceivedLightness
