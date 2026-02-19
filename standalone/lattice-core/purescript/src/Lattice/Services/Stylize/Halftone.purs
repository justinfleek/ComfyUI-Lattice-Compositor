{-
  Lattice.Services.Stylize.Halftone - Halftone Pattern Mathematics

  Pure mathematical functions for halftone effect:
  - RGB to CMYK conversion
  - Dot size calculation from brightness
  - CMYK angle offsets

  Source: ui/src/services/effects/stylizeRenderer.ts (lines 642-788)
-}

module Lattice.Services.Stylize.Halftone
  ( CMYK
  , ColorMode(..)
  , rgbToCMYK
  , dotRadius
  , brightness
  , grayscaleDotRadius
  , cmykAngle
  , degreesToRadians
  , cmykDotOffset
  , rotatePoint
  ) where

import Prelude

import Data.Tuple (Tuple(..))
import Math (cos, pi, sin)

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | CMYK color values
type CMYK =
  { c :: Number   -- Cyan [0, 1]
  , m :: Number   -- Magenta [0, 1]
  , y :: Number   -- Yellow [0, 1]
  , k :: Number   -- Key/Black [0, 1]
  }

-- | Halftone color mode
data ColorMode
  = Grayscale   -- Single black dots
  | RGB         -- Separate RGB dot layers
  | CMYK_Mode   -- Print-style CMYK dots

derive instance eqColorMode :: Eq ColorMode

instance showColorMode :: Show ColorMode where
  show Grayscale = "Grayscale"
  show RGB = "RGB"
  show CMYK_Mode = "CMYK"

-- ────────────────────────────────────────────────────────────────────────────
--                                                                       // rgb
-- ────────────────────────────────────────────────────────────────────────────

-- | Convert RGB to CMYK color space.
rgbToCMYK :: Number -> Number -> Number -> CMYK
rgbToCMYK r g b =
  let k = 1.0 - max r (max g b)
  in if k >= 1.0
     then { c: 0.0, m: 0.0, y: 0.0, k: 1.0 }
     else
       let invK = 1.0 - k
       in { c: (1.0 - r - k) / invK
          , m: (1.0 - g - k) / invK
          , y: (1.0 - b - k) / invK
          , k: k
          }

-- ────────────────────────────────────────────────────────────────────────────
-- Dot Size Calculation
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate halftone dot radius from brightness.
dotRadius :: Number -> Number -> Boolean -> Number
dotRadius value dotSize invert =
  let normalized = if invert then 1.0 - value else value
  in (normalized * dotSize) / 2.0

-- | Calculate brightness from RGB.
brightness :: Number -> Number -> Number -> Number
brightness r g b = (r + g + b) / 3.0

-- | Calculate grayscale dot radius from RGB.
grayscaleDotRadius :: Number -> Number -> Number -> Number -> Number
grayscaleDotRadius r g b dotSize =
  let bright = brightness r g b
  in dotRadius bright dotSize true

-- ────────────────────────────────────────────────────────────────────────────
--                                                                 // cmyk // a
-- ────────────────────────────────────────────────────────────────────────────

-- | Standard CMYK screen angles to minimize moiré.
cmykAngle :: Int -> Number
cmykAngle channel = case channel of
  0 -> 15.0   -- Cyan
  1 -> 75.0   -- Magenta
  2 -> 0.0    -- Yellow
  3 -> 45.0   -- Black
  _ -> 0.0

-- | Convert angle from degrees to radians.
degreesToRadians :: Number -> Number
degreesToRadians degrees = degrees * pi / 180.0

-- | Calculate dot center offset for CMYK channel.
cmykDotOffset :: Int -> Number -> Tuple Number Number
cmykDotOffset channel dotSize =
  let angle = degreesToRadians (cmykAngle channel)
      offset = dotSize * 0.1
  in Tuple (cos angle * offset) (sin angle * offset)

-- ────────────────────────────────────────────────────────────────────────────
-- Pattern Rotation
-- ────────────────────────────────────────────────────────────────────────────

-- | Rotate a point around the image center.
rotatePoint :: Number -> Number -> Number -> Number -> Number -> Tuple Number Number
rotatePoint x y centerX centerY angle =
  let dx = x - centerX
      dy = y - centerY
      cosA = cos angle
      sinA = sin angle
  in Tuple (cosA * dx - sinA * dy + centerX) (sinA * dx + cosA * dy + centerY)
