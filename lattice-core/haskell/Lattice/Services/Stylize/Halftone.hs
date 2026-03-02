{-|
  Lattice.Services.Stylize.Halftone - Halftone Pattern Mathematics

  Pure mathematical functions for halftone effect:
  - RGB to CMYK conversion
  - Dot size calculation from brightness
  - CMYK angle offsets

  Source: ui/src/services/effects/stylizeRenderer.ts (lines 642-788)
-}

module Lattice.Services.Stylize.Halftone
  ( CMYK(..)
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

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | CMYK color values
data CMYK = CMYK
  { cmykC :: !Double   -- ^ Cyan [0, 1]
  , cmykM :: !Double   -- ^ Magenta [0, 1]
  , cmykY :: !Double   -- ^ Yellow [0, 1]
  , cmykK :: !Double   -- ^ Key/Black [0, 1]
  } deriving (Show, Eq)

-- | Halftone color mode
data ColorMode
  = Grayscale   -- ^ Single black dots
  | RGB         -- ^ Separate RGB dot layers
  | CMYK_Mode   -- ^ Print-style CMYK dots
  deriving (Show, Eq, Enum, Bounded)

-- ────────────────────────────────────────────────────────────────────────────
--                                                                       // rgb
-- ────────────────────────────────────────────────────────────────────────────

-- | Convert RGB to CMYK color space.
--
--   K (black) = 1 - max(R, G, B)
--   C = (1 - R - K) / (1 - K)   if K < 1
--   M = (1 - G - K) / (1 - K)   if K < 1
--   Y = (1 - B - K) / (1 - K)   if K < 1
--
--   @param r Red channel (0-1)
--   @param g Green channel (0-1)
--   @param b Blue channel (0-1)
--   @return CMYK values
rgbToCMYK :: Double -> Double -> Double -> CMYK
rgbToCMYK r g b =
  let k = 1.0 - max r (max g b)
  in if k >= 1.0
     then CMYK { cmykC = 0.0, cmykM = 0.0, cmykY = 0.0, cmykK = 1.0 }
     else
       let invK = 1.0 - k
       in CMYK
           { cmykC = (1.0 - r - k) / invK
           , cmykM = (1.0 - g - k) / invK
           , cmykY = (1.0 - b - k) / invK
           , cmykK = k
           }

-- ────────────────────────────────────────────────────────────────────────────
-- Dot Size Calculation
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate halftone dot radius from brightness.
--
--   For grayscale: darker areas have larger dots (inverse brightness).
--   For color: dot size proportional to channel value.
--
--   @param value Brightness or channel value (0-1)
--   @param dotSize Maximum dot diameter
--   @param invert True for grayscale (dark = big), False for color
--   @return Dot radius
dotRadius :: Double -> Double -> Bool -> Double
dotRadius value dotSize invert =
  let normalized = if invert then 1.0 - value else value
  in (normalized * dotSize) / 2.0

-- | Calculate brightness from RGB.
--
--   @param r Red (0-1)
--   @param g Green (0-1)
--   @param b Blue (0-1)
--   @return Brightness (0-1)
brightness :: Double -> Double -> Double -> Double
brightness r g b = (r + g + b) / 3.0

-- | Calculate grayscale dot radius from RGB.
--
--   @param r Red (0-1)
--   @param g Green (0-1)
--   @param b Blue (0-1)
--   @param dotSize Maximum dot diameter
--   @return Dot radius (inverse brightness)
grayscaleDotRadius :: Double -> Double -> Double -> Double -> Double
grayscaleDotRadius r g b dotSize =
  let bright = brightness r g b
  in dotRadius bright dotSize True

-- ────────────────────────────────────────────────────────────────────────────
--                                                                 // cmyk // a
-- ────────────────────────────────────────────────────────────────────────────

-- | Standard CMYK screen angles to minimize moiré.
--
--   Traditional print angles:
--   - Cyan: 15°
--   - Magenta: 75°
--   - Yellow: 0°
--   - Black: 45°
--
--   @param channel Which CMYK channel (0=C, 1=M, 2=Y, 3=K)
--   @return Angle in degrees
cmykAngle :: Int -> Double
cmykAngle channel = case channel of
  0 -> 15.0   -- Cyan
  1 -> 75.0   -- Magenta
  2 -> 0.0    -- Yellow
  3 -> 45.0   -- Black
  _ -> 0.0

-- | Convert angle from degrees to radians.
--
--   @param degrees Angle in degrees
--   @return Angle in radians
degreesToRadians :: Double -> Double
degreesToRadians degrees = degrees * pi / 180.0

-- | Calculate dot center offset for CMYK channel.
--
--   Each channel is slightly offset to create traditional rosette pattern.
--
--   @param channel Channel index (0=C, 1=M, 2=Y, 3=K)
--   @param dotSize Dot spacing
--   @return (dx, dy) offset
cmykDotOffset :: Int -> Double -> (Double, Double)
cmykDotOffset channel dotSize =
  let angle = degreesToRadians (cmykAngle channel)
      offset = dotSize * 0.1
  in (cos angle * offset, sin angle * offset)

-- ────────────────────────────────────────────────────────────────────────────
-- Pattern Rotation
-- ────────────────────────────────────────────────────────────────────────────

-- | Rotate a point around the image center.
--
--   Used to apply overall pattern rotation angle.
--
--   @param x Point X
--   @param y Point Y
--   @param centerX Center X
--   @param centerY Center Y
--   @param angle Rotation angle in radians
--   @return (rotatedX, rotatedY)
rotatePoint :: Double -> Double -> Double -> Double -> Double -> (Double, Double)
rotatePoint x y centerX centerY angle =
  let dx = x - centerX
      dy = y - centerY
      cosA = cos angle
      sinA = sin angle
  in (cosA * dx - sinA * dy + centerX, sinA * dx + cosA * dy + centerY)
