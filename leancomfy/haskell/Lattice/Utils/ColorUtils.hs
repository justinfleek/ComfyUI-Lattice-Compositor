{-# LANGUAGE StrictData #-}

{-|
Module      : Lattice.Utils.ColorUtils
Description : Color conversion and manipulation
Copyright   : (c) Lattice, 2026
License     : MIT

HSV, RGB, HSL conversions and hex parsing.
All functions handle edge cases safely.

Source: leancomfy/lean/Lattice/Utils/ColorUtils.lean
-}

module Lattice.Utils.ColorUtils
  ( -- * Color Types
    HSV(..)
  , HSL(..)
  , HexParseResult(..)
    -- * Color Space Conversions
  , hsvToRgb
  , rgbToHsv
  , hslToRgb
  , rgbToHsl
    -- * Hex Conversion
  , hexToRgb
  , rgbToHex
  , rgbaToHex
  , hsvToHex
  , hexToHsv
    -- * Color Manipulation
  , lerpRgb
  , getContrastColor
    -- * Standard Swatches
  , standardSwatches
  ) where

import Data.Char (digitToInt, intToDigit, isHexDigit, toLower)
import Data.Text (Text)
import qualified Data.Text as T
import Lattice.Primitives

--------------------------------------------------------------------------------
-- Color Types
--------------------------------------------------------------------------------

-- | HSV color (Hue 0-360, Saturation 0-1, Value 0-1)
data HSV = HSV
  { hsvH :: !FiniteFloat  -- 0-360
  , hsvS :: !UnitFloat    -- 0-1
  , hsvV :: !UnitFloat    -- 0-1
  } deriving (Eq, Show)

-- | HSL color (Hue 0-360, Saturation 0-1, Lightness 0-1)
data HSL = HSL
  { hslH :: !FiniteFloat  -- 0-360
  , hslS :: !UnitFloat    -- 0-1
  , hslL :: !UnitFloat    -- 0-1
  } deriving (Eq, Show)

-- | Hex parse result
data HexParseResult
  = HexOk !RGB
  | HexOkWithAlpha !RGBA
  | HexInvalid !Text
  deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Helper Functions
--------------------------------------------------------------------------------

-- | Check if Double is finite
isFiniteDouble :: Double -> Bool
isFiniteDouble x = not (isNaN x) && not (isInfinite x)

-- | Clamp value to range
clamp :: Double -> Double -> Double -> Double
clamp minVal maxVal x = max minVal (min maxVal x)

-- | Normalize hue to [0, 360)
normalizeHue :: Double -> FiniteFloat
normalizeHue h =
  let wrapped = ((h `mod'` 360) + 360) `mod'` 360
  in if isFiniteDouble wrapped
     then FiniteFloat wrapped
     else FiniteFloat 0
  where
    mod' a b = a - b * fromIntegral (floor (a / b) :: Int)

-- | Clamp to unit range
clampUnit :: Double -> UnitFloat
clampUnit = UnitFloat . clamp 0 1

-- | Make finite float
mkFinite :: Double -> FiniteFloat
mkFinite x = if isFiniteDouble x then FiniteFloat x else FiniteFloat 0

--------------------------------------------------------------------------------
-- Color Space Conversions
--------------------------------------------------------------------------------

-- | Convert HSV to RGB
hsvToRgb :: HSV -> RGB
hsvToRgb (HSV (FiniteFloat h) (UnitFloat s) (UnitFloat v)) =
  let hNorm = let wrapped = ((h `mod'` 360) + 360) `mod'` 360 in wrapped
      c = v * s
      x = c * (1 - abs (((hNorm / 60) `mod'` 2) - 1))
      m = v - c
      (r', g', b')
        | hNorm < 60 = (c, x, 0)
        | hNorm < 120 = (x, c, 0)
        | hNorm < 180 = (0, c, x)
        | hNorm < 240 = (0, x, c)
        | hNorm < 300 = (x, 0, c)
        | otherwise = (c, 0, x)
      toChannel n = mkFinite $ fromIntegral (round ((n + m) * 255) :: Int)
  in RGB (toChannel r') (toChannel g') (toChannel b')
  where
    mod' a b = a - b * fromIntegral (floor (a / b) :: Int)

-- | Convert RGB to HSV
rgbToHsv :: RGB -> HSV
rgbToHsv (RGB (FiniteFloat r) (FiniteFloat g) (FiniteFloat b)) =
  let r' = r / 255
      g' = g / 255
      b' = b / 255
      maxC = maximum [r', g', b']
      minC = minimum [r', g', b']
      d = maxC - minC
      s = if maxC == 0 then 0 else d / maxC
      v = maxC
      h | d == 0 = 0
        | maxC == r' = ((g' - b') / d + (if g' < b' then 6 else 0)) * 60
        | maxC == g' = ((b' - r') / d + 2) * 60
        | otherwise = ((r' - g') / d + 4) * 60
  in HSV (normalizeHue h) (clampUnit s) (clampUnit v)

-- | Convert HSL to RGB
hslToRgb :: HSL -> RGB
hslToRgb (HSL (FiniteFloat h) (UnitFloat s) (UnitFloat l)) =
  let hNorm = let wrapped = ((h `mod'` 360) + 360) `mod'` 360 in wrapped
      c = (1 - abs (2 * l - 1)) * s
      x = c * (1 - abs (((hNorm / 60) `mod'` 2) - 1))
      m = l - c / 2
      (r', g', b')
        | hNorm < 60 = (c, x, 0)
        | hNorm < 120 = (x, c, 0)
        | hNorm < 180 = (0, c, x)
        | hNorm < 240 = (0, x, c)
        | hNorm < 300 = (x, 0, c)
        | otherwise = (c, 0, x)
      toChannel n = mkFinite $ fromIntegral (round ((n + m) * 255) :: Int)
  in RGB (toChannel r') (toChannel g') (toChannel b')
  where
    mod' a b = a - b * fromIntegral (floor (a / b) :: Int)

-- | Convert RGB to HSL
rgbToHsl :: RGB -> HSL
rgbToHsl (RGB (FiniteFloat r) (FiniteFloat g) (FiniteFloat b)) =
  let r' = r / 255
      g' = g / 255
      b' = b / 255
      maxC = maximum [r', g', b']
      minC = minimum [r', g', b']
      l = (maxC + minC) / 2
      d = maxC - minC
      (h, s)
        | maxC == minC = (0, 0)
        | otherwise =
            let s' = if l > 0.5 then d / (2 - maxC - minC) else d / (maxC + minC)
                h' | maxC == r' = ((g' - b') / d + (if g' < b' then 6 else 0)) * 60
                   | maxC == g' = ((b' - r') / d + 2) * 60
                   | otherwise = ((r' - g') / d + 4) * 60
            in (h', s')
  in HSL (normalizeHue h) (clampUnit s) (clampUnit l)

--------------------------------------------------------------------------------
-- Hex Conversion
--------------------------------------------------------------------------------

-- | Parse hex color string to RGB
hexToRgb :: Text -> HexParseResult
hexToRgb hex =
  let hex' = T.unpack $ T.dropWhile (== '#') hex
  in case length hex' of
    -- #RGB format
    3 | all isHexDigit hex' ->
        let [r, g, b] = map digitToInt hex'
            r' = r * 16 + r
            g' = g * 16 + g
            b' = b * 16 + b
        in HexOk $ RGB (mkFinite $ fromIntegral r')
                       (mkFinite $ fromIntegral g')
                       (mkFinite $ fromIntegral b')

    -- #RRGGBB format
    6 | all isHexDigit hex' ->
        let pairs = [(hex' !! 0, hex' !! 1), (hex' !! 2, hex' !! 3), (hex' !! 4, hex' !! 5)]
            [r, g, b] = map hexPair pairs
        in HexOk $ RGB (mkFinite $ fromIntegral r)
                       (mkFinite $ fromIntegral g)
                       (mkFinite $ fromIntegral b)

    -- #RRGGBBAA format
    8 | all isHexDigit hex' ->
        let pairs = [(hex' !! 0, hex' !! 1), (hex' !! 2, hex' !! 3),
                     (hex' !! 4, hex' !! 5), (hex' !! 6, hex' !! 7)]
            [r, g, b, a] = map hexPair pairs
        in HexOkWithAlpha $ RGBA (mkFinite $ fromIntegral r)
                                 (mkFinite $ fromIntegral g)
                                 (mkFinite $ fromIntegral b)
                                 (clampUnit $ fromIntegral a / 255)

    _ -> HexInvalid $ T.pack $ "Invalid hex: " ++ hex'
  where
    hexPair (c1, c2) = digitToInt c1 * 16 + digitToInt c2

-- | Convert RGB to hex string
rgbToHex :: RGB -> Text
rgbToHex (RGB (FiniteFloat r) (FiniteFloat g) (FiniteFloat b)) =
  T.pack $ '#' : concatMap toHex [r, g, b]
  where
    toHex n = let x = max 0 (min 255 (round n :: Int))
              in [intToDigit (x `div` 16), intToDigit (x `mod` 16)]

-- | Convert RGBA to hex string with alpha
rgbaToHex :: RGBA -> Text
rgbaToHex (RGBA (FiniteFloat r) (FiniteFloat g) (FiniteFloat b) (UnitFloat a)) =
  T.pack $ '#' : concatMap toHex [r, g, b, a * 255]
  where
    toHex n = let x = max 0 (min 255 (round n :: Int))
              in [intToDigit (x `div` 16), intToDigit (x `mod` 16)]

-- | Convert HSV to hex string
hsvToHex :: HSV -> Text
hsvToHex = rgbToHex . hsvToRgb

-- | Convert hex to HSV
hexToHsv :: Text -> Maybe HSV
hexToHsv hex = case hexToRgb hex of
  HexOk rgb -> Just $ rgbToHsv rgb
  HexOkWithAlpha (RGBA r g b _) -> Just $ rgbToHsv (RGB r g b)
  HexInvalid _ -> Nothing

--------------------------------------------------------------------------------
-- Color Manipulation
--------------------------------------------------------------------------------

-- | Linear interpolation between two RGB colors
lerpRgb :: RGB -> RGB -> UnitFloat -> RGB
lerpRgb (RGB (FiniteFloat r1) (FiniteFloat g1) (FiniteFloat b1))
        (RGB (FiniteFloat r2) (FiniteFloat g2) (FiniteFloat b2))
        (UnitFloat t) =
  let lerp a b = mkFinite $ fromIntegral (round (a + (b - a) * t) :: Int)
  in RGB (lerp r1 r2) (lerp g1 g2) (lerp b1 b2)

-- | Get contrasting text color (black or white) for background
getContrastColor :: RGB -> RGB
getContrastColor (RGB (FiniteFloat r) (FiniteFloat g) (FiniteFloat b)) =
  let luminance = (0.299 * r + 0.587 * g + 0.114 * b) / 255
  in if luminance > 0.5
     then RGB (FiniteFloat 0) (FiniteFloat 0) (FiniteFloat 0)      -- black
     else RGB (FiniteFloat 255) (FiniteFloat 255) (FiniteFloat 255) -- white

--------------------------------------------------------------------------------
-- Standard Swatches
--------------------------------------------------------------------------------

-- | Standard color swatch hex values
standardSwatches :: [Text]
standardSwatches =
  [ "#ff0000", "#ff8000", "#ffff00", "#80ff00"
  , "#00ff00", "#00ff80", "#00ffff", "#0080ff"
  , "#0000ff", "#8000ff", "#ff00ff", "#ff0080"
  , "#ffffff", "#c0c0c0", "#808080", "#404040", "#000000"
  ]
