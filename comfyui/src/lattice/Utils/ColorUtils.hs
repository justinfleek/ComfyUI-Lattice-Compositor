-- |
-- Module      : Lattice.Utils.ColorUtils
-- Description : Color utility functions for HSV, RGB, HSL conversions and hex parsing
-- 
-- Migrated from ui/src/utils/colorUtils.ts
-- Pure color space conversion functions
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.Utils.ColorUtils
  ( -- Types
    RGB(..)
  , HSV(..)
  , HSL(..)
  , RGBA(..)
  --                                                                       // hsv
  , hsvToRgb
  , rgbToHsv
  --                                                                       // hsl
  , hslToRgb
  , rgbToHsl
  -- Hex conversions
  , hexToRgb
  , hexToRgba
  , rgbToHex
  , rgbaToHex
  , hsvToHex
  , hexToHsv
  -- Color parsing
  , parseColor
  -- Color operations
  , lerpColor
  , getContrastColor
  -- Constants
  , standardSwatches
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import Lattice.Utils.NumericSafety
  ( clamp
  , clamp01
  , safeMod
  )
import Lattice.Utils.ArrayUtils
  ( lerp
  )
import Text.Read (readMaybe)
import Data.Maybe (fromMaybe)
import Text.Printf (printf)
import Text.Printf (printf)
import Data.Char (isDigit)
import Data.List (isPrefixOf)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                     // types
-- ════════════════════════════════════════════════════════════════════════════

-- | RGB color tuple (0-255 each)
type RGB = (Double, Double, Double)

-- | HSV color tuple (hue 0-360, saturation 0-1, value 0-1)
type HSV = (Double, Double, Double)

-- | HSL color tuple (hue 0-360, saturation 0-1, lightness 0-1)
type HSL = (Double, Double, Double)

-- | RGBA color tuple (0-255 each for RGB, 0-1 for alpha)
type RGBA = (Double, Double, Double, Double)

-- ════════════════════════════════════════════════════════════════════════════
--                                                        // hsv // conversions
-- ════════════════════════════════════════════════════════════════════════════

-- | Convert HSV to RGB
-- @param h Hue (0-360)
-- @param s Saturation (0-1)
-- @param v Value (0-1)
-- @returns RGB tuple (0-255 each)
hsvToRgb :: Double -> Double -> Double -> RGB
hsvToRgb h s v =
  let h' = safeMod h 360
      c = v * s
      x = c * (1 - abs ((h' / 60) `mod'` 2 - 1))
      m = v - c
      (r', g', b') = if h' < 60
        then (c, x, 0)
        else if h' < 120
          then (x, c, 0)
          else if h' < 180
            then (0, c, x)
            else if h' < 240
              then (0, x, c)
              else if h' < 300
                then (x, 0, c)
                else (c, 0, x)
      r = round ((r' + m) * 255)
      g = round ((g' + m) * 255)
      b = round ((b' + m) * 255)
  in (fromIntegral r, fromIntegral g, fromIntegral b)
  where
    mod' :: Double -> Double -> Double
    mod' x y = fromIntegral (floor x `mod` floor y)

-- | Convert RGB to HSV
-- @param r Red (0-255)
-- @param g Green (0-255)
-- @param b Blue (0-255)
-- @returns HSV tuple [hue (0-360), saturation (0-1), value (0-1)]
rgbToHsv :: Double -> Double -> Double -> HSV
rgbToHsv r g b =
  let r' = r / 255
      g' = g / 255
      b' = b / 255
      maxVal = maximum [r', g', b']
      minVal = minimum [r', g', b']
      d = maxVal - minVal
      s = if maxVal == 0 then 0 else d / maxVal
      v = maxVal
      h = if d == 0
        then 0
        else case () of
          _ | maxVal == r' -> ((g' - b') / d + (if g' < b' then 6 else 0)) * 60
          _ | maxVal == g' -> ((b' - r') / d + 2) * 60
          _ | maxVal == b' -> ((r' - g') / d + 4) * 60
          _ -> 0
  in (h, s, v)

-- ════════════════════════════════════════════════════════════════════════════
--                                                        // hsl // conversions
-- ════════════════════════════════════════════════════════════════════════════

-- | Convert HSL to RGB
-- @param h Hue (0-360)
-- @param s Saturation (0-1)
-- @param l Lightness (0-1)
-- @returns RGB tuple (0-255 each)
hslToRgb :: Double -> Double -> Double -> RGB
hslToRgb h s l =
  let h' = safeMod h 360
      c = (1 - abs (2 * l - 1)) * s
      x = c * (1 - abs ((h' / 60) `mod'` 2 - 1))
      m = l - c / 2
      (r', g', b') = if h' < 60
        then (c, x, 0)
        else if h' < 120
          then (x, c, 0)
          else if h' < 180
            then (0, c, x)
          else if h' < 240
            then (0, x, c)
          else if h' < 300
            then (x, 0, c)
          else (c, 0, x)
      r = round ((r' + m) * 255)
      g = round ((g' + m) * 255)
      b = round ((b' + m) * 255)
  in (fromIntegral r, fromIntegral g, fromIntegral b)
  where
    mod' :: Double -> Double -> Double
    mod' x y = fromIntegral (floor x `mod` floor y)

-- | Convert RGB to HSL
-- @param r Red (0-255)
-- @param g Green (0-255)
-- @param b Blue (0-255)
-- @returns HSL tuple [hue (0-360), saturation (0-1), lightness (0-1)]
rgbToHsl :: Double -> Double -> Double -> HSL
rgbToHsl r g b =
  let r' = r / 255
      g' = g / 255
      b' = b / 255
      maxVal = maximum [r', g', b']
      minVal = minimum [r', g', b']
      l = (maxVal + minVal) / 2
      (h, s) = if maxVal == minVal
        then (0, 0)
        else let d = maxVal - minVal
                 s' = if l > 0.5 then d / (2 - maxVal - minVal) else d / (maxVal + minVal)
                 h' = case () of
                   _ | maxVal == r' -> ((g' - b') / d + (if g' < b' then 6 else 0)) * 60
                   _ | maxVal == g' -> ((b' - r') / d + 2) * 60
                   _ | maxVal == b' -> ((r' - g') / d + 4) * 60
                   _ -> 0
             in (h', s')
  in (h, s, l)

-- ════════════════════════════════════════════════════════════════════════════
--                                                        // hex // conversions
-- ════════════════════════════════════════════════════════════════════════════

-- | Convert hex color to RGB
-- Supports #RGB, #RRGGBB formats
-- Throws error if invalid format
hexToRgb :: Text -> Either String RGB
hexToRgb hex =
  let hex' = T.dropWhile (== '#') hex
      hexExpanded = if T.length hex' == 3
        then T.singleton (T.index hex' 0) <> T.singleton (T.index hex' 0) <>
             T.singleton (T.index hex' 1) <> T.singleton (T.index hex' 1) <>
             T.singleton (T.index hex' 2) <> T.singleton (T.index hex' 2)
        else hex'
  in if T.length hexExpanded == 6
    then case (parseHexByte (T.take 2 hexExpanded),
                parseHexByte (T.take 2 (T.drop 2 hexExpanded)),
                parseHexByte (T.take 2 (T.drop 4 hexExpanded))) of
      (Just r, Just g, Just b) -> Right (fromIntegral r, fromIntegral g, fromIntegral b)
      _ -> Left $ "Invalid hex bytes in: " ++ T.unpack hex
    else Left $ "Invalid hex format. Expected #RGB or #RRGGBB, got: " ++ T.unpack hex
  where
    parseHexByte :: Text -> Maybe Int
    parseHexByte s = readMaybe ("0x" ++ T.unpack s)

-- | Convert hex color to RGBA
-- Supports #RGB, #RRGGBB, #RRGGBBAA formats
hexToRgba :: Text -> Either String RGBA
hexToRgba hex =
  let hex' = T.dropWhile (== '#') hex
      (hexExpanded, alphaHex) = if T.length hex' == 3
        then (T.singleton (T.index hex' 0) <> T.singleton (T.index hex' 0) <>
              T.singleton (T.index hex' 1) <> T.singleton (T.index hex' 1) <>
              T.singleton (T.index hex' 2) <> T.singleton (T.index hex' 2),
              "ff")
        else if T.length hex' == 6
          then (hex', "ff")
          else (T.take 6 hex', T.drop 6 hex')
  in if T.length hexExpanded == 6 && T.length alphaHex == 2
    then case (parseHexByte (T.take 2 hexExpanded),
                parseHexByte (T.take 2 (T.drop 2 hexExpanded)),
                parseHexByte (T.take 2 (T.drop 4 hexExpanded)),
                parseHexByte alphaHex) of
      (Just r, Just g, Just b, Just a) ->
        Right (fromIntegral r, fromIntegral g, fromIntegral b, fromIntegral a / 255)
      _ -> Left $ "Invalid hex bytes in: " ++ T.unpack hex
    else Left $ "Invalid hex format. Expected #RGB, #RRGGBB, or #RRGGBBAA, got: " ++ T.unpack hex
  where
    parseHexByte :: Text -> Maybe Int
    parseHexByte s = readMaybe ("0x" ++ T.unpack s)

-- | Convert RGB to hex color string
-- @param r Red (0-255)
-- @param g Green (0-255)
-- @param b Blue (0-255)
-- @returns Hex color string (#RRGGBB)
rgbToHex :: Double -> Double -> Double -> Text
rgbToHex r g b =
  let toHex n = T.pack $ printf "%02x" (round (clamp 0 255 n) :: Int)
  in "#" <> toHex r <> toHex g <> toHex b

-- | Convert RGBA to hex color string with alpha
-- @param r Red (0-255)
-- @param g Green (0-255)
-- @param b Blue (0-255)
-- @param a Alpha (0-1)
-- @returns Hex color string (#RRGGBBAA)
rgbaToHex :: Double -> Double -> Double -> Double -> Text
rgbaToHex r g b a =
  let toHex n = T.pack $ printf "%02x" (round (clamp 0 255 n) :: Int)
      aHex = T.pack $ printf "%02x" (round (clamp 0 255 (a * 255)) :: Int)
  in "#" <> toHex r <> toHex g <> toHex b <> aHex

-- | Convert HSV to hex color string
hsvToHex :: Double -> Double -> Double -> Either String Text
hsvToHex h s v =
  let (r, g, b) = hsvToRgb h s v
  in Right (rgbToHex r g b)

-- | Convert hex to HSV
hexToHsv :: Text -> Either String HSV
hexToHsv hex = do
  (r, g, b) <- hexToRgb hex
  Right (rgbToHsv r g b)

-- ════════════════════════════════════════════════════════════════════════════
--                                                          // color // parsing
-- ════════════════════════════════════════════════════════════════════════════

-- | Parse any color string to RGB
-- Supports: hex, rgb(), rgba(), hsl(), hsla()
parseColor :: Text -> Either String RGB
parseColor color =
  let color' = T.strip (T.toLower color)
  in if T.isPrefixOf "#" color'
    then hexToRgb color'
    else if T.isPrefixOf "rgb" color'
      then parseRgb color'
      else if T.isPrefixOf "hsl" color'
        then parseHsl color'
        else Left $ "Unsupported color format: " ++ T.unpack color'
  where
    parseRgb :: Text -> Either String RGB
    parseRgb s =
      let s' = T.unpack s
          -- Simple parsing for rgb(r, g, b) or rgba(r, g, b, a)
          -- Find opening paren
          openIdx = case elemIndex '(' s' of
            Just idx -> idx
            Nothing -> -1
      in if openIdx >= 0
        then let afterOpen = drop (openIdx + 1) s'
                 -- Find closing paren
                 closeIdx = case elemIndex ')' afterOpen of
                   Just idx -> idx
                   Nothing -> -1
             in if closeIdx >= 0
               then let argsStr = take closeIdx afterOpen
                        -- Split by comma and parse numbers
                        args = map (readMaybe . filter isDigit) (splitOn ',' argsStr)
                    in case args of
                      [Just r, Just g, Just b] -> Right (fromIntegral r, fromIntegral g, fromIntegral b)
                      _ -> Left "Invalid RGB values"
               else Left "Invalid RGB format (missing closing paren)"
        else Left "Invalid RGB format (missing opening paren)"
    
    parseHsl :: Text -> Either String RGB
    parseHsl s =
      let s' = T.unpack s
          -- Simple parsing for hsl(h, s%, l%) or hsla(h, s%, l%, a)
          openIdx = case elemIndex '(' s' of
            Just idx -> idx
            Nothing -> -1
      in if openIdx >= 0
        then let afterOpen = drop (openIdx + 1) s'
                 closeIdx = case elemIndex ')' afterOpen of
                   Just idx -> idx
                   Nothing -> -1
             in if closeIdx >= 0
               then let argsStr = take closeIdx afterOpen
                        -- Remove % signs and split
                        cleaned = filter (/= '%') argsStr
                        args = map (readMaybe . filter isDigit) (splitOn ',' cleaned)
                    in case args of
                      [Just h, Just s', Just l'] ->
                        Right (hslToRgb (fromIntegral h) (fromIntegral s' / 100) (fromIntegral l' / 100))
                      _ -> Left "Invalid HSL values"
               else Left "Invalid HSL format (missing closing paren)"
        else Left "Invalid HSL format (missing opening paren)"
    
    elemIndex :: Char -> String -> Maybe Int
    elemIndex c str = go 0 str
      where
        go _ [] = Nothing
        go idx (x:xs) = if x == c then Just idx else go (idx + 1) xs
    
    splitOn :: Char -> String -> [String]
    splitOn _ [] = []
    splitOn sep str = case break (== sep) str of
      (chunk, []) -> [chunk]
      (chunk, _:rest) -> chunk : splitOn sep rest

-- ════════════════════════════════════════════════════════════════════════════
--                                                       // color // operations
-- ════════════════════════════════════════════════════════════════════════════

-- | Linear interpolation between two colors
lerpColor :: Text -> Text -> Double -> Either String Text
lerpColor color1 color2 t =
  let t' = clamp01 t
  in do
    rgb1 <- hexToRgb color1
    rgb2 <- hexToRgb color2
    let (r1, g1, b1) = rgb1
        (r2, g2, b2) = rgb2
        r = round (lerp r1 r2 t')
        g = round (lerp g1 g2 t')
        b = round (lerp b1 b2 t')
    Right (rgbToHex (fromIntegral r) (fromIntegral g) (fromIntegral b))

-- | Get contrasting text color (black or white) for a background
getContrastColor :: Text -> Either String Text
getContrastColor bgColor = do
  (r, g, b) <- hexToRgb bgColor
  -- Calculate luminance
  let luminance = (0.299 * r + 0.587 * g + 0.114 * b) / 255
  Right (if luminance > 0.5 then "#000000" else "#ffffff")

-- ════════════════════════════════════════════════════════════════════════════
--                                                                 // constants
-- ════════════════════════════════════════════════════════════════════════════

-- | Standard color swatches
standardSwatches :: [Text]
standardSwatches =
  [ "#ff0000", "#ff8000", "#ffff00", "#80ff00", "#00ff00"
  , "#00ff80", "#00ffff", "#0080ff", "#0000ff", "#8000ff"
  , "#ff00ff", "#ff0080", "#ffffff", "#c0c0c0", "#808080"
  , "#404040", "#000000"
  ]
