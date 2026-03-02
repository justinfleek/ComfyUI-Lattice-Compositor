-- | Lattice.Utils.ColorUtils - Color conversion and manipulation
-- |
-- | HSV, RGB, HSL conversions and hex parsing.
-- | All functions handle edge cases safely.
-- |
-- | Source: lattice-core/lean/Lattice/Utils/ColorUtils.lean

module Lattice.Utils.ColorUtils
  ( HSV
  , HSL
  , HexParseResult(..)
  , hsvToRgb
  , rgbToHsv
  , hslToRgb
  , rgbToHsl
  , hexToRgb
  , rgbToHex
  , rgbaToHex
  , hsvToHex
  , hexToHsv
  , lerpRgb
  , getContrastColor
  , standardSwatches
  ) where

import Prelude
import Data.Array (length, (!!))
import Data.Int (floor, round, toNumber, hexadecimal, fromStringAs)
import Data.Maybe (Maybe(..))
import Data.Number (abs) as Number
import Data.String (Pattern(..), split, drop, take)
import Data.String.CodeUnits as String
import Lattice.Primitives (RGB, RGBA, FiniteFloat(..), UnitFloat(..), mkUnitFloat, unUnitFloat)

-- ────────────────────────────────────────────────────────────────────────────
-- Color Types
-- ────────────────────────────────────────────────────────────────────────────

-- | HSV color (Hue 0-360, Saturation 0-1, Value 0-1)
type HSV =
  { h :: FiniteFloat  -- 0-360
  , s :: UnitFloat    -- 0-1
  , v :: UnitFloat    -- 0-1
  }

-- | HSL color (Hue 0-360, Saturation 0-1, Lightness 0-1)
type HSL =
  { h :: FiniteFloat  -- 0-360
  , s :: UnitFloat    -- 0-1
  , l :: UnitFloat    -- 0-1
  }

-- | Hex parse result
data HexParseResult
  = HexOk RGB
  | HexOkWithAlpha RGBA
  | HexInvalid String

derive instance Eq HexParseResult

instance Show HexParseResult where
  show (HexOk rgb) = "HexOk " <> show rgb
  show (HexOkWithAlpha rgba) = "HexOkWithAlpha " <> show rgba
  show (HexInvalid err) = "HexInvalid " <> err

-- ────────────────────────────────────────────────────────────────────────────
-- Helper Functions
-- ────────────────────────────────────────────────────────────────────────────

-- | Clamp value to range
clamp :: Number -> Number -> Number -> Number
clamp minVal maxVal x = max minVal (min maxVal x)

-- | Float modulo
modFloat :: Number -> Number -> Number
modFloat a b = a - b * toNumber (floor (a / b))

-- | Normalize hue to [0, 360)
normalizeHue :: Number -> FiniteFloat
normalizeHue h =
  let wrapped = modFloat (modFloat h 360.0 + 360.0) 360.0
  in FiniteFloat wrapped

-- | Clamp to unit range
clampUnit :: Number -> UnitFloat
clampUnit n = UnitFloat (clamp 0.0 1.0 n)

-- ────────────────────────────────────────────────────────────────────────────
-- Color Space Conversions
-- ────────────────────────────────────────────────────────────────────────────

-- | Convert HSV to RGB
hsvToRgb :: HSV -> RGB
hsvToRgb { h: FiniteFloat hh, s: UnitFloat ss, v: UnitFloat vv } =
  let hNorm = modFloat (modFloat hh 360.0 + 360.0) 360.0
      c = vv * ss
      x = c * (1.0 - Number.abs (modFloat (hNorm / 60.0) 2.0 - 1.0))
      m = vv - c
      { r', g', b' } =
        if hNorm < 60.0 then { r': c, g': x, b': 0.0 }
        else if hNorm < 120.0 then { r': x, g': c, b': 0.0 }
        else if hNorm < 180.0 then { r': 0.0, g': c, b': x }
        else if hNorm < 240.0 then { r': 0.0, g': x, b': c }
        else if hNorm < 300.0 then { r': x, g': 0.0, b': c }
        else { r': c, g': 0.0, b': x }
      toChannel n = UnitFloat (toNumber (round ((n + m) * 255.0)))
  in { r: toChannel r', g: toChannel g', b: toChannel b' }

-- | Convert RGB to HSV
rgbToHsv :: RGB -> HSV
rgbToHsv { r: UnitFloat rr, g: UnitFloat gg, b: UnitFloat bb } =
  let r' = rr / 255.0
      g' = gg / 255.0
      b' = bb / 255.0
      maxC = max r' (max g' b')
      minC = min r' (min g' b')
      d = maxC - minC
      s = if maxC == 0.0 then 0.0 else d / maxC
      v = maxC
      h = if d == 0.0 then 0.0
          else if maxC == r' then ((g' - b') / d + (if g' < b' then 6.0 else 0.0)) * 60.0
          else if maxC == g' then ((b' - r') / d + 2.0) * 60.0
          else ((r' - g') / d + 4.0) * 60.0
  in { h: normalizeHue h, s: clampUnit s, v: clampUnit v }

-- | Convert HSL to RGB
hslToRgb :: HSL -> RGB
hslToRgb { h: FiniteFloat hh, s: UnitFloat ss, l: UnitFloat ll } =
  let hNorm = modFloat (modFloat hh 360.0 + 360.0) 360.0
      c = (1.0 - Number.abs (2.0 * ll - 1.0)) * ss
      x = c * (1.0 - Number.abs (modFloat (hNorm / 60.0) 2.0 - 1.0))
      m = ll - c / 2.0
      { r', g', b' } =
        if hNorm < 60.0 then { r': c, g': x, b': 0.0 }
        else if hNorm < 120.0 then { r': x, g': c, b': 0.0 }
        else if hNorm < 180.0 then { r': 0.0, g': c, b': x }
        else if hNorm < 240.0 then { r': 0.0, g': x, b': c }
        else if hNorm < 300.0 then { r': x, g': 0.0, b': c }
        else { r': c, g': 0.0, b': x }
      toChannel n = UnitFloat (toNumber (round ((n + m) * 255.0)))
  in { r: toChannel r', g: toChannel g', b: toChannel b' }

-- | Convert RGB to HSL
rgbToHsl :: RGB -> HSL
rgbToHsl { r: UnitFloat rr, g: UnitFloat gg, b: UnitFloat bb } =
  let r' = rr / 255.0
      g' = gg / 255.0
      b' = bb / 255.0
      maxC = max r' (max g' b')
      minC = min r' (min g' b')
      l = (maxC + minC) / 2.0
      d = maxC - minC
      { h, s } =
        if maxC == minC then { h: 0.0, s: 0.0 }
        else
          let s' = if l > 0.5 then d / (2.0 - maxC - minC) else d / (maxC + minC)
              h' = if maxC == r' then ((g' - b') / d + (if g' < b' then 6.0 else 0.0)) * 60.0
                   else if maxC == g' then ((b' - r') / d + 2.0) * 60.0
                   else ((r' - g') / d + 4.0) * 60.0
          in { h: h', s: s' }
  in { h: normalizeHue h, s: clampUnit s, l: clampUnit l }

-- ────────────────────────────────────────────────────────────────────────────
-- Hex Conversion
-- ────────────────────────────────────────────────────────────────────────────

-- | Parse hex color string to RGB
hexToRgb :: String -> HexParseResult
hexToRgb hex =
  let hex' = if String.take 1 hex == "#" then String.drop 1 hex else hex
      len = String.length hex'
  in case len of
    -- #RGB format
    3 ->
      case parseShortHex hex' of
        Just rgb -> HexOk rgb
        Nothing -> HexInvalid ("Invalid hex: " <> hex')

    -- #RRGGBB format
    6 ->
      case parseLongHex hex' of
        Just rgb -> HexOk rgb
        Nothing -> HexInvalid ("Invalid hex: " <> hex')

    -- #RRGGBBAA format
    8 ->
      case parseLongHexAlpha hex' of
        Just rgba -> HexOkWithAlpha rgba
        Nothing -> HexInvalid ("Invalid hex: " <> hex')

    _ -> HexInvalid ("Invalid hex length: " <> show len)

-- | Parse short hex format (#RGB)
parseShortHex :: String -> Maybe RGB
parseShortHex hex = do
  r <- fromStringAs hexadecimal (String.take 1 hex)
  g <- fromStringAs hexadecimal (String.take 1 (String.drop 1 hex))
  b <- fromStringAs hexadecimal (String.take 1 (String.drop 2 hex))
  r' <- mkUnitFloat (toNumber (r * 16 + r) / 255.0)
  g' <- mkUnitFloat (toNumber (g * 16 + g) / 255.0)
  b' <- mkUnitFloat (toNumber (b * 16 + b) / 255.0)
  pure { r: r', g: g', b: b' }

-- | Parse long hex format (#RRGGBB)
parseLongHex :: String -> Maybe RGB
parseLongHex hex = do
  r <- fromStringAs hexadecimal (String.take 2 hex)
  g <- fromStringAs hexadecimal (String.take 2 (String.drop 2 hex))
  b <- fromStringAs hexadecimal (String.take 2 (String.drop 4 hex))
  r' <- mkUnitFloat (toNumber r / 255.0)
  g' <- mkUnitFloat (toNumber g / 255.0)
  b' <- mkUnitFloat (toNumber b / 255.0)
  pure { r: r', g: g', b: b' }

-- | Parse long hex format with alpha (#RRGGBBAA)
parseLongHexAlpha :: String -> Maybe RGBA
parseLongHexAlpha hex = do
  r <- fromStringAs hexadecimal (String.take 2 hex)
  g <- fromStringAs hexadecimal (String.take 2 (String.drop 2 hex))
  b <- fromStringAs hexadecimal (String.take 2 (String.drop 4 hex))
  a <- fromStringAs hexadecimal (String.take 2 (String.drop 6 hex))
  r' <- mkUnitFloat (toNumber r / 255.0)
  g' <- mkUnitFloat (toNumber g / 255.0)
  b' <- mkUnitFloat (toNumber b / 255.0)
  a' <- mkUnitFloat (toNumber a / 255.0)
  pure { r: r', g: g', b: b', a: a' }

-- | Convert number to 2-digit hex string
toHex :: Number -> String
toHex n =
  let x = max 0 (min 255 (round n))
      digits = "0123456789abcdef"
      high = String.take 1 (String.drop (x / 16) digits)
      low = String.take 1 (String.drop (mod x 16) digits)
  in high <> low

-- | Convert RGB to hex string
rgbToHex :: RGB -> String
rgbToHex { r, g, b } = "#" <> toHex (unUnitFloat r * 255.0) <> toHex (unUnitFloat g * 255.0) <> toHex (unUnitFloat b * 255.0)

-- | Convert RGBA to hex string with alpha
rgbaToHex :: RGBA -> String
rgbaToHex { r, g, b, a } =
  let r' = unUnitFloat r
      g' = unUnitFloat g
      b' = unUnitFloat b
      a' = unUnitFloat a
  in "#" <> toHex (r' * 255.0) <> toHex (g' * 255.0) <> toHex (b' * 255.0) <> toHex (a' * 255.0)

-- | Convert HSV to hex string
hsvToHex :: HSV -> String
hsvToHex = rgbToHex <<< hsvToRgb

-- | Convert hex to HSV
hexToHsv :: String -> Maybe HSV
hexToHsv hex = case hexToRgb hex of
  HexOk rgb -> Just (rgbToHsv rgb)
  HexOkWithAlpha { r, g, b } -> Just (rgbToHsv { r, g, b })
  HexInvalid _ -> Nothing

-- ────────────────────────────────────────────────────────────────────────────
-- Color Manipulation
-- ────────────────────────────────────────────────────────────────────────────

-- | Linear interpolation between two RGB colors
lerpRgb :: RGB -> RGB -> UnitFloat -> RGB
lerpRgb c1 c2 (UnitFloat tt) =
  let lerp (UnitFloat a) (UnitFloat b) = UnitFloat (toNumber (round (a + (b - a) * tt)))
  in { r: lerp c1.r c2.r
     , g: lerp c1.g c2.g
     , b: lerp c1.b c2.b
     }

-- | Get contrasting text color (black or white) for background
getContrastColor :: RGB -> RGB
getContrastColor { r: UnitFloat rr, g: UnitFloat gg, b: UnitFloat bb } =
  let luminance = (0.299 * rr + 0.587 * gg + 0.114 * bb) / 255.0
  in if luminance > 0.5
     then { r: UnitFloat 0.0, g: UnitFloat 0.0, b: UnitFloat 0.0 }          -- black
     else { r: UnitFloat 255.0, g: UnitFloat 255.0, b: UnitFloat 255.0 }    -- white

-- ────────────────────────────────────────────────────────────────────────────
-- Standard Swatches
-- ────────────────────────────────────────────────────────────────────────────

-- | Standard color swatch hex values
standardSwatches :: Array String
standardSwatches =
  [ "#ff0000", "#ff8000", "#ffff00", "#80ff00"
  , "#00ff00", "#00ff80", "#00ffff", "#0080ff"
  , "#0000ff", "#8000ff", "#ff00ff", "#ff0080"
  , "#ffffff", "#c0c0c0", "#808080", "#404040", "#000000"
  ]
