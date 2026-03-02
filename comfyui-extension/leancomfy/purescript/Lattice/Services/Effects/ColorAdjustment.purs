-- | Lattice.Services.Effects.ColorAdjustment - Color Adjustment Functions
-- |
-- | Pure mathematical functions for color adjustment:
-- | - Hue/Saturation/Lightness
-- | - Vibrance (smart saturation)
-- | - Tint (black/white mapping)
-- | - Color Balance (shadows/midtones/highlights)
-- |
-- | All functions operate on normalized [0,1] color values.
-- | All functions are total and deterministic.
-- |
-- | Source: ui/src/services/effects/colorRenderer.ts

module Lattice.Services.Effects.ColorAdjustment
  ( HueSatParams
  , VibranceParams
  , TintParams
  , ColorBalanceParams
  , defaultHueSatParams
  , defaultVibranceParams
  , defaultTintParams
  , defaultColorBalanceParams
  , hueSaturation
  , vibrance
  , tint
  , colorBalance
  , rgbToHsl
  , hslToRgb
  ) where

import Prelude

import Data.Int (floor, toNumber)
import Data.Number (abs) as Number
import Data.Tuple (Tuple(..))
import Math (max, min)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Hue/Saturation parameters
type HueSatParams =
  { hueShift :: Number        -- -0.5 to 0.5 (normalized from -180 to 180)
  , saturationShift :: Number  -- -1 to 1 (normalized from -100 to 100)
  , lightnessShift :: Number   -- -1 to 1 (normalized from -100 to 100)
  , colorize :: Boolean        -- Colorize mode
  }

-- | Vibrance parameters
type VibranceParams =
  { vibrance :: Number    -- -1 to 1 (smart saturation)
  , saturation :: Number  -- -1 to 1 (standard saturation)
  }

-- | Tint parameters (map black/white to colors)
type TintParams =
  { blackR :: Number  -- Black point R [0,1]
  , blackG :: Number  -- Black point G [0,1]
  , blackB :: Number  -- Black point B [0,1]
  , whiteR :: Number  -- White point R [0,1]
  , whiteG :: Number  -- White point G [0,1]
  , whiteB :: Number  -- White point B [0,1]
  , amount :: Number  -- Blend amount 0-1
  }

-- | Color Balance parameters
type ColorBalanceParams =
  { shadowR :: Number     -- -1 to 1 (cyan to red in shadows)
  , shadowG :: Number     -- -1 to 1 (magenta to green in shadows)
  , shadowB :: Number     -- -1 to 1 (yellow to blue in shadows)
  , midtoneR :: Number    -- -1 to 1 (cyan to red in midtones)
  , midtoneG :: Number    -- -1 to 1 (magenta to green in midtones)
  , midtoneB :: Number    -- -1 to 1 (yellow to blue in midtones)
  , highlightR :: Number  -- -1 to 1 (cyan to red in highlights)
  , highlightG :: Number  -- -1 to 1 (magenta to green in highlights)
  , highlightB :: Number  -- -1 to 1 (yellow to blue in highlights)
  , preserveLuminosity :: Boolean
  }

--------------------------------------------------------------------------------
-- Default Values
--------------------------------------------------------------------------------

-- | Default hue/saturation (no change)
defaultHueSatParams :: HueSatParams
defaultHueSatParams =
  { hueShift: 0.0
  , saturationShift: 0.0
  , lightnessShift: 0.0
  , colorize: false
  }

-- | Default vibrance (no change)
defaultVibranceParams :: VibranceParams
defaultVibranceParams =
  { vibrance: 0.0
  , saturation: 0.0
  }

-- | Default tint (identity)
defaultTintParams :: TintParams
defaultTintParams =
  { blackR: 0.0, blackG: 0.0, blackB: 0.0
  , whiteR: 1.0, whiteG: 1.0, whiteB: 1.0
  , amount: 1.0
  }

-- | Default color balance (no change)
defaultColorBalanceParams :: ColorBalanceParams
defaultColorBalanceParams =
  { shadowR: 0.0, shadowG: 0.0, shadowB: 0.0
  , midtoneR: 0.0, midtoneG: 0.0, midtoneB: 0.0
  , highlightR: 0.0, highlightG: 0.0, highlightB: 0.0
  , preserveLuminosity: true
  }

--------------------------------------------------------------------------------
-- Utility Functions
--------------------------------------------------------------------------------

-- | Clamp value to [0, 1]
clamp01 :: Number -> Number
clamp01 = max 0.0 <<< min 1.0

-- | Calculate luminance from RGB [0,1]
luminance :: Number -> Number -> Number -> Number
luminance r g b = r * 0.299 + g * 0.587 + b * 0.114

-- | Maximum of three numbers
max3 :: Number -> Number -> Number -> Number
max3 a b c = max a (max b c)

-- | Minimum of three numbers
min3 :: Number -> Number -> Number -> Number
min3 a b c = min a (min b c)

--------------------------------------------------------------------------------
-- HSL Conversion
--------------------------------------------------------------------------------

-- | Convert RGB [0,1] to HSL [0,1]
rgbToHsl :: Tuple Number (Tuple Number Number) -> Tuple Number (Tuple Number Number)
rgbToHsl (Tuple r (Tuple g b)) =
  let maxC = max3 r g b
      minC = min3 r g b
      l = (maxC + minC) / 2.0
      d = maxC - minC
      { h, s } =
        if d == 0.0 then { h: 0.0, s: 0.0 }
        else
          let s' = if l > 0.5 then d / (2.0 - maxC - minC) else d / (maxC + minC)
              h' = if maxC == r then ((g - b) / d + (if g < b then 6.0 else 0.0)) / 6.0
                   else if maxC == g then ((b - r) / d + 2.0) / 6.0
                   else ((r - g) / d + 4.0) / 6.0
          in { h: h', s: s' }
  in Tuple h (Tuple s l)

-- | Convert HSL [0,1] to RGB [0,1]
hslToRgb :: Tuple Number (Tuple Number Number) -> Tuple Number (Tuple Number Number)
hslToRgb (Tuple h (Tuple s l)) =
  if s == 0.0 then Tuple l (Tuple l l)
  else
    let q = if l < 0.5 then l * (1.0 + s) else l + s - l * s
        p = 2.0 * l - q
        hue2rgb t
          | t < 0.0 = hue2rgb (t + 1.0)
          | t > 1.0 = hue2rgb (t - 1.0)
          | t < 1.0/6.0 = p + (q - p) * 6.0 * t
          | t < 1.0/2.0 = q
          | t < 2.0/3.0 = p + (q - p) * (2.0/3.0 - t) * 6.0
          | otherwise = p
    in Tuple (hue2rgb (h + 1.0/3.0)) (Tuple (hue2rgb h) (hue2rgb (h - 1.0/3.0)))

--------------------------------------------------------------------------------
-- Hue/Saturation
--------------------------------------------------------------------------------

-- | Apply hue/saturation adjustment
hueSaturation :: HueSatParams -> Tuple Number (Tuple Number Number) -> Tuple Number (Tuple Number Number)
hueSaturation params (Tuple r (Tuple g b)) =
  let Tuple h0 (Tuple s0 l0) = rgbToHsl (Tuple r (Tuple g b))
      { h, s } = if params.colorize
                 then { h: params.hueShift, s: Number.abs params.saturationShift + 0.25 }
                 else
                   let h' = h0 + params.hueShift
                       hWrapped = h' - toNumber (floor h')
                   in { h: hWrapped, s: s0 + s0 * params.saturationShift }
      l = l0 + l0 * params.lightnessShift
      sClamped = clamp01 s
      lClamped = clamp01 l
  in hslToRgb (Tuple h (Tuple sClamped lClamped))

--------------------------------------------------------------------------------
-- Vibrance
--------------------------------------------------------------------------------

-- | Apply vibrance (smart saturation protecting skin tones)
vibrance :: VibranceParams -> Tuple Number (Tuple Number Number) -> Tuple Number (Tuple Number Number)
vibrance params (Tuple r (Tuple g b)) =
  let vib = params.vibrance
      sat = params.saturation
      maxC = max3 r g b
      minC = min3 r g b
      currentSat = maxC - minC
      lum = luminance r g b
      -- Skin tone protection
      skinProtection = 1.0 - max 0.0 (min 1.0
        (Number.abs (r - 0.8) * 2.0 + Number.abs (g - 0.5) * 2.0 + Number.abs (b - 0.3) * 3.0))
      -- Vibrance inversely proportional to current saturation
      vibranceAmount = vib * (1.0 - currentSat) * (1.0 - skinProtection * 0.5)
      -- Combined saturation adjustment
      satAdjust = 1.0 + sat + vibranceAmount
      -- Apply saturation change
      r' = lum + (r - lum) * satAdjust
      g' = lum + (g - lum) * satAdjust
      b' = lum + (b - lum) * satAdjust
  in Tuple (clamp01 r') (Tuple (clamp01 g') (clamp01 b'))

--------------------------------------------------------------------------------
-- Tint
--------------------------------------------------------------------------------

-- | Apply tint (map black to one color, white to another)
tint :: TintParams -> Tuple Number (Tuple Number Number) -> Tuple Number (Tuple Number Number)
tint params (Tuple r (Tuple g b)) =
  let amount = params.amount
      lum = luminance r g b
      -- Interpolate between black and white colors
      tintR = params.blackR + (params.whiteR - params.blackR) * lum
      tintG = params.blackG + (params.whiteG - params.blackG) * lum
      tintB = params.blackB + (params.whiteB - params.blackB) * lum
      -- Blend with original
      r' = r + (tintR - r) * amount
      g' = g + (tintG - g) * amount
      b' = b + (tintB - b) * amount
  in Tuple (clamp01 r') (Tuple (clamp01 g') (clamp01 b'))

--------------------------------------------------------------------------------
-- Color Balance
--------------------------------------------------------------------------------

-- | Apply color balance (shadows/midtones/highlights)
colorBalance :: ColorBalanceParams -> Tuple Number (Tuple Number Number) -> Tuple Number (Tuple Number Number)
colorBalance params (Tuple r (Tuple g b)) =
  let lum = luminance r g b
      -- Calculate weights for tonal ranges
      shadowWeight = max 0.0 (1.0 - lum * 3.0)
      highlightWeight = max 0.0 ((lum - 0.67) * 3.0)
      midtoneWeight = 1.0 - shadowWeight - highlightWeight
      -- Apply adjustments per tonal range
      rAdj = params.shadowR * shadowWeight
           + params.midtoneR * midtoneWeight
           + params.highlightR * highlightWeight
      gAdj = params.shadowG * shadowWeight
           + params.midtoneG * midtoneWeight
           + params.highlightG * highlightWeight
      bAdj = params.shadowB * shadowWeight
           + params.midtoneB * midtoneWeight
           + params.highlightB * highlightWeight
      r' = r + rAdj
      g' = g + gAdj
      b' = b + bAdj
      -- Preserve luminosity if enabled
      { rFinal, gFinal, bFinal } =
        if params.preserveLuminosity then
          let newLum = luminance r' g' b'
              ratio = if newLum > 0.001 then lum / newLum else 1.0
          in { rFinal: r' * ratio, gFinal: g' * ratio, bFinal: b' * ratio }
        else { rFinal: r', gFinal: g', bFinal: b' }
  in Tuple (clamp01 rFinal) (Tuple (clamp01 gFinal) (clamp01 bFinal))
