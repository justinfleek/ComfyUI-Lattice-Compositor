-- | Lattice.Services.Effects.ColorGlow - Glow and Shadow Color Effects
-- |
-- | Pure mathematical functions for glow and shadow effects:
-- | - Glow (bloom/glow based on luminance threshold)
-- | - Drop Shadow (offset shadow with blur)
-- | - Vignette (darkening around edges)
-- |
-- | All functions operate on normalized [0,1] color values.
-- | All functions are total and deterministic.
-- |
-- | Source: ui/src/services/effects/colorRenderer.ts

module Lattice.Services.Effects.ColorGlow
  ( GlowParams
  , DropShadowParams
  , VignetteParams
  , defaultGlowParams
  , defaultDropShadowParams
  , defaultVignetteParams
  , glowIntensity
  , glowPixel
  , dropShadowOffset
  , vignetteAtPoint
  , applyVignette
  , luminance
  , distance2D
  ) where

import Prelude

import Data.Number (abs, pow, sqrt) as Number
import Data.Tuple (Tuple(..))
import Math (max, min)

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Glow effect parameters
type GlowParams =
  { threshold :: Number   -- Luminance threshold for glow [0,1]
  , intensity :: Number   -- Glow intensity multiplier [0,10]
  , radius :: Number      -- Glow spread radius in pixels [0,100]
  , softness :: Number    -- Glow edge softness [0,1]
  , colorR :: Number      -- Glow color R [0,1]
  , colorG :: Number      -- Glow color G [0,1]
  , colorB :: Number      -- Glow color B [0,1]
  }

-- | Drop shadow parameters
type DropShadowParams =
  { offsetX :: Number   -- Shadow X offset in pixels
  , offsetY :: Number   -- Shadow Y offset in pixels
  , blur :: Number      -- Shadow blur radius [0,100]
  , spread :: Number    -- Shadow spread [-1,1]
  , opacity :: Number   -- Shadow opacity [0,1]
  , colorR :: Number    -- Shadow color R [0,1]
  , colorG :: Number    -- Shadow color G [0,1]
  , colorB :: Number    -- Shadow color B [0,1]
  , inner :: Boolean    -- Inner shadow (vs drop shadow)
  }

-- | Vignette parameters
type VignetteParams =
  { amount :: Number      -- Vignette amount [-1,1]
  , midpoint :: Number    -- Where vignette starts [0,1]
  , roundness :: Number   -- Shape roundness [-1,1]
  , feather :: Number     -- Edge feather amount [0,1]
  , highlights :: Number  -- Highlight reduction [0,1]
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Default Values
-- ────────────────────────────────────────────────────────────────────────────

-- | Default glow (subtle white glow)
defaultGlowParams :: GlowParams
defaultGlowParams =
  { threshold: 0.8
  , intensity: 1.0
  , radius: 10.0
  , softness: 0.5
  , colorR: 1.0
  , colorG: 1.0
  , colorB: 1.0
  }

-- | Default drop shadow
defaultDropShadowParams :: DropShadowParams
defaultDropShadowParams =
  { offsetX: 5.0
  , offsetY: 5.0
  , blur: 5.0
  , spread: 0.0
  , opacity: 0.5
  , colorR: 0.0
  , colorG: 0.0
  , colorB: 0.0
  , inner: false
  }

-- | Default vignette
defaultVignetteParams :: VignetteParams
defaultVignetteParams =
  { amount: 0.5
  , midpoint: 0.5
  , roundness: 0.0
  , feather: 0.5
  , highlights: 0.0
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Utility Functions
-- ────────────────────────────────────────────────────────────────────────────

-- | Clamp value to [0, 1]
clamp01 :: Number -> Number
clamp01 = max 0.0 <<< min 1.0

-- | Calculate luminance from RGB [0,1]
luminance :: Number -> Number -> Number -> Number
luminance r g b = r * 0.299 + g * 0.587 + b * 0.114

-- | 2D Euclidean distance
distance2D :: Number -> Number -> Number -> Number -> Number
distance2D x1 y1 x2 y2 =
  let dx = x2 - x1
      dy = y2 - y1
  in Number.sqrt (dx * dx + dy * dy)

-- | Linear interpolation
lerp :: Number -> Number -> Number -> Number
lerp a b t = a + (b - a) * t

-- | Smooth step function
smoothstep :: Number -> Number -> Number -> Number
smoothstep edge0 edge1 x
  | x <= edge0 = 0.0
  | x >= edge1 = 1.0
  | otherwise =
      let t = (x - edge0) / (edge1 - edge0)
      in t * t * (3.0 - 2.0 * t)

-- ────────────────────────────────────────────────────────────────────────────
-- Glow Effect
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate glow intensity for a pixel
glowIntensity :: GlowParams -> Number -> Number -> Number -> Number
glowIntensity params r g b =
  let lum = luminance r g b
      threshold = params.threshold
      intensity = params.intensity
      softness = params.softness
  in if lum <= threshold
     then 0.0
     else
       let excess = (lum - threshold) / max 0.001 (1.0 - threshold)
           softExcess = if softness > 0.0
                        then Number.pow excess (1.0 / max 0.1 softness)
                        else excess
       in softExcess * intensity

-- | Apply glow to a pixel
glowPixel :: GlowParams -> Tuple Number (Tuple Number Number) -> Number -> Tuple Number (Tuple Number Number)
glowPixel params (Tuple r (Tuple g b)) glowAmount =
  let r' = r + params.colorR * glowAmount
      g' = g + params.colorG * glowAmount
      b' = b + params.colorB * glowAmount
  in Tuple (clamp01 r') (Tuple (clamp01 g') (clamp01 b'))

-- ────────────────────────────────────────────────────────────────────────────
-- Drop Shadow
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate shadow sample offset position
dropShadowOffset :: DropShadowParams -> Tuple Number Number -> Tuple Number Number
dropShadowOffset params (Tuple x y) =
  Tuple (x - params.offsetX) (y - params.offsetY)

-- ────────────────────────────────────────────────────────────────────────────
-- Vignette Effect
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate vignette factor at a point
vignetteAtPoint :: VignetteParams -> Number -> Number -> Number
vignetteAtPoint params x y =
  let cx = x - 0.5
      cy = y - 0.5
      roundness = params.roundness
      dist = if roundness >= 0.0
             then Number.sqrt (cx * cx + cy * cy)
             else max (Number.abs cx) (Number.abs cy)
      midpoint = params.midpoint
      feather = max 0.001 params.feather
      innerEdge = midpoint - feather / 2.0
      outerEdge = midpoint + feather / 2.0
      vigFactor = smoothstep innerEdge outerEdge dist
      amount = params.amount
  in vigFactor * amount

-- | Apply vignette to a pixel
applyVignette :: VignetteParams -> Number -> Number -> Tuple Number (Tuple Number Number) -> Tuple Number (Tuple Number Number)
applyVignette params x y (Tuple r (Tuple g b)) =
  let vigFactor = vignetteAtPoint params x y
      r' = r * (1.0 - vigFactor)
      g' = g * (1.0 - vigFactor)
      b' = b * (1.0 - vigFactor)
      highlights = params.highlights
      lum = luminance r g b
      highlightProtect = lum * highlights
      r'' = lerp r' r highlightProtect
      g'' = lerp g' g highlightProtect
      b'' = lerp b' b highlightProtect
  in Tuple (clamp01 r'') (Tuple (clamp01 g'') (clamp01 b''))
