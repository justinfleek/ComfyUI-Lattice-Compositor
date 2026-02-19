{-|
{-# LANGUAGE OverloadedStrings #-}
Module      : Lattice.Services.Effects.ColorGlow
Description : Glow and Shadow Color Effects
Copyright   : (c) Lattice Team, 2026
License     : MIT

Pure mathematical functions for glow and shadow effects:
- Glow (bloom/glow based on luminance threshold)
- Drop Shadow (offset shadow with blur)
- Vignette (darkening around edges)

All functions operate on normalized [0,1] color values.
All functions are total and deterministic.

Source: ui/src/services/effects/colorRenderer.ts
-}

{-# LANGUAGE StrictData #-}

module Lattice.Services.Effects.ColorGlow
  ( -- * Types
    GlowParams(..)
  , DropShadowParams(..)
  , VignetteParams(..)
    -- * Default Values
  , defaultGlowParams
  , defaultDropShadowParams
  , defaultVignetteParams
    -- * Effect Functions
  , glowIntensity
  , glowPixel
  , dropShadowOffset
  , vignetteAtPoint
  , applyVignette
    -- * Helpers
  , luminance
  , distance2D
  ) where

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Glow effect parameters
data GlowParams = GlowParams
  { gpThreshold  :: !Double  -- ^ Luminance threshold for glow [0,1]
  , gpIntensity  :: !Double  -- ^ Glow intensity multiplier [0,10]
  , gpRadius     :: !Double  -- ^ Glow spread radius in pixels [0,100]
  , gpSoftness   :: !Double  -- ^ Glow edge softness [0,1]
  , gpColorR     :: !Double  -- ^ Glow color R [0,1]
  , gpColorG     :: !Double  -- ^ Glow color G [0,1]
  , gpColorB     :: !Double  -- ^ Glow color B [0,1]
  } deriving (Eq, Show)

-- | Drop shadow parameters
data DropShadowParams = DropShadowParams
  { dspOffsetX   :: !Double  -- ^ Shadow X offset in pixels
  , dspOffsetY   :: !Double  -- ^ Shadow Y offset in pixels
  , dspBlur      :: !Double  -- ^ Shadow blur radius [0,100]
  , dspSpread    :: !Double  -- ^ Shadow spread [-1,1]
  , dspOpacity   :: !Double  -- ^ Shadow opacity [0,1]
  , dspColorR    :: !Double  -- ^ Shadow color R [0,1]
  , dspColorG    :: !Double  -- ^ Shadow color G [0,1]
  , dspColorB    :: !Double  -- ^ Shadow color B [0,1]
  , dspInner     :: !Bool    -- ^ Inner shadow (vs drop shadow)
  } deriving (Eq, Show)

-- | Vignette parameters
data VignetteParams = VignetteParams
  { vpAmount     :: !Double  -- ^ Vignette amount [-1,1] (negative = lighten)
  , vpMidpoint   :: !Double  -- ^ Where vignette starts [0,1]
  , vpRoundness  :: !Double  -- ^ Shape roundness [-1,1]
  , vpFeather    :: !Double  -- ^ Edge feather amount [0,1]
  , vpHighlights :: !Double  -- ^ Highlight reduction [0,1]
  } deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Default Values
--------------------------------------------------------------------------------

-- | Default glow (subtle white glow)
defaultGlowParams :: GlowParams
defaultGlowParams = GlowParams
  { gpThreshold = 0.8
  , gpIntensity = 1.0
  , gpRadius = 10.0
  , gpSoftness = 0.5
  , gpColorR = 1.0
  , gpColorG = 1.0
  , gpColorB = 1.0
  }

-- | Default drop shadow
defaultDropShadowParams :: DropShadowParams
defaultDropShadowParams = DropShadowParams
  { dspOffsetX = 5.0
  , dspOffsetY = 5.0
  , dspBlur = 5.0
  , dspSpread = 0.0
  , dspOpacity = 0.5
  , dspColorR = 0.0
  , dspColorG = 0.0
  , dspColorB = 0.0
  , dspInner = False
  }

-- | Default vignette
defaultVignetteParams :: VignetteParams
defaultVignetteParams = VignetteParams
  { vpAmount = 0.5
  , vpMidpoint = 0.5
  , vpRoundness = 0.0
  , vpFeather = 0.5
  , vpHighlights = 0.0
  }

--------------------------------------------------------------------------------
-- Utility Functions
--------------------------------------------------------------------------------

-- | Clamp value to [0, 1]
clamp01 :: Double -> Double
clamp01 = max 0 . min 1

-- | Clamp value to arbitrary range
clampRange :: Double -> Double -> Double -> Double
clampRange lo hi = max lo . min hi

-- | Calculate luminance from RGB [0,1]
luminance :: Double -> Double -> Double -> Double
luminance r g b = r * 0.299 + g * 0.587 + b * 0.114

-- | 2D Euclidean distance
distance2D :: Double -> Double -> Double -> Double -> Double
distance2D x1 y1 x2 y2 =
  let dx = x2 - x1
      dy = y2 - y1
  in sqrt (dx * dx + dy * dy)

-- | Linear interpolation
lerp :: Double -> Double -> Double -> Double
lerp a b t = a + (b - a) * t

-- | Smooth step function (for soft transitions)
smoothstep :: Double -> Double -> Double -> Double
smoothstep edge0 edge1 x
  | x <= edge0 = 0
  | x >= edge1 = 1
  | otherwise =
      let t = (x - edge0) / (edge1 - edge0)
      in t * t * (3 - 2 * t)

--------------------------------------------------------------------------------
-- Glow Effect
--------------------------------------------------------------------------------

-- | Calculate glow intensity for a pixel based on its luminance
glowIntensity :: GlowParams -> Double -> Double -> Double -> Double
glowIntensity params r g b =
  let lum = luminance r g b
      threshold = gpThreshold params
      intensity = gpIntensity params
      softness = gpSoftness params
  in if lum <= threshold
     then 0
     else
       let excess = (lum - threshold) / max 0.001 (1 - threshold)
           -- Apply softness curve
           softExcess = if softness > 0
                        then excess ** (1 / max 0.1 softness)
                        else excess
       in softExcess * intensity

-- | Apply glow to a pixel (additive blend)
glowPixel :: GlowParams -> (Double, Double, Double) -> Double -> (Double, Double, Double)
glowPixel params (r, g, b) glowAmount =
  let gr = gpColorR params
      gg = gpColorG params
      gb = gpColorB params
      r' = r + gr * glowAmount
      g' = g + gg * glowAmount
      b' = b + gb * glowAmount
  in (clamp01 r', clamp01 g', clamp01 b')

--------------------------------------------------------------------------------
-- Drop Shadow
--------------------------------------------------------------------------------

-- | Calculate shadow sample offset position
dropShadowOffset :: DropShadowParams -> (Double, Double) -> (Double, Double)
dropShadowOffset params (x, y) =
  let ox = x - dspOffsetX params
      oy = y - dspOffsetY params
  in (ox, oy)

-- | Calculate shadow alpha at distance from edge
shadowAlpha :: DropShadowParams -> Double -> Double
shadowAlpha params dist =
  let blur = max 0.001 (dspBlur params)
      spread = dspSpread params
      -- Spread affects the shadow size
      spreadDist = dist - spread * blur
      -- Blur creates falloff
      falloff = smoothstep blur 0 spreadDist
  in falloff * dspOpacity params

--------------------------------------------------------------------------------
-- Vignette Effect
--------------------------------------------------------------------------------

-- | Calculate vignette factor at a point (normalized coordinates 0-1)
vignetteAtPoint :: VignetteParams -> Double -> Double -> Double
vignetteAtPoint params x y =
  let -- Center coordinates at 0.5, 0.5
      cx = x - 0.5
      cy = y - 0.5
      -- Apply roundness (negative = more rectangular)
      roundness = vpRoundness params
      aspectRatio = 1.0  -- Could be parameterized
      -- Calculate distance with roundness adjustment
      dist = if roundness >= 0
             then sqrt (cx * cx + cy * cy)
             else max (abs cx * aspectRatio) (abs cy)
      -- Apply midpoint and feather
      midpoint = vpMidpoint params
      feather = max 0.001 (vpFeather params)
      innerEdge = midpoint - feather / 2
      outerEdge = midpoint + feather / 2
      -- Smooth transition
      vigFactor = smoothstep innerEdge outerEdge dist
      -- Apply amount (negative inverts)
      amount = vpAmount params
  in vigFactor * amount

-- | Apply vignette to a pixel
applyVignette :: VignetteParams -> Double -> Double -> (Double, Double, Double) -> (Double, Double, Double)
applyVignette params x y (r, g, b) =
  let vigFactor = vignetteAtPoint params x y
      -- Darken (or lighten if amount < 0)
      r' = r * (1 - vigFactor)
      g' = g * (1 - vigFactor)
      b' = b * (1 - vigFactor)
      -- Handle highlights preservation
      highlights = vpHighlights params
      lum = luminance r g b
      highlightProtect = lum * highlights
      r'' = lerp r' r highlightProtect
      g'' = lerp g' g highlightProtect
      b'' = lerp b' b highlightProtect
  in (clamp01 r'', clamp01 g'', clamp01 b'')
