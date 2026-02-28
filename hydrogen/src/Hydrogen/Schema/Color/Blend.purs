-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // schema // color // blend
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Blend modes and compositing operations.
-- |
-- | This module provides:
-- | - **Blend Modes**: Photoshop-style blending (multiply, screen, overlay...)
-- | - **Porter-Duff**: Alpha compositing operations
-- | - **Mixing**: Color interpolation

module Hydrogen.Schema.Color.Blend
  ( -- * Blend Modes
    BlendMode(..)
  , blendRGBA
  , blendChannel
  
  -- * Porter-Duff Compositing
  , CompositeOp(..)
  , composite
  
  -- * Color Mixing
  , mixRGB
  , mixRGBA
  , lerpRGB
  
  -- * CSS Output
  , blendModeToCss
  , compositeOpToCss
  ) where

import Prelude
  ( class Eq
  , class Show
  , otherwise
  , ($)
  , (==)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (>)
  , (<=)
  , (>=)
  )

import Data.Int (toNumber, round)
import Hydrogen.Math.Core as Math
import Hydrogen.Schema.Color.RGB as RGB
import Hydrogen.Schema.Color.Channel as Ch
import Hydrogen.Schema.Color.Opacity as Op

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // blend modes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Standard blend modes (Photoshop/CSS)
data BlendMode
  -- Normal modes
  = Normal               -- ^ Top layer only
  | Dissolve             -- ^ Random dithering (not applicable to static)
  
  -- Darken modes
  | Darken               -- ^ Min of each channel
  | Multiply             -- ^ Channels multiplied
  | ColorBurn            -- ^ Darkens by increasing contrast
  | LinearBurn           -- ^ Darkens by decreasing brightness
  | DarkerColor          -- ^ Darker of the two colors
  
  -- Lighten modes
  | Lighten              -- ^ Max of each channel
  | Screen               -- ^ Inverse of multiply
  | ColorDodge           -- ^ Brightens by decreasing contrast
  | LinearDodge          -- ^ Brightens (add)
  | LighterColor         -- ^ Lighter of the two colors
  
  -- Contrast modes
  | Overlay              -- ^ Multiply or screen based on base
  | SoftLight            -- ^ Gentle overlay
  | HardLight            -- ^ Strong overlay
  | VividLight           -- ^ Color burn or dodge
  | LinearLight          -- ^ Linear burn or dodge
  | PinLight             -- ^ Darken or lighten
  | HardMix              -- ^ Extreme posterization
  
  -- Inversion modes
  | Difference           -- ^ Absolute difference
  | Exclusion            -- ^ Lower contrast difference
  | Subtract             -- ^ Subtract blend from base
  | Divide               -- ^ Divide base by blend

derive instance eqBlendMode :: Eq BlendMode

instance showBlendMode :: Show BlendMode where
  show = blendModeToCss

-- | Blend two RGBA colors using a blend mode
blendRGBA :: BlendMode -> RGB.RGBA -> RGB.RGBA -> RGB.RGBA
blendRGBA mode base top =
  let
    baseR = Ch.unwrap (RGB.red (RGB.fromRGBA base))
    baseG = Ch.unwrap (RGB.green (RGB.fromRGBA base))
    baseB = Ch.unwrap (RGB.blue (RGB.fromRGBA base))
    baseA = Op.toUnitInterval (RGB.alpha base)
    
    topR = Ch.unwrap (RGB.red (RGB.fromRGBA top))
    topG = Ch.unwrap (RGB.green (RGB.fromRGBA top))
    topB = Ch.unwrap (RGB.blue (RGB.fromRGBA top))
    topA = Op.toUnitInterval (RGB.alpha top)
    
    -- Apply blend mode to each channel
    blendedR = blendChannel mode baseR topR
    blendedG = blendChannel mode baseG topG
    blendedB = blendChannel mode baseB topB
    
    -- Composite with alpha
    resultA = topA + baseA * (1.0 - topA)
    mixWithAlpha baseC blendedC =
      if resultA == 0.0 then 0
      else round ((toNumber blendedC * topA + toNumber baseC * baseA * (1.0 - topA)) / resultA)
  in 
    RGB.rgba 
      (mixWithAlpha baseR blendedR)
      (mixWithAlpha baseG blendedG)
      (mixWithAlpha baseB blendedB)
      (round (resultA * 100.0))

-- | Apply blend mode to a single channel (0-255)
blendChannel :: BlendMode -> Int -> Int -> Int
blendChannel mode base top =
  let
    b = toNumber base / 255.0
    t = toNumber top / 255.0
    result = case mode of
      Normal -> t
      Dissolve -> t
      
      Darken -> Math.min b t
      Multiply -> b * t
      ColorBurn -> if t == 0.0 then 0.0 else 1.0 - Math.min 1.0 ((1.0 - b) / t)
      LinearBurn -> Math.max 0.0 (b + t - 1.0)
      DarkerColor -> if b < t then b else t
      
      Lighten -> Math.max b t
      Screen -> 1.0 - (1.0 - b) * (1.0 - t)
      ColorDodge -> if t == 1.0 then 1.0 else Math.min 1.0 (b / (1.0 - t))
      LinearDodge -> Math.min 1.0 (b + t)
      LighterColor -> if b > t then b else t
      
      Overlay -> if b < 0.5 then 2.0 * b * t else 1.0 - 2.0 * (1.0 - b) * (1.0 - t)
      SoftLight -> if t < 0.5 
        then b - (1.0 - 2.0 * t) * b * (1.0 - b)
        else b + (2.0 * t - 1.0) * (softLightD b - b)
      HardLight -> if t < 0.5 then 2.0 * b * t else 1.0 - 2.0 * (1.0 - b) * (1.0 - t)
      VividLight -> if t < 0.5 
        then if t == 0.0 then 0.0 else 1.0 - Math.min 1.0 ((1.0 - b) / (2.0 * t))
        else if t == 1.0 then 1.0 else Math.min 1.0 (b / (2.0 * (1.0 - t)))
      LinearLight -> Math.max 0.0 (Math.min 1.0 (b + 2.0 * t - 1.0))
      PinLight -> if t < 0.5 then Math.min b (2.0 * t) else Math.max b (2.0 * t - 1.0)
      HardMix -> if b + t >= 1.0 then 1.0 else 0.0
      
      Difference -> Math.abs (b - t)
      Exclusion -> b + t - 2.0 * b * t
      Subtract -> Math.max 0.0 (b - t)
      Divide -> if t == 0.0 then 1.0 else Math.min 1.0 (b / t)
  in clamp8 (round (result * 255.0))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // porter-duff compositing
-- ═════════════════════════════════════════════════════════════════════════════

-- | Porter-Duff compositing operations
data CompositeOp
  = Clear                -- ^ Neither source nor destination
  | Copy                 -- ^ Source only
  | Destination          -- ^ Destination only
  | SourceOver           -- ^ Source over destination (normal)
  | DestinationOver      -- ^ Destination over source
  | SourceIn             -- ^ Source where destination exists
  | DestinationIn        -- ^ Destination where source exists
  | SourceOut            -- ^ Source where destination doesn't exist
  | DestinationOut       -- ^ Destination where source doesn't exist
  | SourceAtop           -- ^ Source atop destination
  | DestinationAtop      -- ^ Destination atop source
  | Xor                  -- ^ Exclusive or

derive instance eqCompositeOp :: Eq CompositeOp

-- | Apply Porter-Duff compositing
composite :: CompositeOp -> RGB.RGBA -> RGB.RGBA -> RGB.RGBA
composite op src dst =
  let
    srcR = Ch.unwrap (RGB.red (RGB.fromRGBA src))
    srcG = Ch.unwrap (RGB.green (RGB.fromRGBA src))
    srcB = Ch.unwrap (RGB.blue (RGB.fromRGBA src))
    srcA = Op.toUnitInterval (RGB.alpha src)
    
    dstR = Ch.unwrap (RGB.red (RGB.fromRGBA dst))
    dstG = Ch.unwrap (RGB.green (RGB.fromRGBA dst))
    dstB = Ch.unwrap (RGB.blue (RGB.fromRGBA dst))
    dstA = Op.toUnitInterval (RGB.alpha dst)
    
    -- Porter-Duff factors: Fa for source, Fb for destination
    factors = case op of
      Clear -> { fa: 0.0, fb: 0.0 }
      Copy -> { fa: 1.0, fb: 0.0 }
      Destination -> { fa: 0.0, fb: 1.0 }
      SourceOver -> { fa: 1.0, fb: 1.0 - srcA }
      DestinationOver -> { fa: 1.0 - dstA, fb: 1.0 }
      SourceIn -> { fa: dstA, fb: 0.0 }
      DestinationIn -> { fa: 0.0, fb: srcA }
      SourceOut -> { fa: 1.0 - dstA, fb: 0.0 }
      DestinationOut -> { fa: 0.0, fb: 1.0 - srcA }
      SourceAtop -> { fa: dstA, fb: 1.0 - srcA }
      DestinationAtop -> { fa: 1.0 - dstA, fb: srcA }
      Xor -> { fa: 1.0 - dstA, fb: 1.0 - srcA }
    
    resultA = srcA * factors.fa + dstA * factors.fb
    
    compChannel srcC dstC =
      if resultA == 0.0 then 0
      else clamp8 $ round $ 
        (toNumber srcC * srcA * factors.fa + toNumber dstC * dstA * factors.fb) / resultA
  in
    RGB.rgba
      (compChannel srcR dstR)
      (compChannel srcG dstG)
      (compChannel srcB dstB)
      (round (resultA * 100.0))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // color mixing
-- ═════════════════════════════════════════════════════════════════════════════

-- | Mix two RGB colors (t=0 gives first, t=1 gives second)
mixRGB :: Number -> RGB.RGB -> RGB.RGB -> RGB.RGB
mixRGB t c1 c2 =
  let
    w = clampUnit t
    r1 = Ch.unwrap (RGB.red c1)
    g1 = Ch.unwrap (RGB.green c1)
    b1 = Ch.unwrap (RGB.blue c1)
    r2 = Ch.unwrap (RGB.red c2)
    g2 = Ch.unwrap (RGB.green c2)
    b2 = Ch.unwrap (RGB.blue c2)
    mixVal v1 v2 = round (toNumber v1 * (1.0 - w) + toNumber v2 * w)
  in
    RGB.rgb (mixVal r1 r2) (mixVal g1 g2) (mixVal b1 b2)

-- | Mix two RGBA colors (t=0 gives first, t=1 gives second)
mixRGBA :: Number -> RGB.RGBA -> RGB.RGBA -> RGB.RGBA
mixRGBA t c1 c2 =
  let
    w = clampUnit t
    rec1 = RGB.toRecordA c1
    rec2 = RGB.toRecordA c2
    mixVal v1 v2 = round (toNumber v1 * (1.0 - w) + toNumber v2 * w)
  in
    RGB.rgba 
      (mixVal rec1.r rec2.r) 
      (mixVal rec1.g rec2.g) 
      (mixVal rec1.b rec2.b)
      (mixVal rec1.a rec2.a)

-- | Linear interpolation between two RGB colors
lerpRGB :: Number -> RGB.RGB -> RGB.RGB -> RGB.RGB
lerpRGB = mixRGB

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // css output
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert blend mode to CSS mix-blend-mode value
blendModeToCss :: BlendMode -> String
blendModeToCss = case _ of
  Normal -> "normal"
  Dissolve -> "normal"
  Darken -> "darken"
  Multiply -> "multiply"
  ColorBurn -> "color-burn"
  LinearBurn -> "color-burn"
  DarkerColor -> "darken"
  Lighten -> "lighten"
  Screen -> "screen"
  ColorDodge -> "color-dodge"
  LinearDodge -> "color-dodge"
  LighterColor -> "lighten"
  Overlay -> "overlay"
  SoftLight -> "soft-light"
  HardLight -> "hard-light"
  VividLight -> "hard-light"
  LinearLight -> "hard-light"
  PinLight -> "hard-light"
  HardMix -> "hard-light"
  Difference -> "difference"
  Exclusion -> "exclusion"
  Subtract -> "difference"
  Divide -> "normal"

-- | Convert composite op to CSS value
compositeOpToCss :: CompositeOp -> String
compositeOpToCss = case _ of
  Clear -> "clear"
  Copy -> "copy"
  Destination -> "destination"
  SourceOver -> "source-over"
  DestinationOver -> "destination-over"
  SourceIn -> "source-in"
  DestinationIn -> "destination-in"
  SourceOut -> "source-out"
  DestinationOut -> "destination-out"
  SourceAtop -> "source-atop"
  DestinationAtop -> "destination-atop"
  Xor -> "xor"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Soft light helper function
softLightD :: Number -> Number
softLightD x =
  if x <= 0.25 
    then ((16.0 * x - 12.0) * x + 4.0) * x
    else Math.sqrt x

-- | Clamp to 0-255
clamp8 :: Int -> Int
clamp8 n
  | n < 0 = 0
  | n > 255 = 255
  | otherwise = n

-- | Clamp to 0.0-1.0
clampUnit :: Number -> Number
clampUnit n
  | n < 0.0 = 0.0
  | n > 1.0 = 1.0
  | otherwise = n
