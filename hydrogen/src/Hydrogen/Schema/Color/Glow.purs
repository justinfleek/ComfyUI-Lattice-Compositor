-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // schema // color // glow
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Glow - compound for emissive light effects.
-- |
-- | **ATOMIC COMPOSITION DESIGN:**
-- | Glow is a single, static effect. For complex effects, compose:
-- | - **Gradient glow**: `Array Glow` with positions (Geometry pillar)
-- | - **Animated glow**: `Animation Glow` with keyframes (Temporal pillar)
-- | - **Multi-layer glow**: `Array Glow` for inner + outer effects
-- |
-- | Glow combines color temperature, intensity, and spread:
-- | - **glowColor**: Warm to cool (Kelvin)
-- | - **glowIntensity**: Subtle to intense (Luminance in nits)
-- | - **glowSpread**: Blur radius in pixels (>= 0, Gaussian sigma)
-- |
-- | ## Spread Semantics
-- |
-- | Spread is Gaussian blur sigma in CSS pixels:
-- | - `0` = no blur, hard edge
-- | - `5` = tight halo
-- | - `20` = soft diffuse glow
-- | - `50+` = very diffuse, bloom-like
-- |
-- | Renders as CSS `filter: drop-shadow(0 0 {spread}px {color})`
-- | or WebGL Gaussian blur with sigma = spread.
-- |
-- | ## Use Cases
-- |
-- | - Button hover states with warm glow
-- | - Neon text effects
-- | - Active UI element highlights
-- | - Emissive materials in 3D
-- | - HDR bloom effects
-- |
-- | ## Playground Integration
-- |
-- | The visual studio presents sliders:
-- | - \"Glow Color\" (warm tungsten to cool daylight)
-- | - \"Glow Intensity\" (off to intense HDR)
-- | - \"Glow Spread\" (tight halo to soft diffuse)
-- |
-- | These map to physically accurate Kelvin/Luminance values internally.

module Hydrogen.Schema.Color.Glow
  ( Glow
  , glow
  , glowFromRecord
  , glowColor
  , glowIntensity
  , glowSpread
  , glowToRecord
  , glowToRgb
  , glowToCss
  , withColor
  , withIntensity
  , withSpread
  , warmGlow
  , coolGlow
  , neutralGlow
  , subtle
  , bright
  , intense
  , isOff
  ) where

import Prelude
  ( show
  , min
  , negate
  , not
  , otherwise
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (/=)
  , (&&)
  , (<>)
  )

import Data.Int as Int
import Hydrogen.Schema.Color.Channel as Ch
import Hydrogen.Schema.Color.Kelvin as K
import Hydrogen.Schema.Color.Luminance as L
import Hydrogen.Schema.Color.RGB as RGB

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // glow
-- ═════════════════════════════════════════════════════════════════════════════

-- | Glow effect parameters
-- |
-- | Combines color temperature (Kelvin), emission intensity (Luminance),
-- | and spatial spread (pixels) for complete glow control.
type Glow =
  { glowColor :: K.Kelvin      -- ^ Color temperature (warm to cool)
  , glowIntensity :: L.Luminance  -- ^ Emission intensity (nits)
  , glowSpread :: Number          -- ^ Blur radius (pixels)
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a glow effect from raw values
-- |
-- | Spread is clamped to >= 0 (negative blur is nonsensical).
-- | Spread must be finite (no Infinity or NaN).
-- |
-- | ```purescript
-- | glow 3000 200 20   -- Warm glow, 200 nits, 20px spread
-- | glow 6500 100 10   -- Cool glow, 100 nits, 10px spread
-- | glow 2700 50 (-5)  -- Negative spread clamped to 0
-- | ```
glow :: Int -> Number -> Number -> Glow
glow kelvinVal luminanceVal spreadVal =
  { glowColor: K.kelvin kelvinVal
  , glowIntensity: L.luminance luminanceVal
  , glowSpread: clampSpread spreadVal
  }
  where
    clampSpread s
      | s < 0.0 = 0.0
      | not (isFinite s) = 0.0
      | otherwise = s
    
    isFinite n = not (n /= n) && n /= (1.0 / 0.0) && n /= (-1.0 / 0.0)

-- | Create from a record
glowFromRecord :: { color :: Int, intensity :: Number, spread :: Number } -> Glow
glowFromRecord { color, intensity, spread } = glow color intensity spread

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the glow color temperature
glowColor :: Glow -> K.Kelvin
glowColor g = g.glowColor

-- | Get the glow intensity
glowIntensity :: Glow -> L.Luminance
glowIntensity g = g.glowIntensity

-- | Get the glow spread
glowSpread :: Glow -> Number
glowSpread g = g.glowSpread

-- | Convert to record for serialization
glowToRecord :: Glow -> { color :: Int, intensity :: Number, spread :: Number }
glowToRecord g =
  { color: K.unwrap g.glowColor
  , intensity: L.unwrap g.glowIntensity
  , spread: g.glowSpread
  }

-- | Convert glow color temperature to RGB
-- |
-- | Returns the RGB color that agents should render for the glow.
-- | Luminance and spread are separate - this only converts the Kelvin color.
-- |
-- | ```purescript
-- | glowToRgb warmGlow  -- RGB approximation of 2700K
-- | ```
glowToRgb :: Glow -> RGB.RGB
glowToRgb g = K.kelvinToRgb g.glowColor

-- | Convert to CSS drop-shadow filter
-- |
-- | Renders as `filter: drop-shadow(0 0 {spread}px rgba({r}, {g}, {b}, {alpha}))`
-- | where alpha is derived from luminance intensity.
-- |
-- | **Alpha calculation:**
-- | - 0-100 nits: alpha 0.0-0.3 (subtle)
-- | - 100-500 nits: alpha 0.3-0.7 (visible)
-- | - 500+ nits: alpha 0.7-1.0 (intense)
-- |
-- | ```purescript
-- | glowToCss myGlow  -- "drop-shadow(0 0 20px rgba(255, 200, 150, 0.6))"
-- | ```
glowToCss :: Glow -> String
glowToCss g =
  let
    rgb = glowToRgb g
    r = Int.toNumber (Ch.unwrap (RGB.red rgb))
    gv = Int.toNumber (Ch.unwrap (RGB.green rgb))
    b = Int.toNumber (Ch.unwrap (RGB.blue rgb))
    intensity = L.unwrap g.glowIntensity
    spread = g.glowSpread
    
    -- Map luminance (nits) to CSS alpha
    -- 0-100 nits: 0.0-0.3
    -- 100-500 nits: 0.3-0.7
    -- 500-2000 nits: 0.7-1.0
    alpha = if intensity < 100.0
              then (intensity / 100.0) * 0.3
              else if intensity < 500.0
                then 0.3 + ((intensity - 100.0) / 400.0) * 0.4
                else 0.7 + (min ((intensity - 500.0) / 1500.0) 1.0) * 0.3
  in
    "drop-shadow(0 0 " <> show spread <> "px rgba(" 
    <> show r <> ", " <> show gv <> ", " <> show b <> ", " <> show alpha <> "))"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Update glow color temperature
withColor :: K.Kelvin -> Glow -> Glow
withColor k g = g { glowColor = k }

-- | Update glow intensity
withIntensity :: L.Luminance -> Glow -> Glow
withIntensity l g = g { glowIntensity = l }

-- | Update glow spread
withSpread :: Number -> Glow -> Glow
withSpread s g = g { glowSpread = s }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Warm glow preset (tungsten ~2700K)
warmGlow :: Number -> Number -> Glow
warmGlow intensity spread = glow 2700 intensity spread

-- | Cool glow preset (daylight ~6500K)
coolGlow :: Number -> Number -> Glow
coolGlow intensity spread = glow 6500 intensity spread

-- | Neutral glow preset (neutral white ~4000K)
neutralGlow :: Number -> Number -> Glow
neutralGlow intensity spread = glow 4000 intensity spread

-- | Subtle glow (50 nits, 10px spread)
subtle :: K.Kelvin -> Glow
subtle k = glow (K.unwrap k) 50.0 10.0

-- | Bright glow (200 nits, 20px spread)
bright :: K.Kelvin -> Glow
bright k = glow (K.unwrap k) 200.0 20.0

-- | Intense glow (1000 nits, 30px spread)
intense :: K.Kelvin -> Glow
intense k = glow (K.unwrap k) 1000.0 30.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if glow is effectively off (intensity < 1 nit)
isOff :: Glow -> Boolean
isOff g = L.isOff g.glowIntensity
