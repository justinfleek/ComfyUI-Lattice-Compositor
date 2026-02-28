-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // material // frosted
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Frosted — blur + tint + noise compound for glassmorphism effects.
-- |
-- | ## Purpose
-- |
-- | The Frosted compound represents the three essential components of
-- | frosted glass / glassmorphism effects as pure data:
-- |
-- | 1. **Blur**: Background blur radius
-- | 2. **Tint**: Color overlay with opacity
-- | 3. **Noise**: Texture to prevent color banding
-- |
-- | This is **pure data**. The runtime (WebGPU, Canvas, etc.) interprets
-- | these values into actual rendering commands. No CSS, no JavaScript,
-- | no browser assumptions.
-- |
-- | ## Dependencies
-- |
-- | - Schema.Material.BlurRadius (blur amount)
-- | - Schema.Color.SRGB (tint color)
-- | - Schema.Color.Opacity (transparency)

module Hydrogen.Schema.Material.Frosted
  ( -- * Frosted Type
    Frosted(Frosted)
  
  -- * Construction
  , frosted
  , frostedWithNoise
  , frostedMinimal
  
  -- * Accessors
  , blurRadius
  , tintColor
  , tintOpacity
  , noiseOpacity
  , noiseScale
  
  -- * Transformations
  , withBlur
  , withTint
  , withNoise
  , scaleBlur
  , adjustOpacity
  
  -- * Presets
  , frostedLight
  , frostedDark
  , frostedSubtle
  , frostedHeavy
  , frostedWarm
  , frostedCool
  , frostedNone
  
  -- * Queries
  , hasBlur
  , hasTint
  , hasNoise
  , isTransparent
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  , (>)
  , ($)
  , (*)
  , (&&)
  , max
  , not
  )

import Hydrogen.Schema.Color.SRGB as SRGB
import Hydrogen.Schema.Color.Opacity as Op

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // frosted type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Frosted — blur + tint + noise compound.
-- |
-- | Pure data representing glassmorphism parameters:
-- | - Blur radius for background blur
-- | - Tint color with opacity for color overlay
-- | - Noise texture to prevent banding artifacts
-- |
-- | The runtime interprets these values. This type makes no assumptions
-- | about rendering technology.
newtype Frosted = Frosted
  { blurRadius :: Number       -- ^ Blur radius in pixels (>= 0)
  , tintColor :: SRGB.SRGB     -- ^ Tint overlay color
  , tintOpacity :: Op.Opacity  -- ^ Tint opacity (0-100)
  , noiseOpacity :: Op.Opacity -- ^ Noise texture opacity (0-100)
  , noiseScale :: Number       -- ^ Noise texture scale (pixels per cell)
  }

derive instance eqFrosted :: Eq Frosted
derive instance ordFrosted :: Ord Frosted

instance showFrosted :: Show Frosted where
  show (Frosted f) = 
    "(Frosted blur:" <> show f.blurRadius 
    <> "px tint:" <> show f.tintOpacity
    <> " noise:" <> show f.noiseOpacity <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp a number to non-negative
clampNonNegative :: Number -> Number
clampNonNegative n = max 0.0 n

-- | White sRGB color
white :: SRGB.SRGB
white = SRGB.srgb 255 255 255

-- | Black sRGB color
black :: SRGB.SRGB
black = SRGB.srgb 0 0 0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // construction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a Frosted effect from blur, tint color, and tint opacity
-- |
-- | Uses default noise (2% opacity, scale 1.0) per Apple research.
frosted 
  :: { blur :: Number
     , tintColor :: SRGB.SRGB
     , tintOpacity :: Int
     }
  -> Frosted
frosted cfg = Frosted
  { blurRadius: clampNonNegative cfg.blur
  , tintColor: cfg.tintColor
  , tintOpacity: Op.opacity cfg.tintOpacity
  , noiseOpacity: Op.opacity 2  -- Default 2% noise
  , noiseScale: 1.0
  }

-- | Create a Frosted effect with explicit noise configuration
frostedWithNoise 
  :: { blur :: Number
     , tintColor :: SRGB.SRGB
     , tintOpacity :: Int
     , noiseOpacity :: Int
     , noiseScale :: Number
     }
  -> Frosted
frostedWithNoise cfg = Frosted
  { blurRadius: clampNonNegative cfg.blur
  , tintColor: cfg.tintColor
  , tintOpacity: Op.opacity cfg.tintOpacity
  , noiseOpacity: Op.opacity cfg.noiseOpacity
  , noiseScale: clampNonNegative cfg.noiseScale
  }

-- | Create a minimal Frosted with just blur (no tint, no noise)
frostedMinimal :: Number -> Frosted
frostedMinimal blur = Frosted
  { blurRadius: clampNonNegative blur
  , tintColor: white
  , tintOpacity: Op.opacity 0
  , noiseOpacity: Op.opacity 0
  , noiseScale: 1.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the blur radius in pixels
blurRadius :: Frosted -> Number
blurRadius (Frosted f) = f.blurRadius

-- | Get the tint color
tintColor :: Frosted -> SRGB.SRGB
tintColor (Frosted f) = f.tintColor

-- | Get the tint opacity
tintOpacity :: Frosted -> Op.Opacity
tintOpacity (Frosted f) = f.tintOpacity

-- | Get the noise opacity
noiseOpacity :: Frosted -> Op.Opacity
noiseOpacity (Frosted f) = f.noiseOpacity

-- | Get the noise scale (pixels per cell)
noiseScale :: Frosted -> Number
noiseScale (Frosted f) = f.noiseScale

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // transformations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set the blur radius
withBlur :: Number -> Frosted -> Frosted
withBlur blur (Frosted f) = Frosted 
  (f { blurRadius = clampNonNegative blur })

-- | Set the tint color and opacity
withTint :: SRGB.SRGB -> Int -> Frosted -> Frosted
withTint color opacityPct (Frosted f) = Frosted 
  (f { tintColor = color, tintOpacity = Op.opacity opacityPct })

-- | Set the noise opacity
withNoise :: Int -> Frosted -> Frosted
withNoise opacityPct (Frosted f) = Frosted 
  (f { noiseOpacity = Op.opacity opacityPct })

-- | Scale the blur radius by a factor
scaleBlur :: Number -> Frosted -> Frosted
scaleBlur factor (Frosted f) = Frosted 
  (f { blurRadius = clampNonNegative (f.blurRadius * factor) })

-- | Adjust tint and noise opacity by a factor
-- |
-- | Factor is applied to the underlying percentage values.
adjustOpacity :: Number -> Frosted -> Frosted
adjustOpacity factor (Frosted f) = Frosted
  (f { tintOpacity = Op.scale factor f.tintOpacity
     , noiseOpacity = Op.scale factor f.noiseOpacity
     })

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Light frosted glass (classic iOS style)
-- |
-- | 20px blur, white tint at 70%, 2% noise
frostedLight :: Frosted
frostedLight = Frosted
  { blurRadius: 20.0
  , tintColor: white
  , tintOpacity: Op.opacity 70
  , noiseOpacity: Op.opacity 2
  , noiseScale: 1.0
  }

-- | Dark frosted glass (dark mode compatible)
-- |
-- | 20px blur, black tint at 60%, 2% noise
frostedDark :: Frosted
frostedDark = Frosted
  { blurRadius: 20.0
  , tintColor: black
  , tintOpacity: Op.opacity 60
  , noiseOpacity: Op.opacity 2
  , noiseScale: 1.0
  }

-- | Subtle frosted effect (minimal, performant)
-- |
-- | 8px blur, white tint at 50%, no noise
frostedSubtle :: Frosted
frostedSubtle = Frosted
  { blurRadius: 8.0
  , tintColor: white
  , tintOpacity: Op.opacity 50
  , noiseOpacity: Op.opacity 0
  , noiseScale: 1.0
  }

-- | Heavy frosted effect (strong blur)
-- |
-- | 40px blur, white tint at 80%, 3% noise
frostedHeavy :: Frosted
frostedHeavy = Frosted
  { blurRadius: 40.0
  , tintColor: white
  , tintOpacity: Op.opacity 80
  , noiseOpacity: Op.opacity 3
  , noiseScale: 1.0
  }

-- | Warm frosted effect (orange/yellow tint)
-- |
-- | 20px blur, warm white tint at 60%, 2% noise
frostedWarm :: Frosted
frostedWarm = Frosted
  { blurRadius: 20.0
  , tintColor: SRGB.srgb 255 248 240  -- Warm white
  , tintOpacity: Op.opacity 60
  , noiseOpacity: Op.opacity 2
  , noiseScale: 1.0
  }

-- | Cool frosted effect (blue tint)
-- |
-- | 20px blur, cool white tint at 60%, 2% noise
frostedCool :: Frosted
frostedCool = Frosted
  { blurRadius: 20.0
  , tintColor: SRGB.srgb 240 248 255  -- Cool white
  , tintOpacity: Op.opacity 60
  , noiseOpacity: Op.opacity 2
  , noiseScale: 1.0
  }

-- | No frosted effect (transparent)
frostedNone :: Frosted
frostedNone = Frosted
  { blurRadius: 0.0
  , tintColor: white
  , tintOpacity: Op.opacity 0
  , noiseOpacity: Op.opacity 0
  , noiseScale: 1.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if this frosted effect has blur
hasBlur :: Frosted -> Boolean
hasBlur (Frosted f) = f.blurRadius > 0.0

-- | Check if this frosted effect has tint
hasTint :: Frosted -> Boolean
hasTint (Frosted f) = not $ Op.isTransparent f.tintOpacity

-- | Check if this frosted effect has noise
hasNoise :: Frosted -> Boolean
hasNoise (Frosted f) = not $ Op.isTransparent f.noiseOpacity

-- | Check if this frosted effect is essentially transparent
-- |
-- | Returns true if there's no blur, no tint, and no noise.
isTransparent :: Frosted -> Boolean
isTransparent f = not (hasBlur f) && not (hasTint f) && not (hasNoise f)
