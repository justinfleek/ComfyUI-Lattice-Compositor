-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--               // hydrogen // schema // motion // effects // color // exposure
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Exposure — Photographic exposure adjustment.
-- |
-- | ## After Effects Parity
-- |
-- | Mirrors AE's Exposure effect with photographic controls:
-- |
-- | - **Exposure**: Measured in f-stops. Each stop doubles/halves brightness.
-- |   +1 stop = 2× brighter, -1 stop = 0.5× brighter.
-- |
-- | - **Offset**: Adds a constant to all pixel values. Primarily affects
-- |   shadows and midtones. Used to adjust black point.
-- |
-- | - **Gamma Correction**: Power function adjustment. Values < 1.0 brighten
-- |   midtones, values > 1.0 darken midtones.
-- |
-- | ## Properties (All Animatable)
-- |
-- | | Property | Type | Min | Max | Behavior | Default |
-- | |----------|------|-----|-----|----------|---------|
-- | | exposure | Number | -20.0 | 20.0 | clamps | 0.0 |
-- | | offset | Number | -10.0 | 10.0 | clamps | 0.0 |
-- | | gammaCorrection | Number | 0.01 | 10.0 | clamps | 1.0 |
-- |
-- | ## Mathematical Model
-- |
-- | For each pixel:
-- | 1. Apply exposure: `pixel * pow(2.0, exposure)`
-- | 2. Apply offset: `pixel + offset`
-- | 3. Apply gamma: `pow(pixel, gammaCorrection)`

module Hydrogen.Schema.Motion.Effects.ColorCorrection.Exposure
  ( -- * Exposure Effect
    ExposureEffect(..)
  , defaultExposureEffect
  , mkExposureEffect
  
  -- * Accessors
  , exposure
  , offset
  , gammaCorrection
  
  -- * Operations
  , setExposure
  , setOffset
  , setGammaCorrection
  , adjustExposure
  , resetEffect
  
  -- * Presets
  , exposureOverexposed
  , exposureUnderexposed
  , exposureCrushedBlacks
  , exposureLiftedBlacks
  , exposureHighContrast
  , exposureLowContrast
  
  -- * Queries
  , isEffectNeutral
  , isBrightening
  , isDarkening
  
  -- * Conversions
  , exposureToMultiplier
  , multiplierToExposure
  , stopsToExposure
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , class Semigroup
  , show
  , (<>)
  , (&&)
  , (||)
  , not
  , (==)
  , (/=)
  , (<)
  , (<=)
  , (>)
  , (>=)
  , (+)
  , (-)
  , (*)
  , (/)
  , negate
  , otherwise
  , compare
  , map
  , pure
  , bind
  )

import Hydrogen.Schema.Bounded (clampNumber)
import Hydrogen.Math.Core as Math

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // exposure // effect
-- ═════════════════════════════════════════════════════════════════════════════

-- | Exposure effect with photographic controls.
type ExposureEffect =
  { exposure :: Number        -- ^ F-stops (-20 to +20)
  , offset :: Number          -- ^ Constant offset (-10 to +10)
  , gammaCorrection :: Number -- ^ Gamma power (0.01 to 10)
  }

-- | Default neutral effect.
defaultExposureEffect :: ExposureEffect
defaultExposureEffect =
  { exposure: 0.0
  , offset: 0.0
  , gammaCorrection: 1.0
  }

-- | Create exposure effect with clamped values.
mkExposureEffect :: Number -> Number -> Number -> ExposureEffect
mkExposureEffect exp off gam =
  { exposure: clampNumber (negate 20.0) 20.0 exp
  , offset: clampNumber (negate 10.0) 10.0 off
  , gammaCorrection: clampNumber 0.01 10.0 gam
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get exposure value in f-stops.
exposure :: ExposureEffect -> Number
exposure effect = effect.exposure

-- | Get offset value.
offset :: ExposureEffect -> Number
offset effect = effect.offset

-- | Get gamma correction value.
gammaCorrection :: ExposureEffect -> Number
gammaCorrection effect = effect.gammaCorrection

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set exposure value.
setExposure :: Number -> ExposureEffect -> ExposureEffect
setExposure val effect = effect { exposure = clampNumber (negate 20.0) 20.0 val }

-- | Set offset value.
setOffset :: Number -> ExposureEffect -> ExposureEffect
setOffset val effect = effect { offset = clampNumber (negate 10.0) 10.0 val }

-- | Set gamma correction value.
setGammaCorrection :: Number -> ExposureEffect -> ExposureEffect
setGammaCorrection val effect = effect { gammaCorrection = clampNumber 0.01 10.0 val }

-- | Adjust exposure by a delta (add to current value).
adjustExposure :: Number -> ExposureEffect -> ExposureEffect
adjustExposure delta effect = 
  effect { exposure = clampNumber (negate 20.0) 20.0 (effect.exposure + delta) }

-- | Reset effect to neutral.
resetEffect :: ExposureEffect -> ExposureEffect
resetEffect _ = defaultExposureEffect

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Overexposed look — bright and washed out.
exposureOverexposed :: ExposureEffect
exposureOverexposed = mkExposureEffect 1.5 0.0 0.9

-- | Underexposed look — dark and moody.
exposureUnderexposed :: ExposureEffect
exposureUnderexposed = mkExposureEffect (negate 1.0) 0.0 1.1

-- | Crushed blacks — deep shadows for contrast.
exposureCrushedBlacks :: ExposureEffect
exposureCrushedBlacks = mkExposureEffect 0.0 (negate 0.05) 1.2

-- | Lifted blacks — faded/film look.
exposureLiftedBlacks :: ExposureEffect
exposureLiftedBlacks = mkExposureEffect 0.0 0.05 0.95

-- | High contrast — punchy image.
exposureHighContrast :: ExposureEffect
exposureHighContrast = mkExposureEffect 0.3 (negate 0.02) 1.3

-- | Low contrast — soft image.
exposureLowContrast :: ExposureEffect
exposureLowContrast = mkExposureEffect (negate 0.2) 0.03 0.85

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if effect is neutral (no adjustment).
isEffectNeutral :: ExposureEffect -> Boolean
isEffectNeutral effect =
  effect.exposure == 0.0 && 
  effect.offset == 0.0 && 
  effect.gammaCorrection == 1.0

-- | Check if effect is brightening the image.
isBrightening :: ExposureEffect -> Boolean
isBrightening effect =
  effect.exposure > 0.0 || 
  effect.offset > 0.0 || 
  effect.gammaCorrection < 1.0

-- | Check if effect is darkening the image.
isDarkening :: ExposureEffect -> Boolean
isDarkening effect =
  effect.exposure < 0.0 || 
  effect.offset < 0.0 || 
  effect.gammaCorrection > 1.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // conversions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert exposure (f-stops) to linear multiplier.
-- |
-- | +1 stop = 2.0x, +2 stops = 4.0x, -1 stop = 0.5x
exposureToMultiplier :: Number -> Number
exposureToMultiplier stops = Math.pow 2.0 stops

-- | Convert linear multiplier to exposure (f-stops).
-- |
-- | 2.0x = +1 stop, 4.0x = +2 stops, 0.5x = -1 stop
multiplierToExposure :: Number -> Number
multiplierToExposure mult = 
  if mult <= 0.0 
    then negate 20.0  -- Clamp to minimum
    else Math.log2 mult

-- | Create exposure value from f-stop count.
stopsToExposure :: Number -> Number
stopsToExposure stops = clampNumber (negate 20.0) 20.0 stops
