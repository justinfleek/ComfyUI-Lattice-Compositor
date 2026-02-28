-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--               // hydrogen // schema // motion // effects // color // vibrance
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Vibrance — Intelligent saturation adjustment.
-- |
-- | ## After Effects Parity
-- |
-- | Mirrors AE's Vibrance effect which provides smart saturation:
-- |
-- | - **Vibrance**: Increases saturation of muted colors more than
-- |   already-saturated colors. Protects skin tones from over-saturation.
-- |
-- | - **Saturation**: Traditional linear saturation adjustment affecting
-- |   all colors equally.
-- |
-- | ## Properties (All Animatable)
-- |
-- | | Property | Type | Min | Max | Behavior | Default |
-- | |----------|------|-----|-----|----------|---------|
-- | | vibrance | Number | -100.0 | 100.0 | clamps | 0.0 |
-- | | saturation | Number | -100.0 | 100.0 | clamps | 0.0 |
-- |
-- | ## Mathematical Model
-- |
-- | Vibrance uses a non-linear saturation curve:
-- | - Low-saturation pixels receive more boost
-- | - High-saturation pixels receive less boost
-- | - Skin tone hue range (orange-red) is protected
-- |
-- | At vibrance = 100, a 20% saturated pixel might gain 80%,
-- | while an 80% saturated pixel might only gain 20%.

module Hydrogen.Schema.Motion.Effects.ColorCorrection.Vibrance
  ( -- * Vibrance Effect
    VibranceEffect(..)
  , defaultVibranceEffect
  , mkVibranceEffect
  
  -- * Accessors
  , vibrance
  , saturation
  
  -- * Operations
  , setVibrance
  , setSaturation
  , resetEffect
  
  -- * Presets
  , vibranceSubtle
  , vibranceStrong
  , vibranceMuted
  , vibranceDesaturated
  , vibrancePop
  
  -- * Queries
  , isEffectNeutral
  , isDesaturating
  , isSaturating
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

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // vibrance // effect
-- ═════════════════════════════════════════════════════════════════════════════

-- | Vibrance effect with smart and linear saturation controls.
type VibranceEffect =
  { vibrance :: Number     -- ^ Smart saturation (-100 to 100)
  , saturation :: Number   -- ^ Linear saturation (-100 to 100)
  }

-- | Default neutral effect.
defaultVibranceEffect :: VibranceEffect
defaultVibranceEffect =
  { vibrance: 0.0
  , saturation: 0.0
  }

-- | Create vibrance effect with clamped values.
mkVibranceEffect :: Number -> Number -> VibranceEffect
mkVibranceEffect vib sat =
  { vibrance: clampNumber (negate 100.0) 100.0 vib
  , saturation: clampNumber (negate 100.0) 100.0 sat
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get vibrance value.
vibrance :: VibranceEffect -> Number
vibrance effect = effect.vibrance

-- | Get saturation value.
saturation :: VibranceEffect -> Number
saturation effect = effect.saturation

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set vibrance value.
setVibrance :: Number -> VibranceEffect -> VibranceEffect
setVibrance val effect = effect { vibrance = clampNumber (negate 100.0) 100.0 val }

-- | Set saturation value.
setSaturation :: Number -> VibranceEffect -> VibranceEffect
setSaturation val effect = effect { saturation = clampNumber (negate 100.0) 100.0 val }

-- | Reset effect to neutral.
resetEffect :: VibranceEffect -> VibranceEffect
resetEffect _ = defaultVibranceEffect

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Subtle vibrance boost — natural enhancement.
vibranceSubtle :: VibranceEffect
vibranceSubtle = mkVibranceEffect 25.0 0.0

-- | Strong vibrance — punchy colors without clipping.
vibranceStrong :: VibranceEffect
vibranceStrong = mkVibranceEffect 60.0 10.0

-- | Muted look — reduced vibrance for film emulation.
vibranceMuted :: VibranceEffect
vibranceMuted = mkVibranceEffect (negate 30.0) (negate 15.0)

-- | Desaturated — near black and white.
vibranceDesaturated :: VibranceEffect
vibranceDesaturated = mkVibranceEffect (negate 80.0) (negate 70.0)

-- | Pop look — maximum color impact.
vibrancePop :: VibranceEffect
vibrancePop = mkVibranceEffect 80.0 30.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if effect is neutral (no adjustment).
isEffectNeutral :: VibranceEffect -> Boolean
isEffectNeutral effect =
  effect.vibrance == 0.0 && effect.saturation == 0.0

-- | Check if effect is desaturating.
isDesaturating :: VibranceEffect -> Boolean
isDesaturating effect =
  effect.vibrance < 0.0 || effect.saturation < 0.0

-- | Check if effect is saturating.
isSaturating :: VibranceEffect -> Boolean
isSaturating effect =
  effect.vibrance > 0.0 || effect.saturation > 0.0
