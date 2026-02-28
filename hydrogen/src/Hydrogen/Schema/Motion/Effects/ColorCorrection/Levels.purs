-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                  // hydrogen // schema // motion // effects // color // levels
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Levels Effect — Industry-standard levels color correction.
-- |
-- | ## After Effects Parity
-- |
-- | Mirrors AE's Levels effect with per-channel control:
-- |
-- | - **Input Black/White**: Remaps input range (0.0-1.0, clamps)
-- | - **Gamma**: Midtone adjustment (0.1-10.0, clamps)
-- | - **Output Black/White**: Remaps output range (0.0-1.0, clamps)
-- |
-- | Each channel (Master, Red, Green, Blue, Alpha) has independent controls.
-- |
-- | ## Properties (All Animatable)
-- |
-- | | Property | Type | Min | Max | Behavior | Default |
-- | |----------|------|-----|-----|----------|---------|
-- | | inputBlack | Number | 0.0 | 1.0 | clamps | 0.0 |
-- | | inputWhite | Number | 0.0 | 1.0 | clamps | 1.0 |
-- | | gamma | Number | 0.1 | 10.0 | clamps | 1.0 |
-- | | outputBlack | Number | 0.0 | 1.0 | clamps | 0.0 |
-- | | outputWhite | Number | 0.0 | 1.0 | clamps | 1.0 |
-- |
-- | ## GPU Shader
-- |
-- | ```glsl
-- | float applyLevels(float v, float inBlack, float inWhite, float gamma, float outBlack, float outWhite) {
-- |   float normalized = clamp((v - inBlack) / (inWhite - inBlack), 0.0, 1.0);
-- |   float gammaCorrected = pow(normalized, 1.0 / gamma);
-- |   return outBlack + gammaCorrected * (outWhite - outBlack);
-- | }
-- | ```

module Hydrogen.Schema.Motion.Effects.ColorCorrection.Levels
  ( -- * Channel Levels
    ChannelLevels(..)
  , defaultChannelLevels
  , mkChannelLevels
  
  -- * Levels Gamma (0.1-10.0)
  , LevelsGamma
  , levelsGamma
  , unwrapLevelsGamma
  , defaultLevelsGamma
  
  -- * Levels Effect
  , LevelsEffect(..)
  , defaultLevelsEffect
  , mkLevelsEffect
  
  -- * Accessors
  , masterLevels
  , redLevels
  , greenLevels
  , blueLevels
  , alphaLevels
  
  -- * Channel Accessors
  , inputBlack
  , inputWhite
  , gamma
  , outputBlack
  , outputWhite
  
  -- * Operations
  , setMasterLevels
  , setRedLevels
  , setGreenLevels
  , setBlueLevels
  , setAlphaLevels
  , setInputBlack
  , setInputWhite
  , setGamma
  , setOutputBlack
  , setOutputWhite
  
  -- * Presets
  , levelsAutoContrast
  , levelsInvert
  , levelsHighContrast
  , levelsShadowBoost
  , levelsHighlightBoost
  
  -- * Queries
  , isChannelNeutral
  , isEffectNeutral
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  , (<)
  , (>)
  , (==)
  , (&&)
  , otherwise
  )

import Hydrogen.Schema.Dimension.Percentage (Ratio, ratio, unwrapRatio)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // channel // levels
-- ═════════════════════════════════════════════════════════════════════════════

-- | Levels settings for a single channel.
-- |
-- | All properties are animatable.
newtype ChannelLevels = ChannelLevels
  { inputBlack :: Ratio     -- ^ Input black point (0.0-1.0)
  , inputWhite :: Ratio     -- ^ Input white point (0.0-1.0)
  , gamma :: LevelsGamma    -- ^ Gamma/midtone (0.1-10.0)
  , outputBlack :: Ratio    -- ^ Output black point (0.0-1.0)
  , outputWhite :: Ratio    -- ^ Output white point (0.0-1.0)
  }

derive instance eqChannelLevels :: Eq ChannelLevels

instance showChannelLevels :: Show ChannelLevels where
  show (ChannelLevels c) =
    "ChannelLevels { in: " <> show c.inputBlack <> "-" <> show c.inputWhite
    <> ", gamma: " <> show c.gamma
    <> ", out: " <> show c.outputBlack <> "-" <> show c.outputWhite <> " }"

-- | Gamma for Levels effect (0.1-10.0).
-- |
-- | Different from LiftGammaGain.Gamma which has range 0.1-4.0.
-- | Levels allows more extreme gamma correction.
newtype LevelsGamma = LevelsGamma Number

derive instance eqLevelsGamma :: Eq LevelsGamma

instance showLevelsGamma :: Show LevelsGamma where
  show (LevelsGamma g) = show g

-- | Create levels gamma (clamped 0.1-10.0).
levelsGamma :: Number -> LevelsGamma
levelsGamma n
  | n < 0.1 = LevelsGamma 0.1
  | n > 10.0 = LevelsGamma 10.0
  | otherwise = LevelsGamma n

-- | Unwrap levels gamma.
unwrapLevelsGamma :: LevelsGamma -> Number
unwrapLevelsGamma (LevelsGamma g) = g

-- | Default gamma (1.0 = no change).
defaultLevelsGamma :: LevelsGamma
defaultLevelsGamma = LevelsGamma 1.0

-- | Default channel levels (no adjustment).
defaultChannelLevels :: ChannelLevels
defaultChannelLevels = ChannelLevels
  { inputBlack: ratio 0.0
  , inputWhite: ratio 1.0
  , gamma: defaultLevelsGamma
  , outputBlack: ratio 0.0
  , outputWhite: ratio 1.0
  }

-- | Create channel levels with bounds validation.
mkChannelLevels
  :: { inputBlack :: Number
     , inputWhite :: Number
     , gamma :: Number
     , outputBlack :: Number
     , outputWhite :: Number
     }
  -> ChannelLevels
mkChannelLevels cfg = ChannelLevels
  { inputBlack: ratio cfg.inputBlack
  , inputWhite: ratio cfg.inputWhite
  , gamma: levelsGamma cfg.gamma
  , outputBlack: ratio cfg.outputBlack
  , outputWhite: ratio cfg.outputWhite
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // channel // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get input black point.
inputBlack :: ChannelLevels -> Ratio
inputBlack (ChannelLevels c) = c.inputBlack

-- | Get input white point.
inputWhite :: ChannelLevels -> Ratio
inputWhite (ChannelLevels c) = c.inputWhite

-- | Get gamma value.
gamma :: ChannelLevels -> LevelsGamma
gamma (ChannelLevels c) = c.gamma

-- | Get output black point.
outputBlack :: ChannelLevels -> Ratio
outputBlack (ChannelLevels c) = c.outputBlack

-- | Get output white point.
outputWhite :: ChannelLevels -> Ratio
outputWhite (ChannelLevels c) = c.outputWhite

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // channel // setters
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set input black point (clamped 0.0-1.0).
setInputBlack :: Ratio -> ChannelLevels -> ChannelLevels
setInputBlack v (ChannelLevels c) = 
  ChannelLevels c { inputBlack = v }

-- | Set input white point (clamped 0.0-1.0).
setInputWhite :: Ratio -> ChannelLevels -> ChannelLevels
setInputWhite v (ChannelLevels c) = 
  ChannelLevels c { inputWhite = v }

-- | Set gamma (clamped 0.1-10.0).
setGamma :: LevelsGamma -> ChannelLevels -> ChannelLevels
setGamma v (ChannelLevels c) = 
  ChannelLevels c { gamma = v }

-- | Set output black point (clamped 0.0-1.0).
setOutputBlack :: Ratio -> ChannelLevels -> ChannelLevels
setOutputBlack v (ChannelLevels c) = 
  ChannelLevels c { outputBlack = v }

-- | Set output white point (clamped 0.0-1.0).
setOutputWhite :: Ratio -> ChannelLevels -> ChannelLevels
setOutputWhite v (ChannelLevels c) = 
  ChannelLevels c { outputWhite = v }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // levels // effect
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete Levels effect with per-channel control.
newtype LevelsEffect = LevelsEffect
  { master :: ChannelLevels   -- ^ Master (all channels)
  , red :: ChannelLevels      -- ^ Red channel only
  , green :: ChannelLevels    -- ^ Green channel only
  , blue :: ChannelLevels     -- ^ Blue channel only
  , alpha :: ChannelLevels    -- ^ Alpha channel only
  }

derive instance eqLevelsEffect :: Eq LevelsEffect

instance showLevelsEffect :: Show LevelsEffect where
  show (LevelsEffect _) = "LevelsEffect"

-- | Default levels effect (no adjustment).
defaultLevelsEffect :: LevelsEffect
defaultLevelsEffect = LevelsEffect
  { master: defaultChannelLevels
  , red: defaultChannelLevels
  , green: defaultChannelLevels
  , blue: defaultChannelLevels
  , alpha: defaultChannelLevels
  }

-- | Create levels effect with explicit channel settings.
mkLevelsEffect
  :: { master :: ChannelLevels
     , red :: ChannelLevels
     , green :: ChannelLevels
     , blue :: ChannelLevels
     , alpha :: ChannelLevels
     }
  -> LevelsEffect
mkLevelsEffect cfg = LevelsEffect cfg

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // effect // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get master channel levels.
masterLevels :: LevelsEffect -> ChannelLevels
masterLevels (LevelsEffect e) = e.master

-- | Get red channel levels.
redLevels :: LevelsEffect -> ChannelLevels
redLevels (LevelsEffect e) = e.red

-- | Get green channel levels.
greenLevels :: LevelsEffect -> ChannelLevels
greenLevels (LevelsEffect e) = e.green

-- | Get blue channel levels.
blueLevels :: LevelsEffect -> ChannelLevels
blueLevels (LevelsEffect e) = e.blue

-- | Get alpha channel levels.
alphaLevels :: LevelsEffect -> ChannelLevels
alphaLevels (LevelsEffect e) = e.alpha

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // effect // setters
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set master channel levels.
setMasterLevels :: ChannelLevels -> LevelsEffect -> LevelsEffect
setMasterLevels levels (LevelsEffect e) = LevelsEffect e { master = levels }

-- | Set red channel levels.
setRedLevels :: ChannelLevels -> LevelsEffect -> LevelsEffect
setRedLevels levels (LevelsEffect e) = LevelsEffect e { red = levels }

-- | Set green channel levels.
setGreenLevels :: ChannelLevels -> LevelsEffect -> LevelsEffect
setGreenLevels levels (LevelsEffect e) = LevelsEffect e { green = levels }

-- | Set blue channel levels.
setBlueLevels :: ChannelLevels -> LevelsEffect -> LevelsEffect
setBlueLevels levels (LevelsEffect e) = LevelsEffect e { blue = levels }

-- | Set alpha channel levels.
setAlphaLevels :: ChannelLevels -> LevelsEffect -> LevelsEffect
setAlphaLevels levels (LevelsEffect e) = LevelsEffect e { alpha = levels }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Auto-contrast preset (typical range compression).
levelsAutoContrast :: LevelsEffect
levelsAutoContrast = LevelsEffect
  { master: mkChannelLevels
      { inputBlack: 0.05
      , inputWhite: 0.95
      , gamma: 1.0
      , outputBlack: 0.0
      , outputWhite: 1.0
      }
  , red: defaultChannelLevels
  , green: defaultChannelLevels
  , blue: defaultChannelLevels
  , alpha: defaultChannelLevels
  }

-- | Invert preset (swap black and white).
levelsInvert :: LevelsEffect
levelsInvert = LevelsEffect
  { master: mkChannelLevels
      { inputBlack: 0.0
      , inputWhite: 1.0
      , gamma: 1.0
      , outputBlack: 1.0
      , outputWhite: 0.0
      }
  , red: defaultChannelLevels
  , green: defaultChannelLevels
  , blue: defaultChannelLevels
  , alpha: defaultChannelLevels
  }

-- | High contrast preset.
levelsHighContrast :: LevelsEffect
levelsHighContrast = LevelsEffect
  { master: mkChannelLevels
      { inputBlack: 0.15
      , inputWhite: 0.85
      , gamma: 1.0
      , outputBlack: 0.0
      , outputWhite: 1.0
      }
  , red: defaultChannelLevels
  , green: defaultChannelLevels
  , blue: defaultChannelLevels
  , alpha: defaultChannelLevels
  }

-- | Shadow boost preset (lift shadows).
levelsShadowBoost :: LevelsEffect
levelsShadowBoost = LevelsEffect
  { master: mkChannelLevels
      { inputBlack: 0.0
      , inputWhite: 1.0
      , gamma: 1.5
      , outputBlack: 0.0
      , outputWhite: 1.0
      }
  , red: defaultChannelLevels
  , green: defaultChannelLevels
  , blue: defaultChannelLevels
  , alpha: defaultChannelLevels
  }

-- | Highlight boost preset (compress highlights).
levelsHighlightBoost :: LevelsEffect
levelsHighlightBoost = LevelsEffect
  { master: mkChannelLevels
      { inputBlack: 0.0
      , inputWhite: 1.0
      , gamma: 0.7
      , outputBlack: 0.0
      , outputWhite: 1.0
      }
  , red: defaultChannelLevels
  , green: defaultChannelLevels
  , blue: defaultChannelLevels
  , alpha: defaultChannelLevels
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Is channel at default (neutral) settings?
isChannelNeutral :: ChannelLevels -> Boolean
isChannelNeutral (ChannelLevels c) =
  unwrapRatio c.inputBlack == 0.0 &&
  unwrapRatio c.inputWhite == 1.0 &&
  unwrapLevelsGamma c.gamma == 1.0 &&
  unwrapRatio c.outputBlack == 0.0 &&
  unwrapRatio c.outputWhite == 1.0

-- | Is entire effect neutral (no adjustment)?
isEffectNeutral :: LevelsEffect -> Boolean
isEffectNeutral (LevelsEffect e) =
  isChannelNeutral e.master &&
  isChannelNeutral e.red &&
  isChannelNeutral e.green &&
  isChannelNeutral e.blue &&
  isChannelNeutral e.alpha
