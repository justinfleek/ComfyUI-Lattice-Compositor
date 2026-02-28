-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // schema // material // noise-persistence
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | NoisePersistence - amplitude decay factor between octaves in FBM.
-- |
-- | Range: 0.0 to 1.0 (clamps)
-- | - **0.0**: Higher octaves have no contribution (single octave)
-- | - **0.5**: Each octave has half the amplitude (standard, smooth)
-- | - **0.7**: Octaves contribute more (rougher, more chaotic)
-- | - **1.0**: All octaves equal amplitude (very rough)
-- |
-- | Controls how much each octave contributes to the final noise.
-- | Lower persistence = smoother result. Higher persistence = rougher result.
-- | Standard value is 0.5 (also called H = 1.0 in some papers).

module Hydrogen.Schema.Material.NoisePersistence
  ( NoisePersistence
  , noisePersistence
  , unwrap
  , toNumber
  , bounds
  , smooth
  , standard
  , rough
  , veryRough
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  )

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // noise-persistence
-- ═════════════════════════════════════════════════════════════════════════════

-- | Noise persistence (0.0 to 1.0)
-- |
-- | Amplitude multiplier between FBM octaves. Controls roughness.
newtype NoisePersistence = NoisePersistence Number

derive instance eqNoisePersistence :: Eq NoisePersistence
derive instance ordNoisePersistence :: Ord NoisePersistence

instance showNoisePersistence :: Show NoisePersistence where
  show (NoisePersistence p) = "NoisePersistence " <> show p

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a noise persistence, clamping to 0.0-1.0
noisePersistence :: Number -> NoisePersistence
noisePersistence n = NoisePersistence (Bounded.clampNumber 0.0 1.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Smooth (0.3 - low contribution from higher octaves)
smooth :: NoisePersistence
smooth = NoisePersistence 0.3

-- | Standard (0.5 - balanced)
standard :: NoisePersistence
standard = NoisePersistence 0.5

-- | Rough (0.7 - higher octaves contribute more)
rough :: NoisePersistence
rough = NoisePersistence 0.7

-- | Very rough (0.9 - nearly equal octave contribution)
veryRough :: NoisePersistence
veryRough = NoisePersistence 0.9

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Number value
unwrap :: NoisePersistence -> Number
unwrap (NoisePersistence p) = p

-- | Convert to Number (passthrough for this type)
toNumber :: NoisePersistence -> Number
toNumber (NoisePersistence p) = p

-- | Bounds documentation for this type
bounds :: Bounded.NumberBounds
bounds = Bounded.numberBounds 0.0 1.0 "noisePersistence" "FBM amplitude decay per octave"
