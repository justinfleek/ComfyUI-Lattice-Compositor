-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // schema // material // noise-amplitude
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | NoiseAmplitude - output range/height of procedural noise.
-- |
-- | Range: 0.0 to 1.0 (clamps)
-- | - **0.0**: No variation (flat)
-- | - **0.5**: Half amplitude
-- | - **1.0**: Full amplitude
-- |
-- | Controls the intensity of noise output. In FBM (Fractional Brownian Motion),
-- | amplitude decreases by persistence factor at each octave.

module Hydrogen.Schema.Material.NoiseAmplitude
  ( NoiseAmplitude
  , noiseAmplitude
  , unwrap
  , toNumber
  , bounds
  , none
  , subtle
  , moderate
  , full
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
--                                                            // noise-amplitude
-- ═════════════════════════════════════════════════════════════════════════════

-- | Noise amplitude (0.0 to 1.0)
-- |
-- | Vertical scaling of noise output. Controls how much the noise varies.
newtype NoiseAmplitude = NoiseAmplitude Number

derive instance eqNoiseAmplitude :: Eq NoiseAmplitude
derive instance ordNoiseAmplitude :: Ord NoiseAmplitude

instance showNoiseAmplitude :: Show NoiseAmplitude where
  show (NoiseAmplitude a) = "NoiseAmplitude " <> show a

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a noise amplitude, clamping to 0.0-1.0
noiseAmplitude :: Number -> NoiseAmplitude
noiseAmplitude n = NoiseAmplitude (Bounded.clampNumber 0.0 1.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | No amplitude (flat)
none :: NoiseAmplitude
none = NoiseAmplitude 0.0

-- | Subtle variation (0.25)
subtle :: NoiseAmplitude
subtle = NoiseAmplitude 0.25

-- | Moderate variation (0.5)
moderate :: NoiseAmplitude
moderate = NoiseAmplitude 0.5

-- | Full amplitude
full :: NoiseAmplitude
full = NoiseAmplitude 1.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Number value
unwrap :: NoiseAmplitude -> Number
unwrap (NoiseAmplitude a) = a

-- | Convert to Number (passthrough for this type)
toNumber :: NoiseAmplitude -> Number
toNumber (NoiseAmplitude a) = a

-- | Bounds documentation for this type
bounds :: Bounded.NumberBounds
bounds = Bounded.numberBounds 0.0 1.0 "noiseAmplitude" "Noise output amplitude/height"
