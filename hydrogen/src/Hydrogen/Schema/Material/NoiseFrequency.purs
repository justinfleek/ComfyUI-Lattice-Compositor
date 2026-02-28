-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // schema // material // noise-frequency
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | NoiseFrequency - spatial frequency for procedural noise.
-- |
-- | Range: 0.0 to finite (clamps at 0, no upper bound but must remain finite)
-- | - **0.0**: No variation (uniform)
-- | - **0.1**: Very low frequency (large features)
-- | - **1.0**: Standard frequency
-- | - **10.0+**: High frequency (fine detail)
-- |
-- | Higher frequencies produce smaller, more detailed noise patterns.

module Hydrogen.Schema.Material.NoiseFrequency
  ( NoiseFrequency
  , noiseFrequency
  , unwrap
  , toNumber
  , bounds
  , uniform
  , low
  , standard
  , high
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
--                                                            // noise-frequency
-- ═════════════════════════════════════════════════════════════════════════════

-- | Noise frequency (0.0 to finite)
-- |
-- | Controls the spatial frequency of procedural noise generation.
-- | Higher values produce finer detail.
newtype NoiseFrequency = NoiseFrequency Number

derive instance eqNoiseFrequency :: Eq NoiseFrequency
derive instance ordNoiseFrequency :: Ord NoiseFrequency

instance showNoiseFrequency :: Show NoiseFrequency where
  show (NoiseFrequency f) = show f <> "Hz"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a noise frequency, clamping to 0.0 minimum and ensuring finite
noiseFrequency :: Number -> NoiseFrequency
noiseFrequency n = NoiseFrequency (Bounded.clampNumberMin 0.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Uniform (no noise)
uniform :: NoiseFrequency
uniform = NoiseFrequency 0.0

-- | Low frequency (large features)
low :: NoiseFrequency
low = NoiseFrequency 0.1

-- | Standard frequency
standard :: NoiseFrequency
standard = NoiseFrequency 1.0

-- | High frequency (fine detail)
high :: NoiseFrequency
high = NoiseFrequency 10.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Number value
unwrap :: NoiseFrequency -> Number
unwrap (NoiseFrequency f) = f

-- | Convert to Number (passthrough for this type)
toNumber :: NoiseFrequency -> Number
toNumber (NoiseFrequency f) = f

-- | Bounds documentation for this type
bounds :: Bounded.NumberBounds
bounds = Bounded.numberBounds 0.0 100.0 "noiseFrequency" "Spatial frequency for procedural noise"
