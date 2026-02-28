-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // schema // material // noise-octaves
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | NoiseOctaves - number of fractal layers in FBM (Fractional Brownian Motion).
-- |
-- | Range: 1 to 16 (clamps)
-- | - **1**: Single noise layer (smooth, low detail)
-- | - **4**: Standard detail (good balance)
-- | - **8**: High detail
-- | - **16**: Maximum detail (computationally expensive)
-- |
-- | Each octave adds a layer of noise at increasing frequency and decreasing
-- | amplitude. More octaves = more fine detail, but slower computation.

module Hydrogen.Schema.Material.NoiseOctaves
  ( NoiseOctaves
  , noiseOctaves
  , unwrap
  , toInt
  , bounds
  , single
  , standard
  , detailed
  , veryDetailed
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  )

import Data.Int (toNumber) as Int
import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // noise-octaves
-- ═════════════════════════════════════════════════════════════════════════════

-- | Noise octaves (1 to 16)
-- |
-- | Number of fractal layers combined in FBM. Each octave doubles frequency
-- | and reduces amplitude by persistence factor.
newtype NoiseOctaves = NoiseOctaves Int

derive instance eqNoiseOctaves :: Eq NoiseOctaves
derive instance ordNoiseOctaves :: Ord NoiseOctaves

instance showNoiseOctaves :: Show NoiseOctaves where
  show (NoiseOctaves o) = show o <> " octaves"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create noise octaves, clamping to 1-16
noiseOctaves :: Int -> NoiseOctaves
noiseOctaves n = NoiseOctaves (Bounded.clampInt 1 16 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Single octave (smooth)
single :: NoiseOctaves
single = NoiseOctaves 1

-- | Standard detail (4 octaves)
standard :: NoiseOctaves
standard = NoiseOctaves 4

-- | Detailed (8 octaves)
detailed :: NoiseOctaves
detailed = NoiseOctaves 8

-- | Very detailed (12 octaves)
veryDetailed :: NoiseOctaves
veryDetailed = NoiseOctaves 12

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Int value
unwrap :: NoiseOctaves -> Int
unwrap (NoiseOctaves o) = o

-- | Convert to Int (passthrough for this type)
toInt :: NoiseOctaves -> Int
toInt (NoiseOctaves o) = o

-- | Convert to Number for calculations
toNumber :: NoiseOctaves -> Number
toNumber (NoiseOctaves o) = Int.toNumber o

-- | Bounds documentation for this type
bounds :: Bounded.IntBounds
bounds = Bounded.intBounds 1 16 "noiseOctaves" "Fractal octave count for FBM"
