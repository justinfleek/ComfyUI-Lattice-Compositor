-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // schema // material // fbm
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | FBM - Fractal Brownian Motion compound.
-- |
-- | FBM layers multiple octaves of noise at increasing frequencies and
-- | decreasing amplitudes. This creates natural-looking fractal textures
-- | with both large-scale features and fine detail.
-- |
-- | ## The Math
-- |
-- | ```
-- | fbm(x) = Σ (persistence^i) * noise(lacunarity^i * x)
-- |          i=0 to octaves-1
-- | ```
-- |
-- | Where:
-- | - **octaves**: Number of noise layers (1-16)
-- | - **lacunarity**: Frequency multiplier per octave (typically 2.0)
-- | - **persistence**: Amplitude multiplier per octave (typically 0.5)
-- |
-- | ## Composition
-- |
-- | A compound composed from Material pillar atoms and molecules:
-- | - NoiseFrequency: base frequency
-- | - NoiseAmplitude: base amplitude
-- | - NoiseOctaves: number of layers
-- | - NoiseLacunarity: frequency scaling
-- | - NoisePersistence: amplitude scaling
-- | - NoiseSeed: deterministic seed
-- | - NoiseType: which noise algorithm to use
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | -- Classic terrain FBM
-- | terrain = fbm
-- |   { baseFrequency: noiseFrequency 0.5
-- |   , baseAmplitude: noiseAmplitude 1.0
-- |   , octaves: noiseOctaves 6
-- |   , lacunarity: noiseLacunarity 2.0
-- |   , persistence: noisePersistence 0.5
-- |   , seed: noiseSeed 42
-- |   , noiseType: PerlinType
-- |   }
-- | ```
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Material.NoiseFrequency
-- | - Hydrogen.Schema.Material.NoiseAmplitude
-- | - Hydrogen.Schema.Material.NoiseOctaves
-- | - Hydrogen.Schema.Material.NoiseLacunarity
-- | - Hydrogen.Schema.Material.NoisePersistence
-- | - Hydrogen.Schema.Material.NoiseSeed

module Hydrogen.Schema.Material.FBM
  ( -- * Noise Type Selection
    NoiseType(..)
  
  -- * Types
  , FBM(FBM)
  , FBMConfig
  
  -- * Constructors
  , fbm
  , fbmDefault
  , fbmSimple
  
  -- * Accessors
  , baseFrequency
  , baseAmplitude
  , octaves
  , lacunarity
  , persistence
  , seed
  , noiseType
  
  -- * Presets
  , cloudsFBM
  , terrainFBM
  , turbulenceFBM
  , detailFBM
  , smoothFBM
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , compare
  , (<>)
  )

import Hydrogen.Schema.Material.NoiseFrequency (NoiseFrequency)
import Hydrogen.Schema.Material.NoiseFrequency (noiseFrequency, standard) as Freq
import Hydrogen.Schema.Material.NoiseAmplitude (NoiseAmplitude)
import Hydrogen.Schema.Material.NoiseAmplitude (noiseAmplitude, full) as Amp
import Hydrogen.Schema.Material.NoiseOctaves (NoiseOctaves)
import Hydrogen.Schema.Material.NoiseOctaves (noiseOctaves, standard) as Oct
import Hydrogen.Schema.Material.NoiseLacunarity (NoiseLacunarity)
import Hydrogen.Schema.Material.NoiseLacunarity (noiseLacunarity, standard) as Lac
import Hydrogen.Schema.Material.NoisePersistence (NoisePersistence)
import Hydrogen.Schema.Material.NoisePersistence (noisePersistence, standard) as Pers
import Hydrogen.Schema.Material.NoiseSeed (NoiseSeed)
import Hydrogen.Schema.Material.NoiseSeed (zero) as Seed

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // noise type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Base noise algorithm for FBM layering.
data NoiseType
  = PerlinType     -- ^ Classic Perlin gradient noise
  | SimplexType    -- ^ Improved simplex noise
  | WorleyType     -- ^ Cellular/Voronoi noise
  | ValueType      -- ^ Simple value noise (faster, blockier)

derive instance eqNoiseType :: Eq NoiseType
derive instance ordNoiseType :: Ord NoiseType

instance showNoiseType :: Show NoiseType where
  show PerlinType = "perlin"
  show SimplexType = "simplex"
  show WorleyType = "worley"
  show ValueType = "value"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                        // fbm
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration record for creating FBM
type FBMConfig =
  { baseFrequency :: NoiseFrequency
  , baseAmplitude :: NoiseAmplitude
  , octaves :: NoiseOctaves
  , lacunarity :: NoiseLacunarity
  , persistence :: NoisePersistence
  , seed :: NoiseSeed
  , noiseType :: NoiseType
  }

-- | FBM - Fractal Brownian Motion compound.
-- |
-- | Describes the parameters needed to generate layered fractal noise.
-- | This is pure data — actual noise generation happens at the runtime boundary.
newtype FBM = FBM
  { baseFrequency :: NoiseFrequency     -- ^ Starting frequency
  , baseAmplitude :: NoiseAmplitude     -- ^ Starting amplitude
  , octaves :: NoiseOctaves             -- ^ Number of layers (1-16)
  , lacunarity :: NoiseLacunarity       -- ^ Frequency multiplier per octave
  , persistence :: NoisePersistence     -- ^ Amplitude multiplier per octave
  , seed :: NoiseSeed                   -- ^ Deterministic seed
  , noiseType :: NoiseType              -- ^ Base noise algorithm
  , ridged :: Boolean                   -- ^ Use ridged/turbulent variant
  }

derive instance eqFBM :: Eq FBM

instance showFBM :: Show FBM where
  show (FBM f) = 
    "(FBM " <> show f.noiseType
      <> " freq:" <> show f.baseFrequency 
      <> " amp:" <> show f.baseAmplitude 
      <> " oct:" <> show f.octaves
      <> " lac:" <> show f.lacunarity
      <> " pers:" <> show f.persistence
      <> " " <> show f.seed
      <> (if f.ridged then " ridged" else "")
      <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create FBM from full configuration
fbm :: FBMConfig -> FBM
fbm cfg = FBM
  { baseFrequency: cfg.baseFrequency
  , baseAmplitude: cfg.baseAmplitude
  , octaves: cfg.octaves
  , lacunarity: cfg.lacunarity
  , persistence: cfg.persistence
  , seed: cfg.seed
  , noiseType: cfg.noiseType
  , ridged: false
  }

-- | Create FBM with default settings
-- |
-- | - Frequency: 1.0
-- | - Amplitude: 1.0
-- | - Octaves: 4
-- | - Lacunarity: 2.0
-- | - Persistence: 0.5
-- | - Noise: Perlin
fbmDefault :: FBM
fbmDefault = FBM
  { baseFrequency: Freq.standard
  , baseAmplitude: Amp.full
  , octaves: Oct.standard
  , lacunarity: Lac.standard
  , persistence: Pers.standard
  , seed: Seed.zero
  , noiseType: PerlinType
  , ridged: false
  }

-- | Create simple FBM with just octaves and seed
-- |
-- | Uses standard lacunarity and persistence.
fbmSimple :: NoiseOctaves -> NoiseSeed -> FBM
fbmSimple oct s = FBM
  { baseFrequency: Freq.standard
  , baseAmplitude: Amp.full
  , octaves: oct
  , lacunarity: Lac.standard
  , persistence: Pers.standard
  , seed: s
  , noiseType: SimplexType
  , ridged: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the base frequency
baseFrequency :: FBM -> NoiseFrequency
baseFrequency (FBM f) = f.baseFrequency

-- | Get the base amplitude
baseAmplitude :: FBM -> NoiseAmplitude
baseAmplitude (FBM f) = f.baseAmplitude

-- | Get the octave count
octaves :: FBM -> NoiseOctaves
octaves (FBM f) = f.octaves

-- | Get the lacunarity
lacunarity :: FBM -> NoiseLacunarity
lacunarity (FBM f) = f.lacunarity

-- | Get the persistence
persistence :: FBM -> NoisePersistence
persistence (FBM f) = f.persistence

-- | Get the seed
seed :: FBM -> NoiseSeed
seed (FBM f) = f.seed

-- | Get the noise type
noiseType :: FBM -> NoiseType
noiseType (FBM f) = f.noiseType

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Cloud-like FBM
-- |
-- | Low frequency, many octaves, high persistence.
-- | Creates soft, billowy cloud patterns.
cloudsFBM :: NoiseSeed -> FBM
cloudsFBM s = FBM
  { baseFrequency: Freq.noiseFrequency 0.3
  , baseAmplitude: Amp.full
  , octaves: Oct.noiseOctaves 6
  , lacunarity: Lac.noiseLacunarity 2.0
  , persistence: Pers.noisePersistence 0.6
  , seed: s
  , noiseType: SimplexType
  , ridged: false
  }

-- | Terrain/heightmap FBM
-- |
-- | Standard settings optimized for terrain generation.
terrainFBM :: NoiseSeed -> FBM
terrainFBM s = FBM
  { baseFrequency: Freq.noiseFrequency 0.5
  , baseAmplitude: Amp.full
  , octaves: Oct.noiseOctaves 8
  , lacunarity: Lac.noiseLacunarity 2.0
  , persistence: Pers.noisePersistence 0.5
  , seed: s
  , noiseType: SimplexType
  , ridged: false
  }

-- | Turbulence FBM
-- |
-- | Ridged noise with high lacunarity for dramatic terrain.
-- | Creates mountain ridges, sharp features.
turbulenceFBM :: NoiseSeed -> FBM
turbulenceFBM s = FBM
  { baseFrequency: Freq.noiseFrequency 0.8
  , baseAmplitude: Amp.full
  , octaves: Oct.noiseOctaves 6
  , lacunarity: Lac.noiseLacunarity 2.5
  , persistence: Pers.noisePersistence 0.45
  , seed: s
  , noiseType: PerlinType
  , ridged: true
  }

-- | High-detail FBM
-- |
-- | Many octaves for maximum detail. Computationally expensive.
detailFBM :: NoiseSeed -> FBM
detailFBM s = FBM
  { baseFrequency: Freq.noiseFrequency 1.0
  , baseAmplitude: Amp.full
  , octaves: Oct.noiseOctaves 12
  , lacunarity: Lac.noiseLacunarity 2.0
  , persistence: Pers.noisePersistence 0.5
  , seed: s
  , noiseType: SimplexType
  , ridged: false
  }

-- | Smooth FBM
-- |
-- | Few octaves, low lacunarity for gentle, smooth features.
smoothFBM :: NoiseSeed -> FBM
smoothFBM s = FBM
  { baseFrequency: Freq.noiseFrequency 0.4
  , baseAmplitude: Amp.full
  , octaves: Oct.noiseOctaves 3
  , lacunarity: Lac.noiseLacunarity 1.8
  , persistence: Pers.noisePersistence 0.6
  , seed: s
  , noiseType: SimplexType
  , ridged: false
  }
