-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // schema // material // simplex-noise
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | SimplexNoise - improved gradient noise with better performance.
-- |
-- | Ken Perlin's improved noise algorithm (2001), addressing the
-- | computational complexity and visual artifacts of classic Perlin noise.
-- |
-- | ## Advantages over Perlin Noise
-- |
-- | - **O(n^2) vs O(2^n)**: Scales better to higher dimensions
-- | - **No axis-aligned artifacts**: Uses simplex grid instead of hypercube
-- | - **Better gradient distribution**: More isotropic appearance
-- | - **Lower computational cost**: Fewer multiplications per sample
-- |
-- | ## Composition
-- |
-- | A molecule composed from Material pillar atoms:
-- | - NoiseFrequency: spatial frequency (0.0 to finite)
-- | - NoiseAmplitude: output range (0.0 to 1.0)
-- | - NoiseSeed: deterministic seed (any Int)
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | -- Organic terrain noise
-- | terrain = simplexNoise
-- |   { frequency: noiseFrequency 0.5
-- |   , amplitude: noiseAmplitude 1.0
-- |   , seed: noiseSeed 12345
-- |   }
-- |
-- | -- High-frequency detail
-- | detail = simplexNoiseDetail (noiseSeed 42)
-- | ```
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Material.NoiseFrequency
-- | - Hydrogen.Schema.Material.NoiseAmplitude
-- | - Hydrogen.Schema.Material.NoiseSeed

module Hydrogen.Schema.Material.SimplexNoise
  ( -- * Types
    SimplexNoise(SimplexNoise)
  , SimplexNoiseConfig
  
  -- * Constructors
  , simplexNoise
  , simplexNoiseDefault
  , simplexNoiseDetail
  , simplexNoiseLarge
  
  -- * Accessors
  , frequency
  , amplitude
  , seed
  
  -- * Presets
  , terrainNoise
  , organicNoise
  , flowNoise
  , cellularBaseNoise
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  )

import Hydrogen.Schema.Material.NoiseFrequency (NoiseFrequency)
import Hydrogen.Schema.Material.NoiseFrequency (noiseFrequency, standard) as Freq
import Hydrogen.Schema.Material.NoiseAmplitude (NoiseAmplitude)
import Hydrogen.Schema.Material.NoiseAmplitude (noiseAmplitude, moderate, full) as Amp
import Hydrogen.Schema.Material.NoiseSeed (NoiseSeed)
import Hydrogen.Schema.Material.NoiseSeed (zero) as Seed

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // simplex-noise
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration record for creating SimplexNoise
type SimplexNoiseConfig =
  { frequency :: NoiseFrequency
  , amplitude :: NoiseAmplitude
  , seed :: NoiseSeed
  }

-- | SimplexNoise - improved gradient noise configuration molecule.
-- |
-- | Describes the parameters needed to generate Simplex noise.
-- | This is pure data — actual noise generation happens at the runtime boundary.
newtype SimplexNoise = SimplexNoise
  { frequency :: NoiseFrequency    -- ^ Spatial frequency (higher = finer detail)
  , amplitude :: NoiseAmplitude    -- ^ Output amplitude (0.0-1.0)
  , seed :: NoiseSeed              -- ^ Deterministic seed
  }

derive instance eqSimplexNoise :: Eq SimplexNoise

instance showSimplexNoise :: Show SimplexNoise where
  show (SimplexNoise s) = 
    "(SimplexNoise freq:" <> show s.frequency 
      <> " amp:" <> show s.amplitude 
      <> " " <> show s.seed
      <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create SimplexNoise from configuration
simplexNoise :: SimplexNoiseConfig -> SimplexNoise
simplexNoise cfg = SimplexNoise
  { frequency: cfg.frequency
  , amplitude: cfg.amplitude
  , seed: cfg.seed
  }

-- | Create SimplexNoise with default settings
-- |
-- | - Frequency: 1.0 (standard)
-- | - Amplitude: 0.5 (moderate)
-- | - Seed: 0
simplexNoiseDefault :: SimplexNoise
simplexNoiseDefault = SimplexNoise
  { frequency: Freq.standard
  , amplitude: Amp.moderate
  , seed: Seed.zero
  }

-- | Create high-frequency detail noise
-- |
-- | High frequency, low amplitude — adds fine detail to surfaces.
simplexNoiseDetail :: NoiseSeed -> SimplexNoise
simplexNoiseDetail s = SimplexNoise
  { frequency: Freq.noiseFrequency 8.0
  , amplitude: Amp.noiseAmplitude 0.2
  , seed: s
  }

-- | Create low-frequency large-scale noise
-- |
-- | Low frequency, high amplitude — creates large features.
simplexNoiseLarge :: NoiseSeed -> SimplexNoise
simplexNoiseLarge s = SimplexNoise
  { frequency: Freq.noiseFrequency 0.2
  , amplitude: Amp.full
  , seed: s
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the frequency
frequency :: SimplexNoise -> NoiseFrequency
frequency (SimplexNoise s) = s.frequency

-- | Get the amplitude
amplitude :: SimplexNoise -> NoiseAmplitude
amplitude (SimplexNoise s) = s.amplitude

-- | Get the seed
seed :: SimplexNoise -> NoiseSeed
seed (SimplexNoise s) = s.seed

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Terrain-like noise
-- |
-- | Low frequency, full amplitude — creates landscape-like undulations.
-- | Good base layer for heightmaps.
terrainNoise :: NoiseSeed -> SimplexNoise
terrainNoise s = SimplexNoise
  { frequency: Freq.noiseFrequency 0.3
  , amplitude: Amp.full
  , seed: s
  }

-- | Organic/biological noise
-- |
-- | Medium frequency, moderate amplitude — creates natural, organic patterns.
-- | Good for skin textures, cellular structures.
organicNoise :: NoiseSeed -> SimplexNoise
organicNoise s = SimplexNoise
  { frequency: Freq.noiseFrequency 1.5
  , amplitude: Amp.noiseAmplitude 0.6
  , seed: s
  }

-- | Flow/current noise
-- |
-- | Medium-high frequency — creates flowing, current-like patterns.
-- | Good for water, wind visualization.
flowNoise :: NoiseSeed -> SimplexNoise
flowNoise s = SimplexNoise
  { frequency: Freq.noiseFrequency 2.5
  , amplitude: Amp.noiseAmplitude 0.5
  , seed: s
  }

-- | Base noise for cellular effects
-- |
-- | High frequency, low amplitude — used as input to Worley noise
-- | for more organic cell boundaries.
cellularBaseNoise :: NoiseSeed -> SimplexNoise
cellularBaseNoise s = SimplexNoise
  { frequency: Freq.noiseFrequency 4.0
  , amplitude: Amp.noiseAmplitude 0.3
  , seed: s
  }
