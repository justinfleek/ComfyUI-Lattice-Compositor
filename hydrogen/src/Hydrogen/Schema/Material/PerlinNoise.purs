-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // schema // material // perlin-noise
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | PerlinNoise - classic gradient noise configuration.
-- |
-- | Ken Perlin's gradient noise algorithm (1983/2002), the foundation of
-- | procedural texture generation. Produces smooth, natural-looking random
-- | patterns without the harsh edges of value noise.
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
-- | -- Subtle texture noise
-- | subtle = perlinNoise
-- |   { frequency: NoiseFrequency.standard
-- |   , amplitude: NoiseAmplitude.subtle
-- |   , seed: NoiseSeed.zero
-- |   }
-- |
-- | -- Turbulent cloud-like noise
-- | turbulent = perlinNoiseTurbulent
-- |   { frequency: noiseFrequency 2.0
-- |   , amplitude: noiseAmplitude 0.8
-- |   , seed: noiseSeed 42
-- |   }
-- | ```
-- |
-- | ## Performance
-- |
-- | Perlin noise is O(2^n) where n is dimensions. 2D is fast, 3D is moderate.
-- | For better performance with similar quality, consider SimplexNoise.
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Material.NoiseFrequency
-- | - Hydrogen.Schema.Material.NoiseAmplitude
-- | - Hydrogen.Schema.Material.NoiseSeed

module Hydrogen.Schema.Material.PerlinNoise
  ( -- * Types
    PerlinNoise(PerlinNoise)
  , PerlinNoiseConfig
  
  -- * Constructors
  , perlinNoise
  , perlinNoiseDefault
  , perlinNoiseTurbulent
  , perlinNoiseSubtle
  
  -- * Accessors
  , frequency
  , amplitude
  , seed
  
  -- * Presets
  , cloudNoise
  , marbleNoise
  , woodNoise
  , fabricNoise
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
import Hydrogen.Schema.Material.NoiseAmplitude (noiseAmplitude, moderate) as Amp
import Hydrogen.Schema.Material.NoiseSeed (NoiseSeed)
import Hydrogen.Schema.Material.NoiseSeed (noiseSeed, zero) as Seed

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // perlin-noise
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration record for creating PerlinNoise
type PerlinNoiseConfig =
  { frequency :: NoiseFrequency
  , amplitude :: NoiseAmplitude
  , seed :: NoiseSeed
  }

-- | PerlinNoise - gradient noise configuration molecule.
-- |
-- | Describes the parameters needed to generate Perlin noise.
-- | This is pure data — actual noise generation happens at the runtime boundary.
newtype PerlinNoise = PerlinNoise
  { frequency :: NoiseFrequency    -- ^ Spatial frequency (higher = finer detail)
  , amplitude :: NoiseAmplitude    -- ^ Output amplitude (0.0-1.0)
  , seed :: NoiseSeed              -- ^ Deterministic seed
  , turbulent :: Boolean           -- ^ Use absolute value for turbulent look
  }

derive instance eqPerlinNoise :: Eq PerlinNoise

instance showPerlinNoise :: Show PerlinNoise where
  show (PerlinNoise p) = 
    "(PerlinNoise freq:" <> show p.frequency 
      <> " amp:" <> show p.amplitude 
      <> " " <> show p.seed
      <> (if p.turbulent then " turbulent" else "")
      <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create PerlinNoise from configuration
perlinNoise :: PerlinNoiseConfig -> PerlinNoise
perlinNoise cfg = PerlinNoise
  { frequency: cfg.frequency
  , amplitude: cfg.amplitude
  , seed: cfg.seed
  , turbulent: false
  }

-- | Create PerlinNoise with default settings
-- |
-- | - Frequency: 1.0 (standard)
-- | - Amplitude: 0.5 (standard)
-- | - Seed: 0
-- | - Turbulent: false
perlinNoiseDefault :: PerlinNoise
perlinNoiseDefault = PerlinNoise
  { frequency: Freq.standard
  , amplitude: Amp.moderate
  , seed: Seed.zero
  , turbulent: false
  }

-- | Create turbulent PerlinNoise
-- |
-- | Turbulent noise uses absolute values, creating sharper edges
-- | and more dramatic contrast. Good for fire, smoke, marble veins.
perlinNoiseTurbulent :: PerlinNoiseConfig -> PerlinNoise
perlinNoiseTurbulent cfg = PerlinNoise
  { frequency: cfg.frequency
  , amplitude: cfg.amplitude
  , seed: cfg.seed
  , turbulent: true
  }

-- | Create subtle PerlinNoise for texture overlays
-- |
-- | Low amplitude noise suitable for adding texture without
-- | overwhelming the base design.
perlinNoiseSubtle :: NoiseSeed -> PerlinNoise
perlinNoiseSubtle s = PerlinNoise
  { frequency: Freq.noiseFrequency 2.0
  , amplitude: Amp.noiseAmplitude 0.1
  , seed: s
  , turbulent: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the frequency
frequency :: PerlinNoise -> NoiseFrequency
frequency (PerlinNoise p) = p.frequency

-- | Get the amplitude
amplitude :: PerlinNoise -> NoiseAmplitude
amplitude (PerlinNoise p) = p.amplitude

-- | Get the seed
seed :: PerlinNoise -> NoiseSeed
seed (PerlinNoise p) = p.seed

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Cloud-like noise
-- |
-- | Low frequency, high amplitude, non-turbulent.
-- | Creates soft, billowy patterns.
cloudNoise :: NoiseSeed -> PerlinNoise
cloudNoise s = PerlinNoise
  { frequency: Freq.noiseFrequency 0.5
  , amplitude: Amp.noiseAmplitude 0.8
  , seed: s
  , turbulent: false
  }

-- | Marble-like noise
-- |
-- | Turbulent noise with medium frequency.
-- | Creates vein-like patterns when combined with sin waves.
marbleNoise :: NoiseSeed -> PerlinNoise
marbleNoise s = PerlinNoise
  { frequency: Freq.noiseFrequency 1.5
  , amplitude: Amp.noiseAmplitude 0.6
  , seed: s
  , turbulent: true
  }

-- | Wood grain noise
-- |
-- | Low frequency turbulent noise.
-- | Creates ring-like patterns when used with polar coordinates.
woodNoise :: NoiseSeed -> PerlinNoise
woodNoise s = PerlinNoise
  { frequency: Freq.noiseFrequency 0.3
  , amplitude: Amp.noiseAmplitude 0.7
  , seed: s
  , turbulent: true
  }

-- | Fabric/textile noise
-- |
-- | High frequency, low amplitude.
-- | Creates subtle woven texture appearance.
fabricNoise :: NoiseSeed -> PerlinNoise
fabricNoise s = PerlinNoise
  { frequency: Freq.noiseFrequency 8.0
  , amplitude: Amp.noiseAmplitude 0.15
  , seed: s
  , turbulent: false
  }
