-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // schema // material // worley-noise
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | WorleyNoise - cellular/Voronoi noise configuration.
-- |
-- | Steven Worley's cellular noise algorithm (1996), based on distance
-- | to randomly distributed feature points. Creates organic, cell-like
-- | patterns found in nature: stone, scales, cells, bubbles.
-- |
-- | ## Distance Functions
-- |
-- | The noise value at each point is determined by distance to nearby
-- | feature points. Different distance metrics create different looks:
-- |
-- | - **F1**: Distance to nearest point (cell interiors)
-- | - **F2**: Distance to second-nearest point (cell boundaries)
-- | - **F2-F1**: Difference creates sharp cell edges
-- | - **F1+F2**: Sum creates softer, blob-like cells
-- |
-- | ## Composition
-- |
-- | A molecule composed from Material pillar atoms:
-- | - NoiseFrequency: cell density (0.0 to finite)
-- | - NoiseAmplitude: output range (0.0 to 1.0)
-- | - NoiseSeed: deterministic seed (any Int)
-- | - DistanceType: F1, F2, F2MinusF1, F1PlusF2
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | -- Cell interior pattern
-- | cells = worleyNoise
-- |   { frequency: noiseFrequency 3.0
-- |   , amplitude: noiseAmplitude 1.0
-- |   , seed: noiseSeed 42
-- |   , distanceType: F1
-- |   }
-- |
-- | -- Sharp cell edges
-- | edges = worleyNoiseEdges (noiseSeed 42)
-- | ```
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Material.NoiseFrequency
-- | - Hydrogen.Schema.Material.NoiseAmplitude
-- | - Hydrogen.Schema.Material.NoiseSeed

module Hydrogen.Schema.Material.WorleyNoise
  ( -- * Distance Types
    DistanceType(..)
  
  -- * Types
  , WorleyNoise(WorleyNoise)
  , WorleyNoiseConfig
  
  -- * Constructors
  , worleyNoise
  , worleyNoiseDefault
  , worleyNoiseEdges
  , worleyNoiseCells
  
  -- * Accessors
  , frequency
  , amplitude
  , seed
  , distanceType
  
  -- * Presets
  , stoneNoise
  , scalesNoise
  , bubblesNoise
  , crackledNoise
  , voronoiNoise
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
import Hydrogen.Schema.Material.NoiseAmplitude (noiseAmplitude, moderate, full) as Amp
import Hydrogen.Schema.Material.NoiseSeed (NoiseSeed)
import Hydrogen.Schema.Material.NoiseSeed (zero) as Seed

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // distance types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Distance function type for Worley noise.
-- |
-- | Determines how the noise value is calculated from feature point distances.
data DistanceType
  = F1           -- ^ Distance to nearest point (cell interiors)
  | F2           -- ^ Distance to second-nearest (outer regions)
  | F2MinusF1    -- ^ Difference creates sharp cell boundaries
  | F1PlusF2     -- ^ Sum creates softer, blob-like cells
  | F3           -- ^ Distance to third-nearest (complex patterns)

derive instance eqDistanceType :: Eq DistanceType
derive instance ordDistanceType :: Ord DistanceType

instance showDistanceType :: Show DistanceType where
  show F1 = "F1"
  show F2 = "F2"
  show F2MinusF1 = "F2-F1"
  show F1PlusF2 = "F1+F2"
  show F3 = "F3"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // worley-noise
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration record for creating WorleyNoise
type WorleyNoiseConfig =
  { frequency :: NoiseFrequency
  , amplitude :: NoiseAmplitude
  , seed :: NoiseSeed
  , distanceType :: DistanceType
  }

-- | WorleyNoise - cellular noise configuration molecule.
-- |
-- | Describes the parameters needed to generate Worley/Voronoi noise.
-- | This is pure data — actual noise generation happens at the runtime boundary.
newtype WorleyNoise = WorleyNoise
  { frequency :: NoiseFrequency    -- ^ Cell density (higher = smaller cells)
  , amplitude :: NoiseAmplitude    -- ^ Output amplitude (0.0-1.0)
  , seed :: NoiseSeed              -- ^ Deterministic seed
  , distanceType :: DistanceType   -- ^ Distance function
  , invert :: Boolean              -- ^ Invert output (dark cells vs light cells)
  }

derive instance eqWorleyNoise :: Eq WorleyNoise

instance showWorleyNoise :: Show WorleyNoise where
  show (WorleyNoise w) = 
    "(WorleyNoise freq:" <> show w.frequency 
      <> " amp:" <> show w.amplitude 
      <> " " <> show w.seed
      <> " type:" <> show w.distanceType
      <> (if w.invert then " inverted" else "")
      <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create WorleyNoise from configuration
worleyNoise :: WorleyNoiseConfig -> WorleyNoise
worleyNoise cfg = WorleyNoise
  { frequency: cfg.frequency
  , amplitude: cfg.amplitude
  , seed: cfg.seed
  , distanceType: cfg.distanceType
  , invert: false
  }

-- | Create WorleyNoise with default settings
-- |
-- | - Frequency: 1.0 (standard)
-- | - Amplitude: 0.5 (moderate)
-- | - Seed: 0
-- | - Distance: F1 (cell interiors)
worleyNoiseDefault :: WorleyNoise
worleyNoiseDefault = WorleyNoise
  { frequency: Freq.standard
  , amplitude: Amp.moderate
  , seed: Seed.zero
  , distanceType: F1
  , invert: false
  }

-- | Create Worley noise optimized for cell edges
-- |
-- | Uses F2-F1 distance for sharp cell boundaries.
worleyNoiseEdges :: NoiseSeed -> WorleyNoise
worleyNoiseEdges s = WorleyNoise
  { frequency: Freq.noiseFrequency 3.0
  , amplitude: Amp.full
  , seed: s
  , distanceType: F2MinusF1
  , invert: false
  }

-- | Create Worley noise optimized for cell interiors
-- |
-- | Uses inverted F1 distance for bright cell centers.
worleyNoiseCells :: NoiseSeed -> WorleyNoise
worleyNoiseCells s = WorleyNoise
  { frequency: Freq.noiseFrequency 3.0
  , amplitude: Amp.full
  , seed: s
  , distanceType: F1
  , invert: true
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the frequency
frequency :: WorleyNoise -> NoiseFrequency
frequency (WorleyNoise w) = w.frequency

-- | Get the amplitude
amplitude :: WorleyNoise -> NoiseAmplitude
amplitude (WorleyNoise w) = w.amplitude

-- | Get the seed
seed :: WorleyNoise -> NoiseSeed
seed (WorleyNoise w) = w.seed

-- | Get the distance type
distanceType :: WorleyNoise -> DistanceType
distanceType (WorleyNoise w) = w.distanceType

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Stone/cobblestone texture
-- |
-- | Medium cells with F1 distance — creates rounded stone appearance.
stoneNoise :: NoiseSeed -> WorleyNoise
stoneNoise s = WorleyNoise
  { frequency: Freq.noiseFrequency 2.0
  , amplitude: Amp.noiseAmplitude 0.8
  , seed: s
  , distanceType: F1
  , invert: false
  }

-- | Reptile scales texture
-- |
-- | Dense cells with F2-F1 — creates scale-like pattern.
scalesNoise :: NoiseSeed -> WorleyNoise
scalesNoise s = WorleyNoise
  { frequency: Freq.noiseFrequency 5.0
  , amplitude: Amp.full
  , seed: s
  , distanceType: F2MinusF1
  , invert: false
  }

-- | Bubbles/foam texture
-- |
-- | Inverted F1 with medium density — creates bubble-like appearance.
bubblesNoise :: NoiseSeed -> WorleyNoise
bubblesNoise s = WorleyNoise
  { frequency: Freq.noiseFrequency 4.0
  , amplitude: Amp.noiseAmplitude 0.9
  , seed: s
  , distanceType: F1
  , invert: true
  }

-- | Crackled/dried mud texture
-- |
-- | F2-F1 with high amplitude — creates crack network pattern.
crackledNoise :: NoiseSeed -> WorleyNoise
crackledNoise s = WorleyNoise
  { frequency: Freq.noiseFrequency 3.5
  , amplitude: Amp.full
  , seed: s
  , distanceType: F2MinusF1
  , invert: true
  }

-- | Pure Voronoi diagram
-- |
-- | Standard F1 distance — clean cell interiors.
-- | Good for stylized, geometric patterns.
voronoiNoise :: NoiseSeed -> WorleyNoise
voronoiNoise s = WorleyNoise
  { frequency: Freq.noiseFrequency 3.0
  , amplitude: Amp.full
  , seed: s
  , distanceType: F1
  , invert: false
  }
