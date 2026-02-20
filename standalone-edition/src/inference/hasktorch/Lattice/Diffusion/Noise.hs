-- | Noise generation for diffusion sampling
-- Ported from RES4LYF noise_classes.py
module Lattice.Diffusion.Noise where

import System.Random

-- | Noise type
data NoiseType
  = Gaussian      -- Standard normal
  | Uniform       -- Uniform [-1, 1]
  | Brownian      -- Correlated (fractal)
  | Pyramid       -- Multi-scale
  | Pink          -- 1/f noise
  | Blue          -- High-frequency emphasis
  deriving (Show, Eq, Ord, Enum, Bounded)

-- | Noise mode for SDE samplers
data NoiseMode
  = Hard          -- Full noise, aggressive
  | Soft          -- Soft falloff
  | Softer        -- More gentle falloff
  | Sinusoidal    -- Affects middle steps
  deriving (Show, Eq, Ord, Enum, Bounded)

-- | SDE noise parameters
data SDENoiseConfig = SDENoiseConfig
  { sncType    :: !NoiseType
  , sncMode    :: !NoiseMode
  , sncEta     :: !Double      -- Noise multiplier
  , sncSeed    :: !(Maybe Int)
  } deriving (Show, Eq)

-- | Default SDE noise config
defaultSDENoise :: SDENoiseConfig
defaultSDENoise = SDENoiseConfig
  { sncType = Gaussian
  , sncMode = Hard
  , sncEta  = 0.5
  , sncSeed = Nothing
  }

-- | Noise scaling based on mode
-- Determines how noise amount varies with sigma
noiseScale :: NoiseMode -> Double -> Double -> Double -> Double
noiseScale mode eta sigma sigmaMax = case mode of
  Hard       -> eta
  Soft       -> eta * (sigma / sigmaMax)
  Softer     -> eta * (sigma / sigmaMax) ** 2
  Sinusoidal -> eta * sin (pi * sigma / sigmaMax)

-- | Ancestral noise computation (for SDE samplers)
-- sigma_up² + sigma_down² = sigma_next²
-- sigma_down = sigma_next * sqrt(1 - eta²)  
-- sigma_up = sigma_next * eta
ancestralNoise :: Double -> Double -> Double -> (Double, Double)
ancestralNoise sigmaNext eta sNoise =
  let sigmaUp   = min (sigmaNext * eta) (sigmaNext * sNoise)
      sigmaDown = sqrt (sigmaNext^2 - sigmaUp^2)
  in (sigmaUp, sigmaDown)

-- | Variance floor for SDE sampling
-- Prevents too-small steps: σ_next ≥ (-1 + √(1 + 4σ)) / 2
varianceFloor :: Double -> Double
varianceFloor sigma = (-1 + sqrt (1 + 4 * sigma)) / 2

-- | Brownian tree noise (correlated across scales)
data BrownianTree = BrownianTree
  { btSeed   :: !Int
  , btDepth  :: !Int
  , btSigmas :: ![Double]
  } deriving (Show, Eq)

-- | Initialize Brownian tree for consistent noise
mkBrownianTree :: Int -> [Double] -> BrownianTree
mkBrownianTree seed sigmas = BrownianTree
  { btSeed   = seed
  , btDepth  = ceiling (logBase 2 (fromIntegral $ length sigmas))
  , btSigmas = sigmas
  }
