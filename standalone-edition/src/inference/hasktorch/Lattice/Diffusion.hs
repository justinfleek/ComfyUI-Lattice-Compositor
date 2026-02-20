-- | Lattice Diffusion Inference Library
-- HaskTorch implementation of RES4LYF samplers with Landauer precision
--
-- Core modules:
-- * Phi - φ functions for exponential integrators  
-- * RKCoefficients - Butcher tableaux for RK methods
-- * Schedulers - Sigma schedule generation
-- * Noise - Noise types for SDE sampling
-- * Precision.Landauer - Thermodynamic precision framework
-- * Workflows - Standard workflow presets for t2i, i2i, i2v, v2v
module Lattice.Diffusion
  ( -- * Re-exports
    module Lattice.Diffusion.Phi
  , module Lattice.Diffusion.RKCoefficients
  , module Lattice.Diffusion.Schedulers
  , module Lattice.Diffusion.Noise
  , module Lattice.Diffusion.Precision.Landauer
  , module Lattice.Diffusion.Workflows
  
    -- * High-level API
  , SamplerConfig(..)
  , defaultConfig
  , sample
  ) where

import Lattice.Diffusion.Phi
import Lattice.Diffusion.RKCoefficients
import Lattice.Diffusion.Schedulers
import Lattice.Diffusion.Noise
import Lattice.Diffusion.Precision.Landauer
import Lattice.Diffusion.Workflows

-- | Full sampler configuration
data SamplerConfig = SamplerConfig
  { scSampler     :: !String       -- Sampler name
  , scScheduler   :: !String       -- Scheduler name
  , scSteps       :: !Int          -- Number of steps
  , scCFGScale    :: !Double       -- Classifier-free guidance
  , scEta         :: !Double       -- SDE noise amount
  , scSNoise      :: !Double       -- Noise scaling
  , scPrecision   :: !Precision    -- Target precision
  , scSeed        :: !(Maybe Int)  -- RNG seed
  } deriving (Show, Eq)

-- | Sensible defaults for SDXL/Flux
defaultConfig :: SamplerConfig
defaultConfig = SamplerConfig
  { scSampler   = "res_2m"
  , scScheduler = "karras"
  , scSteps     = 20
  , scCFGScale  = 7.5
  , scEta       = 0.5
  , scSNoise    = 1.0
  , scPrecision = FP4   -- Landauer-optimal for latents
  , scSeed      = Nothing
  }

-- | Run sampling loop
-- This is the core denoising loop that iteratively applies the model
-- Full implementation requires HaskTorch tensors - this is the pure algorithmic structure
sample :: SamplerConfig -> a -> (a -> Double -> a) -> [Double] -> a
sample _cfg latent model sigmas = foldl' step latent sigmaPairs
  where
    sigmaPairs = zip sigmas (drop 1 sigmas)
    step x (sigma, sigmaNext) = model x ((sigma + sigmaNext) / 2)  -- Midpoint
