-- | Landauer Precision Framework
-- Precision is MEASURED not optimized
-- Based on thermodynamic principles from the Landauer paper
module Lattice.Diffusion.Precision.Landauer where

-- | Boltzmann constant * temperature (at room temp ~300K)
kT :: Double
kT = 1.38e-23 * 300  -- J

-- | Landauer minimum energy cost per bit erased
landauerBit :: Double
landauerBit = kT * log 2  -- ~2.87e-21 J at room temp

-- | Precision level (bits)
data Precision = FP4 | FP8 | FP16 | BF16 | FP32 | FP64
  deriving (Show, Eq, Ord, Enum, Bounded)

precisionBits :: Precision -> Int
precisionBits FP4  = 4
precisionBits FP8  = 8
precisionBits FP16 = 16
precisionBits BF16 = 16
precisionBits FP32 = 32
precisionBits FP64 = 64

-- | Landauer cost of precision transition
-- Cost is zero when H_source <= b_target (codebook injective)
landauerCost :: Double -> Int -> Double
landauerCost hSource bTarget
  | hSource <= fromIntegral bTarget = 0  -- Free boundary!
  | otherwise = landauerBit * (hSource - fromIntegral bTarget)

-- | Natural precision - minimum bits needed for distortion tolerance
-- b*_v(ε) = min { b ∈ ℕ : E[D(φ_v(x), φ_v(Q_b(x)))] ≤ ε }
data NaturalPrecision = NaturalPrecision
  { npBits       :: !Int
  , npEntropy    :: !Double   -- Measured entropy
  , npDistortion :: !Double   -- Task distortion at this precision
  } deriving (Show, Eq)

-- | Precision domain in computation graph
data PrecisionDomain = PrecisionDomain
  { pdName      :: !String
  , pdPrecision :: !Precision
  , pdEntropy   :: !Double    -- Max entropy in domain
  } deriving (Show, Eq)

-- | Boundary between precision domains
data PrecisionBoundary = PrecisionBoundary
  { pbSource :: !PrecisionDomain
  , pbTarget :: !PrecisionDomain
  , pbCost   :: !Double       -- Landauer cost (0 if free)
  , pbFusible :: !Bool        -- Can fuse into epilogue?
  } deriving (Show, Eq)

-- | Check if boundary is free (no information loss)
isFree :: PrecisionBoundary -> Bool
isFree pb = pbCost pb == 0

-- | Entropy of latent space (VAE already compressed)
-- For latent diffusion: ~3-4 bits per element
latentEntropy :: Double
latentEntropy = 4.0  -- bits

-- | Entropy of pixel space
pixelEntropy :: Double
pixelEntropy = 24.0  -- 8 bits * 3 channels

-- | VAE-DiT-VAE precision landscape
-- H(x) >> H(z) ≈ H(z') >> H(x̂)
data LatentDiffusionPrecision = LatentDiffusionPrecision
  { ldpVAEEncoder    :: !Precision  -- High (16-bit)
  , ldpLatent        :: !Precision  -- Low (4-bit)
  , ldpDiT           :: !Precision  -- Low (4-bit) 
  , ldpVAEDecoder    :: !Precision  -- High (16-bit)
  } deriving (Show, Eq)

-- | Optimal precision for latent diffusion (Landauer-derived)
optimalLatentDiffusion :: LatentDiffusionPrecision
optimalLatentDiffusion = LatentDiffusionPrecision
  { ldpVAEEncoder = FP16
  , ldpLatent     = FP4   -- VAE already paid Landauer cost!
  , ldpDiT        = FP4   -- Operating in compressed space
  , ldpVAEDecoder = FP16
  }

-- | Gauge transformation (bijective, preserves information)
-- These are FREE in Landauer sense
data GaugeTransform
  = PerChannelScale ![Double]       -- Per-channel affine rescale
  | CodeRemap (Int -> Int)          -- Injective code remap
  | QuantizeDequant Precision       -- When b >= entropy

-- | Epilogue = last reversible place to change gauges
-- Fuse: scale -> bias -> activation -> quantize (ONCE)
data Epilogue = Epilogue
  { epScale      :: !(Maybe [Double])
  , epBias       :: !(Maybe [Double])
  , epActivation :: !(Maybe Activation)
  , epQuantize   :: !Precision
  } deriving (Show, Eq)

data Activation = ReLU | SiLU | GELU | Tanh
  deriving (Show, Eq)

-- | NVFP4 specific: 4-bit floating point for inference
-- Natural precision for latent space diffusion
nvfp4Config :: Epilogue
nvfp4Config = Epilogue
  { epScale      = Nothing  -- Computed per-channel
  , epBias       = Nothing
  , epActivation = Just SiLU
  , epQuantize   = FP4
  }
