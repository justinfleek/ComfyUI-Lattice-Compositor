-- | Precision-Aware Sampler Pipeline
-- Integrates Landauer precision framework with diffusion samplers
-- Key insight: FP4 is optimal for latent space because VAE already paid the Landauer cost
module Lattice.Diffusion.Samplers.PrecisionAware where

import Lattice.Diffusion.Precision.Landauer
import Lattice.Diffusion.Samplers.Exponential

-- | Stage in the diffusion pipeline with precision requirements
data PipelineStage
  = StageVAEEncoder    -- ^ Image -> Latent (high precision)
  | StageDiT          -- ^ Latent manipulation (can use FP4!)
  | StageVAEDecoder   -- ^ Latent -> Image (high precision)
  | StageUpscaler     -- ^ Additional upscaling stage
  deriving (Show, Eq, Ord, Enum, Bounded)

-- | Precision configuration for each pipeline stage
-- Derived from Landauer framework - costs computed at type level
data PrecisionConfig = PrecisionConfig
  { pcEncoderPrecision  :: !Precision
  , pcLatentPrecision  :: !Precision   -- DiT operates here
  , pcDecoderPrecision :: !Precision
  , pcUpscalerPrecision :: !Precision
  , pcEnableNVFP4      :: !Bool         -- Use NVFP4 for latent ops?
  } deriving (Show, Eq)

-- | Default precision config matching Landauer optimal
-- VAE: FP16 (high), Latent: FP4 (optimal!), Decoder: FP16
defaultPrecisionConfig :: PrecisionConfig
defaultPrecisionConfig = PrecisionConfig
  { pcEncoderPrecision  = FP16
  , pcLatentPrecision   = FP4   -- Landauer: VAE already paid cost!
  , pcDecoderPrecision  = FP16
  , pcUpscalerPrecision = FP16
  , pcEnableNVFP4       = True
  }

-- | Full precision for maximum quality (slower)
fullPrecisionConfig :: PrecisionConfig
fullPrecisionConfig = PrecisionConfig
  { pcEncoderPrecision  = FP32
  , pcLatentPrecision   = FP16
  , pcDecoderPrecision  = FP32
  , pcUpscalerPrecision = FP32
  , pcEnableNVFP4       = False
  }

-- | Precision boundary analysis between stages
analyzeBoundaries :: PrecisionConfig -> [PrecisionBoundary]
analyzeBoundaries cfg =
  let encoderDomain = PrecisionDomain "encoder" (pcEncoderPrecision cfg) pixelEntropy
      latentDomain  = PrecisionDomain "latent" (pcLatentPrecision cfg) latentEntropy
      decoderDomain = PrecisionDomain "decoder" (pcDecoderPrecision cfg) pixelEntropy
      
      -- Encoder -> Latent: VAE compression (paid by VAE)
      encToLat = PrecisionBoundary
        { pbSource = encoderDomain
        , pbTarget = latentDomain
        , pbCost = landauerCost (pdEntropy encoderDomain) (precisionBits $ pcLatentPrecision cfg)
        , pbFusible = True  -- Fuse quantize into VAE decoder epilogue
        }
      
      -- Latent -> Decoder: VAE reconstruction
      latToDec = PrecisionBoundary
        { pbSource = latentDomain
        , pbTarget = decoderDomain
        , pbCost = landauerCost (pdEntropy latentDomain) (precisionBits $ pcDecoderPrecision cfg)
        , pbFusible = True
        }
  in [encToLat, latToDec]

-- | Check if all boundaries are free (zero Landauer cost)
allBoundariesFree :: PrecisionConfig -> Bool
allBoundariesFree cfg = all isFree (analyzeBoundaries cfg)

-- | Get epilogue configuration for each stage based on precision config
getEpilogue :: PipelineStage -> PrecisionConfig -> Epilogue
getEpilogue stage cfg = case stage of
  StageVAEEncoder -> Epilogue
    { epScale = Nothing
    , epBias = Nothing
    , epActivation = Just GELU
    , epQuantize = pcLatentPrecision cfg  -- Quantize to latent precision
    }
  StageDiT -> Epilogue
    { epScale = Nothing
    , epBias = Nothing
    , epActivation = Just SiLU
    , epQuantize = pcLatentPrecision cfg  -- Can use FP4!
    }
  StageVAEDecoder -> Epilogue
    { epScale = Nothing
    , epBias = Nothing
    , epActivation = Just GELU
    , epQuantize = FP16  -- Final output in FP16
    }
  StageUpscaler -> Epilogue
    { epScale = Nothing
    , epBias = Nothing
    , epActivation = Just SiLU
    , epQuantize = pcUpscalerPrecision cfg
    }

-- | Sampler with precision awareness
-- Returns not just the next latent, but also the precision at which to operate
data PrecisionAwareResult a = PrecisionAwareResult
  { parLatent     :: !a
  , parPrecision  :: !Precision     -- Precision used for this step
  , parLandauerCost :: !Double     -- Energy cost of precision transition
  , parIsFree    :: !Bool          -- Was this transition information-preserving?
  }

-- | Wrap a sampler with precision tracking
-- Key: DiT steps can use FP4 because we're in latent space
wrapWithPrecision :: PrecisionConfig -> (Double -> Double -> Double -> Double -> Double) -> Double -> Double -> Double -> PrecisionAwareResult Double
wrapWithPrecision cfg sampler sigma sigmaNext xn dn =
  let prec = pcLatentPrecision cfg
      precBits = precisionBits prec
      cost = landauerCost latentEntropy precBits
      isFreeBoundary = cost == 0
      result = sampler sigma sigmaNext xn dn
  in PrecisionAwareResult
    { parLatent = result
    , parPrecision = prec
    , parLandauerCost = cost
    , parIsFree = isFreeBoundary
    }

-- | RES 2M with Landauer precision
res2mPrecision :: PrecisionConfig -> Double -> Double -> Double -> Double -> Double -> PrecisionAwareResult Double
res2mPrecision cfg = wrapWithPrecision cfg res2m

-- | DPM++ 2M with Landauer precision
dpmpp2mPrecision :: PrecisionConfig -> Double -> Double -> Double -> Double -> Double -> PrecisionAwareResult Double
dpmpp2mPrecision cfg = wrapWithPrecision cfg dpmpp2m

-- | Euler with Landauer precision
eulerPrecision :: PrecisionConfig -> Double -> Double -> Double -> Double -> PrecisionAwareResult Double
eulerPrecision cfg sigma sigmaNext xn dn =
  let prec = pcLatentPrecision cfg
      cost = landauerCost latentEntropy (precisionBits prec)
      result = euler sigma sigmaNext xn dn
  in PrecisionAwareResult
    { parLatent = result
    , parPrecision = prec
    , parLandauerCost = cost
    , parIsFree = cost == 0
    }

-- | Compute total Landauer energy cost for a full sampling trajectory
totalLandauerCost :: PrecisionConfig -> [Double] -> Double
totalLandauerCost cfg sigmas =
  let costs = map (\s -> landauerCost latentEntropy (precisionBits $ pcLatentPrecision cfg)) sigmas
  in sum costs

-- | NVFP4-specific configuration for Blackwell/Ada+ GPUs
nvfp4PrecisionConfig :: PrecisionConfig
nvfp4PrecisionConfig = defaultPrecisionConfig { pcEnableNVFP4 = True }
