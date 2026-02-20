-- | Standard workflows for diffusion inference
-- Based on RES4LYF patterns for t2i, i2i, i2v, v2v
module Lattice.Diffusion.Workflows where

import Lattice.Diffusion.Precision.Landauer (Precision(..))

-- | Generation task type
data TaskType
  = TextToImage      -- t2i
  | ImageToImage     -- i2i  
  | ImageToVideo     -- i2v
  | VideoToVideo     -- v2v
  | TextToVideo      -- t2v
  | Inpainting       -- inpaint
  | Outpainting      -- outpaint
  | Upscale          -- hires fix
  | StyleTransfer    -- style guide
  deriving (Show, Eq, Ord, Enum, Bounded)

-- | Model architecture
data ModelArch
  = SDXL
  | SD35
  | Flux
  | FluxSchnell
  | HiDream
  | Chroma
  | WAN          -- Wan video model
  | LTXV         -- LTX video
  | CogVideoX
  deriving (Show, Eq, Ord, Enum, Bounded)

-- | Workflow configuration
data Workflow = Workflow
  { wfTask        :: !TaskType
  , wfModel       :: !ModelArch
  , wfSampler     :: !SamplerPreset
  , wfScheduler   :: !SchedulerPreset
  , wfSteps       :: !Int
  , wfCFG         :: !Double
  , wfDenoise     :: !Double       -- 1.0 for t2i, <1.0 for i2i/v2v
  , wfPrecision   :: !Precision
  , wfGuides      :: ![GuideConfig]
  } deriving (Show, Eq)

-- | Sampler presets from RES4LYF
data SamplerPreset
  = RES2M           -- Fast, good quality
  | RES3M           -- Higher quality
  | DPMpp2M         -- Classic DPM++
  | DPMpp2S         -- Single-step variant
  | DPMppSDE        -- Stochastic
  | Euler           -- Baseline
  | EulerAncestral  -- With noise injection
  | HeunPP          -- Heun with predictor
  | UniPC           -- Universal predictor-corrector
  | DEIS            -- Diffusion exponential integrator
  -- Implicit methods for high quality
  | GaussLegendre   -- Symplectic, energy conserving
  | RadauIIA        -- L-stable, stiff problems
  | LobattoIIIC     -- Boundary value friendly
  deriving (Show, Eq, Ord, Enum, Bounded)

-- | Scheduler presets
data SchedulerPreset
  = Karras            -- σ schedule with rho parameter
  | Beta57            -- RES4LYF beta with α=0.5, β=0.7
  | LinearSchedule    -- Simple linear
  | ExponentialSchedule -- Log-linear
  | Polyexponential   -- Power law
  | Cosine            -- DDPM cosine
  | Tangent           -- Arctan-based
  | SGM               -- Simple guidance matching
  deriving (Show, Eq, Ord, Enum, Bounded)

-- | Guide configuration for style/structure control
data GuideConfig = GuideConfig
  { gcType       :: !GuideType
  , gcWeight     :: !Double
  , gcStartStep  :: !Int
  , gcEndStep    :: !Int
  , gcScheduler  :: !SchedulerPreset
  } deriving (Show, Eq)

data GuideType
  = MeanGuide       -- Guide toward mean latent
  | StyleGuide      -- AdaIN/WCT style transfer
  | StructureGuide  -- Preserve structure
  | FlowGuide       -- Optical flow for video
  | DepthGuide      -- Depth-aware
  | RegionalGuide   -- Masked regional control
  deriving (Show, Eq, Ord, Enum, Bounded)

--------------------------------------------------------------------------------
-- Standard Workflow Presets
--------------------------------------------------------------------------------

-- | Default workflow constructor with sane defaults
defaultWorkflow :: TaskType -> ModelArch -> Workflow
defaultWorkflow task model = Workflow
  { wfTask      = task
  , wfModel     = model
  , wfSampler   = RES2M
  , wfScheduler = Karras
  , wfSteps     = 28
  , wfCFG       = 7.0
  , wfDenoise   = 1.0
  , wfPrecision = FP4  -- Thermodynamically optimal (Landauer)
  , wfGuides    = []
  }

-- | Flux text-to-image - fast, high quality
fluxT2I :: Workflow
fluxT2I = (defaultWorkflow TextToImage Flux)
  { wfSampler   = RES2M
  , wfScheduler = Beta57
  , wfSteps     = 20
  , wfCFG       = 3.5  -- Flux uses lower CFG
  }

-- | Flux Schnell - ultra fast (4 steps)
fluxSchnellT2I :: Workflow
fluxSchnellT2I = (defaultWorkflow TextToImage FluxSchnell)
  { wfSampler   = Euler
  , wfScheduler = LinearSchedule
  , wfSteps     = 4
  , wfCFG       = 1.0  -- Schnell needs minimal guidance
  }

-- | SD3.5 text-to-image
sd35T2I :: Workflow
sd35T2I = (defaultWorkflow TextToImage SD35)
  { wfSampler   = DPMpp2M
  , wfScheduler = Karras
  , wfSteps     = 28
  , wfCFG       = 7.0
  }

-- | SDXL text-to-image - classic reliable
sdxlT2I :: Workflow
sdxlT2I = (defaultWorkflow TextToImage SDXL)
  { wfSampler   = DPMpp2M
  , wfScheduler = Karras
  , wfSteps     = 30
  , wfCFG       = 7.5
  }

-- | HiDream text-to-image - high resolution specialist
hidreamT2I :: Workflow
hidreamT2I = (defaultWorkflow TextToImage HiDream)
  { wfSampler   = RES3M
  , wfScheduler = Beta57
  , wfSteps     = 25
  , wfCFG       = 5.0
  }

-- | Chroma text-to-image 
chromaT2I :: Workflow
chromaT2I = (defaultWorkflow TextToImage Chroma)
  { wfSampler   = RES2M
  , wfScheduler = Karras
  , wfSteps     = 24
  , wfCFG       = 6.0
  }

--------------------------------------------------------------------------------
-- Image-to-Image Workflows
--------------------------------------------------------------------------------

-- | Flux image-to-image
fluxI2I :: Double -> Workflow
fluxI2I denoise = (defaultWorkflow ImageToImage Flux)
  { wfSampler   = RES2M
  , wfScheduler = Beta57
  , wfSteps     = ceiling (20.0 * denoise)
  , wfCFG       = 3.5
  , wfDenoise   = denoise
  }

-- | SDXL image-to-image with structure preservation
sdxlI2I :: Double -> Workflow
sdxlI2I denoise = (defaultWorkflow ImageToImage SDXL)
  { wfSampler   = DPMpp2M
  , wfScheduler = Karras
  , wfSteps     = ceiling (30.0 * denoise)
  , wfCFG       = 7.0
  , wfDenoise   = denoise
  , wfGuides    = [structureGuide 0.3]
  }

--------------------------------------------------------------------------------
-- Video Workflows (WAN model based on RES4LYF patterns)
--------------------------------------------------------------------------------

-- | WAN image-to-video - high quality video generation
wanI2V :: Workflow
wanI2V = (defaultWorkflow ImageToVideo WAN)
  { wfSampler   = RES3M       -- Higher order for temporal coherence
  , wfScheduler = Beta57
  , wfSteps     = 30
  , wfCFG       = 5.0
  , wfGuides    = [flowGuide 0.5]  -- Optical flow for smooth motion
  }

-- | WAN video-to-video - style transfer while preserving motion
wanV2V :: Double -> Workflow
wanV2V denoise = (defaultWorkflow VideoToVideo WAN)
  { wfSampler   = GaussLegendre  -- Symplectic for energy conservation
  , wfScheduler = Beta57
  , wfSteps     = ceiling (30.0 * denoise)
  , wfCFG       = 4.5
  , wfDenoise   = denoise
  , wfGuides    = [flowGuide 0.7, structureGuide 0.4]
  }

-- | LTX video generation
ltxvI2V :: Workflow
ltxvI2V = (defaultWorkflow ImageToVideo LTXV)
  { wfSampler   = RES2M
  , wfScheduler = Karras
  , wfSteps     = 25
  , wfCFG       = 6.0
  }

-- | CogVideoX for text-to-video
cogvideoT2V :: Workflow
cogvideoT2V = (defaultWorkflow TextToVideo CogVideoX)
  { wfSampler   = DPMpp2M
  , wfScheduler = Karras
  , wfSteps     = 50
  , wfCFG       = 7.0
  }

--------------------------------------------------------------------------------
-- High Quality Workflows (Implicit Solvers)
--------------------------------------------------------------------------------

-- | High quality t2i using Gauss-Legendre (symplectic)
hqSymplecticT2I :: ModelArch -> Workflow
hqSymplecticT2I model = (defaultWorkflow TextToImage model)
  { wfSampler   = GaussLegendre
  , wfScheduler = Karras
  , wfSteps     = 15  -- Fewer steps needed with higher order
  , wfCFG       = 7.0
  , wfPrecision = FP8  -- Higher precision for implicit solver
  }

-- | Ultra quality using Radau IIA (L-stable)
hqRadauT2I :: ModelArch -> Workflow
hqRadauT2I model = (defaultWorkflow TextToImage model)
  { wfSampler   = RadauIIA
  , wfScheduler = Beta57
  , wfSteps     = 12
  , wfCFG       = 6.5
  , wfPrecision = FP8
  }

--------------------------------------------------------------------------------
-- Specialty Workflows
--------------------------------------------------------------------------------

-- | Inpainting with structure guide
fluxInpaint :: Workflow
fluxInpaint = (defaultWorkflow Inpainting Flux)
  { wfSampler   = RES2M
  , wfScheduler = Beta57
  , wfSteps     = 25
  , wfCFG       = 4.0
  , wfGuides    = [regionalGuide 1.0, structureGuide 0.5]
  }

-- | Upscale/hires fix
sdxlUpscale :: Workflow
sdxlUpscale = (defaultWorkflow Upscale SDXL)
  { wfSampler   = DPMpp2S
  , wfScheduler = Karras
  , wfSteps     = 15
  , wfCFG       = 5.0
  , wfDenoise   = 0.4
  }

-- | Style transfer workflow
fluxStyleTransfer :: Workflow
fluxStyleTransfer = (defaultWorkflow StyleTransfer Flux)
  { wfSampler   = RES2M
  , wfScheduler = Beta57
  , wfSteps     = 20
  , wfCFG       = 3.0
  , wfDenoise   = 0.7
  , wfGuides    = [styleGuide 0.8, structureGuide 0.3]
  }

--------------------------------------------------------------------------------
-- Guide Presets
--------------------------------------------------------------------------------

-- | Structure preservation guide
structureGuide :: Double -> GuideConfig
structureGuide weight = GuideConfig
  { gcType      = StructureGuide
  , gcWeight    = weight
  , gcStartStep = 0
  , gcEndStep   = -1  -- -1 means all steps
  , gcScheduler = Karras
  }

-- | Style injection guide  
styleGuide :: Double -> GuideConfig
styleGuide weight = GuideConfig
  { gcType      = StyleGuide
  , gcWeight    = weight
  , gcStartStep = 5   -- Start after initial structure forms
  , gcEndStep   = -1
  , gcScheduler = Cosine
  }

-- | Optical flow guide for video
flowGuide :: Double -> GuideConfig
flowGuide weight = GuideConfig
  { gcType      = FlowGuide
  , gcWeight    = weight
  , gcStartStep = 0
  , gcEndStep   = -1
  , gcScheduler = LinearSchedule
  }

-- | Regional/masked guide
regionalGuide :: Double -> GuideConfig
regionalGuide weight = GuideConfig
  { gcType      = RegionalGuide
  , gcWeight    = weight
  , gcStartStep = 0
  , gcEndStep   = -1
  , gcScheduler = Karras
  }

-- | Depth-aware guide
depthGuide :: Double -> GuideConfig
depthGuide weight = GuideConfig
  { gcType      = DepthGuide
  , gcWeight    = weight
  , gcStartStep = 0
  , gcEndStep   = -1
  , gcScheduler = LinearSchedule
  }

--------------------------------------------------------------------------------
-- Workflow Modifiers
--------------------------------------------------------------------------------

-- | Adjust steps for a workflow
withSteps :: Int -> Workflow -> Workflow
withSteps n wf = wf { wfSteps = n }

-- | Adjust CFG scale
withCFG :: Double -> Workflow -> Workflow
withCFG cfg wf = wf { wfCFG = cfg }

-- | Set precision
withPrecision :: Precision -> Workflow -> Workflow
withPrecision p wf = wf { wfPrecision = p }

-- | Add a guide to workflow
withGuide :: GuideConfig -> Workflow -> Workflow
withGuide g wf = wf { wfGuides = g : wfGuides wf }

-- | Set sampler
withSampler :: SamplerPreset -> Workflow -> Workflow
withSampler s wf = wf { wfSampler = s }

-- | Set scheduler
withScheduler :: SchedulerPreset -> Workflow -> Workflow
withScheduler s wf = wf { wfScheduler = s }
