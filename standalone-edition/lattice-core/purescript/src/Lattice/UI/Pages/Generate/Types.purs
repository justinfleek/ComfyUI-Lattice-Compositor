-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- generate // types
-- all type definitions for the AI generation page
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
module Lattice.UI.Pages.Generate.Types
  ( -- ── generation mode ──
    GenMode(..)
    -- ── sampler types ──
  , Sampler(..)
    -- ── scheduler types ──
  , Scheduler(..)
    -- ── model types ──
  , Model(..)
    -- ── resolution types ──
  , Resolution(..)
    -- ── controlnet types ──
  , ControlNet(..)
    -- ── state types ──
  , State
  , Input
  , Output(..)
  , Action(..)
  , Query(..)
  , Slots
    -- ── data types ──
  , GenerationResult
  , GenerationData(..)
  , GenerationHistoryEntry
  , ModelInfo
  , allModels
  ) where

import Prelude

import Data.Maybe (Maybe)
import Lattice.Services.Bridge.Client as Bridge
import Lattice.Project (LayerType)

-- ═══════════════════════════════════════════════════════════════════════════
--                                                         // generation mode
-- ═══════════════════════════════════════════════════════════════════════════

data GenMode
  = GenTextToImage      -- T2I - still image from prompt
  | GenImageToVideo     -- I2V - video from image + prompt
  | GenTextToVideo      -- T2V - video from prompt
  | GenImageToImage     -- I2I - image from image + prompt
  | GenInpaint          -- Inpaint existing content
  | GenOutpaint         -- Extend image
  | GenUpscale          -- AI upscaling
  | GenRemoveBackground -- Rm background

derive instance eqGenMode :: Eq GenMode

-- ═══════════════════════════════════════════════════════════════════════════
--                                                               // samplers
-- ═══════════════════════════════════════════════════════════════════════════

-- | RES4LYF Samplers (100+ RK methods)
-- Ported from beta/rk_coefficients_beta.py
data Sampler
  -- Multistep RES
  = S_res_2m | S_res_3m | S_res_2s | S_res_3m_sde
  | S_res_2s_sde | S_res_3s_sde
  -- DPM++ multistep
  | S_dpmpp_2m | S_dpmpp_3m
  -- DPM++ singlestep
  | S_dpmpp_2s | S_dpmpp_sde_2s | S_dpmpp_3s
  -- Euler family
  | S_euler | S_euler_ancestral | S_euler_a
  -- DEIS
  | S_deis_2m | S_deis_3m | S_deis_4m
  -- Exponential/ETDRK
  | S_etdrk2_2s | S_etdrk3_a_3s | S_etdrk3_b_3s | S_etdrk4_4s
  | S_etdrk4_4s_alt
  -- UniPC
  | S_unipc | S_unipc_snr
  -- DDIM/PLMS
  | S_ddim | S_plms
  -- LMS/KDPM
  | S_lms | S_kdpm_2_ancestral | S_kdpm_2
  -- ICP/TCD
  | S_icv_ieks | S_tcd
  -- Additional RES4LYF samplers
  | S_res_2m_ancestral | S_res_3m_ancestral
  | S_res_2s_ancestral | S_res_3s_ancestral
  | S_res_2m_sde_ancestral | S_res_3m_sde_ancestral

derive instance eqSampler :: Eq Sampler

-- ═══════════════════════════════════════════════════════════════════════════
--                                                              // schedulers
-- ═══════════════════════════════════════════════════════════════════════════

data Scheduler
  = Sch_normal
  | Sch_beta57
  | Sch_karras
  | Sch_exponential
  | Sch_shifted_linear
  | Sch_sqrt_linear
  | Sch_linear
  | Sch_linear_quadratic
  | Sch_simple
  | Sch_sgm_uniform
  | Sch_ddim_uniform
  | Sch_kl_optimal

derive instance eqScheduler :: Eq Scheduler

-- ═══════════════════════════════════════════════════════════════════════════
--                                                                  // models
-- ═══════════════════════════════════════════════════════════════════════════

data Model
  = ModelSD15     -- Stable Diffusion 1.5
  | ModelSD21     -- Stable Diffusion 2.1
  | ModelSDXL     -- SDXL 1.0
  | ModelSDXL_Turbo
  | ModelSDXL_Lightning
  | ModelWan20I2V -- Wan 2.0 I2V
  | ModelWan20T2V -- Wan 2.0 T2V
  | ModelWan20I2I -- Wan 2.0 I2I
  | ModelWan21I2V -- Wan 2.1 I2V
  | ModelWan21T2V -- Wan 2.1 T2V
  | ModelWan21I2I -- Wan 2.1 I2I
  | ModelWan21Canny  -- Wan 2.1 Canny control
  | ModelWan21Depth  -- Wan 2.1 Depth control
  | ModelWan21Pose   -- Wan 2.1 Pose control
  | ModelWan21Sketch -- Wan 2.1 Sketch control
  | ModelWan21IPAdapter -- Wan 2.1 IP Adapter
  | ModelFluxDev  -- Flux Dev
  | ModelFluxSchnell
  | ModelFluxFill
  | ModelFluxRealism
  | ModelPixartSigma
  | ModelPixartAlpha
  | ModelKolors
  | ModelPlayground
  | ModelPlaygroundV2

derive instance eqModel :: Eq Model

-- ═══════════════════════════════════════════════════════════════════════════
--                                                              // resolution
-- ═══════════════════════════════════════════════════════════════════════════

data Resolution
  = Res512x512
  | Res768x768
  | Res1024x1024
  | Res1024x576  -- 16:9
  | Res576x1024  -- 9:16
  | Res1280x720  -- 720p
  | Res1920x1080 -- Full HD
  | Res1080x1920 -- Full HD vertical / Reels
  | Res2048x1152 -- 2K
  | Res2560x1440 -- 2K QHD
  | Res832x1512  -- Shorts/TikTok 9:16
  | Res720x1280  -- Mobile

derive instance eqResolution :: Eq Resolution

-- ═══════════════════════════════════════════════════════════════════════════
--                                                              // controlnet
-- ═══════════════════════════════════════════════════════════════════════════

data ControlNet
  = ControlNone     -- No controlnet
  | ControlDepth    -- Depth map conditioning
  | ControlCanny    -- Canny edge conditioning
  | ControlLineart  -- Line art conditioning
  | ControlSoftEdge -- Soft edge/HED conditioning
  | ControlNormal   -- Normal map conditioning
  | ControlScribble -- Scribble/sketch conditioning
  | ControlSeg      -- Semantic segmentation conditioning
  | ControlPose     -- OpenPose skeleton conditioning
  | ControlIPAdapter -- IP-Adapter conditioning

derive instance eqControlNet :: Eq ControlNet

-- ═══════════════════════════════════════════════════════════════════════════
--                                                           // component types
-- ═══════════════════════════════════════════════════════════════════════════

type State =
  { -- Mode
    mode :: GenMode
    -- Prompt
  , prompt :: String
  , negativePrompt :: String
    -- Source image (for I2V, I2I, Inpaint, Outpaint)
  , sourceImage :: Maybe String  -- Base64 or URL
    -- ControlNet conditioning
  , controlNet :: ControlNet
  , controlNetImage :: Maybe String  -- Base64 or URL for controlnet input
  , controlNetStrength :: Number     -- 0.0 to 1.0
  , controlNetStartStep :: Number    -- Start step (0.0 to 1.0 = percentage)
  , controlNetEndStep :: Number      -- End step (0.0 to 1.0 = percentage)
  , controlNetStartFrame :: Int      -- Start frame for video generation
  , controlNetEndFrame :: Int        -- End frame for video generation
    -- Generation settings
  , model :: Model
  , sampler :: Sampler
  , scheduler :: Scheduler
  , steps :: Int
  , cfgScale :: Number
  , seed :: Int
  , resolution :: Resolution
    -- Advanced settings
  , eta :: Number           -- Stochasticity
  , sigmaMin :: Number
  , sigmaMax :: Number
  , sigmaChi :: Number
  , rho :: Number
  , schulerAdvance :: Int
    -- UI state
  , isGenerating :: Boolean
  , progress :: Number      -- 0.0 to 100.0
  , stage :: String         -- "idle" | "encoding" | "sampling" | "decoding"
  , previewUrl :: Maybe String
  , error :: Maybe String
  , generationHistory :: Array GenerationHistoryEntry
    -- Bridge client (for backend communication)
  , bridgeClient :: Maybe Bridge.BridgeClient
    -- Composition settings (from parent)
  , numFrames :: Int
  , fps :: Int
  , compositionWidth :: Int
  , compositionHeight :: Int
  }

type Input = 
  { mode :: GenMode
  , bridgeClient :: Maybe Bridge.BridgeClient
  , numFrames :: Int      -- From composition settings
  , fps :: Int            -- From composition settings
  , width :: Int          -- From composition settings
  , height :: Int         -- From composition settings
  }

data Output 
  = GenerationComplete GenerationResult
  | GenerationProgress Number
  | GenerationError String

type GenerationResult =
  { layerId :: String
  , layerType :: LayerType
  , name :: String
  , previewUrl :: String  -- Base64 or URL for viewport display
  , width :: Int
  , height :: Int
  , frames :: Int  -- For video: frame count, for image: 1
  , data :: GenerationData
  }

newtype GenerationData = GenerationData
  { prompt :: String
  , negativePrompt :: String
  , model :: Model
  , sampler :: Sampler
  , scheduler :: Scheduler
  , steps :: Int
  , cfgScale :: Number
  , seed :: Int
  , resolution :: Resolution
  , eta :: Number
  , sigmaMin :: Number
  , sigmaMax :: Number
  , rho :: Number
  }

type GenerationHistoryEntry =
  { prompt :: String
  , model :: Model
  , seed :: Int
  , previewUrl :: Maybe String
  , timestamp :: Number
  }

-- ═══════════════════════════════════════════════════════════════════════════
--                                                                  // actions
-- ═══════════════════════════════════════════════════════════════════════════

data Action
  = SetMode GenMode
  | SetPrompt String
  | SetNegativePrompt String
  | SetSampler Sampler
  | SetScheduler Scheduler
  | SetSteps Int
  | SetCfgScale Number
  | SetSeed Int
  | SetModel Model
  | SetResolution Resolution
  | SetControlNet ControlNet
  | SetControlNetStrength Number
  | SetControlNetImage String
  | SetControlNetStartStep Number
  | SetControlNetEndStep Number
  | SetControlNetStartFrame Int
  | SetControlNetEndFrame Int
  | RandomizeSeed
  | StartGeneration
  | CancelGeneration

-- ═══════════════════════════════════════════════════════════════════════════
--                                                                  // queries
-- ═══════════════════════════════════════════════════════════════════════════

data Query a
  = QuerySetMode GenMode a
  | QuerySetPrompt String a
  | QuerySetSampler Sampler a
  | QuerySetScheduler Scheduler a
  | QuerySetSteps Int a
  | QuerySetCfgScale Number a
  | QuerySetSeed Int a
  | QuerySetModel Model a
  | QuerySetResolution Resolution a

type Slots = ()

-- ═══════════════════════════════════════════════════════════════════════════
--                                                              // model info
-- ═══════════════════════════════════════════════════════════════════════════

type ModelInfo =
  { model :: Model
  , value :: String
  , label :: String
  , supportsT2I :: Boolean
  , supportsI2V :: Boolean
  , supportsT2V :: Boolean
  , supportsI2I :: Boolean
  }

allModels :: Array ModelInfo
allModels =
  [ { model: ModelSD15, value: "sd15", label: "Stable Diffusion 1.5"
    , supportsT2I: true, supportsI2V: false, supportsT2V: false, supportsI2I: true }
  , { model: ModelSD21, value: "sd21", label: "Stable Diffusion 2.1"
    , supportsT2I: true, supportsI2V: false, supportsT2V: false, supportsI2I: true }
  , { model: ModelSDXL, value: "sdxl", label: "SDXL 1.0"
    , supportsT2I: true, supportsI2V: false, supportsT2V: false, supportsI2I: true }
  , { model: ModelSDXL_Turbo, value: "sdxl_turbo", label: "SDXL Turbo"
    , supportsT2I: true, supportsI2V: false, supportsT2V: false, supportsI2I: true }
  , { model: ModelSDXL_Lightning, value: "sdxl_lightning", label: "SDXL Lightning"
    , supportsT2I: true, supportsI2V: false, supportsT2V: false, supportsI2I: true }
  , { model: ModelWan20I2V, value: "wan20_i2v", label: "Wan 2.0 I2V"
    , supportsT2I: false, supportsI2V: true, supportsT2V: false, supportsI2I: false }
  , { model: ModelWan20T2V, value: "wan20_t2v", label: "Wan 2.0 T2V"
    , supportsT2I: false, supportsI2V: false, supportsT2V: true, supportsI2I: false }
  , { model: ModelWan20I2I, value: "wan20_i2i", label: "Wan 2.0 I2I"
    , supportsT2I: false, supportsI2V: false, supportsT2V: false, supportsI2I: true }
  , { model: ModelWan21I2V, value: "wan21_i2v", label: "Wan 2.1 I2V"
    , supportsT2I: false, supportsI2V: true, supportsT2V: false, supportsI2I: false }
  , { model: ModelWan21T2V, value: "wan21_t2v", label: "Wan 2.1 T2V"
    , supportsT2I: false, supportsI2V: false, supportsT2V: true, supportsI2I: false }
  , { model: ModelWan21I2I, value: "wan21_i2i", label: "Wan 2.1 I2I"
    , supportsT2I: false, supportsI2V: false, supportsT2V: false, supportsI2I: true }
  , { model: ModelWan21Canny, value: "wan21_canny", label: "Wan 2.1 Canny"
    , supportsT2I: false, supportsI2V: true, supportsT2V: true, supportsI2I: true }
  , { model: ModelWan21Depth, value: "wan21_depth", label: "Wan 2.1 Depth"
    , supportsT2I: false, supportsI2V: true, supportsT2V: true, supportsI2I: true }
  , { model: ModelWan21Pose, value: "wan21_pose", label: "Wan 2.1 Pose"
    , supportsT2I: false, supportsI2V: true, supportsT2V: true, supportsI2I: true }
  , { model: ModelWan21Sketch, value: "wan21_sketch", label: "Wan 2.1 Sketch"
    , supportsT2I: false, supportsI2V: true, supportsT2V: true, supportsI2I: true }
  , { model: ModelWan21IPAdapter, value: "wan21_ipadapter", label: "Wan 2.1 IP-Adapter"
    , supportsT2I: false, supportsI2V: true, supportsT2V: true, supportsI2I: true }
  , { model: ModelFluxDev, value: "flux_dev", label: "Flux Dev"
    , supportsT2I: true, supportsI2V: false, supportsT2V: false, supportsI2I: true }
  , { model: ModelFluxSchnell, value: "flux_schnell", label: "Flux Schnell"
    , supportsT2I: true, supportsI2V: false, supportsT2V: false, supportsI2I: true }
  , { model: ModelFluxFill, value: "flux_fill", label: "Flux Fill"
    , supportsT2I: true, supportsI2V: false, supportsT2V: false, supportsI2I: true }
  , { model: ModelFluxRealism, value: "flux_realism", label: "Flux Realism"
    , supportsT2I: true, supportsI2V: false, supportsT2V: false, supportsI2I: true }
  , { model: ModelPixartSigma, value: "pixart_sigma", label: "Pixart Sigma"
    , supportsT2I: true, supportsI2V: false, supportsT2V: false, supportsI2I: true }
  , { model: ModelPixartAlpha, value: "pixart_alpha", label: "Pixart Alpha"
    , supportsT2I: true, supportsI2V: false, supportsT2V: false, supportsI2I: true }
  , { model: ModelKolors, value: "kolors", label: "Kolors"
    , supportsT2I: true, supportsI2V: false, supportsT2V: false, supportsI2I: true }
  , { model: ModelPlayground, value: "playground", label: "Playground"
    , supportsT2I: true, supportsI2V: false, supportsT2V: false, supportsI2I: true }
  , { model: ModelPlaygroundV2, value: "playground_v2", label: "Playground v2"
    , supportsT2I: true, supportsI2V: false, supportsT2V: false, supportsI2I: true }
  ]
