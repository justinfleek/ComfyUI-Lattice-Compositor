-- | Generate Page Component
-- |
-- | AI-powered generation panel for T2I, I2V, T2V, I2I and more.
-- | Exposes all RES4LYF samplers and schedulers.
-- |
-- | ┌─────────────────────────────────────────────────────────────────────┐
-- | │ Mode: [T2I] [I2V] [T2V] [I2I] [Inpaint] [Upscale]               │
-- | ├─────────────────────────────────────────────────────────────────────┤
-- | │ Prompt                                                           │
-- | │ ┌───────────────────────────────────────────────────────────────┐ │
-- | │ │                                                               │ │
-- | │ └───────────────────────────────────────────────────────────────┘ │
-- | │ Negative Prompt                                                  │
-- | │ ┌───────────────────────────────────────────────────────────────┐ │
-- | │ │                                                               │ │
-- | │ └───────────────────────────────────────────────────────────────┘ │
-- | ├─────────────────────────────────────────────────────────────────────┤
-- | │ Model: [─────────────────▼]  Resolution: [1024x1024▼]            │
-- | ├─────────────────────────────────────────────────────────────────────┤
-- | │ Sampler: [RES 2M────────────────▼]  Scheduler: [Normal─────▼]   │
-- | │ Steps: [────30───]  CFG: [──5.0──]  Seed: [────0────] [🎲]      │
-- | ├─────────────────────────────────────────────────────────────────────┤
-- | │ Advanced ▼ (eta, sigma, etc.)                                     │
-- | ├─────────────────────────────────────────────────────────────────────┤
-- | │ [═══════════════════════════════════════════════════════════════] │
-- | │                        PREVIEW                                    │
-- | ├─────────────────────────────────────────────────────────────────────┤
-- | │                                          [Cancel] [Generate]      │
-- | └─────────────────────────────────────────────────────────────────────┘
module Lattice.UI.Pages.Generate
  ( component
  , Input
  , Output
  , Query
  ) where

import Prelude

import Data.Array (length, filter, cons, last)
import Data.Either (Either(..))
import Data.Int (toNumber, round)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String (joinWith)
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Data.DateTime.Instant (unInstant, Milliseconds(..))
import Effect (Effect)
import Effect.Now (now)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Type.Proxy (Proxy(..))

import Lattice.UI.Core (cls)
import Lattice.Services.Bridge.Client as Bridge
import Lattice.Project (LayerType(LTTextToImage, LTImageToVideo, LTTextToVideo, LTImageToImage, LTInpaint, LTOutpaint, LTUpscale, LTRemoveBackground))

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                     // types
-- ═══════════════════════════════════════════════════════════════════════════

-- | Generation mode types
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

-- | RES4LYF Schedulers
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

-- | Available models
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

-- | Resolution presets
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

-- | ControlNet types for conditioning
data ControlNet
  = ControlNone     -- No controlnet
  | ControlDepth    -- Depth map conditioning
  | ControlCanny    -- Canny edge conditioning
  | ControlLineart -- Line art conditioning
  | ControlSoftEdge -- Soft edge/HED conditioning
  | ControlNormal   -- Normal map conditioning
  | ControlScribble -- Scribble/sketch conditioning
  | ControlSeg      -- Semantic segmentation conditioning
  | ControlPose     -- OpenPose skeleton conditioning
  | ControlIPAdapter -- IP-Adapter conditioning

derive instance eqControlNet :: Eq ControlNet

-- | Component state
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
  , controlNetStartStep :: Number   -- Start step (0.0 to 1.0 = percentage of total steps)
  , controlNetEndStep :: Number      -- End step (0.0 to 1.0 = percentage of total steps)
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
    -- Bridge client (for backend communication)
  , bridgeClient :: Maybe Bridge.BridgeClient
    -- Composition settings (from parent)
  , numFrames :: Int
  , fps :: Int
  , compositionWidth :: Int
  , compositionHeight :: Int
  }

-- | Input
type Input = 
  { mode :: GenMode
  , bridgeClient :: Maybe Bridge.BridgeClient
  , numFrames :: Int      -- From composition settings
  , fps :: Int           -- From composition settings
  , width :: Int         -- From composition settings
  , height :: Int        -- From composition settings
  }

-- | Output - emitted when generation completes
data Output 
  = GenerationComplete GenerationResult
  | GenerationProgress Number
  | GenerationError String

-- | Generation result - layer data to add to timeline
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

-- | Generation data stored with layer
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

-- | Queries
data Query a
  = SetMode GenMode a
  | SetPrompt String a
  | SetNegativePrompt String a
  | SetSampler Sampler a
  | SetScheduler Scheduler a
  | SetSteps Int a
  | SetCfgScale Number a
  | SetSeed Int a
  | SetModel Model a
  | SetResolution Resolution a
  | SetControlNet ControlNet a
  | SetControlNetStrength Number a
  | SetControlNetImage String a
  | SetControlNetStartStep Number a
  | SetControlNetEndStep Number a
  | SetControlNetStartFrame Int a
  | SetControlNetEndFrame Int a
  | RandomizeSeed a
  | StartGeneration a
  | CancelGeneration a

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // component
-- ════════════════════════════════════════════════════════════════════════════

component :: forall q i o m. MonadAff m => H.Component q i o m
component = H.mkComponent
  { initialState: \input -> initialState input
  , render
  , eval: H.mkEval H.defaultEval
      { handleAction = handleAction
      , handleQuery = handleQuery
      }
  }

initialState :: Input -> State
initialState input =
  { mode: input.mode
  , prompt: ""
  , negativePrompt: "blurry, low quality, distorted, deformed, ugly"
  , sourceImage: Nothing
  , controlNet: ControlNone
  , controlNetImage: Nothing
  , controlNetStrength: 1.0
  , controlNetStartStep: 0.0
  , controlNetEndStep: 1.0
  , controlNetStartFrame: 0
  , controlNetEndFrame: input.numFrames
  , model: ModelSDXL
  , sampler: S_res_2m
  , scheduler: Sch_normal
  , steps: 30
  , cfgScale: 5.0
  , seed: 0
  , resolution: Res1024x1024
  , eta: 0.0
  , sigmaMin: 0.0292
  , sigmaMax: 14.61
  , sigmaChi: 0.0
  , rho: 7.0
  , schulerAdvance: 0
  , isGenerating: false
  , progress: 0.0
  , stage: "idle"
  , previewUrl: Nothing
  , error: Nothing
  , bridgeClient: input.bridgeClient
  , numFrames: input.numFrames
  , fps: input.fps
  , compositionWidth: input.width
  , compositionHeight: input.height
  }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                 // rendering
-- ════════════════════════════════════════════════════════════════════════════

render :: forall m. MonadAff m => State -> H.ComponentHTML Query () m
render state =
  HH.div [ cls [ "lattice-generate-page" ] ]
    [ renderModeSelector state
    , renderPromptSection state
    , renderSettingsSection state
    , renderControlNetSection state
    , renderAdvancedSection state
    , renderPreviewSection state
    , renderActionButtons state
    ]

renderModeSelector :: forall m. MonadAff m => State -> H.ComponentHTML Query () m
renderModeSelector state =
  HH.div [ cls [ "lattice-generate-mode-selector" ] ]
    [ HH.text "Mode: "
    , HH.button [ cls [ "mode-btn", if state.mode == GenTextToImage then "active" else "" ] 
                , HE.onClick \_ -> H.query_ (SetMode GenTextToImage)
                ] [ HH.text "T2I" ]
    , HH.button [ cls [ "mode-btn", if state.mode == GenImageToVideo then "active" else "" ]
                , HE.onClick \_ -> H.query_ (SetMode GenImageToVideo)
                ] [ HH.text "I2V" ]
    , HH.button [ cls [ "mode-btn", if state.mode == GenTextToVideo then "active" else "" ]
                , HE.onClick \_ -> H.query_ (SetMode GenTextToVideo)
                ] [ HH.text "T2V" ]
    , HH.button [ cls [ "mode-btn", if state.mode == GenImageToImage then "active" else "" ]
                , HE.onClick \_ -> H.query_ (SetMode GenImageToImage)
                ] [ HH.text "I2I" ]
    , HH.button [ cls [ "mode-btn", if state.mode == GenInpaint then "active" else "" ]
                , HE.onClick \_ -> H.query_ (SetMode GenInpaint)
                ] [ HH.text "Inpaint" ]
    , HH.button [ cls [ "mode-btn", if state.mode == GenUpscale then "active" else "" ]
                , HE.onClick \_ -> H.query_ (SetMode GenUpscale)
                ] [ HH.text "Upscale" ]
    ]

renderPromptSection :: forall m. MonadAff m => State -> H.ComponentHTML Query () m
renderPromptSection state =
  HH.div [ cls [ "lattice-generate-prompt-section" ] ]
    [ HH.div [ cls [ "lattice-form-group" ] ]
        [ HH.label [] [ HH.text "Prompt" ]
        , HH.textarea
            [ HP.value state.prompt
            , HP.placeholder "Describe what you want to generate..."
            , HP.rows 4
            , HE.onValueInput \s -> H.query_ (SetPrompt s)
            ]
        ]
    , HH.div [ cls [ "lattice-form-group" ] ]
        [ HH.label [] [ HH.text "Negative Prompt" ]
        , HH.textarea
            [ HP.value state.negativePrompt
            , HP.placeholder "What to avoid..."
            , HP.rows 2
            , HE.onValueInput \s -> H.query_ (SetNegativePrompt s)
            ]
        ]
    ]

renderSettingsSection :: forall m. MonadAff m => State -> H.ComponentHTML Query () m
renderSettingsSection state =
  HH.div [ cls [ "lattice-generate-settings" ] ]
    [ HH.div [ cls [ "lattice-form-row" ] ]
        [ HH.div [ cls [ "lattice-form-group" ] ]
            [ HH.label [] [ HH.text "Model" ]
            , HH.select [ HE.onChange \s -> H.query_ (SetModel (parseModel s)) ]
                [ HH.option [ HP.value "sd15" ] [ HH.text "Stable Diffusion 1.5" ]
                , HH.option [ HP.value "sd21" ] [ HH.text "Stable Diffusion 2.1" ]
                , HH.option [ HP.value "sdxl", HP.selected (state.model == ModelSDXL) ] [ HH.text "SDXL 1.0" ]
                , HH.option [ HP.value "sdxl_turbo" ] [ HH.text "SDXL Turbo" ]
                , HH.option [ HP.value "sdxl_lightning" ] [ HH.text "SDXL Lightning" ]
                , HH.option [] [ HH.hr [] ]
                , HH.option [ HP.value "wan20_i2v" ] [ HH.text "Wan 2.0 I2V" ]
                , HH.option [ HP.value "wan20_t2v" ] [ HH.text "Wan 2.0 T2V" ]
                , HH.option [ HP.value "wan20_i2i" ] [ HH.text "Wan 2.0 I2I" ]
                , HH.option [] [ HH.hr [] ]
                , HH.option [ HP.value "wan21_i2v" ] [ HH.text "Wan 2.1 I2V" ]
                , HH.option [ HP.value "wan21_t2v" ] [ HH.text "Wan 2.1 T2V" ]
                , HH.option [ HP.value "wan21_i2i" ] [ HH.text "Wan 2.1 I2I" ]
                , HH.option [ HP.value "wan21_canny" ] [ HH.text "Wan 2.1 Canny" ]
                , HH.option [ HP.value "wan21_depth" ] [ HH.text "Wan 2.1 Depth" ]
                , HH.option [ HP.value "wan21_pose" ] [ HH.text "Wan 2.1 Pose" ]
                , HH.option [ HP.value "wan21_sketch" ] [ HH.text "Wan 2.1 Sketch" ]
                , HH.option [ HP.value "wan21_ipadapter" ] [ HH.text "Wan 2.1 IP-Adapter" ]
                , HH.option [] [ HH.hr [] ]
                , HH.option [ HP.value "flux_dev" ] [ HH.text "Flux Dev" ]
                , HH.option [ HP.value "flux_schnell" ] [ HH.text "Flux Schnell" ]
                , HH.option [ HP.value "flux_fill" ] [ HH.text "Flux Fill" ]
                , HH.option [ HP.value "flux_realism" ] [ HH.text "Flux Realism" ]
                , HH.option [] [ HH.hr [] ]
                , HH.option [ HP.value "pixart_sigma" ] [ HH.text "Pixart Sigma" ]
                , HH.option [ HP.value "pixart_alpha" ] [ HH.text "Pixart Alpha" ]
                , HH.option [ HP.value "kolors" ] [ HH.text "Kolors" ]
                , HH.option [] [ HH.hr [] ]
                , HH.option [ HP.value "playground" ] [ HH.text "Playground" ]
                , HH.option [ HP.value "playground_v2" ] [ HH.text "Playground v2" ]
                ]
            ]
        , HH.div [ cls [ "lattice-form-group" ] ]
            [ HH.label [] [ HH.text "Resolution" ]
            , HH.select [ HE.onChange \s -> H.query_ (SetResolution (parseResolution s)) ]
                [ HH.option [ HP.value "512x512" ] [ HH.text "512×512" ]
                , HH.option [ HP.value "768x768" ] [ HH.text "768×768" ]
                , HH.option [ HP.value "1024x1024", HP.selected (state.resolution == Res1024x1024) ] [ HH.text "1024×1024" ]
                , HH.option [ HP.value "1024x576" ] [ HH.text "1024×576 (16:9)" ]
                , HH.option [ HP.value "576x1024" ] [ HH.text "576×1024 (9:16)" ]
                , HH.option [ HP.value "1920x1080" ] [ HH.text "1920×1080" ]
                , HH.option [ HP.value "1080x1920" ] [ HH.text "1080×1920" ]
                ]
            ]
        ]
    , HH.div [ cls [ "lattice-form-row" ] ]
        [ HH.div [ cls [ "lattice-form-group" ] ]
            [ HH.label [] [ HH.text "Sampler" ]
            , HH.select [ HE.onChange \s -> H.query_ (SetSampler (parseSampler s)) ]
                (renderSamplerOptions state.sampler)
            ]
        , HH.div [ cls [ "lattice-form-group" ] ]
            [ HH.label [] [ HH.text "Scheduler" ]
            , HH.select [ HE.onChange \s -> H.query_ (SetScheduler (parseScheduler s)) ]
                (renderSchedulerOptions state.scheduler)
            ]
        ]
    , HH.div [ cls [ "lattice-form-row" ] ]
        [ HH.div [ cls [ "lattice-form-group", "lattice-form-inline" ] ]
            [ HH.label [] [ HH.text "Steps" ]
            , HH.input
                [ HP.type_ HP.InputNumber
                , HP.value (show state.steps)
                , HP.min 1
                , HP.max 200
                , HE.onValueInput \s -> H.query_ (SetSteps (parseInt s 30))
                ]
            ]
        , HH.div [ cls [ "lattice-form-group", "lattice-form-inline" ] ]
            [ HH.label [] [ HH.text "CFG" ]
            , HH.input
                [ HP.type_ HP.InputNumber
                , HP.value (show state.cfgScale)
                , HP.min 1.0
                , HP.max 30.0
                , HP.step 0.5
                , HE.onValueInput \s -> H.query_ (SetCfgScale (parseFloat s 5.0))
                ]
            ]
        , HH.div [ cls [ "lattice-form-group", "lattice-form-inline" ] ]
            [ HH.label [] [ HH.text "Seed" ]
            , HH.input
                [ HP.type_ HP.InputNumber
                , HP.value (show state.seed)
                , HP.min 0
                , HP.max 2147483647
                , HE.onValueInput \s -> H.query_ (SetSeed (parseInt s 0))
                ]
            , HH.button [ cls [ "lattice-btn-icon" ], HE.onClick \_ -> H.query_ RandomizeSeed ] [ HH.text "🎲" ]
            ]
        ]
    ]

renderSamplerOptions :: forall m. Sampler -> Array (H.ComponentHTML Query () m)
renderSamplerOptions current =
  let samplerOptions = 
        [ ("res_2m", "RES 2M (multistep)", S_res_2m)
        , ("res_3m", "RES 3M (multistep)", S_res_3m)
        , ("res_2s", "RES 2S (singlestep)", S_res_2s)
        , ("res_3m_sde", "RES 3M SDE", S_res_3m_sde)
        , ("res_2s_sde", "RES 2S SDE", S_res_2s_sde)
        , ("res_3s_sde", "RES 3S SDE", S_res_3s_sde)
        , ("dpmpp_2m", "DPM++ 2M", S_dpmpp_2m)
        , ("dpmpp_3m", "DPM++ 3M", S_dpmpp_3m)
        , ("dpmpp_2s", "DPM++ 2S", S_dpmpp_2s)
        , ("dpmpp_sde_2s", "DPM++ SDE 2S", S_dpmpp_sde_2s)
        , ("dpmpp_3s", "DPM++ 3S", S_dpmpp_3s)
        , ("euler", "Euler", S_euler)
        , ("euler_ancestral", "Euler Ancestral", S_euler_ancestral)
        , ("euler_a", "Euler A", S_euler_a)
        , ("deis_2m", "DEIS 2M", S_deis_2m)
        , ("deis_3m", "DEIS 3M", S_deis_3m)
        , ("deis_4m", "DEIS 4M", S_deis_4m)
        , ("etdrk2_2s", "ETDRK2 2S", S_etdrk2_2s)
        , ("etdrk3_a_3s", "ETDRK3-A 3S", S_etdrk3_a_3s)
        , ("etdrk3_b_3s", "ETDRK3-B 3S", S_etdrk3_b_3s)
        , ("etdrk4_4s", "ETDRK4 4S", S_etdrk4_4s)
        , ("etdrk4_4s_alt", "ETDRK4 4S Alt", S_etdrk4_4s_alt)
        , ("unipc", "UniPC", S_unipc)
        , ("unipc_snr", "UniPC SNR", S_unipc_snr)
        , ("ddim", "DDIM", S_ddim)
        , ("plms", "PLMS", S_plms)
        , ("lms", "LMS", S_lms)
        , ("kdpm_2_ancestral", "KDPM 2 Ancestral", S_kdpm_2_ancestral)
        , ("kdpm_2", "KDPM 2", S_kdpm_2)
        , ("icv_ieks", "ICV IEKS", S_icv_ieks)
        , ("tcd", "TCD", S_tcd)
        ]
  in map (\(val, label, sampler) -> 
          HH.option [ HP.value val, HP.selected (sampler == current) ] [ HH.text label ]
        ) samplerOptions

renderSchedulerOptions :: forall m. Scheduler -> Array (H.ComponentHTML Query () m)
renderSchedulerOptions current =
  let schedulerOptions =
        [ ("normal", "Normal", Sch_normal)
        , ("beta57", "Beta 57", Sch_beta57)
        , ("karras", "Karras", Sch_karras)
        , ("exponential", "Exponential", Sch_exponential)
        , ("shifted_linear", "Shifted Linear", Sch_shifted_linear)
        , ("sqrt_linear", "Sqrt Linear", Sch_sqrt_linear)
        , ("linear", "Linear", Sch_linear)
        , ("linear_quadratic", "Linear Quadratic", Sch_linear_quadratic)
        , ("simple", "Simple", Sch_simple)
        , ("sgm_uniform", "SGM Uniform", Sch_sgm_uniform)
        , ("ddim_uniform", "DDIM Uniform", Sch_ddim_uniform)
        , ("kl_optimal", "KL Optimal", Sch_kl_optimal)
        ]
  in map (\(val, label, scheduler) ->
          HH.option [ HP.value val, HP.selected (scheduler == current) ] [ HH.text label ]
        ) schedulerOptions

renderControlNetSection :: forall m. MonadAff m => State -> H.ComponentHTML Query () m
renderControlNetSection state =
  HH.div [ cls [ "lattice-generate-controlnet" ] ]
    [ HH.text "ControlNet Conditioning"
    , HH.div [ cls [ "lattice-form-row" ] ]
        [ HH.div [ cls [ "lattice-form-group" ] ]
            [ HH.label [] [ HH.text "Control Type" ]
            , HH.select [ HE.onChange \s -> H.query_ (SetControlNet (parseControlNet s)) ]
                [ HH.option [ HP.value "none", HP.selected (state.controlNet == ControlNone) ] [ HH.text "None" ]
                , HH.option [ HP.value "depth", HP.selected (state.controlNet == ControlDepth) ] [ HH.text "Depth" ]
                , HH.option [ HP.value "canny", HP.selected (state.controlNet == ControlCanny) ] [ HH.text "Canny Edge" ]
                , HH.option [ HP.value "lineart", HP.selected (state.controlNet == ControlLineart) ] [ HH.text "Line Art" ]
                , HH.option [ HP.value "softedge", HP.selected (state.controlNet == ControlSoftEdge) ] [ HH.text "Soft Edge" ]
                , HH.option [ HP.value "normal", HP.selected (state.controlNet == ControlNormal) ] [ HH.text "Normal Map" ]
                , HH.option [ HP.value "scribble", HP.selected (state.controlNet == ControlScribble) ] [ HH.text "Scribble" ]
                , HH.option [ HP.value "seg", HP.selected (state.controlNet == ControlSeg) ] [ HH.text "Segmentation" ]
                , HH.option [ HP.value "pose", HP.selected (state.controlNet == ControlPose) ] [ HH.text "OpenPose" ]
                , HH.option [ HP.value "ipadapter", HP.selected (state.controlNet == ControlIPAdapter) ] [ HH.text "IP-Adapter" ]
                ]
            ]
        ]
    , HH.div [ cls [ "lattice-form-row" ] ]
        [ HH.div [ cls [ "lattice-form-group", "lattice-form-inline" ] ]
            [ HH.label [] [ HH.text "Strength" ]
            , HH.input
                [ HP.type_ HP.InputNumber
                , HP.value (show state.controlNetStrength)
                , HP.min 0.0
                , HP.max 1.0
                , HP.step 0.05
                ]
            ]
        , HH.div [ cls [ "lattice-form-group", "lattice-form-inline" ] ]
            [ HH.label [] [ HH.text "Start Step" ]
            , HH.input
                [ HP.type_ HP.InputNumber
                , HP.value (show state.controlNetStartStep)
                , HP.min 0.0
                , HP.max 1.0
                , HP.step 0.05
                ]
            ]
        , HH.div [ cls [ "lattice-form-group", "lattice-form-inline" ] ]
            [ HH.label [] [ HH.text "End Step" ]
            , HH.input
                [ HP.type_ HP.InputNumber
                , HP.value (show state.controlNetEndStep)
                , HP.min 0.0
                , HP.max 1.0
                , HP.step 0.05
                ]
            ]
        ]
    , HH.div [ cls [ "lattice-form-row" ] ]
        [ HH.div [ cls [ "lattice-form-group", "lattice-form-inline" ] ]
            [ HH.label [] [ HH.text "Start Frame" ]
            , HH.input
                [ HP.type_ HP.InputNumber
                , HP.value (show state.controlNetStartFrame)
                , HP.min 0
                , HP.step 1
                ]
            ]
        , HH.div [ cls [ "lattice-form-group", "lattice-form-inline" ] ]
            [ HH.label [] [ HH.text "End Frame" ]
            , HH.input
                [ HP.type_ HP.InputNumber
                , HP.value (show state.controlNetEndFrame)
                , HP.min 0
                , HP.step 1
                ]
            ]
        ]
    , HH.div [ cls [ "lattice-form-group" ] ]
        [ HH.label [] [ HH.text "Control Image" ]
        , HH.input
            [ HP.type_ HP.InputText
            , HP.placeholder "Paste image URL or drop file..."
            , HP.value (fromMaybe "" state.controlNetImage)
            ]
        ]
    ]

renderAdvancedSection :: forall m. MonadAff m => State -> H.ComponentHTML Query () m
renderAdvancedSection state =
  HH.div [ cls [ "lattice-generate-advanced" ] ]
    [ HH.text "Advanced Settings"
    , HH.div [ cls [ "lattice-form-row" ] ]
        [ HH.div [ cls [ "lattice-form-group", "lattice-form-inline" ] ]
            [ HH.label [] [ HH.text "η (Eta)" ]
            , HH.input
                [ HP.type_ HP.InputNumber
                , HP.value (show state.eta)
                , HP.min 0.0
                , HP.max 2.0
                , HP.step 0.1
                ]
            ]
        , HH.div [ cls [ "lattice-form-group", "lattice-form-inline" ] ]
            [ HH.label [] [ HH.text "σ min" ]
            , HH.input [ HP.value (show state.sigmaMin) ]
            ]
        , HH.div [ cls [ "lattice-form-group", "lattice-form-inline" ] ]
            [ HH.label [] [ HH.text "σ max" ]
            , HH.input [ HP.value (show state.sigmaMax) ]
            ]
        , HH.div [ cls [ "lattice-form-group", "lattice-form-inline" ] ]
            [ HH.label [] [ HH.text "ρ" ]
            , HH.input [ HP.value (show state.rho) ]
            ]
        ]
    ]

renderPreviewSection :: forall m. MonadAff m => State -> H.ComponentHTML Query () m
renderPreviewSection state =
  HH.div [ cls [ "lattice-generate-preview" ] ]
    [ HH.div [ cls [ "lattice-preview-header" ] ] 
        [ HH.text "Preview" 
        , HH.text (state.stage <> " - " <> show state.progress <> "%")
        ]
    , HH.div [ cls [ "lattice-preview-content" ] ]
        [ case state.previewUrl of
            Just url -> HH.img [ HP.src url ]
            Nothing -> HH.text "No preview yet"
        ]
    , HH.div [ cls [ "lattice-progress-bar" ] ]
        [ HH.div [ cls [ "lattice-progress-fill" ], HP.style ("width: " <> show state.progress <> "%") ] [] ]
    ]

renderActionButtons :: forall m. MonadAff m => State -> H.ComponentHTML Query () m
renderActionButtons state =
  HH.div [ cls [ "lattice-generate-actions" ] ]
    [ if state.isGenerating 
        then HH.button [ cls [ "lattice-btn-danger" ], HE.onClick \_ -> H.query_ CancelGeneration ] 
            [ HH.text "Cancel" ]
        else HH.button [ cls [ "lattice-btn-primary" ], HE.onClick \_ -> H.query_ StartGeneration ] 
            [ HH.text "Generate" ]
    ]

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                  // actions
-- ═══════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Query ~> H.HalogenM State Query () Output m
handleAction = case _ of
  SetMode mode a -> do
    H.modify_ _ { mode = mode }
    pure a

  SetPrompt prompt a -> do
    H.modify_ _ { prompt = prompt }
    pure a

  SetNegativePrompt np a -> do
    H.modify_ _ { negativePrompt = np }
    pure a

  SetSampler sampler a -> do
    H.modify_ _ { sampler = sampler }
    pure a

  SetScheduler scheduler a -> do
    H.modify_ _ { scheduler = scheduler }
    pure a

  SetSteps steps a -> do
    H.modify_ _ { steps = steps }
    pure a

  SetCfgScale cfg a -> do
    H.modify_ _ { cfgScale = cfg }
    pure a

  SetSeed seed a -> do
    H.modify_ _ { seed = seed }
    pure a

  SetModel model a -> do
    H.modify_ _ { model = model }
    pure a

  SetResolution resolution a -> do
    H.modify_ _ { resolution = resolution }
    pure a

  RandomizeSeed a -> do
    instant <- liftEffect now
    let (Milliseconds ms) = unInstant instant
    let newSeed = round ms `mod` 2147483647
    H.modify_ _ { seed = newSeed }
    pure a

  StartGeneration a -> do
    state <- H.get
    case state.bridgeClient of
      Nothing -> do
        H.modify_ _ { isGenerating = false, error = Just "Backend not connected" }
        pure a
      Just client -> do
        H.modify_ _ { isGenerating = true, progress = 0.0, stage = "encoding", error = Nothing }
        let config = buildGenerateConfig state
        result <- liftAff $ case state.mode of
          GenTextToImage -> Bridge.generateImage client config
          GenImageToVideo -> Bridge.generateVideo client config
          GenTextToVideo -> Bridge.generateVideo client config
          GenImageToImage -> Bridge.generateImage client config
          GenInpaint -> Bridge.generateImage client config
          GenOutpaint -> Bridge.generateImage client config
          GenUpscale -> Bridge.generateImage client config
          GenRemoveBackground -> Bridge.generateImage client config
        case result of
          Left err -> do
            H.modify_ _ { isGenerating = false, error = Just err, stage = "idle" }
            H.raise (GenerationError err)
          Right genResult ->
            if genResult.success
              then do
                let previewUrl = case genResult.frames of
                      [] -> Nothing
                      frames -> Just ("data:image/png;base64," <> headOrLast frames)
                H.modify_ _ 
                  { isGenerating = false
                  , progress = 100.0
                  , stage = "idle"
                  , previewUrl = previewUrl
                  , error = Nothing
                  }
                let layerType = genModeToLayerType state.mode
                let genData = GenerationData
                      { prompt: state.prompt
                      , negativePrompt: state.negativePrompt
                      , model: state.model
                      , sampler: state.sampler
                      , scheduler: state.scheduler
                      , steps: state.steps
                      , cfgScale: state.cfgScale
                      , seed: genResult.seed
                      , resolution: state.resolution
                      , eta: state.eta
                      , sigmaMin: state.sigmaMin
                      , sigmaMax: state.sigmaMax
                      , rho: state.rho
                      }
                let result_ = GenerationResult
                      { layerId: ""
                      , layerType: layerType
                      , name: state.prompt
                      , previewUrl: fromMaybe "" previewUrl
                      , width: resolutionWidth state.resolution
                      , height: resolutionHeight state.resolution
                      , frames: 1
                      , data: genData
                      }
                H.raise (GenerationComplete result_)
              else do
                let errMsg = fromMaybe "Generation failed" genResult.error
                H.modify_ _ { isGenerating = false, error = Just errMsg, stage = "idle" }
                H.raise (GenerationError errMsg)
        pure a

  CancelGeneration a -> do
    H.modify_ _ { isGenerating = false, stage = "idle", progress = 0.0 }
    pure a

  SetControlNet cn a -> do
    H.modify_ _ { controlNet = cn }
    pure a

  SetControlNetStrength s a -> do
    H.modify_ _ { controlNetStrength = s }
    pure a

  SetControlNetImage img a -> do
    H.modify_ _ { controlNetImage = if img == "" then Nothing else Just img }
    pure a

  SetControlNetStartStep s a -> do
    H.modify_ _ { controlNetStartStep = s }
    pure a

  SetControlNetEndStep s a -> do
    H.modify_ _ { controlNetEndStep = s }
    pure a

  SetControlNetStartFrame f a -> do
    H.modify_ _ { controlNetStartFrame = f }
    pure a

  SetControlNetEndFrame f a -> do
    H.modify_ _ { controlNetEndFrame = f }
    pure a

handleQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Query () Output m (Maybe a)
handleQuery = case _ of
  SetMode mode a -> do
    H.modify_ _ { mode = mode }
    pure (Just a)
  SetPrompt prompt a -> do
    H.modify_ _ { prompt = prompt }
    pure (Just a)
  SetNegativePrompt np a -> do
    H.modify_ _ { negativePrompt = np }
    pure (Just a)
  SetSampler sampler a -> do
    H.modify_ _ { sampler = sampler }
    pure (Just a)
  SetScheduler scheduler a -> do
    H.modify_ _ { scheduler = scheduler }
    pure (Just a)
  SetSteps steps a -> do
    H.modify_ _ { steps = steps }
    pure (Just a)
  SetCfgScale cfg a -> do
    H.modify_ _ { cfgScale = cfg }
    pure (Just a)
  SetSeed seed a -> do
    H.modify_ _ { seed = seed }
    pure (Just a)
  SetModel model a -> do
    H.modify_ _ { model = model }
    pure (Just a)
  SetResolution resolution a -> do
    H.modify_ _ { resolution = resolution }
    pure (Just a)
  RandomizeSeed a -> do
    H.modify_ _ { seed = 0 }
    pure (Just a)
  StartGeneration a -> do
    pure (Just a)
  CancelGeneration a -> do
    pure (Just a)
  SetControlNet cn a -> do
    H.modify_ _ { controlNet = cn }
    pure (Just a)
  SetControlNetStrength s a -> do
    H.modify_ _ { controlNetStrength = s }
    pure (Just a)
  SetControlNetImage img a -> do
    H.modify_ _ { controlNetImage = if img == "" then Nothing else Just img }
    pure (Just a)
  SetControlNetStartStep s a -> do
    H.modify_ _ { controlNetStartStep = s }
    pure (Just a)
  SetControlNetEndStep s a -> do
    H.modify_ _ { controlNetEndStep = s }
    pure (Just a)
  SetControlNetStartFrame f a -> do
    H.modify_ _ { controlNetStartFrame = f }
    pure (Just a)
  SetControlNetEndFrame f a -> do
    H.modify_ _ { controlNetEndFrame = f }
    pure (Just a)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                  // helpers
-- ════════════════════════════════════════════════════════════════════════════

parseModel :: String -> Model
parseModel = case _ of
  "sd15" -> ModelSD15
  "sd21" -> ModelSD21
  "sdxl" -> ModelSDXL
  "sdxl_turbo" -> ModelSDXL_Turbo
  "sdxl_lightning" -> ModelSDXL_Lightning
  "wan20_i2v" -> ModelWan20I2V
  "wan20_t2v" -> ModelWan20T2V
  "wan20_i2i" -> ModelWan20I2I
  "wan21_i2v" -> ModelWan21I2V
  "wan21_t2v" -> ModelWan21T2V
  "wan21_i2i" -> ModelWan21I2I
  "wan21_canny" -> ModelWan21Canny
  "wan21_depth" -> ModelWan21Depth
  "wan21_pose" -> ModelWan21Pose
  "wan21_sketch" -> ModelWan21Sketch
  "wan21_ipadapter" -> ModelWan21IPAdapter
  "flux_dev" -> ModelFluxDev
  "flux_schnell" -> ModelFluxSchnell
  "flux_fill" -> ModelFluxFill
  "flux_realism" -> ModelFluxRealism
  "pixart_sigma" -> ModelPixartSigma
  "pixart_alpha" -> ModelPixartAlpha
  "kolors" -> ModelKolors
  "playground" -> ModelPlayground
  "playground_v2" -> ModelPlaygroundV2
  _ -> ModelSDXL
  _ -> ModelSDXL

parseResolution :: String -> Resolution
parseResolution = case _ of
  "512x512" -> Res512x512
  "768x768" -> Res768x768
  "1024x1024" -> Res1024x1024
  "1024x576" -> Res1024x576
  "576x1024" -> Res576x1024
  "1280x720" -> Res1280x720
  "1920x1080" -> Res1920x1080
  "1080x1920" -> Res1080x1920
  "2048x1152" -> Res2048x1152
  "2560x1440" -> Res2560x1440
  "832x1512" -> Res832x1512
  "720x1280" -> Res720x1280
  _ -> Res1024x1024

parseSampler :: String -> Sampler
parseSampler = case _ of
  "res_2m" -> S_res_2m
  "res_3m" -> S_res_3m
  "res_2s" -> S_res_2s
  "res_3m_sde" -> S_res_3m_sde
  "res_2s_sde" -> S_res_2s_sde
  "res_3s_sde" -> S_res_3s_sde
  "dpmpp_2m" -> S_dpmpp_2m
  "dpmpp_3m" -> S_dpmpp_3m
  "dpmpp_2s" -> S_dpmpp_2s
  "dpmpp_sde_2s" -> S_dpmpp_sde_2s
  "dpmpp_3s" -> S_dpmpp_3s
  "euler" -> S_euler
  "euler_ancestral" -> S_euler_ancestral
  "euler_a" -> S_euler_a
  "deis_2m" -> S_deis_2m
  "deis_3m" -> S_deis_3m
  "deis_4m" -> S_deis_4m
  "etdrk2_2s" -> S_etdrk2_2s
  "etdrk3_a_3s" -> S_etdrk3_a_3s
  "etdrk3_b_3s" -> S_etdrk3_b_3s
  "etdrk4_4s" -> S_etdrk4_4s
  "etdrk4_4s_alt" -> S_etdrk4_4s_alt
  "unipc" -> S_unipc
  "unipc_snr" -> S_unipc_snr
  "ddim" -> S_ddim
  "plms" -> S_plms
  "lms" -> S_lms
  "kdpm_2_ancestral" -> S_kdpm_2_ancestral
  "kdpm_2" -> S_kdpm_2
  "icv_ieks" -> S_icv_ieks
  "tcd" -> S_tcd
  _ -> S_res_2m

parseScheduler :: String -> Scheduler
parseScheduler = case _ of
  "normal" -> Sch_normal
  "beta57" -> Sch_beta57
  "karras" -> Sch_karras
  "exponential" -> Sch_exponential
  "shifted_linear" -> Sch_shifted_linear
  "sqrt_linear" -> Sch_sqrt_linear
  "linear" -> Sch_linear
  "linear_quadratic" -> Sch_linear_quadratic
  "simple" -> Sch_simple
  "sgm_uniform" -> Sch_sgm_uniform
  "ddim_uniform" -> Sch_ddim_uniform
  "kl_optimal" -> Sch_kl_optimal
  _ -> Sch_normal

parseControlNet :: String -> ControlNet
parseControlNet = case _ of
  "none" -> ControlNone
  "depth" -> ControlDepth
  "canny" -> ControlCanny
  "lineart" -> ControlLineart
  "softedge" -> ControlSoftEdge
  "normal" -> ControlNormal
  "scribble" -> ControlScribble
  "seg" -> ControlSeg
  "pose" -> ControlPose
  "ipadapter" -> ControlIPAdapter
  _ -> ControlNone

controlNetToString :: ControlNet -> String
controlNetToString = case _ of
  ControlNone -> "none"
  ControlDepth -> "depth"
  ControlCanny -> "canny"
  ControlLineart -> "lineart"
  ControlSoftEdge -> "softedge"
  ControlNormal -> "normal"
  ControlScribble -> "scribble"
  ControlSeg -> "seg"
  ControlPose -> "pose"
  ControlIPAdapter -> "ipadapter"

parseInt :: String -> Int -> Int
parseInt s def = case s of
  "" -> def
  _ -> def

parseFloat :: String -> Number -> Number
parseFloat s def = case s of
  "" -> def
  _ -> def

buildGenerateConfig :: State -> Bridge.GenerateConfig
buildGenerateConfig state =
  { prompt: state.prompt
  , negativePrompt: if state.negativePrompt == "" then Nothing else Just state.negativePrompt
  , width: state.compositionWidth
  , height: state.compositionHeight
  , numFrames: case state.mode of
      GenTextToImage -> Nothing
      GenImageToVideo -> Just state.numFrames
      GenTextToVideo -> Just state.numFrames
      _ -> Nothing
  , fps: Just (toNumber state.fps)
  , model: modelToString state.model
  , seed: Just state.seed
  , steps: Just state.steps
  , cfgScale: Just state.cfgScale
  , controlnetImage: case state.controlNet of
      ControlNone -> Nothing
      _ -> state.controlNetImage
  , controlnetType: case state.controlNet of
      ControlNone -> Nothing
      _ -> Just (controlNetToString state.controlNet)
  , controlnetStrength: case state.controlNet of
      ControlNone -> Nothing
      _ -> Just state.controlNetStrength
  , controlnetStartStep: case state.controlNet of
      ControlNone -> Nothing
      _ -> Just state.controlNetStartStep
  , controlnetEndStep: case state.controlNet of
      ControlNone -> Nothing
      _ -> Just state.controlNetEndStep
  , controlnetStartFrame: case state.controlNet of
      ControlNone -> Nothing
      _ -> Just state.controlNetStartFrame
  , controlnetEndFrame: case state.controlNet of
      ControlNone -> Nothing
      _ -> Just state.controlNetEndFrame
  }

genModeToLayerType :: GenMode -> LayerType
genModeToLayerType = case _ of
  GenTextToImage -> LTTextToImage
  GenImageToVideo -> LTImageToVideo
  GenTextToVideo -> LTTextToVideo
  GenImageToImage -> LTImageToImage
  GenInpaint -> LTInpaint
  GenOutpaint -> LTOutpaint
  GenUpscale -> LTUpscale
  GenRemoveBackground -> LTRemoveBackground

resolutionWidth :: Resolution -> Int
resolutionWidth = case _ of
  Res512x512 -> 512
  Res768x768 -> 768
  Res1024x1024 -> 1024
  Res1024x576 -> 1024
  Res576x1024 -> 576
  Res1280x720 -> 1280
  Res1920x1080 -> 1920
  Res1080x1920 -> 1080
  Res2048x1152 -> 2048
  Res2560x1440 -> 2560
  Res832x1512 -> 832
  Res720x1280 -> 720

resolutionHeight :: Resolution -> Int
resolutionHeight = case _ of
  Res512x512 -> 512
  Res768x768 -> 768
  Res1024x1024 -> 1024
  Res1024x576 -> 576
  Res576x1024 -> 1024
  Res1280x720 -> 720
  Res1920x1080 -> 1080
  Res1080x1920 -> 1920
  Res2048x1152 -> 1152
  Res2560x1440 -> 1440
  Res832x1512 -> 1512
  Res720x1280 -> 1280

modelToString :: Model -> String
modelToString = case _ of
  ModelSD15 -> "sd15"
  ModelSD21 -> "sd21"
  ModelSDXL -> "sdxl"
  ModelSDXL_Turbo -> "sdxl_turbo"
  ModelSDXL_Lightning -> "sdxl_lightning"
  ModelWan20I2V -> "wan20_i2v"
  ModelWan20T2V -> "wan20_t2v"
  ModelWan20I2I -> "wan20_i2i"
  ModelWan21I2V -> "wan21_i2v"
  ModelWan21T2V -> "wan21_t2v"
  ModelWan21I2I -> "wan21_i2i"
  ModelWan21Canny -> "wan21_canny"
  ModelWan21Depth -> "wan21_depth"
  ModelWan21Pose -> "wan21_pose"
  ModelWan21Sketch -> "wan21_sketch"
  ModelWan21IPAdapter -> "wan21_ipadapter"
  ModelFluxDev -> "flux_dev"
  ModelFluxSchnell -> "flux_schnell"
  ModelFluxFill -> "flux_fill"
  ModelFluxRealism -> "flux_realism"
  ModelPixartSigma -> "pixart_sigma"
  ModelPixartAlpha -> "pixart_alpha"
  ModelKolors -> "kolors"
  ModelPlayground -> "playground"
  ModelPlaygroundV2 -> "playground_v2"

headOrLast :: Array String -> String
headOrLast arr = case arr of
  [] -> ""
  [x] -> x
  xs -> fromMaybe "" (Array.last xs)
