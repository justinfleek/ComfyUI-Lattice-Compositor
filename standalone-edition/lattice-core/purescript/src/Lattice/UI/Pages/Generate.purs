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

import Data.Array (length, filter, cons)
import Data.Either (Either(..))
import Data.Int (toNumber)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String (joinWith)
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Effect (Effect)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Type.Proxy (Proxy(..))

import Lattice.UI.Core (cls)
import Lattice.Services.Bridge.Client as Bridge

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
  | ModelWan22I2V -- Wan 2.1 I2V
  | ModelWan22T2V -- Wan 2.1 T2V
  | ModelFluxDev  -- Flux Dev
  | ModelFluxSchnell

derive instance eqModel :: Eq Model

-- | Resolution presets
data Resolution
  = Res512x512
  | Res768x768
  | Res1024x1024
  | Res1024x576  -- 16:9
  | Res576x1024  -- 9:16
  | Res1920x1080 -- Full HD
  | Res1080x1920 -- Full HD vertical

derive instance eqResolution :: Eq Resolution

-- | Component state
type State =
  { -- Mode
    mode :: GenMode
    -- Prompt
  , prompt :: String
  , negativePrompt :: String
    -- Source image (for I2V, I2I, Inpaint, Outpaint)
  , sourceImage :: Maybe String  -- Base64 or URL
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
  }

-- | Input
type Input = 
  { mode :: GenMode
  , bridgeClient :: Maybe Bridge.BridgeClient
  }

-- | Output
type Output = 
  { layerCreated :: String  -- Layer ID
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
  | RandomizeSeed a
  | StartGeneration a
  | CancelGeneration a

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // component
-- ════════════════════════════════════════════════════════════════════════════

component :: forall q i o m. MonadAff m => H.Component q i o m
component = H.mkComponent
  { initialState: const initialState
  , render
  , eval: H.mkEval H.defaultEval
      { handleAction = handleAction
      , handleQuery = handleQuery
      }
  }

initialState :: State
initialState =
  { mode: GenTextToImage
  , prompt: ""
  , negativePrompt: "blurry, low quality, distorted, deformed, ugly"
  , sourceImage: Nothing
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
  , bridgeClient: Nothing
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
                , HH.option [ HP.value "wan22_i2v" ] [ HH.text "Wan 2.1 I2V" ]
                , HH.option [ HP.value "wan22_t2v" ] [ HH.text "Wan 2.1 T2V" ]
                , HH.option [ HP.value "flux_dev" ] [ HH.text "Flux Dev" ]
                , HH.option [ HP.value "flux_schnell" ] [ HH.text "Flux Schnell" ]
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
    now <- liftEffect nowTime
    let newSeed = mod now 2147483647
    H.modify_ _ { seed = newSeed }
    pure a
  where
    nowTime :: Effect Int
    nowTime = pure 0  -- Placeholder - actual implementation uses Date.now()

  StartGeneration a -> do
    H.modify_ _ { isGenerating = true, progress = 0.0, stage = "encoding", error = Nothing }
    pure a

  CancelGeneration a -> do
    H.modify_ _ { isGenerating = false, stage = "idle", progress = 0.0 }
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

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                  // helpers
-- ════════════════════════════════════════════════════════════════════════════

parseModel :: String -> Model
parseModel = case _ of
  "sd15" -> ModelSD15
  "sd21" -> ModelSD21
  "sdxl" -> ModelSDXL
  "sdxl_turbo" -> ModelSDXL_Turbo
  "wan22_i2v" -> ModelWan22I2V
  "wan22_t2v" -> ModelWan22T2V
  "flux_dev" -> ModelFluxDev
  "flux_schnell" -> ModelFluxSchnell
  _ -> ModelSDXL

parseResolution :: String -> Resolution
parseResolution = case _ of
  "512x512" -> Res512x512
  "768x768" -> Res768x768
  "1024x1024" -> Res1024x1024
  "1024x576" -> Res1024x576
  "576x1024" -> Res576x1024
  "1920x1080" -> Res1920x1080
  "1080x1920" -> Res1080x1920
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

parseInt :: String -> Int -> Int
parseInt s def = case s of
  "" -> def
  _ -> def

parseFloat :: String -> Number -> Number
parseFloat s def = case s of
  "" -> def
  _ -> def
