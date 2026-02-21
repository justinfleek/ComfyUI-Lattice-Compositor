-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- generate // render
-- render functions for the AI generation page
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
module Lattice.UI.Pages.Generate.Render
  ( render
  ) where

import Prelude

import Data.Maybe (Maybe(..), fromMaybe, isJust)
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP

import Lattice.UI.Core (cls)
import Lattice.UI.Pages.Generate.Types as Types
import Lattice.UI.Pages.Generate.Helpers as Helpers

-- ═══════════════════════════════════════════════════════════════════════════
--                                                               // main render
-- ═══════════════════════════════════════════════════════════════════════════

render :: forall m. MonadAff m => Types.State -> H.ComponentHTML Types.Action Types.Slots m
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

-- ═══════════════════════════════════════════════════════════════════════════
--                                                          // mode selector
-- ═══════════════════════════════════════════════════════════════════════════

renderModeSelector :: forall m. MonadAff m => Types.State -> H.ComponentHTML Types.Action Types.Slots m
renderModeSelector state =
  HH.div [ cls [ "lattice-generate-mode-selector" ] ]
    [ HH.text "Mode: "
    , modeButton state Types.GenTextToImage "T2I"
    , modeButton state Types.GenImageToVideo "I2V"
    , modeButton state Types.GenTextToVideo "T2V"
    , modeButton state Types.GenImageToImage "I2I"
    , modeButton state Types.GenInpaint "Inpaint"
    , modeButton state Types.GenUpscale "Upscale"
    ]

modeButton :: forall m. MonadAff m => Types.State -> Types.GenMode -> String -> H.ComponentHTML Types.Action Types.Slots m
modeButton state mode label =
  HH.button 
    [ cls [ "mode-btn", if state.mode == mode then "active" else "" ] 
    , HE.onClick \_ -> Types.SetMode mode
    ] 
    [ HH.text label ]

-- ═══════════════════════════════════════════════════════════════════════════
--                                                          // prompt section
-- ═══════════════════════════════════════════════════════════════════════════

renderPromptSection :: forall m. MonadAff m => Types.State -> H.ComponentHTML Types.Action Types.Slots m
renderPromptSection state =
  HH.div [ cls [ "lattice-generate-prompt-section" ] ]
    [ HH.div [ cls [ "lattice-form-group" ] ]
        [ HH.label [] [ HH.text "Prompt" ]
        , HH.textarea
            [ HP.value state.prompt
            , HP.placeholder "Describe what you want to generate..."
            , HP.rows 4
            , HE.onValueInput \s -> Types.SetPrompt s
            ]
        ]
    , HH.div [ cls [ "lattice-form-group" ] ]
        [ HH.label [] [ HH.text "Negative Prompt" ]
        , HH.textarea
            [ HP.value state.negativePrompt
            , HP.placeholder "What to avoid..."
            , HP.rows 2
            , HE.onValueInput \s -> Types.SetNegativePrompt s
            ]
        ]
    ]

-- ═══════════════════════════════════════════════════════════════════════════
--                                                        // settings section
-- ═══════════════════════════════════════════════════════════════════════════

renderSettingsSection :: forall m. MonadAff m => Types.State -> H.ComponentHTML Types.Action Types.Slots m
renderSettingsSection state =
  HH.div [ cls [ "lattice-generate-settings" ] ]
    [ -- model and resolution row
      HH.div [ cls [ "lattice-form-row" ] ]
        [ renderModelSelect state
        , renderResolutionSelect state
        ]
    -- sampler and scheduler row
    , HH.div [ cls [ "lattice-form-row" ] ]
        [ renderSamplerSelect state
        , renderSchedulerSelect state
        ]
    -- steps, cfg, seed row
    , HH.div [ cls [ "lattice-form-row" ] ]
        [ renderStepsInput state
        , renderCfgInput state
        , renderSeedInput state
        ]
    ]

renderModelSelect :: forall m. MonadAff m => Types.State -> H.ComponentHTML Types.Action Types.Slots m
renderModelSelect state =
  HH.div [ cls [ "lattice-form-group" ] ]
    [ HH.label [] [ HH.text "Model" ]
    , HH.select [ HE.onValueChange \s -> Types.SetModel (Helpers.parseModel s) ]
        [ HH.option [ HP.value "sd15" ] [ HH.text "Stable Diffusion 1.5" ]
        , HH.option [ HP.value "sd21" ] [ HH.text "Stable Diffusion 2.1" ]
        , HH.option [ HP.value "sdxl", HP.selected (state.model == Types.ModelSDXL) ] [ HH.text "SDXL 1.0" ]
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

renderResolutionSelect :: forall m. MonadAff m => Types.State -> H.ComponentHTML Types.Action Types.Slots m
renderResolutionSelect state =
  HH.div [ cls [ "lattice-form-group" ] ]
    [ HH.label [] [ HH.text "Resolution" ]
    , HH.select [ HE.onValueChange \s -> Types.SetResolution (Helpers.parseResolution s) ]
        [ HH.option [ HP.value "512x512" ] [ HH.text "512x512" ]
        , HH.option [ HP.value "768x768" ] [ HH.text "768x768" ]
        , HH.option [ HP.value "1024x1024", HP.selected (state.resolution == Types.Res1024x1024) ] 
            [ HH.text "1024x1024" ]
        , HH.option [ HP.value "1024x576" ] [ HH.text "1024x576 (16:9)" ]
        , HH.option [ HP.value "576x1024" ] [ HH.text "576x1024 (9:16)" ]
        , HH.option [ HP.value "1920x1080" ] [ HH.text "1920x1080" ]
        , HH.option [ HP.value "1080x1920" ] [ HH.text "1080x1920" ]
        ]
    ]

renderSamplerSelect :: forall m. MonadAff m => Types.State -> H.ComponentHTML Types.Action Types.Slots m
renderSamplerSelect state =
  HH.div [ cls [ "lattice-form-group" ] ]
    [ HH.label [] [ HH.text "Sampler" ]
    , HH.select [ HE.onValueChange \s -> Types.SetSampler (Helpers.parseSampler s) ]
        (renderSamplerOptions state.sampler)
    ]

renderSchedulerSelect :: forall m. MonadAff m => Types.State -> H.ComponentHTML Types.Action Types.Slots m
renderSchedulerSelect state =
  HH.div [ cls [ "lattice-form-group" ] ]
    [ HH.label [] [ HH.text "Scheduler" ]
    , HH.select [ HE.onValueChange \s -> Types.SetScheduler (Helpers.parseScheduler s) ]
        (renderSchedulerOptions state.scheduler)
    ]

renderStepsInput :: forall m. MonadAff m => Types.State -> H.ComponentHTML Types.Action Types.Slots m
renderStepsInput state =
  HH.div [ cls [ "lattice-form-group", "lattice-form-inline" ] ]
    [ HH.label [] [ HH.text "Steps" ]
    , HH.input
        [ HP.type_ HP.InputNumber
        , HP.value (show state.steps)
        , HP.min 1.0
        , HP.max 200.0
        , HE.onValueInput \s -> Types.SetSteps (Helpers.parseInt s 30)
        ]
    ]

renderCfgInput :: forall m. MonadAff m => Types.State -> H.ComponentHTML Types.Action Types.Slots m
renderCfgInput state =
  HH.div [ cls [ "lattice-form-group", "lattice-form-inline" ] ]
    [ HH.label [] [ HH.text "CFG" ]
    , HH.input
        [ HP.type_ HP.InputNumber
        , HP.value (show state.cfgScale)
        , HP.min 1.0
        , HP.max 30.0
        , HP.step (HP.Step 0.5)
        , HE.onValueInput \s -> Types.SetCfgScale (Helpers.parseFloat s 5.0)
        ]
    ]

renderSeedInput :: forall m. MonadAff m => Types.State -> H.ComponentHTML Types.Action Types.Slots m
renderSeedInput state =
  HH.div [ cls [ "lattice-form-group", "lattice-form-inline" ] ]
    [ HH.label [] [ HH.text "Seed" ]
    , HH.input
        [ HP.type_ HP.InputNumber
        , HP.value (show state.seed)
        , HP.min 0.0
        , HP.max 2147483647.0
        , HE.onValueInput \s -> Types.SetSeed (Helpers.parseInt s 0)
        ]
    , HH.button [ cls [ "lattice-btn-icon" ], HE.onClick \_ -> Types.RandomizeSeed ] 
        [ HH.text "🎲" ]
    ]

-- ═══════════════════════════════════════════════════════════════════════════
--                                                       // sampler/scheduler options
-- ═══════════════════════════════════════════════════════════════════════════

renderSamplerOptions :: forall m. Types.Sampler -> Array (H.ComponentHTML Types.Action Types.Slots m)
renderSamplerOptions current =
  map (\r -> HH.option [ HP.value r.val, HP.selected (r.sampler == current) ] [ HH.text r.label ])
    [ { val: "res_2m", label: "RES 2M (multistep)", sampler: Types.S_res_2m }
    , { val: "res_3m", label: "RES 3M (multistep)", sampler: Types.S_res_3m }
    , { val: "res_2s", label: "RES 2S (singlestep)", sampler: Types.S_res_2s }
    , { val: "res_3m_sde", label: "RES 3M SDE", sampler: Types.S_res_3m_sde }
    , { val: "res_2s_sde", label: "RES 2S SDE", sampler: Types.S_res_2s_sde }
    , { val: "res_3s_sde", label: "RES 3S SDE", sampler: Types.S_res_3s_sde }
    , { val: "dpmpp_2m", label: "DPM++ 2M", sampler: Types.S_dpmpp_2m }
    , { val: "dpmpp_3m", label: "DPM++ 3M", sampler: Types.S_dpmpp_3m }
    , { val: "dpmpp_2s", label: "DPM++ 2S", sampler: Types.S_dpmpp_2s }
    , { val: "dpmpp_sde_2s", label: "DPM++ SDE 2S", sampler: Types.S_dpmpp_sde_2s }
    , { val: "dpmpp_3s", label: "DPM++ 3S", sampler: Types.S_dpmpp_3s }
    , { val: "euler", label: "Euler", sampler: Types.S_euler }
    , { val: "euler_ancestral", label: "Euler Ancestral", sampler: Types.S_euler_ancestral }
    , { val: "euler_a", label: "Euler A", sampler: Types.S_euler_a }
    , { val: "deis_2m", label: "DEIS 2M", sampler: Types.S_deis_2m }
    , { val: "deis_3m", label: "DEIS 3M", sampler: Types.S_deis_3m }
    , { val: "deis_4m", label: "DEIS 4M", sampler: Types.S_deis_4m }
    , { val: "etdrk2_2s", label: "ETDRK2 2S", sampler: Types.S_etdrk2_2s }
    , { val: "etdrk3_a_3s", label: "ETDRK3-A 3S", sampler: Types.S_etdrk3_a_3s }
    , { val: "etdrk3_b_3s", label: "ETDRK3-B 3S", sampler: Types.S_etdrk3_b_3s }
    , { val: "etdrk4_4s", label: "ETDRK4 4S", sampler: Types.S_etdrk4_4s }
    , { val: "etdrk4_4s_alt", label: "ETDRK4 4S Alt", sampler: Types.S_etdrk4_4s_alt }
    , { val: "unipc", label: "UniPC", sampler: Types.S_unipc }
    , { val: "unipc_snr", label: "UniPC SNR", sampler: Types.S_unipc_snr }
    , { val: "ddim", label: "DDIM", sampler: Types.S_ddim }
    , { val: "plms", label: "PLMS", sampler: Types.S_plms }
    , { val: "lms", label: "LMS", sampler: Types.S_lms }
    , { val: "kdpm_2_ancestral", label: "KDPM 2 Ancestral", sampler: Types.S_kdpm_2_ancestral }
    , { val: "kdpm_2", label: "KDPM 2", sampler: Types.S_kdpm_2 }
    , { val: "icv_ieks", label: "ICV IEKS", sampler: Types.S_icv_ieks }
    , { val: "tcd", label: "TCD", sampler: Types.S_tcd }
    ]

renderSchedulerOptions :: forall m. Types.Scheduler -> Array (H.ComponentHTML Types.Action Types.Slots m)
renderSchedulerOptions current =
  map (\r -> HH.option [ HP.value r.val, HP.selected (r.scheduler == current) ] [ HH.text r.label ])
    [ { val: "normal", label: "Normal", scheduler: Types.Sch_normal }
    , { val: "beta57", label: "Beta 57", scheduler: Types.Sch_beta57 }
    , { val: "karras", label: "Karras", scheduler: Types.Sch_karras }
    , { val: "exponential", label: "Exponential", scheduler: Types.Sch_exponential }
    , { val: "shifted_linear", label: "Shifted Linear", scheduler: Types.Sch_shifted_linear }
    , { val: "sqrt_linear", label: "Sqrt Linear", scheduler: Types.Sch_sqrt_linear }
    , { val: "linear", label: "Linear", scheduler: Types.Sch_linear }
    , { val: "linear_quadratic", label: "Linear Quadratic", scheduler: Types.Sch_linear_quadratic }
    , { val: "simple", label: "Simple", scheduler: Types.Sch_simple }
    , { val: "sgm_uniform", label: "SGM Uniform", scheduler: Types.Sch_sgm_uniform }
    , { val: "ddim_uniform", label: "DDIM Uniform", scheduler: Types.Sch_ddim_uniform }
    , { val: "kl_optimal", label: "KL Optimal", scheduler: Types.Sch_kl_optimal }
    ]

-- ═══════════════════════════════════════════════════════════════════════════
--                                                      // controlnet section
-- ═══════════════════════════════════════════════════════════════════════════

renderControlNetSection :: forall m. MonadAff m => Types.State -> H.ComponentHTML Types.Action Types.Slots m
renderControlNetSection state =
  HH.div [ cls [ "lattice-generate-controlnet" ] ]
    [ HH.text "ControlNet Conditioning"
    , HH.div [ cls [ "lattice-form-row" ] ]
        [ HH.div [ cls [ "lattice-form-group" ] ]
            [ HH.label [] [ HH.text "Control Type" ]
            , HH.select [ HE.onValueChange \s -> Types.SetControlNet (Helpers.parseControlNet s) ]
                [ HH.option [ HP.value "none", HP.selected (state.controlNet == Types.ControlNone) ] 
                    [ HH.text "None" ]
                , HH.option [ HP.value "depth", HP.selected (state.controlNet == Types.ControlDepth) ] 
                    [ HH.text "Depth" ]
                , HH.option [ HP.value "canny", HP.selected (state.controlNet == Types.ControlCanny) ] 
                    [ HH.text "Canny Edge" ]
                , HH.option [ HP.value "lineart", HP.selected (state.controlNet == Types.ControlLineart) ] 
                    [ HH.text "Line Art" ]
                , HH.option [ HP.value "softedge", HP.selected (state.controlNet == Types.ControlSoftEdge) ] 
                    [ HH.text "Soft Edge" ]
                , HH.option [ HP.value "normal", HP.selected (state.controlNet == Types.ControlNormal) ] 
                    [ HH.text "Normal Map" ]
                , HH.option [ HP.value "scribble", HP.selected (state.controlNet == Types.ControlScribble) ] 
                    [ HH.text "Scribble" ]
                , HH.option [ HP.value "seg", HP.selected (state.controlNet == Types.ControlSeg) ] 
                    [ HH.text "Segmentation" ]
                , HH.option [ HP.value "pose", HP.selected (state.controlNet == Types.ControlPose) ] 
                    [ HH.text "OpenPose" ]
                , HH.option [ HP.value "ipadapter", HP.selected (state.controlNet == Types.ControlIPAdapter) ] 
                    [ HH.text "IP-Adapter" ]
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
                , HP.step (HP.Step 0.05)
                ]
            ]
        , HH.div [ cls [ "lattice-form-group", "lattice-form-inline" ] ]
            [ HH.label [] [ HH.text "Start Step" ]
            , HH.input
                [ HP.type_ HP.InputNumber
                , HP.value (show state.controlNetStartStep)
                , HP.min 0.0
                , HP.max 1.0
                , HP.step (HP.Step 0.05)
                ]
            ]
        , HH.div [ cls [ "lattice-form-group", "lattice-form-inline" ] ]
            [ HH.label [] [ HH.text "End Step" ]
            , HH.input
                [ HP.type_ HP.InputNumber
                , HP.value (show state.controlNetEndStep)
                , HP.min 0.0
                , HP.max 1.0
                , HP.step (HP.Step 0.05)
                ]
            ]
        ]
    , HH.div [ cls [ "lattice-form-row" ] ]
        [ HH.div [ cls [ "lattice-form-group", "lattice-form-inline" ] ]
            [ HH.label [] [ HH.text "Start Frame" ]
            , HH.input
                [ HP.type_ HP.InputNumber
                , HP.value (show state.controlNetStartFrame)
                , HP.min 0.0
                , HP.step (HP.Step 1.0)
                ]
            ]
        , HH.div [ cls [ "lattice-form-group", "lattice-form-inline" ] ]
            [ HH.label [] [ HH.text "End Frame" ]
            , HH.input
                [ HP.type_ HP.InputNumber
                , HP.value (show state.controlNetEndFrame)
                , HP.min 0.0
                , HP.step (HP.Step 1.0)
                ]
            ]
        ]
    , HH.div [ cls [ "lattice-form-group" ] ]
        [ HH.label [] 
            [ HH.text "Control Image"
            , if isJust state.controlNetImage 
                then HH.span [ cls [ "lattice-badge-success" ] ] [ HH.text " (loaded)" ]
                else HH.text ""
            ]
        , HH.input
            [ HP.type_ HP.InputText
            , HP.placeholder "Paste image URL or drop file..."
            , HP.value (fromMaybe "" state.controlNetImage)
            ]
        ]
    ]

-- ═══════════════════════════════════════════════════════════════════════════
--                                                       // advanced section
-- ═══════════════════════════════════════════════════════════════════════════

renderAdvancedSection :: forall m. MonadAff m => Types.State -> H.ComponentHTML Types.Action Types.Slots m
renderAdvancedSection state =
  HH.div [ cls [ "lattice-generate-advanced" ] ]
    [ HH.text "Advanced Settings"
    , HH.div [ cls [ "lattice-form-row" ] ]
        [ HH.div [ cls [ "lattice-form-group", "lattice-form-inline" ] ]
            [ HH.label [] [ HH.text "\x{03B7} (Eta)" ]
            , HH.input
                [ HP.type_ HP.InputNumber
                , HP.value (show state.eta)
                , HP.min 0.0
                , HP.max 2.0
                , HP.step (HP.Step 0.1)
                ]
            ]
        , HH.div [ cls [ "lattice-form-group", "lattice-form-inline" ] ]
            [ HH.label [] [ HH.text "\x{03C3} min" ]
            , HH.input [ HP.value (show state.sigmaMin) ]
            ]
        , HH.div [ cls [ "lattice-form-group", "lattice-form-inline" ] ]
            [ HH.label [] [ HH.text "\x{03C3} max" ]
            , HH.input [ HP.value (show state.sigmaMax) ]
            ]
        , HH.div [ cls [ "lattice-form-group", "lattice-form-inline" ] ]
            [ HH.label [] [ HH.text "\x{03C1}" ]
            , HH.input [ HP.value (show state.rho) ]
            ]
        ]
    ]

-- ═══════════════════════════════════════════════════════════════════════════
--                                                        // preview section
-- ═══════════════════════════════════════════════════════════════════════════

renderPreviewSection :: forall m. MonadAff m => Types.State -> H.ComponentHTML Types.Action Types.Slots m
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

-- ═══════════════════════════════════════════════════════════════════════════
--                                                        // action buttons
-- ═══════════════════════════════════════════════════════════════════════════

renderActionButtons :: forall m. MonadAff m => Types.State -> H.ComponentHTML Types.Action Types.Slots m
renderActionButtons state =
  HH.div [ cls [ "lattice-generate-actions" ] ]
    [ if state.isGenerating 
        then HH.button [ cls [ "lattice-btn-danger" ], HE.onClick \_ -> Types.CancelGeneration ] 
            [ HH.text "Cancel" ]
        else HH.button [ cls [ "lattice-btn-primary" ], HE.onClick \_ -> Types.StartGeneration ] 
            [ HH.text "Generate" ]
    ]
