-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- generate // helpers
-- utility functions, parsers, and converters for the AI generation page
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
module Lattice.UI.Pages.Generate.Helpers
  ( -- ── parsers ──
    parseModel
  , parseResolution
  , parseSampler
  , parseScheduler
  , parseControlNet
  , parseInt
  , parseFloat
    -- ── converters ──
  , modelToString
  , controlNetToString
  , resolutionWidth
  , resolutionHeight
  , genModeToLayerType
    -- ── utilities ──
  , clampNumber
  , clampInt
  , headOrLast
  , buildGenerateConfig
  ) where

import Prelude

import Data.Array (last)
import Data.Int as Int
import Data.Int (toNumber)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Number (fromString, isFinite) as Number
import Data.String (trim) as String

import Lattice.Project (LayerType(..))
import Lattice.Services.Bridge.Client as Bridge
import Lattice.UI.Pages.Generate.Types 
  ( GenMode(..)
  , Model(..)
  , Resolution(..)
  , Sampler(..)
  , Scheduler(..)
  , ControlNet(..)
  , State
  )

-- ═══════════════════════════════════════════════════════════════════════════
--                                                             // model parser
-- ═══════════════════════════════════════════════════════════════════════════

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

-- ═══════════════════════════════════════════════════════════════════════════
--                                                        // resolution parser
-- ═══════════════════════════════════════════════════════════════════════════

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

-- ═══════════════════════════════════════════════════════════════════════════
--                                                           // sampler parser
-- ═══════════════════════════════════════════════════════════════════════════

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

-- ═══════════════════════════════════════════════════════════════════════════
--                                                         // scheduler parser
-- ═══════════════════════════════════════════════════════════════════════════

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

-- ═══════════════════════════════════════════════════════════════════════════
--                                                        // controlnet parser
-- ═══════════════════════════════════════════════════════════════════════════

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

-- ═══════════════════════════════════════════════════════════════════════════
--                                                          // number parsers
-- ═══════════════════════════════════════════════════════════════════════════

parseInt :: String -> Int -> Int
parseInt s def = 
  case String.trim s of
    "" -> def
    trimmed -> case Int.fromString trimmed of
      Just n -> n
      Nothing -> def

parseFloat :: String -> Number -> Number
parseFloat s def = 
  case String.trim s of
    "" -> def
    trimmed -> case Number.fromString trimmed of
      Just n -> if Number.isFinite n then n else def
      Nothing -> def

-- ═══════════════════════════════════════════════════════════════════════════
--                                                               // utilities
-- ═══════════════════════════════════════════════════════════════════════════

clampNumber :: Number -> Number -> Number -> Number
clampNumber minVal maxVal n = max minVal (min maxVal n)

clampInt :: Int -> Int -> Int -> Int
clampInt minVal maxVal n = max minVal (min maxVal n)

headOrLast :: Array String -> String
headOrLast arr = case arr of
  [] -> ""
  [x] -> x
  xs -> fromMaybe "" (last xs)

-- ═══════════════════════════════════════════════════════════════════════════
--                                                        // layer type mapper
-- ═══════════════════════════════════════════════════════════════════════════

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

-- ═══════════════════════════════════════════════════════════════════════════
--                                                        // bridge config builder
-- ═══════════════════════════════════════════════════════════════════════════

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
