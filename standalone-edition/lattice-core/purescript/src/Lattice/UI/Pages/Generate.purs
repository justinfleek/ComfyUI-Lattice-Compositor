-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- generate // main
-- AI-powered generation panel for T2I, I2V, T2V, I2I and more
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- |
-- | Generate Page Component
-- |
-- | AI-powered generation panel for T2I, I2V, T2V, I2I and more.
-- | Exposes all RES4LYF samplers and schedulers.
-- |
-- | ┌─────────────────────────────────────────────────────────────────────┐
-- | │ Mode: [T2I] [I2V] [T2V] [I2I] [Inpaint] [Upscale]                   │
-- | ├─────────────────────────────────────────────────────────────────────┤
-- | │ Prompt / Negative Prompt / Model / Sampler / Scheduler / Steps     │
-- | │ CFG / Seed / ControlNet / Advanced Settings / Preview              │
-- | └─────────────────────────────────────────────────────────────────────┘
module Lattice.UI.Pages.Generate
  ( component
  , module Types
  ) where

import Prelude

import Data.Array (length, cons)
import Data.Either (Either(..))
import Data.Int (round)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.DateTime.Instant (unInstant)
import Data.Time.Duration (Milliseconds(..))
import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Class (liftEffect)
import Effect.Now (now)
import Halogen as H

import Lattice.Services.Bridge.Client as Bridge
import Lattice.UI.Pages.Generate.Types 
  ( GenMode(..)
  , Sampler(..)
  , Scheduler(..)
  , Model(..)
  , Resolution(..)
  , ControlNet(..)
  , State
  , Input
  , Output(..)
  , Action(..)
  , Query(..)
  , Slots
  , GenerationResult
  , GenerationData(..)
  ) as Types
import Lattice.UI.Pages.Generate.Render (render)
import Lattice.UI.Pages.Generate.Helpers as Helpers

-- ═══════════════════════════════════════════════════════════════════════════
--                                                                // component
-- ═══════════════════════════════════════════════════════════════════════════

component :: forall m. MonadAff m => H.Component Types.Query Types.Input Types.Output m
component = H.mkComponent
  { initialState
  , render
  , eval: H.mkEval H.defaultEval
      { handleAction = handleAction
      , handleQuery = handleQuery
      }
  }

initialState :: Types.Input -> Types.State
initialState input =
  { mode: input.mode
  , prompt: ""
  , negativePrompt: "blurry, low quality, distorted, deformed, ugly"
  , sourceImage: Nothing
  , controlNet: Types.ControlNone
  , controlNetImage: Nothing
  , controlNetStrength: 1.0
  , controlNetStartStep: 0.0
  , controlNetEndStep: 1.0
  , controlNetStartFrame: 0
  , controlNetEndFrame: input.numFrames
  , model: Types.ModelSDXL
  , sampler: Types.S_res_2m
  , scheduler: Types.Sch_normal
  , steps: 30
  , cfgScale: 5.0
  , seed: 0
  , resolution: Types.Res1024x1024
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
  , generationHistory: []
  , bridgeClient: input.bridgeClient
  , numFrames: input.numFrames
  , fps: input.fps
  , compositionWidth: input.width
  , compositionHeight: input.height
  }

-- ═══════════════════════════════════════════════════════════════════════════
--                                                                  // actions
-- ═══════════════════════════════════════════════════════════════════════════

handleAction 
  :: forall m
   . MonadAff m 
  => Types.Action 
  -> H.HalogenM Types.State Types.Action Types.Slots Types.Output m Unit
handleAction = case _ of
  Types.SetMode mode -> do
    H.modify_ _ { mode = mode }

  Types.SetPrompt prompt -> do
    H.modify_ _ { prompt = prompt }

  Types.SetNegativePrompt np -> do
    H.modify_ _ { negativePrompt = np }

  Types.SetSampler sampler -> do
    H.modify_ _ { sampler = sampler }

  Types.SetScheduler scheduler -> do
    H.modify_ _ { scheduler = scheduler }

  Types.SetSteps steps -> do
    H.modify_ _ { steps = steps }

  Types.SetCfgScale cfg -> do
    H.modify_ _ { cfgScale = cfg }

  Types.SetSeed seed -> do
    H.modify_ _ { seed = seed }

  Types.SetModel model -> do
    H.modify_ _ { model = model }

  Types.SetResolution resolution -> do
    H.modify_ _ { resolution = resolution }

  Types.RandomizeSeed -> do
    instant <- liftEffect now
    let (Milliseconds ms) = unInstant instant
    let newSeed = round ms `mod` 2147483647
    H.modify_ _ { seed = newSeed }

  Types.StartGeneration -> do
    state <- H.get
    case state.bridgeClient of
      Nothing -> 
        H.modify_ _ { isGenerating = false, error = Just "Backend not connected" }
      Just client -> do
        H.modify_ _ { isGenerating = true, progress = 0.0, stage = "encoding", error = Nothing }
        let config = Helpers.buildGenerateConfig state
        result <- liftAff $ case state.mode of
          Types.GenTextToImage -> Bridge.generateImage client config
          Types.GenImageToVideo -> Bridge.generateVideo client config
          Types.GenTextToVideo -> Bridge.generateVideo client config
          Types.GenImageToImage -> Bridge.generateImage client config
          Types.GenInpaint -> Bridge.generateImage client config
          Types.GenOutpaint -> Bridge.generateImage client config
          Types.GenUpscale -> Bridge.generateImage client config
          Types.GenRemoveBackground -> Bridge.generateImage client config
        case result of
          Left err -> do
            H.modify_ _ { isGenerating = false, error = Just err, stage = "idle" }
            H.raise (Types.GenerationError err)
          Right genResult ->
            if genResult.success
              then do
                let previewUrl = case genResult.frames of
                      [] -> Nothing
                      frames -> Just ("data:image/png;base64," <> Helpers.headOrLast frames)
                -- add to generation history
                instant <- liftEffect now
                let (Milliseconds timestamp) = unInstant instant
                let historyEntry = 
                      { prompt: state.prompt
                      , model: state.model
                      , seed: genResult.seed
                      , previewUrl: previewUrl
                      , timestamp: timestamp
                      }
                H.modify_ \s -> s
                  { isGenerating = false
                  , progress = 100.0
                  , stage = "idle"
                  , previewUrl = previewUrl
                  , error = Nothing
                  , generationHistory = cons historyEntry s.generationHistory
                  }
                let layerType = Helpers.genModeToLayerType state.mode
                let genData = Types.GenerationData
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
                let result_ = 
                      { layerId: ""
                      , layerType: layerType
                      , name: state.prompt
                      , previewUrl: fromMaybe "" previewUrl
                      , width: Helpers.resolutionWidth state.resolution
                      , height: Helpers.resolutionHeight state.resolution
                      , frames: length genResult.frames
                      , data: genData
                      }
                H.raise (Types.GenerationComplete result_)
              else do
                let errMsg = fromMaybe "Generation failed" genResult.error
                H.modify_ _ { isGenerating = false, error = Just errMsg, stage = "idle" }
                H.raise (Types.GenerationError errMsg)

  Types.CancelGeneration ->
    H.modify_ _ { isGenerating = false, stage = "idle", progress = 0.0 }

  Types.SetControlNet cn ->
    H.modify_ _ { controlNet = cn }

  Types.SetControlNetStrength s ->
    H.modify_ _ { controlNetStrength = s }

  Types.SetControlNetImage img ->
    H.modify_ _ { controlNetImage = if img == "" then Nothing else Just img }

  Types.SetControlNetStartStep s ->
    H.modify_ _ { controlNetStartStep = s }

  Types.SetControlNetEndStep s ->
    H.modify_ _ { controlNetEndStep = s }

  Types.SetControlNetStartFrame f ->
    H.modify_ _ { controlNetStartFrame = f }

  Types.SetControlNetEndFrame f ->
    H.modify_ _ { controlNetEndFrame = f }

-- ═══════════════════════════════════════════════════════════════════════════
--                                                                  // queries
-- ═══════════════════════════════════════════════════════════════════════════

handleQuery 
  :: forall m a
   . MonadAff m 
  => Types.Query a 
  -> H.HalogenM Types.State Types.Action Types.Slots Types.Output m (Maybe a)
handleQuery = case _ of
  Types.QuerySetMode mode a -> do
    H.modify_ _ { mode = mode }
    pure (Just a)
  Types.QuerySetPrompt prompt a -> do
    H.modify_ _ { prompt = prompt }
    pure (Just a)
  Types.QuerySetSampler sampler a -> do
    H.modify_ _ { sampler = sampler }
    pure (Just a)
  Types.QuerySetScheduler scheduler a -> do
    H.modify_ _ { scheduler = scheduler }
    pure (Just a)
  Types.QuerySetSteps steps a -> do
    H.modify_ _ { steps = steps }
    pure (Just a)
  Types.QuerySetCfgScale cfg a -> do
    H.modify_ _ { cfgScale = cfg }
    pure (Just a)
  Types.QuerySetSeed seed a -> do
    H.modify_ _ { seed = seed }
    pure (Just a)
  Types.QuerySetModel model a -> do
    H.modify_ _ { model = model }
    pure (Just a)
  Types.QuerySetResolution resolution a -> do
    H.modify_ _ { resolution = resolution }
    pure (Just a)
