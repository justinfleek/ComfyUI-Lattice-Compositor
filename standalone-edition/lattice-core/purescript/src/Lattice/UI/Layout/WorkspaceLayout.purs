-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- | Workspace Layout Component
-- |
-- | The main workspace layout for the Lattice Compositor.
-- |
-- | +-------------------------------------------------------------------------+
-- | | MenuBar (28px)                                                          |
-- | +-------------------------------------------------------------------------+
-- | | Toolbar (54px)                                                          |
-- | +--------+--------------------------------------------+-------------------+
-- | |        |  +-----------------+-----------------+     |                   |
-- | |  Left  |  |  3D Scene View  |  Render Preview |     |    Right          |
-- | | Sidebar|  |  (Working)      |  (Final Output) |     |   Sidebar         |
-- | | (14%)  |  |  Shadowbox      |  Black -> Render|     |    (20%)          |
-- | |        |  +-----------------+-----------------+     |                   |
-- | | Tabs:  |  +-----------------------------------+     |  Properties       |
-- | | -Project|  |           Timeline               |     |  + AI Panel       |
-- | | -Assets |  |                                  |     |                   |
-- | | -Draw  |  +-----------------------------------+     |                   |
-- | +--------+--------------------------------------------+-------------------+
-- |
-- | ## Viewports:
-- | - **3D Scene View**: Interactive editing, camera rotation, z-space navigation
-- | - **Render Preview**: Displays backend-rendered output, starts black
-- | - **Drawing Canvas**: Tab in left panel for ControlNet brush painting
-- | - **Asset Browser**: Tab in left panel for imported files
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
module Lattice.UI.Layout.WorkspaceLayout
  ( component
  , module Types
  ) where

import Prelude

import Data.Array (uncons) as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..), Just, Nothing)
import Effect.Aff.Class (class MonadAff, liftAff)
import Halogen as H

import Lattice.UI.Components.LayerList as LayerList
import Lattice.UI.Components.Timeline as Timeline
import Lattice.Services.Bridge.Client as Bridge

import Lattice.UI.Layout.WorkspaceLayout.Types
  ( Input
  , Output
  , Query
  , Slot
  , State
  , Action(..)
  , Slots
  , LeftTab(..)
  , GenerationMode(..)
  ) as Types
import Lattice.UI.Layout.WorkspaceLayout.Types
  ( Input
  , State
  , Action(..)
  , Slots
  , LeftTab(..)
  , GenerationMode(..)
  )
import Lattice.UI.Layout.WorkspaceLayout.Render (render)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                 // component
-- ════════════════════════════════════════════════════════════════════════════

component :: forall q o m. MonadAff m => H.Component q Input o m
component = H.mkComponent
  { initialState
  , render
  , eval: H.mkEval H.defaultEval
      { handleAction = handleAction
      , initialize = Just Initialize
      , receive = Just <<< Receive
      }
  }

initialState :: Input -> State
initialState input =
  { leftSidebarWidth: 14.0
  , rightSidebarWidth: 20.0
  , timelineHeight: 35.0
  , viewportSplit: 50.0
  , layers: []
  , selectedLayerIds: []
  , currentFrame: 0
  , totalFrames: 81
  , fps: 16.0
  , isPlaying: false
  , compositionDimensions: { width: 1920, height: 1080 }
  , activeLeftTab: TabProject
  , renderPreviewUrl: Nothing
  , isRendering: false
  , renderError: Nothing
  , generationProgress: 0.0
  , generationStage: "idle"
  , generationEta: Nothing
  , sceneCameraRotation: { x: 0.0, y: 0.0, z: 0.0 }
  , sceneCameraPosition: { x: 0.0, y: 0.0, z: 0.0 }
  , sceneCameraZoom: 1.0
  , bridgeClient: input.bridgeClient
  , promptText: ""
  , negativePrompt: ""
  , generationMode: TextToVideo
  , selectedModel: "wan-2.1"
  , sourceImageUrl: Nothing
  , maskImageUrl: Nothing
  , numFrames: 81
  , cfgScale: 7.0
  , steps: 30
  , seed: Nothing
  }

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // actions
-- ════════════════════════════════════════════════════════════════════════════

handleAction :: forall o m. MonadAff m => Action -> H.HalogenM State Action Slots o m Unit
handleAction = case _ of
  Initialize -> pure unit
  
  SetLeftTab tab -> H.modify_ _ { activeLeftTab = tab }
  
  HandleLayerList output -> case output of
    LayerList.SelectLayer layerId -> 
      H.modify_ _ { selectedLayerIds = [layerId] }
    LayerList.ToggleVisibility _layerId -> pure unit
    LayerList.ToggleLock _layerId -> pure unit
    LayerList.ReorderLayer _layerId _index -> pure unit
  
  HandleTimeline output -> case output of
    Timeline.SeekToFrame frame -> 
      H.modify_ _ { currentFrame = frame }
    Timeline.TogglePlayback -> 
      H.modify_ \s -> s { isPlaying = not s.isPlaying }
    Timeline.SelectLayer layerId -> 
      H.modify_ _ { selectedLayerIds = [layerId] }
    Timeline.ToggleLayerExpanded _layerId -> pure unit
  
  HandleProperties _output -> pure unit
  
  -- scene camera controls
  RotateSceneCamera dx dy ->
    H.modify_ \s -> s 
      { sceneCameraRotation = s.sceneCameraRotation 
          { x = s.sceneCameraRotation.x + dx
          , y = s.sceneCameraRotation.y + dy
          }
      }
  
  PanSceneCamera dx dy ->
    H.modify_ \s -> s 
      { sceneCameraPosition = s.sceneCameraPosition 
          { x = s.sceneCameraPosition.x + dx
          , y = s.sceneCameraPosition.y + dy
          }
      }
  
  ZoomSceneCamera delta ->
    H.modify_ \s -> s 
      { sceneCameraZoom = clamp 0.1 10.0 (s.sceneCameraZoom + delta) }
  
  ResetSceneCamera ->
    H.modify_ _ 
      { sceneCameraRotation = { x: 0.0, y: 0.0, z: 0.0 }
      , sceneCameraPosition = { x: 0.0, y: 0.0, z: 0.0 }
      , sceneCameraZoom = 1.0
      }
  
  -- drawing canvas
  SetBrushSize _size -> pure unit  -- will wire up to canvas
  SetBrushColor _color -> pure unit
  SetBrushOpacity _opacity -> pure unit
  ClearDrawingCanvas -> pure unit  -- will clear the canvas
  
  -- ai generation
  SetPromptText text -> 
    H.modify_ _ { promptText = text }
  
  SetNegativePrompt text -> 
    H.modify_ _ { negativePrompt = text }
  
  SetGenerationMode mode -> do
    -- when mode changes, select a default model for that mode
    let defaultModel = case mode of
          TextToImage -> "flux-1-dev"
          ImageEdit -> "flux-2-dev"
          ImageToVideo -> "wan-move"
          TextToVideo -> "wan-2.1"
          TextTo3D -> "trellis-2"
    H.modify_ _ { generationMode = mode, selectedModel = defaultModel }
  
  SetModel model -> 
    H.modify_ _ { selectedModel = model }
  
  SetNumFrames n -> 
    H.modify_ _ { numFrames = n }
  
  SetCfgScale scale -> 
    H.modify_ _ { cfgScale = scale }
  
  SetSteps s -> 
    H.modify_ _ { steps = s }
  
  SetSourceImage url -> 
    H.modify_ _ { sourceImageUrl = if url == "" then Nothing else Just url }
  
  GenerateFromPrompt -> do
    state <- H.get
    case state.bridgeClient of
      Nothing -> 
        H.modify_ _ { renderError = Just "Backend not connected" }
      Just client -> do
        -- reset progress and start rendering
        H.modify_ _ 
          { isRendering = true
          , renderError = Nothing
          , generationProgress = 0.0
          , generationStage = "encoding"
          , generationEta = Nothing
          }
        -- build generation config
        let config =
              { prompt: state.promptText
              , negativePrompt: if state.negativePrompt == "" then Nothing else Just state.negativePrompt
              , width: state.compositionDimensions.width
              , height: state.compositionDimensions.height
              , numFrames: case state.generationMode of
                  TextToImage -> Nothing
                  _ -> Just state.numFrames
              , fps: Just state.fps
              , model: state.selectedModel
              , seed: state.seed
              , steps: Just state.steps
              , cfgScale: Just state.cfgScale
              , controlnetImage: state.maskImageUrl  -- use mask as controlnet for edit mode
              , controlnetType: case state.generationMode of
                  ImageEdit -> Just "inpaint"
                  _ -> Nothing
              , controlnetStrength: Nothing
              }
        -- call appropriate generation function based on mode
        result <- liftAff $ case state.generationMode of
          TextToImage -> Bridge.generateImage client config
          ImageEdit -> Bridge.generateImage client config
          TextTo3D -> Bridge.generateImage client config  -- 3d returns image for now
          ImageToVideo -> Bridge.generateVideo client config
          TextToVideo -> Bridge.generateVideo client config
        handleAction (ReceiveGenerateResult result)
  
  ReceiveGenerateProgress percentage stage ->
    H.modify_ _ 
      { generationProgress = percentage
      , generationStage = stage
      }
  
  ReceiveGenerateResult result -> 
    case result of
      Left err -> 
        H.modify_ _ 
          { isRendering = false
          , renderError = Just err
          , generationProgress = 0.0
          , generationStage = "idle"
          , generationEta = Nothing
          }
      Right genResult -> 
        if genResult.success
          then case genResult.frames of
            [] -> H.modify_ _ 
              { isRendering = false
              , renderError = Just "No frames generated"
              , generationProgress = 0.0
              , generationStage = "idle"
              , generationEta = Nothing
              }
            frames -> do
              -- take first frame for preview (or last for video)
              let previewFrame = case frames of
                    [f] -> f
                    fs -> lastOrFirst fs
              H.modify_ _ 
                { isRendering = false
                , renderError = Nothing
                , renderPreviewUrl = Just ("data:image/png;base64," <> previewFrame)
                , generationProgress = 100.0
                , generationStage = "idle"
                , generationEta = Nothing
                }
          else 
            H.modify_ _ 
              { isRendering = false
              , renderError = genResult.error
              , generationProgress = 0.0
              , generationStage = "idle"
              , generationEta = Nothing
              }
  
  Receive input -> 
    H.modify_ _ { bridgeClient = input.bridgeClient }

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // helpers
-- ════════════════════════════════════════════════════════════════════════════

-- | get last element of array, or first if only one
lastOrFirst :: Array String -> String
lastOrFirst [] = ""
lastOrFirst [x] = x
lastOrFirst arr = case arr of
  [] -> ""
  _ -> go arr
  where
    go [x] = x
    go xs = case Array.uncons xs of
      Nothing -> ""
      Just { head: _, tail: rest } -> go rest

clamp :: Number -> Number -> Number -> Number
clamp minVal maxVal val = max minVal (min maxVal val)
