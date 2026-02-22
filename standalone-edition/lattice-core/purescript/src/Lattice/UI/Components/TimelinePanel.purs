-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- | TimelinePanel Component
-- |
-- | Main timeline and layer management panel for Lattice Compositor.
-- | Provides professional timeline with keyframe editing:
-- | - Composition tabs for multi-comp workflows
-- | - Playback controls (play, pause, loop, frame stepping)
-- | - Layer track list with visibility/lock toggles
-- | - Keyframe visualization on time ruler
-- | - Scrubbing and frame navigation
-- | - Layer creation menu (Solid, Text, Shape, Particles, etc.)
-- | - Zoom controls for timeline scale
-- | - Work area (render range) support
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
module Lattice.UI.Components.TimelinePanel
  ( component
  , module Types
  ) where

import Prelude

import Effect.Aff.Class (class MonadAff)
import Halogen as H

import Lattice.UI.Components.TimelinePanel.Types
  ( Input
  , Output(..)
  , Query
  , Slot
  , LayerType(..)
  , WorkArea
  , State
  , Action(..)
  ) as Types
import Lattice.UI.Components.TimelinePanel.Render (render)

-- ════════════════════════════════════════════════════════════════════════════
--                                                                // component
-- ════════════════════════════════════════════════════════════════════════════

component :: forall q m. MonadAff m => H.Component q Types.Input Types.Output m
component = H.mkComponent
  { initialState
  , render
  , eval: H.mkEval H.defaultEval
      { handleAction = handleAction
      , initialize = Just Types.Initialize
      , receive = Just <<< Types.Receive
      }
  }

initialState :: Types.Input -> Types.State
initialState input =
  { layers: input.layers
  , compositions: input.compositions
  , activeCompositionId: input.activeCompositionId
  , mainCompositionId: input.mainCompositionId
  , breadcrumbs: input.breadcrumbs
  , currentFrame: input.currentFrame
  , totalFrames: input.totalFrames
  , fps: input.fps
  , isPlaying: input.isPlaying
  , selectedLayerIds: input.selectedLayerIds
  , expandedLayerIds: input.expandedLayerIds
  , workArea: input.workArea
  , hasAudio: input.hasAudio
  -- UI state
  , zoomPercent: 0.0
  , sidebarWidth: 450
  , showAddLayerMenu: false
  , viewportWidth: 1000.0
  }

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // actions
-- ════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Types.Action -> H.HalogenM Types.State Types.Action Types.Slots Types.Output m Unit
handleAction = case _ of
  Types.Initialize -> do
    pure unit
  
  Types.Receive input -> do
    H.modify_ _
      { layers = input.layers
      , compositions = input.compositions
      , activeCompositionId = input.activeCompositionId
      , mainCompositionId = input.mainCompositionId
      , breadcrumbs = input.breadcrumbs
      , currentFrame = input.currentFrame
      , totalFrames = input.totalFrames
      , fps = input.fps
      , isPlaying = input.isPlaying
      , selectedLayerIds = input.selectedLayerIds
      , expandedLayerIds = input.expandedLayerIds
      , workArea = input.workArea
      , hasAudio = input.hasAudio
      }
  
  Types.HandleTogglePlayback -> do
    H.raise Types.TogglePlayback
  
  Types.HandleGoToStart -> do
    H.raise Types.GoToStart
  
  Types.HandleGoToEnd -> do
    H.raise Types.GoToEnd
  
  Types.HandlePrevFrame -> do
    H.raise Types.PrevFrame
  
  Types.HandleNextFrame -> do
    H.raise Types.NextFrame
  
  Types.HandleSetFrame frame -> do
    H.raise (Types.SeekToFrame frame)
  
  Types.HandleZoomChange pct -> do
    H.modify_ _ { zoomPercent = pct }
    H.raise (Types.SetZoom pct)
  
  Types.HandleToggleAddLayerMenu -> do
    H.modify_ \s -> s { showAddLayerMenu = not s.showAddLayerMenu }
  
  Types.HandleAddLayer layerType -> do
    H.modify_ _ { showAddLayerMenu = false }
    H.raise (Types.AddLayer layerType)
  
  Types.HandleDeleteSelected -> do
    H.raise Types.DeleteSelectedLayers
  
  Types.HandleOpenCompSettings -> do
    H.raise Types.OpenCompositionSettings
  
  Types.HandleOpenAI -> do
    H.raise Types.OpenPathSuggestion
  
  Types.HandleSidebarResize width -> do
    H.modify_ _ { sidebarWidth = max 450 width }
  
  Types.HandleSetWorkAreaStart frame -> do
    state <- H.get
    let newWorkArea = case state.workArea of
          Just wa -> Just { start: frame, end: wa.end }
          Nothing -> Just { start: frame, end: state.totalFrames - 1 }
    H.raise (Types.SetWorkArea newWorkArea)
  
  Types.HandleSetWorkAreaEnd frame -> do
    state <- H.get
    let newWorkArea = case state.workArea of
          Just wa -> Just { start: wa.start, end: frame }
          Nothing -> Just { start: 0, end: frame }
    H.raise (Types.SetWorkArea newWorkArea)
  
  Types.HandleClearWorkArea -> do
    H.raise (Types.SetWorkArea Nothing)
  
  Types.HandleRulerScrub frame -> do
    H.raise (Types.SeekToFrame frame)
  
  Types.HandleCompositionTabsOutput output -> do
    H.raise (Types.CompositionTabsOutput output)
  
  Types.HandleLayerTrackOutput _idx output -> do
    H.raise (Types.UpdateLayer output)
  
  Types.HandleKeydown key -> do
    case key of
      "Space" -> handleAction Types.HandleTogglePlayback
      "Home" -> handleAction Types.HandleGoToStart
      "End" -> handleAction Types.HandleGoToEnd
      "ArrowLeft" -> handleAction Types.HandlePrevFrame
      "ArrowRight" -> handleAction Types.HandleNextFrame
      "Delete" -> handleAction Types.HandleDeleteSelected
      "Backspace" -> handleAction Types.HandleDeleteSelected
      _ -> pure unit
