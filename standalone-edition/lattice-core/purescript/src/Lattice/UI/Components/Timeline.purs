-- | Timeline Component
-- |
-- | The main timeline for animation editing. Shows layers with their
-- | time ranges and keyframes. Supports scrubbing, layer selection,
-- | and basic keyframe editing.
module Lattice.UI.Components.Timeline
  ( component
  , Input
  , Output(..)
  , Query
  , Slot
  ) where

import Prelude

import Data.Array (mapWithIndex, length, filter, uncons)
import Data.Int as Int
import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP

import Lattice.UI.Core (cls)
import Lattice.Project (LayerBase)
import Lattice.Primitives (FrameNumber(..))

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                     // types
-- ════════════════════════════════════════════════════════════════════════════

type Input =
  { layers :: Array LayerBase
  , currentFrame :: Int
  , totalFrames :: Int
  , fps :: Number
  , selectedLayerIds :: Array String
  , isPlaying :: Boolean
  }

data Output
  = SeekToFrame Int
  | TogglePlayback
  | SelectLayer String
  | ToggleLayerExpanded String

data Query a

type Slot id = H.Slot Query Output id

type State =
  { layers :: Array LayerBase
  , currentFrame :: Int
  , totalFrames :: Int
  , fps :: Number
  , selectedLayerIds :: Array String
  , isPlaying :: Boolean
  , zoom :: Number  -- Pixels per frame
  , scrollX :: Number
  , layerRowHeight :: Number
  }

data Action
  = Initialize
  | Receive Input
  | HandleSeek Int
  | HandlePlayPause
  | HandleSelectLayer String
  | HandleZoomIn
  | HandleZoomOut
  | HandleScroll Number
  | HandleGoToStart
  | HandleGoToEnd
  | HandlePrevFrame
  | HandleNextFrame

-- ════════════════════════════════════════════════════════════════════════════
--                                                                 // component
-- ════════════════════════════════════════════════════════════════════════════

component :: forall q m. MonadAff m => H.Component q Input Output m
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
  { layers: input.layers
  , currentFrame: input.currentFrame
  , totalFrames: input.totalFrames
  , fps: input.fps
  , selectedLayerIds: input.selectedLayerIds
  , isPlaying: input.isPlaying
  , zoom: 10.0  -- 10 pixels per frame
  , scrollX: 0.0
  , layerRowHeight: 28.0
  }

-- ════════════════════════════════════════════════════════════════════════════
--                                                                    // render
-- ════════════════════════════════════════════════════════════════════════════

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ cls [ "lattice-timeline" ]
    , HP.attr (HH.AttrName "style") timelineStyle
    ]
    [ -- Timeline header with controls
      renderHeader state
    
      -- Timeline body (layer sidebar + tracks)
    , renderBody state
    ]

renderHeader :: forall m. State -> H.ComponentHTML Action () m
renderHeader state =
  HH.div
    [ cls [ "lattice-timeline-header" ]
    , HP.attr (HH.AttrName "style") headerStyle
    ]
    [ -- Left side: composition tabs
      HH.div [ cls [ "lattice-timeline-tabs" ] ]
        [ HH.button 
            [ cls [ "lattice-timeline-tab" ]
            , HP.attr (HH.AttrName "data-state") "active"
            ]
            [ HH.text "Main Comp" ]
        ]
    
      -- Center: playback controls
    , HH.div 
        [ cls [ "lattice-playback-controls" ]
        , HP.attr (HH.AttrName "style") playbackStyle
        ]
        [ controlButton "⏮" "Go to Start" HandleGoToStart
        , controlButton "⏪" "Previous Frame" HandlePrevFrame
        , controlButton (if state.isPlaying then "⏸" else "▶") "Play/Pause" HandlePlayPause
        , controlButton "⏩" "Next Frame" HandleNextFrame
        , controlButton "⏭" "Go to End" HandleGoToEnd
        ]
    
      -- Right side: time display and zoom
    , HH.div 
        [ cls [ "lattice-timeline-info" ]
        , HP.attr (HH.AttrName "style") infoStyle
        ]
        [ HH.span [ cls [ "lattice-time-display" ] ]
            [ HH.text (formatTimecode state.currentFrame state.fps) ]
        , HH.span [ cls [ "lattice-frame-display" ] ]
            [ HH.text (" / " <> show state.currentFrame <> "f") ]
        , HH.div [ cls [ "lattice-zoom-controls" ] ]
            [ HH.button 
                [ cls [ "lattice-zoom-btn" ]
                , HE.onClick \_ -> HandleZoomOut
                ]
                [ HH.text "-" ]
            , HH.button 
                [ cls [ "lattice-zoom-btn" ]
                , HE.onClick \_ -> HandleZoomIn
                ]
                [ HH.text "+" ]
            ]
        ]
    ]

controlButton :: forall m. String -> String -> Action -> H.ComponentHTML Action () m
controlButton icon tooltip action =
  HH.button
    [ cls [ "lattice-playback-btn" ]
    , HP.title tooltip
    , HE.onClick \_ -> action
    ]
    [ HH.text icon ]

renderBody :: forall m. State -> H.ComponentHTML Action () m
renderBody state =
  HH.div
    [ cls [ "lattice-timeline-body" ]
    , HP.attr (HH.AttrName "style") bodyStyle
    ]
    [ -- Layer sidebar
      HH.div
        [ cls [ "lattice-layer-sidebar" ]
        , HP.attr (HH.AttrName "style") sidebarStyle
        ]
        [ renderLayerSidebar state ]
    
      -- Track viewport
    , HH.div
        [ cls [ "lattice-track-viewport" ]
        , HP.attr (HH.AttrName "style") viewportStyle
        ]
        [ -- Time ruler
          renderTimeRuler state
        
          -- Layer tracks
        , renderTracks state
        
          -- Playhead
        , renderPlayhead state
        ]
    ]

renderLayerSidebar :: forall m. State -> H.ComponentHTML Action () m
renderLayerSidebar state =
  HH.div [ cls [ "lattice-layer-list-timeline" ] ]
    (mapWithIndex (renderLayerRow state) state.layers)

renderLayerRow :: forall m. State -> Int -> LayerBase -> H.ComponentHTML Action () m
renderLayerRow state _index layer =
  let
    isSelected = show layer.id `elem` state.selectedLayerIds
  in
  HH.div
    [ cls [ "lattice-layer-row" ]
    , HP.attr (HH.AttrName "style") (layerRowStyle state.layerRowHeight isSelected)
    , HE.onClick \_ -> HandleSelectLayer (show layer.id)
    ]
    [ -- Visibility toggle
      HH.span [ cls [ "lattice-layer-icon" ] ]
        [ HH.text (if layer.visible then "👁" else "○") ]
    
      -- Layer name
    , HH.span [ cls [ "lattice-layer-name-timeline" ] ]
        [ HH.text (show layer.name) ]
    ]

renderTimeRuler :: forall m. State -> H.ComponentHTML Action () m
renderTimeRuler state =
  let
    rulerWidth = show (Int.toNumber state.totalFrames * state.zoom) <> "px"
  in
  HH.div
    [ cls [ "lattice-time-ruler" ]
    , HP.attr (HH.AttrName "style") (rulerStyle rulerWidth)
    ]
    (renderRulerMarks state)

renderRulerMarks :: forall m. State -> Array (H.ComponentHTML Action () m)
renderRulerMarks state =
  let
    markInterval = if state.zoom < 5.0 then 10
                   else if state.zoom < 10.0 then 5
                   else 1
    marks = generateMarks 0 state.totalFrames markInterval
  in
  map (renderMark state) marks
  where
    generateMarks :: Int -> Int -> Int -> Array Int
    generateMarks start end interval =
      if start > end then []
      else [start] <> generateMarks (start + interval) end interval

renderMark :: forall m. State -> Int -> H.ComponentHTML Action () m
renderMark state frame =
  let
    x = show (toNumber frame * state.zoom) <> "px"
    isMajor = frame `mod` 10 == 0
  in
  HH.div
    [ cls [ "lattice-ruler-mark" ]
    , HP.attr (HH.AttrName "style") (markStyle x isMajor)
    ]
    [ if isMajor
        then HH.span [ cls [ "lattice-ruler-label" ] ]
               [ HH.text (show frame) ]
        else HH.text ""
    ]

renderTracks :: forall m. State -> H.ComponentHTML Action () m
renderTracks state =
  let
    trackWidth = show (Int.toNumber state.totalFrames * state.zoom) <> "px"
  in
  HH.div
    [ cls [ "lattice-tracks" ]
    , HP.attr (HH.AttrName "style") (tracksStyle trackWidth)
    ]
    (mapWithIndex (renderTrack state) state.layers)

renderTrack :: forall m. State -> Int -> LayerBase -> H.ComponentHTML Action () m
renderTrack state _index layer =
  let
    startPx = toNumber (unwrapFrame layer.startFrame) * state.zoom
    endPx = toNumber (unwrapFrame layer.endFrame) * state.zoom
    width = endPx - startPx
  in
  HH.div
    [ cls [ "lattice-track" ]
    , HP.attr (HH.AttrName "style") (trackStyle state.layerRowHeight)
    ]
    [ -- Layer bar
      HH.div
        [ cls [ "lattice-layer-bar" ]
        , HP.attr (HH.AttrName "style") (layerBarStyle startPx width)
        ]
        []
    ]

renderPlayhead :: forall m. State -> H.ComponentHTML Action () m
renderPlayhead state =
  let
    x = toNumber state.currentFrame * state.zoom
  in
  HH.div
    [ cls [ "lattice-playhead" ]
    , HP.attr (HH.AttrName "style") (playheadStyle x)
    ]
    [ HH.div [ cls [ "lattice-playhead-head" ] ] []
    , HH.div [ cls [ "lattice-playhead-line" ] ] []
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // helpers
-- ════════════════════════════════════════════════════════════════════════════

formatTimecode :: Int -> Number -> String
formatTimecode frame fps =
  let
    totalSeconds = toNumber frame / fps
    hours = Int.floor (totalSeconds / 3600.0)
    hoursNum = Int.toNumber hours
    minutes = Int.floor ((totalSeconds - hoursNum * 3600.0) / 60.0)
    minutesNum = Int.toNumber minutes
    seconds = Int.floor (totalSeconds - hoursNum * 3600.0 - minutesNum * 60.0)
    fpsInt = Int.floor fps
    frames = if fpsInt > 0 then frame `mod` fpsInt else 0
  in
  padZero hours <> ":" <> padZero minutes <> ":" <> padZero seconds <> ":" <> padZero frames
  where
    padZero n = if n < 10 then "0" <> show n else show n

unwrapFrame :: FrameNumber -> Int
unwrapFrame (FrameNumber n) = n

toNumber :: Int -> Number
toNumber n = Int.toNumber n

elem :: forall a. Eq a => a -> Array a -> Boolean
elem x arr = length (filter (_ == x) arr) > 0

-- ════════════════════════════════════════════════════════════════════════════
--                                                          // inline // styles
-- ════════════════════════════════════════════════════════════════════════════

timelineStyle :: String
timelineStyle =
  "display: flex; flex-direction: column; height: 100%; " <>
  "background: var(--lattice-surface-1); overflow: hidden;"

headerStyle :: String
headerStyle =
  "display: flex; align-items: center; justify-content: space-between; " <>
  "padding: var(--lattice-space-2); min-height: 40px; " <>
  "border-bottom: 1px solid var(--lattice-border-subtle);"

playbackStyle :: String
playbackStyle =
  "display: flex; gap: var(--lattice-space-1);"

infoStyle :: String
infoStyle =
  "display: flex; align-items: center; gap: var(--lattice-space-3); " <>
  "font-family: var(--lattice-font-mono); font-size: var(--lattice-text-sm);"

bodyStyle :: String
bodyStyle =
  "display: flex; flex: 1; overflow: hidden;"

sidebarStyle :: String
sidebarStyle =
  "width: 200px; min-width: 150px; " <>
  "border-right: 1px solid var(--lattice-border-subtle); " <>
  "overflow-y: auto;"

viewportStyle :: String
viewportStyle =
  "flex: 1; position: relative; overflow-x: auto; overflow-y: hidden;"

layerRowStyle :: Number -> Boolean -> String
layerRowStyle height selected =
  "display: flex; align-items: center; gap: var(--lattice-space-2); " <>
  "height: " <> show height <> "px; padding: 0 var(--lattice-space-2); " <>
  "border-bottom: 1px solid var(--lattice-border-subtle); " <>
  "cursor: pointer; " <>
  (if selected then "background: var(--lattice-accent-muted);" else "")

rulerStyle :: String -> String
rulerStyle width =
  "display: flex; position: relative; height: 24px; " <>
  "min-width: " <> width <> "; " <>
  "background: var(--lattice-surface-2); " <>
  "border-bottom: 1px solid var(--lattice-border-subtle);"

markStyle :: String -> Boolean -> String
markStyle x isMajor =
  "position: absolute; left: " <> x <> "; " <>
  "height: " <> (if isMajor then "16px" else "8px") <> "; " <>
  "width: 1px; background: var(--lattice-border-subtle); " <>
  "bottom: 0;"

tracksStyle :: String -> String
tracksStyle width =
  "position: relative; min-width: " <> width <> ";"

trackStyle :: Number -> String
trackStyle height =
  "position: relative; height: " <> show height <> "px; " <>
  "border-bottom: 1px solid var(--lattice-border-subtle);"

layerBarStyle :: Number -> Number -> String
layerBarStyle left width =
  "position: absolute; left: " <> show left <> "px; " <>
  "width: " <> show width <> "px; height: 20px; top: 4px; " <>
  "background: var(--lattice-accent); border-radius: var(--lattice-radius-sm); " <>
  "cursor: pointer;"

playheadStyle :: Number -> String
playheadStyle x =
  "position: absolute; left: " <> show x <> "px; top: 0; bottom: 0; " <>
  "width: 1px; background: var(--lattice-accent-vivid); " <>
  "pointer-events: none; z-index: 10;"

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // actions
-- ════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> pure unit
  
  Receive input -> do
    H.modify_ _ 
      { layers = input.layers
      , currentFrame = input.currentFrame
      , totalFrames = input.totalFrames
      , fps = input.fps
      , selectedLayerIds = input.selectedLayerIds
      , isPlaying = input.isPlaying
      }
  
  HandleSeek frame -> do
    H.raise (SeekToFrame frame)
  
  HandlePlayPause -> do
    H.raise TogglePlayback
  
  HandleSelectLayer layerId -> do
    H.raise (SelectLayer layerId)
  
  HandleZoomIn -> do
    H.modify_ \s -> s { zoom = min 50.0 (s.zoom * 1.5) }
  
  HandleZoomOut -> do
    H.modify_ \s -> s { zoom = max 1.0 (s.zoom / 1.5) }
  
  HandleScroll x -> do
    H.modify_ _ { scrollX = x }
  
  HandleGoToStart -> do
    H.raise (SeekToFrame 0)
  
  HandleGoToEnd -> do
    state <- H.get
    H.raise (SeekToFrame (state.totalFrames - 1))
  
  HandlePrevFrame -> do
    state <- H.get
    when (state.currentFrame > 0) do
      H.raise (SeekToFrame (state.currentFrame - 1))
  
  HandleNextFrame -> do
    state <- H.get
    when (state.currentFrame < state.totalFrames - 1) do
      H.raise (SeekToFrame (state.currentFrame + 1))
