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
module Lattice.UI.Components.TimelinePanel
  ( component
  , Input
  , Output(..)
  , Query
  , Slot
  , LayerType(..)
  , WorkArea
  ) where

import Prelude

import Data.Array (filter, length, mapWithIndex)
import Data.Int as Int
import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP

import Lattice.UI.Core (cls)
import Lattice.UI.Components.EnhancedLayerTrack as EnhancedLayerTrack
import Lattice.UI.Components.CompositionTabs as CompositionTabs

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                     // types
-- ════════════════════════════════════════════════════════════════════════════

-- | Layer types that can be created
data LayerType
  = Solid
  | Text
  | Shape
  | Spline
  | Path
  | Particles
  | Control
  | Camera
  | Light
  | Video
  | Model3D
  | PointCloud
  | DepthMap
  | NormalMap
  | Audio
  | AIGenerated
  | Group

derive instance eqLayerType :: Eq LayerType

-- | Work area (render range)
type WorkArea =
  { start :: Int
  , end :: Int
  }

type Input =
  { layers :: Array EnhancedLayerTrack.EnhancedLayerInfo
  , compositions :: Array CompositionTabs.CompositionInfo
  , activeCompositionId :: String
  , mainCompositionId :: String
  , breadcrumbs :: Array CompositionTabs.BreadcrumbItem
  , currentFrame :: Int
  , totalFrames :: Int
  , fps :: Int
  , isPlaying :: Boolean
  , selectedLayerIds :: Array String
  , expandedLayerIds :: Array String
  , workArea :: Maybe WorkArea
  , hasAudio :: Boolean
  }

data Output
  = SeekToFrame Int
  | TogglePlayback
  | GoToStart
  | GoToEnd
  | PrevFrame
  | NextFrame
  | SetZoom Number
  | AddLayer LayerType
  | DeleteSelectedLayers
  | SelectLayer String
  | ToggleLayerExpanded String Boolean
  | UpdateLayer EnhancedLayerTrack.Output
  | OpenCompositionSettings
  | OpenPathSuggestion
  | SetWorkArea (Maybe WorkArea)
  | CompositionTabsOutput CompositionTabs.Output

data Query a

type Slot id = H.Slot Query Output id

type State =
  { layers :: Array EnhancedLayerTrack.EnhancedLayerInfo
  , compositions :: Array CompositionTabs.CompositionInfo
  , activeCompositionId :: String
  , mainCompositionId :: String
  , breadcrumbs :: Array CompositionTabs.BreadcrumbItem
  , currentFrame :: Int
  , totalFrames :: Int
  , fps :: Int
  , isPlaying :: Boolean
  , selectedLayerIds :: Array String
  , expandedLayerIds :: Array String
  , workArea :: Maybe WorkArea
  , hasAudio :: Boolean
  -- UI state
  , zoomPercent :: Number  -- 0 = fit to viewport, 100 = max zoom
  , sidebarWidth :: Int
  , showAddLayerMenu :: Boolean
  , viewportWidth :: Number
  }

-- Child slots
type Slots =
  ( compositionTabs :: CompositionTabs.Slot Unit
  , layerTrack :: EnhancedLayerTrack.Slot Int
  )

data Action
  = Initialize
  | Receive Input
  -- Playback
  | HandleTogglePlayback
  | HandleGoToStart
  | HandleGoToEnd
  | HandlePrevFrame
  | HandleNextFrame
  -- Frame input
  | HandleSetFrame Int
  -- Zoom
  | HandleZoomChange Number
  -- Add layer menu
  | HandleToggleAddLayerMenu
  | HandleAddLayer LayerType
  -- Delete
  | HandleDeleteSelected
  -- Settings
  | HandleOpenCompSettings
  | HandleOpenAI
  -- Sidebar resize
  | HandleSidebarResize Int
  -- Work area
  | HandleSetWorkAreaStart Int
  | HandleSetWorkAreaEnd Int
  | HandleClearWorkArea
  -- Ruler scrub
  | HandleRulerScrub Int
  -- Child outputs
  | HandleCompositionTabsOutput CompositionTabs.Output
  | HandleLayerTrackOutput Int EnhancedLayerTrack.Output
  -- Keyboard
  | HandleKeydown String

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
--                                                                    // render
-- ════════════════════════════════════════════════════════════════════════════

render :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
render state =
  HH.div
    [ cls [ "lattice-timeline-panel" ]
    , HP.attr (HH.AttrName "style") timelinePanelStyle
    , HP.tabIndex 0
    , HP.attr (HH.AttrName "role") "region"
    , HP.attr (HH.AttrName "aria-label") "Timeline"
    ]
    [ -- Composition Tabs
      HH.slot
        (Proxy :: Proxy "compositionTabs")
        unit
        CompositionTabs.component
        { compositions: state.compositions
        , activeCompositionId: state.activeCompositionId
        , mainCompositionId: state.mainCompositionId
        , breadcrumbs: state.breadcrumbs
        }
        HandleCompositionTabsOutput
    
      -- Timeline Header
    , renderHeader state
    
      -- Timeline Content (sidebar + tracks)
    , renderContent state
    ]

renderHeader :: forall m. State -> H.ComponentHTML Action Slots m
renderHeader state =
  HH.div
    [ cls [ "lattice-timeline-header" ]
    , HP.attr (HH.AttrName "style") timelineHeaderStyle
    ]
    [ -- Left: Timecode and frame display
      HH.div
        [ cls [ "lattice-header-left" ]
        , HP.attr (HH.AttrName "style") headerLeftStyle
        ]
        [ HH.span
            [ cls [ "lattice-timecode" ]
            , HP.attr (HH.AttrName "style") timecodeStyle
            ]
            [ HH.text (formatTimecode state.currentFrame state.fps) ]
        , HH.div [ cls [ "lattice-frame-display" ] ]
            [ HH.input
                [ cls [ "lattice-frame-input" ]
                , HP.attr (HH.AttrName "style") frameInputStyle
                , HP.type_ HP.InputNumber
                , HP.value (show state.currentFrame)
                , HE.onValueChange \val -> HandleSetFrame (parseIntDefault val 0)
                ]
            , HH.span [ cls [ "lattice-fps-label" ] ]
                [ HH.text (show state.fps <> " fps") ]
            ]
        ]
    
      -- Center: Add layer, delete, comp settings, AI
    , HH.div
        [ cls [ "lattice-header-center" ]
        , HP.attr (HH.AttrName "style") headerCenterStyle
        ]
        [ -- Add Layer dropdown
          renderAddLayerButton state
        
          -- Delete button
        , HH.div [ cls [ "lattice-tool-group" ] ]
            [ HH.button
                [ cls [ "lattice-delete-btn" ]
                , HP.attr (HH.AttrName "style") deleteBtnStyle
                , HP.disabled (length state.selectedLayerIds == 0)
                , HP.attr (HH.AttrName "aria-label") "Delete selected layers"
                , HE.onClick \_ -> HandleDeleteSelected
                ]
                [ HH.text "🗑" ]
            ]
        
          -- Comp Settings button
        , HH.div [ cls [ "lattice-tool-group" ] ]
            [ HH.button
                [ cls [ "lattice-comp-settings-btn" ]
                , HP.attr (HH.AttrName "style") compSettingsBtnStyle
                , HP.title "Composition Settings (Ctrl+K)"
                , HE.onClick \_ -> HandleOpenCompSettings
                ]
                [ HH.text "⚙ Comp Settings" ]
            
              -- AI button
            , HH.button
                [ cls [ "lattice-ai-btn" ]
                , HP.attr (HH.AttrName "style") aiBtnStyle
                , HP.title "AI Path Suggestion"
                , HE.onClick \_ -> HandleOpenAI
                ]
                [ HH.text "✨ AI" ]
            ]
        ]
    
      -- Right: Zoom slider
    , HH.div
        [ cls [ "lattice-header-right" ]
        , HP.attr (HH.AttrName "style") headerRightStyle
        ]
        [ HH.input
            [ cls [ "lattice-zoom-slider" ]
            , HP.type_ HP.InputRange
            , HP.attr (HH.AttrName "min") "0"
            , HP.attr (HH.AttrName "max") "100"
            , HP.attr (HH.AttrName "step") "1"
            , HP.value (show (Int.round state.zoomPercent))
            , HP.title "Zoom Timeline"
            , HP.attr (HH.AttrName "aria-label") "Timeline zoom level"
            , HE.onValueChange \val -> HandleZoomChange (parseNumberDefault val 0.0)
            ]
        ]
    ]

renderAddLayerButton :: forall m. State -> H.ComponentHTML Action Slots m
renderAddLayerButton state =
  HH.div
    [ cls [ "lattice-tool-group", "add-layer-wrapper" ]
    , HP.attr (HH.AttrName "style") addLayerWrapperStyle
    ]
    [ HH.button
        [ cls $ [ "lattice-add-layer-btn" ] <> (if state.showAddLayerMenu then [ "active" ] else [])
        , HP.attr (HH.AttrName "style") addLayerBtnStyle
        , HP.attr (HH.AttrName "aria-label") "Add Layer"
        , HP.attr (HH.AttrName "aria-haspopup") "menu"
        , HP.attr (HH.AttrName "aria-expanded") (if state.showAddLayerMenu then "true" else "false")
        , HE.onClick \_ -> HandleToggleAddLayerMenu
        ]
        [ HH.text "+ Layer" ]
    
      -- Dropdown menu
    , if state.showAddLayerMenu
        then renderAddLayerMenu
        else HH.text ""
    ]

renderAddLayerMenu :: forall m. H.ComponentHTML Action Slots m
renderAddLayerMenu =
  HH.div
    [ cls [ "lattice-add-layer-menu" ]
    , HP.attr (HH.AttrName "style") addLayerMenuStyle
    , HP.attr (HH.AttrName "role") "menu"
    , HP.attr (HH.AttrName "aria-label") "Layer types"
    ]
    [ menuItem "■" "Solid" Solid
    , menuItem "T" "Text" Text
    , menuItem "◇" "Shape" Shape
    , menuItem "〰" "Spline" Spline
    , menuItem "⤳" "Path" Path
    , menuItem "✨" "Particles" Particles
    , menuItem "□" "Control" Control
    , menuItem "◎" "Camera" Camera
    , menuItem "💡" "Light" Light
    , menuItem "▶" "Video" Video
    , menuItem "🎲" "3D Model" Model3D
    , menuItem "☁" "Point Cloud" PointCloud
    , menuItem "〜" "Depth Map" DepthMap
    , menuItem "↗" "Normal Map" NormalMap
    , menuItem "🔊" "Audio" Audio
    , menuItem "🤖" "AI Generated" AIGenerated
    , menuItem "📁" "Group" Group
    ]
  where
    menuItem :: String -> String -> LayerType -> H.ComponentHTML Action Slots m
    menuItem icon label layerType =
      HH.button
        [ cls [ "lattice-add-layer-menu-item" ]
        , HP.attr (HH.AttrName "style") addLayerMenuItemStyle
        , HP.attr (HH.AttrName "role") "menuitem"
        , HE.onClick \_ -> HandleAddLayer layerType
        ]
        [ HH.span [ cls [ "lattice-menu-icon" ] ] [ HH.text icon ]
        , HH.text (" " <> label)
        ]

renderContent :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
renderContent state =
  HH.div
    [ cls [ "lattice-timeline-content" ]
    , HP.attr (HH.AttrName "style") timelineContentStyle
    ]
    [ -- Sidebar (layer list)
      HH.div
        [ cls [ "lattice-timeline-sidebar" ]
        , HP.attr (HH.AttrName "style") (timelineSidebarStyle state.sidebarWidth)
        ]
        [ renderSidebarHeader
        , renderSidebarLayers state
        ]
    
      -- Sidebar resizer
    , HH.div
        [ cls [ "lattice-sidebar-resizer" ]
        , HP.attr (HH.AttrName "style") sidebarResizerStyle
        ]
        []
    
      -- Track viewport
    , HH.div
        [ cls [ "lattice-track-viewport" ]
        , HP.attr (HH.AttrName "style") trackViewportStyle
        ]
        [ -- Time ruler
          renderTimeRuler state
        
          -- Track scroll area
        , renderTrackScrollArea state
        ]
    ]

renderSidebarHeader :: forall m. H.ComponentHTML Action Slots m
renderSidebarHeader =
  HH.div
    [ cls [ "lattice-sidebar-header-row" ]
    , HP.attr (HH.AttrName "style") sidebarHeaderRowStyle
    ]
    [ -- AV Features headers
      HH.div [ cls [ "lattice-col-header", "col-av-features" ] ]
        [ HH.span [ cls [ "lattice-header-icon" ], HP.title "Toggle Layer Visibility (V)" ] [ HH.text "👁" ]
        , HH.span [ cls [ "lattice-header-icon" ], HP.title "Toggle Audio Mute" ] [ HH.text "🔊" ]
        , HH.span [ cls [ "lattice-header-icon" ], HP.title "Isolate Layer" ] [ HH.text "●" ]
        , HH.span [ cls [ "lattice-header-icon" ], HP.title "Lock Layer (Ctrl+L)" ] [ HH.text "🔒" ]
        ]
    
      -- Layer info headers
    , HH.div [ cls [ "lattice-col-header", "col-number" ], HP.title "Layer Number" ] [ HH.text "#" ]
    , HH.div [ cls [ "lattice-col-header", "col-name" ], HP.title "Layer Name" ] [ HH.text "Source Name" ]
    
      -- Switches headers
    , HH.div [ cls [ "lattice-col-header", "col-switches" ] ]
        [ HH.span [ cls [ "lattice-header-icon" ], HP.title "Hide Minimized" ] [ HH.text "👁" ]
        , HH.span [ cls [ "lattice-header-icon" ], HP.title "Rasterize" ] [ HH.text "☀" ]
        , HH.span [ cls [ "lattice-header-icon" ], HP.title "Quality" ] [ HH.text "◐" ]
        , HH.span [ cls [ "lattice-header-icon" ], HP.title "Effects" ] [ HH.text "fx" ]
        , HH.span [ cls [ "lattice-header-icon" ], HP.title "Frame Blending" ] [ HH.text "⊞" ]
        , HH.span [ cls [ "lattice-header-icon" ], HP.title "Motion Blur" ] [ HH.text "◔" ]
        , HH.span [ cls [ "lattice-header-icon" ], HP.title "Effect Layer" ] [ HH.text "◐" ]
        , HH.span [ cls [ "lattice-header-icon" ], HP.title "3D Layer" ] [ HH.text "⬡" ]
        ]
    
      -- Parent header
    , HH.div [ cls [ "lattice-col-header", "col-parent" ], HP.title "Parent & Link" ] [ HH.text "Parent & Link" ]
    ]

renderSidebarLayers :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
renderSidebarLayers state =
  HH.div
    [ cls [ "lattice-sidebar-scroll-area" ]
    , HP.attr (HH.AttrName "style") sidebarScrollAreaStyle
    ]
    (mapWithIndex (renderLayerSlot state EnhancedLayerTrack.SidebarLayout) state.layers)

renderTrackScrollArea :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
renderTrackScrollArea state =
  let
    timelineWidth = calculateTimelineWidth state
    playheadPct = Int.toNumber state.currentFrame / Int.toNumber state.totalFrames * 100.0
  in
  HH.div
    [ cls [ "lattice-track-scroll-area" ]
    , HP.attr (HH.AttrName "style") trackScrollAreaStyle
    ]
    [ HH.div
        [ cls [ "lattice-layer-bars-container" ]
        , HP.attr (HH.AttrName "style") (layerBarsContainerStyle timelineWidth)
        ]
        [ -- Grid background
          HH.div [ cls [ "lattice-grid-background" ] ] []
        
          -- Layer tracks
        , HH.div_
            (mapWithIndex (renderLayerSlot state EnhancedLayerTrack.TrackLayout) state.layers)
        
          -- Playhead line
        , HH.div
            [ cls [ "lattice-playhead-line" ]
            , HP.attr (HH.AttrName "style") (playheadLineStyle playheadPct)
            ]
            []
        ]
    ]

renderLayerSlot :: forall m. MonadAff m 
  => State 
  -> EnhancedLayerTrack.LayoutMode 
  -> Int 
  -> EnhancedLayerTrack.EnhancedLayerInfo 
  -> H.ComponentHTML Action Slots m
renderLayerSlot state layoutMode idx layer =
  let
    isSelected = layer.id `elem` state.selectedLayerIds
    isExpanded = layer.id `elem` state.expandedLayerIds
    availableParents = filter (\l -> l.id /= layer.id) state.layers
      # map \l -> { id: l.id, index: l.index, name: l.name }
    hasAudioCap = layer.layerType == "video" || layer.layerType == "audio" || layer.layerType == "nestedComp"
  in
  HH.slot
    (Proxy :: Proxy "layerTrack")
    idx
    EnhancedLayerTrack.component
    { layer: layer
    , layoutMode: layoutMode
    , isExpanded: isExpanded
    , isSelected: isSelected
    , frameCount: state.totalFrames
    , pixelsPerFrame: calculatePixelsPerFrame state
    , availableParents: availableParents
    , hasAudioCapability: hasAudioCap
    }
    (HandleLayerTrackOutput idx)

renderTimeRuler :: forall m. State -> H.ComponentHTML Action Slots m
renderTimeRuler state =
  let
    timelineWidth = calculateTimelineWidth state
    playheadPct = Int.toNumber state.currentFrame / Int.toNumber state.totalFrames * 100.0
  in
  HH.div
    [ cls [ "lattice-ruler-scroll-wrapper" ]
    , HP.attr (HH.AttrName "style") rulerScrollWrapperStyle
    ]
    [ HH.div
        [ cls [ "lattice-time-ruler" ]
        , HP.attr (HH.AttrName "style") (timeRulerStyle timelineWidth)
        ]
        [ -- Ruler marks (simplified - actual canvas drawing would need FFI)
          renderRulerMarks state
        
          -- Work area bar
        , case state.workArea of
            Just wa -> renderWorkAreaBar state wa
            Nothing -> HH.text ""
        
          -- Playhead head
        , HH.div
            [ cls [ "lattice-playhead-head" ]
            , HP.attr (HH.AttrName "style") (playheadHeadStyle playheadPct)
            ]
            []
        ]
    ]

renderRulerMarks :: forall m. State -> H.ComponentHTML Action Slots m
renderRulerMarks state =
  let
    ppf = calculatePixelsPerFrame state
    majorStep = calculateMajorStep ppf
    marks = generateMarks 0 state.totalFrames majorStep
  in
  HH.div [ cls [ "lattice-ruler-marks" ] ]
    (map (renderMark state majorStep) marks)
  where
    generateMarks :: Int -> Int -> Int -> Array Int
    generateMarks start end step =
      if start > end then []
      else [start] <> generateMarks (start + step) end step
    
    renderMark :: State -> Int -> Int -> H.ComponentHTML Action Slots m
    renderMark st majorStep frame =
      let
        pct = Int.toNumber frame / Int.toNumber st.totalFrames * 100.0
        isMajor = frame `mod` majorStep == 0
      in
      HH.div
        [ cls [ "lattice-ruler-mark" ]
        , HP.attr (HH.AttrName "style") (rulerMarkStyle pct isMajor)
        ]
        [ if isMajor
            then HH.span [ cls [ "lattice-ruler-label" ] ] [ HH.text (show frame) ]
            else HH.text ""
        ]

renderWorkAreaBar :: forall m. State -> WorkArea -> H.ComponentHTML Action Slots m
renderWorkAreaBar state wa =
  let
    startPct = Int.toNumber wa.start / Int.toNumber state.totalFrames * 100.0
    widthPct = Int.toNumber (wa.end - wa.start) / Int.toNumber state.totalFrames * 100.0
  in
  HH.div
    [ cls [ "lattice-work-area-bar" ]
    , HP.attr (HH.AttrName "style") (workAreaBarStyle startPct widthPct)
    , HP.title "Render Range (B/N to set, double-click to clear)"
    , HE.onDoubleClick \_ -> HandleClearWorkArea
    ]
    [ HH.div [ cls [ "lattice-work-area-handle", "left" ] ] []
    , HH.div [ cls [ "lattice-work-area-handle", "right" ] ] []
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                                  // helpers
-- ════════════════════════════════════════════════════════════════════════════

elem :: forall a. Eq a => a -> Array a -> Boolean
elem x arr = length (filter (_ == x) arr) > 0

formatTimecode :: Int -> Int -> String
formatTimecode frame fps =
  let
    totalSeconds = Int.toNumber frame / Int.toNumber fps
    hours = Int.floor (totalSeconds / 3600.0)
    hoursNum = Int.toNumber hours
    minutes = Int.floor ((totalSeconds - hoursNum * 3600.0) / 60.0)
    minutesNum = Int.toNumber minutes
    seconds = Int.floor (totalSeconds - hoursNum * 3600.0 - minutesNum * 60.0)
    frames = if fps > 0 then frame `mod` fps else 0
  in
  padZero hours <> ";" <> padZero minutes <> ";" <> padZero seconds <> ";" <> padZero frames
  where
    padZero n = if n < 10 then "0" <> show n else show n

parseIntDefault :: String -> Int -> Int
parseIntDefault s def = 
  case Int.fromString s of
    Just n -> n
    Nothing -> def

parseNumberDefault :: String -> Number -> Number
parseNumberDefault s def =
  case Int.fromString s of
    Just n -> Int.toNumber n
    Nothing -> def

calculatePixelsPerFrame :: State -> Number
calculatePixelsPerFrame state =
  let
    minPpf = state.viewportWidth / Int.toNumber state.totalFrames
    maxPpf = 80.0
  in
  minPpf + (state.zoomPercent / 100.0) * (maxPpf - minPpf)

calculateTimelineWidth :: State -> Number
calculateTimelineWidth state =
  if state.zoomPercent == 0.0
    then state.viewportWidth
    else Int.toNumber state.totalFrames * calculatePixelsPerFrame state

calculateMajorStep :: Number -> Int
calculateMajorStep ppf =
  if ppf < 5.0 then 10
  else if ppf < 10.0 then 5
  else 1

-- ════════════════════════════════════════════════════════════════════════════
--                                                                    // styles
-- ════════════════════════════════════════════════════════════════════════════

timelinePanelStyle :: String
timelinePanelStyle =
  "display: flex; " <>
  "flex-direction: column; " <>
  "height: 100%; " <>
  "background: var(--lattice-surface-1, #0f0f0f); " <>
  "color: var(--lattice-text-primary, #eee); " <>
  "font-family: var(--lattice-font-sans, 'Segoe UI', sans-serif); " <>
  "font-size: 13px; " <>
  "user-select: none;"

timelineHeaderStyle :: String
timelineHeaderStyle =
  "height: 48px; " <>
  "background: var(--lattice-surface-1, #0f0f0f); " <>
  "display: flex; " <>
  "justify-content: space-between; " <>
  "padding: 0 16px; " <>
  "align-items: center; " <>
  "z-index: 20; " <>
  "flex-shrink: 0;"

headerLeftStyle :: String
headerLeftStyle =
  "display: flex; " <>
  "gap: 12px; " <>
  "align-items: center;"

headerCenterStyle :: String
headerCenterStyle =
  "display: flex; " <>
  "gap: 12px; " <>
  "align-items: center;"

headerRightStyle :: String
headerRightStyle =
  "display: flex; " <>
  "gap: 12px; " <>
  "align-items: center;"

timecodeStyle :: String
timecodeStyle =
  "font-family: var(--lattice-font-mono, 'Consolas', monospace); " <>
  "font-size: 16px; " <>
  "color: var(--lattice-accent, #8B5CF6); " <>
  "font-weight: bold; " <>
  "letter-spacing: 1px;"

frameInputStyle :: String
frameInputStyle =
  "width: 60px; " <>
  "background: var(--lattice-surface-2, #161616); " <>
  "border: 1px solid var(--lattice-border-default, #2a2a2a); " <>
  "color: var(--lattice-text-primary, #eee); " <>
  "padding: 4px 8px; " <>
  "border-radius: 4px; " <>
  "font-size: 13px;"

addLayerWrapperStyle :: String
addLayerWrapperStyle =
  "position: relative;"

addLayerBtnStyle :: String
addLayerBtnStyle =
  "padding: 6px 12px; " <>
  "background: var(--lattice-surface-3, #1e1e1e); " <>
  "border: 1px solid var(--lattice-border-default, #2a2a2a); " <>
  "color: white; " <>
  "border-radius: 4px; " <>
  "cursor: pointer; " <>
  "font-size: 13px; " <>
  "font-weight: bold;"

addLayerMenuStyle :: String
addLayerMenuStyle =
  "position: absolute; " <>
  "bottom: 100%; " <>
  "left: 0; " <>
  "margin-bottom: 8px; " <>
  "background: var(--lattice-surface-2, #161616); " <>
  "border: 1px solid var(--lattice-border-default, #2a2a2a); " <>
  "border-radius: 6px; " <>
  "display: flex; " <>
  "flex-direction: column; " <>
  "min-width: 160px; " <>
  "max-height: 320px; " <>
  "overflow-y: auto; " <>
  "z-index: 100000; " <>
  "box-shadow: 0 -8px 24px rgba(0,0,0,0.6);"

addLayerMenuItemStyle :: String
addLayerMenuItemStyle =
  "text-align: left; " <>
  "padding: 10px 14px; " <>
  "border: none; " <>
  "background: transparent; " <>
  "color: var(--lattice-text-primary, #ddd); " <>
  "cursor: pointer; " <>
  "font-size: 13px; " <>
  "display: flex; " <>
  "align-items: center; " <>
  "gap: 8px;"

deleteBtnStyle :: String
deleteBtnStyle =
  "padding: 6px 10px; " <>
  "background: transparent; " <>
  "border: 1px solid var(--lattice-border-default, #2a2a2a); " <>
  "color: var(--lattice-text-muted, #888); " <>
  "border-radius: 4px; " <>
  "cursor: pointer;"

compSettingsBtnStyle :: String
compSettingsBtnStyle =
  "padding: 6px 14px; " <>
  "background: var(--lattice-accent-muted, rgba(139, 92, 246, 0.15)); " <>
  "border: 1px solid var(--lattice-accent, #8B5CF6); " <>
  "color: white; " <>
  "border-radius: 4px; " <>
  "cursor: pointer; " <>
  "font-size: 13px; " <>
  "font-weight: 500;"

aiBtnStyle :: String
aiBtnStyle =
  "padding: 6px 12px; " <>
  "background: linear-gradient(135deg, #8B5CF6, #A78BFA); " <>
  "border: none; " <>
  "color: white; " <>
  "border-radius: 4px; " <>
  "cursor: pointer; " <>
  "font-size: 13px; " <>
  "font-weight: 500;"

timelineContentStyle :: String
timelineContentStyle =
  "flex: 1; " <>
  "display: flex; " <>
  "overflow: hidden; " <>
  "position: relative; " <>
  "min-height: 0;"

timelineSidebarStyle :: Int -> String
timelineSidebarStyle width =
  "width: " <> show width <> "px; " <>
  "background: var(--lattice-surface-1, #0f0f0f); " <>
  "border-right: 1px solid var(--lattice-border-subtle, #1a1a1a); " <>
  "display: flex; " <>
  "flex-direction: column; " <>
  "flex-shrink: 0; " <>
  "z-index: 10;"

sidebarHeaderRowStyle :: String
sidebarHeaderRowStyle =
  "height: 34px; " <>
  "background: var(--lattice-surface-2, #161616); " <>
  "display: flex; " <>
  "align-items: center; " <>
  "border-bottom: 1px solid var(--lattice-border-subtle, #1a1a1a);"

sidebarScrollAreaStyle :: String
sidebarScrollAreaStyle =
  "flex: 1; " <>
  "overflow-y: auto; " <>
  "overflow-x: hidden;"

sidebarResizerStyle :: String
sidebarResizerStyle =
  "width: 4px; " <>
  "background: var(--lattice-surface-0, #080808); " <>
  "cursor: col-resize; " <>
  "flex-shrink: 0; " <>
  "z-index: 15;"

trackViewportStyle :: String
trackViewportStyle =
  "flex: 1; " <>
  "display: flex; " <>
  "flex-direction: column; " <>
  "overflow: hidden; " <>
  "position: relative; " <>
  "background: var(--lattice-surface-1, #121212);"

rulerScrollWrapperStyle :: String
rulerScrollWrapperStyle =
  "height: 42px; " <>
  "overflow-x: auto; " <>
  "overflow-y: hidden; " <>
  "flex-shrink: 0; " <>
  "padding-top: 2px;"

timeRulerStyle :: Number -> String
timeRulerStyle width =
  "height: 36px; " <>
  "margin-top: 4px; " <>
  "width: " <> show width <> "px; " <>
  "position: relative; " <>
  "background: var(--lattice-surface-2, #1a1a1a); " <>
  "border-bottom: 1px solid var(--lattice-border-subtle, #1a1a1a); " <>
  "border-top: 1px solid var(--lattice-border-subtle, #1a1a1a); " <>
  "cursor: pointer; " <>
  "z-index: 10;"

rulerMarkStyle :: Number -> Boolean -> String
rulerMarkStyle pct isMajor =
  "position: absolute; " <>
  "left: " <> show pct <> "%; " <>
  "height: " <> (if isMajor then "16px" else "8px") <> "; " <>
  "width: 1px; " <>
  "background: var(--lattice-border-subtle, #555); " <>
  "bottom: 0;"

workAreaBarStyle :: Number -> Number -> String
workAreaBarStyle leftPct widthPct =
  "position: absolute; " <>
  "top: 0; " <>
  "height: 100%; " <>
  "left: " <> show leftPct <> "%; " <>
  "width: " <> show widthPct <> "%; " <>
  "background: var(--lattice-accent-muted, rgba(139, 92, 246, 0.25)); " <>
  "border-left: 2px solid var(--lattice-accent, #8B5CF6); " <>
  "border-right: 2px solid var(--lattice-accent, #8B5CF6); " <>
  "z-index: 5; " <>
  "cursor: move;"

playheadHeadStyle :: Number -> String
playheadHeadStyle pct =
  "position: absolute; " <>
  "top: 0; " <>
  "left: " <> show pct <> "%; " <>
  "width: 2px; " <>
  "height: 30px; " <>
  "background: var(--lattice-accent, #8B5CF6); " <>
  "z-index: 20; " <>
  "pointer-events: none; " <>
  "box-shadow: 0 0 8px var(--lattice-accent-glow, rgba(139, 92, 246, 0.3));"

trackScrollAreaStyle :: String
trackScrollAreaStyle =
  "flex: 1; " <>
  "overflow: auto; " <>
  "min-height: 0;"

layerBarsContainerStyle :: Number -> String
layerBarsContainerStyle width =
  "position: relative; " <>
  "width: " <> show width <> "px; " <>
  "min-height: 100%;"

playheadLineStyle :: Number -> String
playheadLineStyle pct =
  "position: absolute; " <>
  "top: 0; " <>
  "bottom: 0; " <>
  "left: " <> show pct <> "%; " <>
  "width: 2px; " <>
  "background: var(--lattice-accent, #8B5CF6); " <>
  "pointer-events: none; " <>
  "z-index: 10; " <>
  "box-shadow: 0 0 8px var(--lattice-accent-glow, rgba(139, 92, 246, 0.3));"

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // actions
-- ════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action Slots Output m Unit
handleAction = case _ of
  Initialize -> do
    pure unit
  
  Receive input -> do
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
  
  HandleTogglePlayback -> do
    H.raise TogglePlayback
  
  HandleGoToStart -> do
    H.raise GoToStart
  
  HandleGoToEnd -> do
    H.raise GoToEnd
  
  HandlePrevFrame -> do
    H.raise PrevFrame
  
  HandleNextFrame -> do
    H.raise NextFrame
  
  HandleSetFrame frame -> do
    H.raise (SeekToFrame frame)
  
  HandleZoomChange pct -> do
    H.modify_ _ { zoomPercent = pct }
    H.raise (SetZoom pct)
  
  HandleToggleAddLayerMenu -> do
    H.modify_ \s -> s { showAddLayerMenu = not s.showAddLayerMenu }
  
  HandleAddLayer layerType -> do
    H.modify_ _ { showAddLayerMenu = false }
    H.raise (AddLayer layerType)
  
  HandleDeleteSelected -> do
    H.raise DeleteSelectedLayers
  
  HandleOpenCompSettings -> do
    H.raise OpenCompositionSettings
  
  HandleOpenAI -> do
    H.raise OpenPathSuggestion
  
  HandleSidebarResize width -> do
    H.modify_ _ { sidebarWidth = max 450 width }
  
  HandleSetWorkAreaStart frame -> do
    state <- H.get
    let newWorkArea = case state.workArea of
          Just wa -> Just { start: frame, end: wa.end }
          Nothing -> Just { start: frame, end: state.totalFrames - 1 }
    H.raise (SetWorkArea newWorkArea)
  
  HandleSetWorkAreaEnd frame -> do
    state <- H.get
    let newWorkArea = case state.workArea of
          Just wa -> Just { start: wa.start, end: frame }
          Nothing -> Just { start: 0, end: frame }
    H.raise (SetWorkArea newWorkArea)
  
  HandleClearWorkArea -> do
    H.raise (SetWorkArea Nothing)
  
  HandleRulerScrub frame -> do
    H.raise (SeekToFrame frame)
  
  HandleCompositionTabsOutput output -> do
    H.raise (CompositionTabsOutput output)
  
  HandleLayerTrackOutput _idx output -> do
    H.raise (UpdateLayer output)
  
  HandleKeydown key -> do
    case key of
      "Space" -> handleAction HandleTogglePlayback
      "Home" -> handleAction HandleGoToStart
      "End" -> handleAction HandleGoToEnd
      "ArrowLeft" -> handleAction HandlePrevFrame
      "ArrowRight" -> handleAction HandleNextFrame
      "Delete" -> handleAction HandleDeleteSelected
      "Backspace" -> handleAction HandleDeleteSelected
      _ -> pure unit

-- Type-level proxy for slot selection
data Proxy (sym :: Symbol) = Proxy
