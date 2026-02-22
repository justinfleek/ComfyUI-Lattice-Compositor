-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- | TimelinePanel Render
-- |
-- | Render functions for timeline UI.
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
module Lattice.UI.Components.TimelinePanel.Render
  ( render
  ) where

import Prelude

import Data.Array (filter, length, mapWithIndex)
import Data.Int as Int
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP

import Lattice.UI.Core (cls)
import Lattice.UI.Components.CompositionTabs as CompositionTabs
import Lattice.UI.Components.EnhancedLayerTrack as EnhancedLayerTrack
import Lattice.UI.Components.TimelinePanel.Types
  ( State
  , Action(..)
  , Slots
  , LayerType(..)
  , WorkArea
  , Proxy(..)
  )
import Lattice.UI.Components.TimelinePanel.Styles as S
import Lattice.UI.Components.TimelinePanel.Helpers
  ( elem
  , formatTimecode
  , parseIntDefault
  , parseNumberDefault
  , calculatePixelsPerFrame
  , calculateTimelineWidth
  , calculateMajorStep
  )

-- ════════════════════════════════════════════════════════════════════════════
--                                                             // main render
-- ════════════════════════════════════════════════════════════════════════════

render :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
render state =
  HH.div
    [ cls [ "lattice-timeline-panel" ]
    , HP.attr (HH.AttrName "style") S.timelinePanelStyle
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

-- ════════════════════════════════════════════════════════════════════════════
--                                                                // header
-- ════════════════════════════════════════════════════════════════════════════

renderHeader :: forall m. State -> H.ComponentHTML Action Slots m
renderHeader state =
  HH.div
    [ cls [ "lattice-timeline-header" ]
    , HP.attr (HH.AttrName "style") S.timelineHeaderStyle
    ]
    [ -- Left: Timecode and frame display
      HH.div
        [ cls [ "lattice-header-left" ]
        , HP.attr (HH.AttrName "style") S.headerLeftStyle
        ]
        [ HH.span
            [ cls [ "lattice-timecode" ]
            , HP.attr (HH.AttrName "style") S.timecodeStyle
            ]
            [ HH.text (formatTimecode state.currentFrame state.fps) ]
        , HH.div [ cls [ "lattice-frame-display" ] ]
            [ HH.input
                [ cls [ "lattice-frame-input" ]
                , HP.attr (HH.AttrName "style") S.frameInputStyle
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
        , HP.attr (HH.AttrName "style") S.headerCenterStyle
        ]
        [ -- Add Layer dropdown
          renderAddLayerButton state
        
          -- Delete button
        , HH.div [ cls [ "lattice-tool-group" ] ]
            [ HH.button
                [ cls [ "lattice-delete-btn" ]
                , HP.attr (HH.AttrName "style") S.deleteBtnStyle
                , HP.disabled (length state.selectedLayerIds == 0)
                , HP.attr (HH.AttrName "aria-label") "Delete selected layers"
                , HE.onClick \_ -> HandleDeleteSelected
                ]
                [ HH.text "X" ]
            ]
        
          -- Comp Settings button
        , HH.div [ cls [ "lattice-tool-group" ] ]
            [ HH.button
                [ cls [ "lattice-comp-settings-btn" ]
                , HP.attr (HH.AttrName "style") S.compSettingsBtnStyle
                , HP.title "Composition Settings (Ctrl+K)"
                , HE.onClick \_ -> HandleOpenCompSettings
                ]
                [ HH.text "[S] Comp Settings" ]
            
              -- AI button
            , HH.button
                [ cls [ "lattice-ai-btn" ]
                , HP.attr (HH.AttrName "style") S.aiBtnStyle
                , HP.title "AI Path Suggestion"
                , HE.onClick \_ -> HandleOpenAI
                ]
                [ HH.text "[*] AI" ]
            ]
        ]
    
      -- Right: Zoom slider
    , HH.div
        [ cls [ "lattice-header-right" ]
        , HP.attr (HH.AttrName "style") S.headerRightStyle
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

-- ════════════════════════════════════════════════════════════════════════════
--                                                         // add layer menu
-- ════════════════════════════════════════════════════════════════════════════

renderAddLayerButton :: forall m. State -> H.ComponentHTML Action Slots m
renderAddLayerButton state =
  HH.div
    [ cls [ "lattice-tool-group", "add-layer-wrapper" ]
    , HP.attr (HH.AttrName "style") S.addLayerWrapperStyle
    ]
    [ HH.button
        [ cls $ [ "lattice-add-layer-btn" ] <> (if state.showAddLayerMenu then [ "active" ] else [])
        , HP.attr (HH.AttrName "style") S.addLayerBtnStyle
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
    , HP.attr (HH.AttrName "style") S.addLayerMenuStyle
    , HP.attr (HH.AttrName "role") "menu"
    , HP.attr (HH.AttrName "aria-label") "Layer types"
    ]
    [ menuItem "[S]" "Solid" Solid
    , menuItem "T" "Text" Text
    , menuItem "<>" "Shape" Shape
    , menuItem "~" "Spline" Spline
    , menuItem "->" "Path" Path
    , menuItem "[*]" "Particles" Particles
    , menuItem "[ ]" "Control" Control
    , menuItem "[C]" "Camera" Camera
    , menuItem "[L]" "Light" Light
    , menuItem ">" "Video" Video
    , menuItem "[3D]" "3D Model" Model3D
    , menuItem "[...]" "Point Cloud" PointCloud
    , menuItem "~" "Depth Map" DepthMap
    , menuItem "^" "Normal Map" NormalMap
    , menuItem "[A]" "Audio" Audio
    , menuItem "[AI]" "AI Generated" AIGenerated
    , menuItem "[G]" "Group" Group
    ]
  where
    menuItem :: String -> String -> LayerType -> H.ComponentHTML Action Slots m
    menuItem icon label layerType =
      HH.button
        [ cls [ "lattice-add-layer-menu-item" ]
        , HP.attr (HH.AttrName "style") S.addLayerMenuItemStyle
        , HP.attr (HH.AttrName "role") "menuitem"
        , HE.onClick \_ -> HandleAddLayer layerType
        ]
        [ HH.span [ cls [ "lattice-menu-icon" ] ] [ HH.text icon ]
        , HH.text (" " <> label)
        ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                              // content
-- ════════════════════════════════════════════════════════════════════════════

renderContent :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
renderContent state =
  HH.div
    [ cls [ "lattice-timeline-content" ]
    , HP.attr (HH.AttrName "style") S.timelineContentStyle
    ]
    [ -- Sidebar (layer list)
      HH.div
        [ cls [ "lattice-timeline-sidebar" ]
        , HP.attr (HH.AttrName "style") (S.timelineSidebarStyle state.sidebarWidth)
        ]
        [ renderSidebarHeader
        , renderSidebarLayers state
        ]
    
      -- Sidebar resizer
    , HH.div
        [ cls [ "lattice-sidebar-resizer" ]
        , HP.attr (HH.AttrName "style") S.sidebarResizerStyle
        ]
        []
    
      -- Track viewport
    , HH.div
        [ cls [ "lattice-track-viewport" ]
        , HP.attr (HH.AttrName "style") S.trackViewportStyle
        ]
        [ -- Time ruler
          renderTimeRuler state
        
          -- Track scroll area
        , renderTrackScrollArea state
        ]
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                             // sidebar
-- ════════════════════════════════════════════════════════════════════════════

renderSidebarHeader :: forall m. H.ComponentHTML Action Slots m
renderSidebarHeader =
  HH.div
    [ cls [ "lattice-sidebar-header-row" ]
    , HP.attr (HH.AttrName "style") S.sidebarHeaderRowStyle
    ]
    [ -- AV Features headers
      HH.div [ cls [ "lattice-col-header", "col-av-features" ] ]
        [ HH.span [ cls [ "lattice-header-icon" ], HP.title "Toggle Layer Visibility (V)" ] [ HH.text "V" ]
        , HH.span [ cls [ "lattice-header-icon" ], HP.title "Toggle Audio Mute" ] [ HH.text "A" ]
        , HH.span [ cls [ "lattice-header-icon" ], HP.title "Isolate Layer" ] [ HH.text "O" ]
        , HH.span [ cls [ "lattice-header-icon" ], HP.title "Lock Layer (Ctrl+L)" ] [ HH.text "L" ]
        ]
    
      -- Layer info headers
    , HH.div [ cls [ "lattice-col-header", "col-number" ], HP.title "Layer Number" ] [ HH.text "#" ]
    , HH.div [ cls [ "lattice-col-header", "col-name" ], HP.title "Layer Name" ] [ HH.text "Source Name" ]
    
      -- Switches headers
    , HH.div [ cls [ "lattice-col-header", "col-switches" ] ]
        [ HH.span [ cls [ "lattice-header-icon" ], HP.title "Hide Minimized" ] [ HH.text "H" ]
        , HH.span [ cls [ "lattice-header-icon" ], HP.title "Rasterize" ] [ HH.text "R" ]
        , HH.span [ cls [ "lattice-header-icon" ], HP.title "Quality" ] [ HH.text "Q" ]
        , HH.span [ cls [ "lattice-header-icon" ], HP.title "Effects" ] [ HH.text "fx" ]
        , HH.span [ cls [ "lattice-header-icon" ], HP.title "Frame Blending" ] [ HH.text "FB" ]
        , HH.span [ cls [ "lattice-header-icon" ], HP.title "Motion Blur" ] [ HH.text "MB" ]
        , HH.span [ cls [ "lattice-header-icon" ], HP.title "Effect Layer" ] [ HH.text "EL" ]
        , HH.span [ cls [ "lattice-header-icon" ], HP.title "3D Layer" ] [ HH.text "3D" ]
        ]
    
      -- Parent header
    , HH.div [ cls [ "lattice-col-header", "col-parent" ], HP.title "Parent & Link" ] [ HH.text "Parent & Link" ]
    ]

renderSidebarLayers :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
renderSidebarLayers state =
  HH.div
    [ cls [ "lattice-sidebar-scroll-area" ]
    , HP.attr (HH.AttrName "style") S.sidebarScrollAreaStyle
    ]
    (mapWithIndex (renderLayerSlot state EnhancedLayerTrack.SidebarLayout) state.layers)

-- ════════════════════════════════════════════════════════════════════════════
--                                                        // track scroll area
-- ════════════════════════════════════════════════════════════════════════════

renderTrackScrollArea :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
renderTrackScrollArea state =
  let
    timelineWidth = calculateTimelineWidth state
    playheadPct = Int.toNumber state.currentFrame / Int.toNumber state.totalFrames * 100.0
  in
  HH.div
    [ cls [ "lattice-track-scroll-area" ]
    , HP.attr (HH.AttrName "style") S.trackScrollAreaStyle
    ]
    [ HH.div
        [ cls [ "lattice-layer-bars-container" ]
        , HP.attr (HH.AttrName "style") (S.layerBarsContainerStyle timelineWidth)
        ]
        [ -- Grid background
          HH.div [ cls [ "lattice-grid-background" ] ] []
        
          -- Layer tracks
        , HH.div_
            (mapWithIndex (renderLayerSlot state EnhancedLayerTrack.TrackLayout) state.layers)
        
          -- Playhead line
        , HH.div
            [ cls [ "lattice-playhead-line" ]
            , HP.attr (HH.AttrName "style") (S.playheadLineStyle playheadPct)
            ]
            []
        ]
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                           // layer slot
-- ════════════════════════════════════════════════════════════════════════════

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

-- ════════════════════════════════════════════════════════════════════════════
--                                                            // time ruler
-- ════════════════════════════════════════════════════════════════════════════

renderTimeRuler :: forall m. State -> H.ComponentHTML Action Slots m
renderTimeRuler state =
  let
    timelineWidth = calculateTimelineWidth state
    playheadPct = Int.toNumber state.currentFrame / Int.toNumber state.totalFrames * 100.0
  in
  HH.div
    [ cls [ "lattice-ruler-scroll-wrapper" ]
    , HP.attr (HH.AttrName "style") S.rulerScrollWrapperStyle
    ]
    [ HH.div
        [ cls [ "lattice-time-ruler" ]
        , HP.attr (HH.AttrName "style") (S.timeRulerStyle timelineWidth)
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
            , HP.attr (HH.AttrName "style") (S.playheadHeadStyle playheadPct)
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
        , HP.attr (HH.AttrName "style") (S.rulerMarkStyle pct isMajor)
        ]
        [ if isMajor
            then HH.span [ cls [ "lattice-ruler-label" ] ] [ HH.text (show frame) ]
            else HH.text ""
        ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                           // work area bar
-- ════════════════════════════════════════════════════════════════════════════

renderWorkAreaBar :: forall m. State -> WorkArea -> H.ComponentHTML Action Slots m
renderWorkAreaBar state wa =
  let
    startPct = Int.toNumber wa.start / Int.toNumber state.totalFrames * 100.0
    widthPct = Int.toNumber (wa.end - wa.start) / Int.toNumber state.totalFrames * 100.0
  in
  HH.div
    [ cls [ "lattice-work-area-bar" ]
    , HP.attr (HH.AttrName "style") (S.workAreaBarStyle startPct widthPct)
    , HP.title "Render Range (B/N to set, double-click to clear)"
    , HE.onDoubleClick \_ -> HandleClearWorkArea
    ]
    [ HH.div [ cls [ "lattice-work-area-handle", "left" ] ] []
    , HH.div [ cls [ "lattice-work-area-handle", "right" ] ] []
    ]
