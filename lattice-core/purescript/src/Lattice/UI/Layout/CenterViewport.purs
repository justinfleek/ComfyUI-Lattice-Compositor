-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                           // lattice // ui // center-viewport
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- |
-- | Center Viewport Component
-- |
-- | Main viewport area with canvas, rulers, guides, and timeline.
-- | Split pane: viewport (top) and timeline/curve editor (bottom).
-- |
-- | Viewport Tabs:
-- | - Composition: 3D canvas view of the composition
-- | - Layer: Isolated view of selected layer
-- | - Footage: Raw footage preview
-- |
-- | Features:
-- | - Grid overlay (toggleable)
-- | - Rulers with draggable guides
-- | - Snap indicators
-- | - Safe zones
-- | - Curve editor panel (toggleable)
-- |
module Lattice.UI.Layout.CenterViewport
  ( component
  , Input
  , Output(..)
  , Query
  , Slot
  , ViewportTab(..)
  , ViewOptions
  , Guide
  , ViewportAction(..)
  ) where

import Prelude

import Data.Array (mapWithIndex, length)
import Data.Int (toNumber, floor)
import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP

import Lattice.UI.Core (cls)

-- ════════════════════════════════════════════════════════════════════════════
--                                                                     // types
-- ════════════════════════════════════════════════════════════════════════════

data ViewportTab
  = TabComposition
  | TabLayer
  | TabFootage

derive instance eqViewportTab :: Eq ViewportTab

type ViewOptions =
  { showGrid :: Boolean
  , showRulers :: Boolean
  , showAxes :: Boolean
  , showCameraFrustum :: Boolean
  , showCompositionBounds :: Boolean
  , showFocalPlane :: Boolean
  , showLayerOutlines :: Boolean
  , showSafeZones :: Boolean
  , showGuides :: Boolean
  , gridSize :: Int
  , gridDivisions :: Int
  }

type Guide =
  { id :: String
  , orientation :: String  -- "horizontal" | "vertical"
  , position :: Number
  }

type Input =
  { viewportTab :: ViewportTab
  , viewOptions :: ViewOptions
  , showCurveEditor :: Boolean
  , guides :: Array Guide
  , snapEnabled :: Boolean
  , snapIndicatorX :: Maybe Number
  , snapIndicatorY :: Maybe Number
  , compWidth :: Int
  , compHeight :: Int
  , currentFrame :: Int
  , totalFrames :: Int
  , fps :: Number
  }

-- | Actions emitted from viewport
data ViewportAction
  = ViewportTabChanged ViewportTab
  | ViewOptionsChanged ViewOptions
  | ToggleCurveEditor
  | GuideCreated String Number  -- orientation, position
  | GuideMoved String Number    -- id, newPosition
  | GuideDeleted String
  | AllGuidesCleared
  | OpenCompositionSettings
  | OpenPathSuggestion
  | CanvasClicked Number Number
  | CanvasZoomed Number

data Output = ViewportActionSelected ViewportAction

data Query a

type Slot id = H.Slot Query Output id

type State =
  { viewportTab :: ViewportTab
  , viewOptions :: ViewOptions
  , showCurveEditor :: Boolean
  , guides :: Array Guide
  , snapEnabled :: Boolean
  , snapIndicatorX :: Maybe Number
  , snapIndicatorY :: Maybe Number
  , compWidth :: Int
  , compHeight :: Int
  , currentFrame :: Int
  , totalFrames :: Int
  , fps :: Number
  }

data Action
  = Initialize
  | Receive Input
  | SwitchTab ViewportTab
  | ToggleRulers
  | ToggleGrid
  | ToggleCurveEditorAction
  | EmitAction ViewportAction

type Slots :: Row Type
type Slots = ()

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
  { viewportTab: input.viewportTab
  , viewOptions: input.viewOptions
  , showCurveEditor: input.showCurveEditor
  , guides: input.guides
  , snapEnabled: input.snapEnabled
  , snapIndicatorX: input.snapIndicatorX
  , snapIndicatorY: input.snapIndicatorY
  , compWidth: input.compWidth
  , compHeight: input.compHeight
  , currentFrame: input.currentFrame
  , totalFrames: input.totalFrames
  , fps: input.fps
  }

-- ════════════════════════════════════════════════════════════════════════════
--                                                                    // render
-- ════════════════════════════════════════════════════════════════════════════

render :: forall m. State -> H.ComponentHTML Action Slots m
render state =
  HH.div
    [ cls [ "lattice-center-viewport" ]
    , HP.attr (HH.AttrName "style") viewportContainerStyle
    ]
    [ -- Viewport section (top)
      HH.div
        [ cls [ "lattice-viewport-section" ]
        , HP.attr (HH.AttrName "style") viewportSectionStyle
        ]
        [ renderViewportHeader state
        , renderViewportContent state
        ]
    
    , -- Resize handle
      HH.div
        [ cls [ "lattice-resize-handle" ]
        , HP.attr (HH.AttrName "style") resizeHandleStyle
        ]
        []
    
    , -- Timeline section (bottom)
      HH.div
        [ cls [ "lattice-timeline-section" ]
        , HP.attr (HH.AttrName "style") timelineSectionStyle
        ]
        [ if state.showCurveEditor
            then renderSplitTimeline state
            else renderTimeline state
        ]
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                           // viewport header
-- ════════════════════════════════════════════════════════════════════════════

renderViewportHeader :: forall m. State -> H.ComponentHTML Action Slots m
renderViewportHeader state =
  HH.div
    [ cls [ "lattice-viewport-header" ]
    , HP.attr (HH.AttrName "style") viewportHeaderStyle
    ]
    [ -- Tabs
      HH.div
        [ cls [ "lattice-viewport-tabs" ]
        , HP.attr (HH.AttrName "role") "tablist"
        , HP.attr (HH.AttrName "aria-label") "Viewport tabs"
        ]
        [ viewportTabButton state TabComposition "Composition"
        , viewportTabButton state TabLayer "Layer"
        , viewportTabButton state TabFootage "Footage"
        ]
    
    , -- Controls
      HH.div [ cls [ "lattice-viewport-controls" ] ]
        [ controlButton state.viewOptions.showRulers "ruler" "Toggle Rulers/Guides" ToggleRulers
        , controlButton state.viewOptions.showGrid "grid" "Toggle Grid" ToggleGrid
        ]
    ]

viewportTabButton :: forall m. State -> ViewportTab -> String -> H.ComponentHTML Action Slots m
viewportTabButton state tab label =
  HH.button
    [ cls [ "lattice-viewport-tab-btn" ]
    , HP.attr (HH.AttrName "role") "tab"
    , HP.attr (HH.AttrName "aria-selected") (if state.viewportTab == tab then "true" else "false")
    , HP.attr (HH.AttrName "style") (viewportTabStyle (state.viewportTab == tab))
    , HE.onClick \_ -> SwitchTab tab
    ]
    [ HH.text label ]

controlButton :: forall m. Boolean -> String -> String -> Action -> H.ComponentHTML Action Slots m
controlButton active iconName tooltip action =
  HH.button
    [ cls [ "lattice-control-btn" ]
    , HP.attr (HH.AttrName "style") (controlBtnStyle active)
    , HP.title tooltip
    , HP.attr (HH.AttrName "aria-pressed") (if active then "true" else "false")
    , HE.onClick \_ -> action
    ]
    [ HH.span [ cls [ "lattice-control-icon" ] ] 
        [ HH.text (iconText iconName) ]
    ]

iconText :: String -> String
iconText = case _ of
  "ruler" -> "📏"
  "grid" -> "▦"
  _ -> "●"

-- ════════════════════════════════════════════════════════════════════════════
--                                                          // viewport content
-- ════════════════════════════════════════════════════════════════════════════

renderViewportContent :: forall m. State -> H.ComponentHTML Action Slots m
renderViewportContent state =
  HH.div
    [ cls [ "lattice-viewport-content" ]
    , HP.attr (HH.AttrName "style") (viewportContentStyle state.viewOptions.showRulers)
    ]
    [ -- Grid overlay
      if state.viewOptions.showGrid
        then renderGridOverlay state
        else HH.text ""
    
    , -- Guides overlay
      if length state.guides > 0
        then renderGuidesOverlay state.guides
        else HH.text ""
    
    , -- Rulers overlay
      if state.viewOptions.showRulers
        then renderRulersOverlay state
        else HH.text ""
    
    , -- Snap indicator
      if state.snapEnabled
        then renderSnapIndicator state.snapIndicatorX state.snapIndicatorY
        else HH.text ""
    
    , -- Main canvas area
      renderCanvasArea state
    ]

renderGridOverlay :: forall m. State -> H.ComponentHTML Action Slots m
renderGridOverlay state =
  HH.div
    [ cls [ "lattice-grid-overlay" ]
    , HP.attr (HH.AttrName "style") (gridOverlayStyle state.viewOptions.gridSize)
    ]
    []

renderGuidesOverlay :: forall m. Array Guide -> H.ComponentHTML Action Slots m
renderGuidesOverlay guides =
  HH.div
    [ cls [ "lattice-guides-overlay" ]
    , HP.attr (HH.AttrName "style") guidesOverlayStyle
    ]
    (map renderGuide guides)

renderGuide :: forall m. Guide -> H.ComponentHTML Action Slots m
renderGuide guide =
  HH.div
    [ cls [ "lattice-guide", "lattice-guide-" <> guide.orientation ]
    , HP.attr (HH.AttrName "style") (guideStyle guide)
    ]
    [ HH.button
        [ cls [ "lattice-guide-delete" ]
        , HP.attr (HH.AttrName "style") guideDeleteStyle
        , HP.title "Delete guide"
        ]
        [ HH.text "×" ]
    ]

renderRulersOverlay :: forall m. State -> H.ComponentHTML Action Slots m
renderRulersOverlay state =
  HH.div
    [ cls [ "lattice-rulers-overlay" ]
    , HP.attr (HH.AttrName "style") rulersOverlayStyle
    ]
    [ -- Horizontal ruler
      HH.div
        [ cls [ "lattice-ruler", "lattice-ruler-horizontal" ]
        , HP.attr (HH.AttrName "style") horizontalRulerStyle
        ]
        (mapWithIndex (renderHorizontalTick state.compWidth) (tickPositions 20))
    
    , -- Vertical ruler
      HH.div
        [ cls [ "lattice-ruler", "lattice-ruler-vertical" ]
        , HP.attr (HH.AttrName "style") verticalRulerStyle
        ]
        (mapWithIndex (renderVerticalTick state.compHeight) (tickPositions 20))
    ]

tickPositions :: Int -> Array Int
tickPositions n = 
  let go i acc = if i > n then acc else go (i + 1) (acc <> [i])
  in go 1 []

renderHorizontalTick :: forall m. Int -> Int -> Int -> H.ComponentHTML Action Slots m
renderHorizontalTick compWidth _ i =
  let
    percent = toNumber (i * 5)
    value = floor ((percent / 100.0) * toNumber compWidth)
  in
    HH.span
      [ cls [ "lattice-ruler-tick" ]
      , HP.attr (HH.AttrName "style") ("position: absolute; left: " <> show percent <> "%; transform: translateX(-50%); bottom: 2px; font-size: 8px; color: var(--lattice-text-secondary, #888);")
      ]
      [ HH.text (show value) ]

renderVerticalTick :: forall m. Int -> Int -> Int -> H.ComponentHTML Action Slots m
renderVerticalTick compHeight _ i =
  let
    percent = toNumber (i * 5)
    value = floor ((percent / 100.0) * toNumber compHeight)
  in
    HH.span
      [ cls [ "lattice-ruler-tick" ]
      , HP.attr (HH.AttrName "style") ("position: absolute; top: " <> show percent <> "%; transform: translateY(-50%); right: 2px; font-size: 8px; color: var(--lattice-text-secondary, #888); writing-mode: vertical-rl; text-orientation: mixed;")
      ]
      [ HH.text (show value) ]

renderSnapIndicator :: forall m. Maybe Number -> Maybe Number -> H.ComponentHTML Action Slots m
renderSnapIndicator snapX snapY =
  HH.div
    [ cls [ "lattice-snap-indicator" ]
    , HP.attr (HH.AttrName "style") snapIndicatorContainerStyle
    ]
    [ case snapX of
        Just x -> HH.div
                    [ cls [ "lattice-snap-line", "lattice-snap-vertical" ]
                    , HP.attr (HH.AttrName "style") ("position: absolute; left: " <> show x <> "px; top: 0; bottom: 0; width: 1px; background: var(--lattice-warning, #f59e0b);")
                    ]
                    []
        Nothing -> HH.text ""
    , case snapY of
        Just y -> HH.div
                    [ cls [ "lattice-snap-line", "lattice-snap-horizontal" ]
                    , HP.attr (HH.AttrName "style") ("position: absolute; top: " <> show y <> "px; left: 0; right: 0; height: 1px; background: var(--lattice-warning, #f59e0b);")
                    ]
                    []
        Nothing -> HH.text ""
    ]

renderCanvasArea :: forall m. State -> H.ComponentHTML Action Slots m
renderCanvasArea state =
  HH.div
    [ cls [ "lattice-canvas-area" ]
    , HP.attr (HH.AttrName "style") canvasAreaStyle
    ]
    [ -- Canvas placeholder - actual WebGPU canvas is managed by Haskell backend
      HH.div
        [ cls [ "lattice-canvas-placeholder" ]
        , HP.attr (HH.AttrName "style") canvasPlaceholderStyle
        , HP.id "lattice-webgpu-canvas"
        ]
        [ -- Canvas info overlay
          HH.div
            [ cls [ "lattice-canvas-info" ]
            , HP.attr (HH.AttrName "style") canvasInfoStyle
            ]
            [ HH.text (show state.compWidth <> " × " <> show state.compHeight)
            , HH.text " | "
            , HH.text (viewportTabName state.viewportTab)
            ]
        ]
    ]

viewportTabName :: ViewportTab -> String
viewportTabName = case _ of
  TabComposition -> "Composition"
  TabLayer -> "Layer"
  TabFootage -> "Footage"

-- ════════════════════════════════════════════════════════════════════════════
--                                                                  // timeline
-- ════════════════════════════════════════════════════════════════════════════

renderTimeline :: forall m. State -> H.ComponentHTML Action Slots m
renderTimeline state =
  HH.div
    [ cls [ "lattice-timeline-panel" ]
    , HP.attr (HH.AttrName "style") timelinePanelStyle
    ]
    [ -- Timeline header
      renderTimelineHeader state
    
    , -- Timeline content (layer tracks + time ruler)
      HH.div
        [ cls [ "lattice-timeline-content" ]
        , HP.attr (HH.AttrName "style") timelineContentStyle
        ]
        [ -- Layer list (left)
          HH.div
            [ cls [ "lattice-layer-list" ]
            , HP.attr (HH.AttrName "style") layerListStyle
            ]
            [ renderTimelineLayer "Background" "visible" false
            , renderTimelineLayer "Camera 1" "camera" false
            , renderTimelineLayer "Shape Layer" "shape" true
            , renderTimelineLayer "Text Layer" "text" false
            ]
        
        , -- Keyframe area (right)
          HH.div
            [ cls [ "lattice-keyframe-area" ]
            , HP.attr (HH.AttrName "style") keyframeAreaStyle
            ]
            [ -- Time ruler
              HH.div
                [ cls [ "lattice-time-ruler" ]
                , HP.attr (HH.AttrName "style") timeRulerStyle
                ]
                []
            
            , -- Playhead
              HH.div
                [ cls [ "lattice-playhead" ]
                , HP.attr (HH.AttrName "style") (playheadStyle state.currentFrame state.totalFrames)
                ]
                []
            
            , -- Keyframe tracks
              HH.div
                [ cls [ "lattice-keyframe-tracks" ]
                , HP.attr (HH.AttrName "style") keyframeTracksStyle
                ]
                [ renderKeyframeTrack 0 [0.1, 0.3, 0.7]
                , renderKeyframeTrack 1 []
                , renderKeyframeTrack 2 [0.0, 0.5, 1.0]
                , renderKeyframeTrack 3 [0.2, 0.8]
                ]
            ]
        ]
    ]

renderTimelineHeader :: forall m. State -> H.ComponentHTML Action Slots m
renderTimelineHeader state =
  HH.div
    [ cls [ "lattice-timeline-header" ]
    , HP.attr (HH.AttrName "style") timelineHeaderStyle
    ]
    [ HH.span [] [ HH.text "Timeline" ]
    , HH.div [ cls [ "lattice-timeline-controls" ] ]
        [ HH.button
            [ cls [ "lattice-icon-btn" ]
            , HP.title "Composition Settings"
            , HP.attr (HH.AttrName "style") iconBtnStyle
            , HE.onClick \_ -> EmitAction OpenCompositionSettings
            ]
            [ HH.text "⚙" ]
        , HH.button
            [ cls [ "lattice-icon-btn" ]
            , HP.attr (HH.AttrName "style") (iconBtnStyle <> if state.showCurveEditor then " color: var(--lattice-accent);" else "")
            , HP.title "Toggle Curve Editor"
            , HE.onClick \_ -> ToggleCurveEditorAction
            ]
            [ HH.text "📈" ]
        ]
    ]

renderTimelineLayer :: forall m. String -> String -> Boolean -> H.ComponentHTML Action Slots m
renderTimelineLayer name layerType selected =
  HH.div
    [ cls [ "lattice-timeline-layer" ]
    , HP.attr (HH.AttrName "style") (timelineLayerStyle selected)
    ]
    [ HH.span [ cls [ "lattice-layer-icon" ] ] [ HH.text (layerIcon layerType) ]
    , HH.span [ cls [ "lattice-layer-name" ] ] [ HH.text name ]
    , HH.div [ cls [ "lattice-layer-controls" ] ]
        [ HH.button
            [ cls [ "lattice-tiny-btn" ]
            , HP.title "Visibility"
            ]
            [ HH.text "👁" ]
        , HH.button
            [ cls [ "lattice-tiny-btn" ]
            , HP.title "Lock"
            ]
            [ HH.text "🔓" ]
        ]
    ]

layerIcon :: String -> String
layerIcon = case _ of
  "camera" -> "📷"
  "shape" -> "⬜"
  "text" -> "T"
  "light" -> "💡"
  "audio" -> "🔊"
  _ -> "◻"

renderKeyframeTrack :: forall m. Int -> Array Number -> H.ComponentHTML Action Slots m
renderKeyframeTrack _ keyframes =
  HH.div
    [ cls [ "lattice-keyframe-track" ]
    , HP.attr (HH.AttrName "style") keyframeTrackStyle
    ]
    (map renderKeyframe keyframes)

renderKeyframe :: forall m. Number -> H.ComponentHTML Action Slots m
renderKeyframe position =
  HH.div
    [ cls [ "lattice-keyframe" ]
    , HP.attr (HH.AttrName "style") (keyframeStyle position)
    ]
    []

-- ════════════════════════════════════════════════════════════════════════════
--                                                   // timeline + curve editor
-- ════════════════════════════════════════════════════════════════════════════

renderSplitTimeline :: forall m. State -> H.ComponentHTML Action Slots m
renderSplitTimeline state =
  HH.div
    [ cls [ "lattice-split-timeline" ]
    , HP.attr (HH.AttrName "style") splitTimelineStyle
    ]
    [ -- Timeline (top half)
      HH.div
        [ cls [ "lattice-timeline-half" ]
        , HP.attr (HH.AttrName "style") timelineHalfStyle
        ]
        [ renderTimeline state ]
    
    , -- Curve Editor (bottom half)
      HH.div
        [ cls [ "lattice-curve-editor-half" ]
        , HP.attr (HH.AttrName "style") curveEditorHalfStyle
        ]
        [ renderCurveEditor state ]
    ]

renderCurveEditor :: forall m. State -> H.ComponentHTML Action Slots m
renderCurveEditor _ =
  HH.div
    [ cls [ "lattice-curve-editor" ]
    , HP.attr (HH.AttrName "style") curveEditorStyle
    ]
    [ -- Header
      HH.div
        [ cls [ "lattice-curve-header" ]
        , HP.attr (HH.AttrName "style") curveHeaderStyle
        ]
        [ HH.span [] [ HH.text "Curve Editor" ]
        , HH.button
            [ cls [ "lattice-icon-btn" ]
            , HP.title "Close Curve Editor"
            , HP.attr (HH.AttrName "style") iconBtnStyle
            , HE.onClick \_ -> ToggleCurveEditorAction
            ]
            [ HH.text "×" ]
        ]
    
    , -- Curve canvas
      HH.div
        [ cls [ "lattice-curve-canvas" ]
        , HP.attr (HH.AttrName "style") curveCanvasStyle
        ]
        [ -- Grid lines placeholder
          HH.div [ cls [ "lattice-curve-grid" ] ] []
        , -- Curve placeholder
          HH.div
            [ cls [ "lattice-curve-placeholder" ]
            , HP.attr (HH.AttrName "style") curvePlaceholderStyle
            ]
            [ HH.text "Select a property to edit its curve" ]
        ]
    
    , -- Toolbar
      HH.div
        [ cls [ "lattice-curve-toolbar" ]
        , HP.attr (HH.AttrName "style") curveToolbarStyle
        ]
        [ HH.button [ cls [ "lattice-curve-tool" ] ] [ HH.text "Linear" ]
        , HH.button [ cls [ "lattice-curve-tool" ] ] [ HH.text "Bezier" ]
        , HH.button [ cls [ "lattice-curve-tool" ] ] [ HH.text "Hold" ]
        , HH.button [ cls [ "lattice-curve-tool" ] ] [ HH.text "Ease In" ]
        , HH.button [ cls [ "lattice-curve-tool" ] ] [ HH.text "Ease Out" ]
        ]
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                                    // styles
-- ════════════════════════════════════════════════════════════════════════════

viewportContainerStyle :: String
viewportContainerStyle =
  "display: flex; flex-direction: column; height: 100%; " <>
  "background: var(--lattice-void, #050505);"

viewportSectionStyle :: String
viewportSectionStyle =
  "flex: 0 0 65%; min-height: 200px; display: flex; flex-direction: column;"

resizeHandleStyle :: String
resizeHandleStyle =
  "height: 4px; cursor: row-resize; " <>
  "background: var(--lattice-surface-2, #1a1a1a);"

timelineSectionStyle :: String
timelineSectionStyle =
  "flex: 1; min-height: 150px;"

viewportHeaderStyle :: String
viewportHeaderStyle =
  "display: flex; justify-content: space-between; align-items: center; " <>
  "padding: 4px 8px; background: var(--lattice-surface-2, #1a1a1a); " <>
  "border-bottom: 1px solid var(--lattice-border, #333);"

viewportTabStyle :: Boolean -> String
viewportTabStyle active =
  "padding: 4px 12px; background: transparent; border: none; " <>
  "cursor: pointer; font-size: 11px; font-weight: 500; " <>
  "transition: all 0.15s ease; " <>
  if active
    then "color: var(--lattice-accent, #8b5cf6); " <>
         "border-bottom: 2px solid var(--lattice-accent, #8b5cf6);"
    else "color: var(--lattice-text-secondary, #888);"

controlBtnStyle :: Boolean -> String
controlBtnStyle active =
  "padding: 4px 8px; background: transparent; " <>
  "border: 1px solid transparent; border-radius: 4px; " <>
  "cursor: pointer; font-size: 12px; transition: all 0.15s ease; " <>
  if active
    then "background: var(--lattice-accent-dim, rgba(139, 92, 246, 0.2)); " <>
         "color: var(--lattice-accent, #8b5cf6); " <>
         "border-color: var(--lattice-accent, #8b5cf6);"
    else "color: var(--lattice-text-secondary, #888);"

viewportContentStyle :: Boolean -> String
viewportContentStyle hasRulers =
  "flex: 1; position: relative; overflow: hidden; " <>
  "display: flex; justify-content: center; align-items: center; " <>
  if hasRulers then "margin-left: 20px; margin-top: 20px;" else ""

gridOverlayStyle :: Int -> String
gridOverlayStyle gridSize =
  "position: absolute; top: 0; left: 0; right: 0; bottom: 0; " <>
  "pointer-events: none; z-index: 1; " <>
  "background-image: linear-gradient(var(--lattice-border-subtle, #2a2a2a) 1px, transparent 1px), " <>
  "linear-gradient(90deg, var(--lattice-border-subtle, #2a2a2a) 1px, transparent 1px); " <>
  "background-size: " <> show gridSize <> "px " <> show gridSize <> "px;"

guidesOverlayStyle :: String
guidesOverlayStyle =
  "position: absolute; top: 0; left: 0; right: 0; bottom: 0; " <>
  "pointer-events: none; z-index: 10;"

guideStyle :: Guide -> String
guideStyle guide =
  "position: absolute; pointer-events: auto; cursor: move; " <>
  if guide.orientation == "horizontal"
    then "height: 1px; left: 0; right: 0; top: " <> show guide.position <> "px; " <>
         "background: var(--lattice-accent, #8b5cf6);"
    else "width: 1px; top: 0; bottom: 0; left: " <> show guide.position <> "px; " <>
         "background: var(--lattice-accent, #8b5cf6);"

guideDeleteStyle :: String
guideDeleteStyle =
  "position: absolute; width: 14px; height: 14px; padding: 0; " <>
  "background: var(--lattice-surface-3, #252525); " <>
  "border: 1px solid var(--lattice-accent, #8b5cf6); " <>
  "color: var(--lattice-text-primary, #e5e5e5); " <>
  "cursor: pointer; font-size: 10px; line-height: 1; " <>
  "border-radius: 2px; opacity: 0; transition: opacity 0.15s ease;"

rulersOverlayStyle :: String
rulersOverlayStyle =
  "position: absolute; top: 0; left: 0; right: 0; bottom: 0; " <>
  "pointer-events: none; z-index: 5;"

horizontalRulerStyle :: String
horizontalRulerStyle =
  "position: absolute; top: -20px; left: 0; right: 0; height: 20px; " <>
  "background: var(--lattice-surface-2, #1a1a1a); " <>
  "border-bottom: 1px solid var(--lattice-border, #333); " <>
  "pointer-events: auto; cursor: crosshair;"

verticalRulerStyle :: String
verticalRulerStyle =
  "position: absolute; left: -20px; top: 0; bottom: 0; width: 20px; " <>
  "background: var(--lattice-surface-2, #1a1a1a); " <>
  "border-right: 1px solid var(--lattice-border, #333); " <>
  "pointer-events: auto; cursor: crosshair;"

snapIndicatorContainerStyle :: String
snapIndicatorContainerStyle =
  "position: absolute; top: 0; left: 0; right: 0; bottom: 0; " <>
  "pointer-events: none; z-index: 15;"

canvasAreaStyle :: String
canvasAreaStyle =
  "position: relative; width: 100%; height: 100%; " <>
  "display: flex; justify-content: center; align-items: center;"

canvasPlaceholderStyle :: String
canvasPlaceholderStyle =
  "width: 80%; height: 80%; max-width: 1920px; max-height: 1080px; " <>
  "background: var(--lattice-surface-0, #0a0a0a); " <>
  "border: 1px solid var(--lattice-border, #333); " <>
  "display: flex; justify-content: center; align-items: center; " <>
  "position: relative;"

canvasInfoStyle :: String
canvasInfoStyle =
  "position: absolute; bottom: 8px; right: 8px; " <>
  "padding: 4px 8px; background: rgba(0, 0, 0, 0.7); " <>
  "border-radius: 4px; font-size: 10px; " <>
  "color: var(--lattice-text-secondary, #888);"

timelinePanelStyle :: String
timelinePanelStyle =
  "height: 100%; display: flex; flex-direction: column; " <>
  "background: var(--lattice-surface-1, #121212);"

timelineHeaderStyle :: String
timelineHeaderStyle =
  "display: flex; justify-content: space-between; align-items: center; " <>
  "padding: 4px 8px; background: var(--lattice-surface-2, #1a1a1a); " <>
  "border-bottom: 1px solid var(--lattice-border, #333); " <>
  "font-size: 11px; font-weight: 500;"

iconBtnStyle :: String
iconBtnStyle =
  "padding: 4px 8px; background: transparent; border: none; " <>
  "cursor: pointer; color: var(--lattice-text-secondary, #888); " <>
  "border-radius: 4px; transition: all 0.15s ease;"

timelineContentStyle :: String
timelineContentStyle =
  "flex: 1; display: flex; overflow: hidden;"

layerListStyle :: String
layerListStyle =
  "width: 200px; flex-shrink: 0; overflow-y: auto; " <>
  "border-right: 1px solid var(--lattice-border, #333);"

timelineLayerStyle :: Boolean -> String
timelineLayerStyle selected =
  "display: flex; align-items: center; gap: 8px; " <>
  "padding: 6px 8px; cursor: pointer; font-size: 11px; " <>
  "border-bottom: 1px solid var(--lattice-border-subtle, #2a2a2a); " <>
  "transition: background 0.15s ease; " <>
  if selected
    then "background: var(--lattice-accent-dim, rgba(139, 92, 246, 0.2)); " <>
         "color: var(--lattice-accent, #8b5cf6);"
    else "color: var(--lattice-text-primary, #e5e5e5);"

keyframeAreaStyle :: String
keyframeAreaStyle =
  "flex: 1; position: relative; overflow-x: auto; overflow-y: hidden;"

timeRulerStyle :: String
timeRulerStyle =
  "position: absolute; top: 0; left: 0; right: 0; height: 20px; " <>
  "background: var(--lattice-surface-2, #1a1a1a); " <>
  "border-bottom: 1px solid var(--lattice-border, #333);"

playheadStyle :: Int -> Int -> String
playheadStyle currentFrame totalFrames =
  let 
    percent = if totalFrames > 0 
              then (toNumber currentFrame / toNumber totalFrames) * 100.0
              else 0.0
  in
    "position: absolute; top: 0; bottom: 0; width: 2px; " <>
    "left: " <> show percent <> "%; " <>
    "background: var(--lattice-accent, #8b5cf6); z-index: 10; " <>
    "pointer-events: none;"

keyframeTracksStyle :: String
keyframeTracksStyle =
  "position: absolute; top: 20px; left: 0; right: 0; bottom: 0;"

keyframeTrackStyle :: String
keyframeTrackStyle =
  "height: 24px; position: relative; " <>
  "border-bottom: 1px solid var(--lattice-border-subtle, #2a2a2a);"

keyframeStyle :: Number -> String
keyframeStyle position =
  "position: absolute; top: 50%; left: " <> show (position * 100.0) <> "%; " <>
  "width: 10px; height: 10px; transform: translate(-50%, -50%) rotate(45deg); " <>
  "background: var(--lattice-accent, #8b5cf6); cursor: pointer;"

splitTimelineStyle :: String
splitTimelineStyle =
  "height: 100%; display: flex; flex-direction: column;"

timelineHalfStyle :: String
timelineHalfStyle =
  "flex: 0 0 50%; min-height: 100px; " <>
  "border-bottom: 1px solid var(--lattice-border, #333);"

curveEditorHalfStyle :: String
curveEditorHalfStyle =
  "flex: 1; min-height: 100px;"

curveEditorStyle :: String
curveEditorStyle =
  "height: 100%; display: flex; flex-direction: column; " <>
  "background: var(--lattice-surface-1, #121212);"

curveHeaderStyle :: String
curveHeaderStyle =
  "display: flex; justify-content: space-between; align-items: center; " <>
  "padding: 4px 8px; background: var(--lattice-surface-2, #1a1a1a); " <>
  "border-bottom: 1px solid var(--lattice-border, #333); " <>
  "font-size: 11px; font-weight: 500;"

curveCanvasStyle :: String
curveCanvasStyle =
  "flex: 1; position: relative; background: var(--lattice-surface-0, #0a0a0a);"

curvePlaceholderStyle :: String
curvePlaceholderStyle =
  "position: absolute; top: 50%; left: 50%; transform: translate(-50%, -50%); " <>
  "font-size: 11px; color: var(--lattice-text-tertiary, #666);"

curveToolbarStyle :: String
curveToolbarStyle =
  "display: flex; gap: 4px; padding: 4px 8px; " <>
  "background: var(--lattice-surface-2, #1a1a1a); " <>
  "border-top: 1px solid var(--lattice-border, #333);"

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // actions
-- ════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action Slots Output m Unit
handleAction = case _ of
  Initialize -> pure unit
  
  Receive input -> 
    H.modify_ _ 
      { viewportTab = input.viewportTab
      , viewOptions = input.viewOptions
      , showCurveEditor = input.showCurveEditor
      , guides = input.guides
      , snapEnabled = input.snapEnabled
      , snapIndicatorX = input.snapIndicatorX
      , snapIndicatorY = input.snapIndicatorY
      , compWidth = input.compWidth
      , compHeight = input.compHeight
      , currentFrame = input.currentFrame
      , totalFrames = input.totalFrames
      , fps = input.fps
      }
  
  SwitchTab tab -> do
    H.modify_ _ { viewportTab = tab }
    H.raise (ViewportActionSelected (ViewportTabChanged tab))
  
  ToggleRulers -> do
    state <- H.get
    let newOptions = state.viewOptions { showRulers = not state.viewOptions.showRulers }
    H.modify_ _ { viewOptions = newOptions }
    H.raise (ViewportActionSelected (ViewOptionsChanged newOptions))
  
  ToggleGrid -> do
    state <- H.get
    let newOptions = state.viewOptions { showGrid = not state.viewOptions.showGrid }
    H.modify_ _ { viewOptions = newOptions }
    H.raise (ViewportActionSelected (ViewOptionsChanged newOptions))
  
  ToggleCurveEditorAction -> do
    state <- H.get
    H.modify_ _ { showCurveEditor = not state.showCurveEditor }
    H.raise (ViewportActionSelected ToggleCurveEditor)
  
  EmitAction action -> 
    H.raise (ViewportActionSelected action)
