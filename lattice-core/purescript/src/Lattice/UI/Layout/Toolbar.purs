-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                  // lattice // ui // toolbar
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- |
-- | Toolbar Component
-- |
-- | Tool selection, playback controls, undo/redo, and action buttons.
-- |
-- | Tool Groups:
-- | - Selection/Drawing: Select, Pen, Text, Hand, Zoom, AI Segment
-- | - Shape Tools: Rectangle, Ellipse, Polygon, Star
-- | - Playback: Start, Back, Play/Pause, Forward, End
-- | - Actions: Import, Preview, Template, Export, ComfyUI
-- |
module Lattice.UI.Layout.Toolbar
  ( component
  , Input
  , Output(..)
  , Query
  , Slot
  , Tool(..)
  , ToolbarAction(..)
  ) where

import Prelude

import Data.Int (floor, toNumber)
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

-- | Available tools
data Tool
  = ToolSelect
  | ToolPen
  | ToolText
  | ToolHand
  | ToolZoom
  | ToolSegment
  | ToolRectangle
  | ToolEllipse
  | ToolPolygon
  | ToolStar

derive instance eqTool :: Eq Tool

type Input =
  { currentTool :: Tool
  , isPlaying :: Boolean
  , currentFrame :: Int
  , totalFrames :: Int
  , fps :: Number
  , canUndo :: Boolean
  , canRedo :: Boolean
  , gpuTier :: String
  }

-- | Actions emitted from toolbar
data ToolbarAction
  = SetTool Tool
  -- Playback
  | GoToStart
  | StepBackward
  | TogglePlayback
  | StepForward
  | GoToEnd
  -- Edit
  | UndoAction
  | RedoAction
  -- Buttons
  | ImportAction
  | ShowPreview
  | ShowTemplateBuilder
  | ShowExport
  | ShowComfyUI

derive instance eqToolbarAction :: Eq ToolbarAction

data Output = ToolbarActionSelected ToolbarAction

data Query a

type Slot id = H.Slot Query Output id

type State =
  { currentTool :: Tool
  , isPlaying :: Boolean
  , currentFrame :: Int
  , totalFrames :: Int
  , fps :: Number
  , canUndo :: Boolean
  , canRedo :: Boolean
  , gpuTier :: String
  }

data Action
  = Initialize
  | Receive Input
  | EmitAction ToolbarAction

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
  { currentTool: input.currentTool
  , isPlaying: input.isPlaying
  , currentFrame: input.currentFrame
  , totalFrames: input.totalFrames
  , fps: input.fps
  , canUndo: input.canUndo
  , canRedo: input.canRedo
  , gpuTier: input.gpuTier
  }

-- ════════════════════════════════════════════════════════════════════════════
--                                                                    // render
-- ════════════════════════════════════════════════════════════════════════════

render :: forall m. State -> H.ComponentHTML Action Slots m
render state =
  HH.div
    [ cls [ "lattice-toolbar" ]
    , HP.attr (HH.AttrName "style") toolbarStyle
    , HP.attr (HH.AttrName "role") "toolbar"
    ]
    [ -- Selection & Drawing Tools
      HH.div [ cls [ "lattice-tool-group", "lattice-labeled-tools" ] ]
        [ toolButton state ToolSelect "cursor" "Select Tool (V)"
        , toolButton state ToolPen "pen" "Pen Tool (P)"
        , toolButton state ToolText "text" "Text Tool (T)"
        , toolButton state ToolHand "hand" "Hand Tool (H)"
        , toolButton state ToolZoom "zoom" "Zoom Tool (Z)"
        , toolButton state ToolSegment "sparkle" "AI Segment (S)"
        ]
    
    , divider
    
      -- Shape Tools
    , HH.div [ cls [ "lattice-tool-group", "lattice-shape-tools" ] ]
        [ toolButton state ToolRectangle "square" "Rectangle Tool (R)"
        , toolButton state ToolEllipse "circle" "Ellipse Tool (E)"
        , toolButton state ToolPolygon "polygon" "Polygon Tool"
        , toolButton state ToolStar "star" "Star Tool"
        ]
    
    , divider
    
      -- Import
    , HH.div [ cls [ "lattice-tool-group" ] ]
        [ actionButton "download" "Import Asset (Ctrl+I)" ImportAction ]
    
    , divider
    
      -- Playback Controls
    , HH.div [ cls [ "lattice-tool-group" ] ]
        [ playbackButton "skip-back" "Go to Start (Home)" GoToStart
        , playbackButton "rewind" "Step Backward (←)" StepBackward
        , if state.isPlaying
            then playbackButton "pause" "Pause (Space)" TogglePlayback
            else playbackButton "play" "Play (Space)" TogglePlayback
        , playbackButton "fast-forward" "Step Forward (→)" StepForward
        , playbackButton "skip-forward" "Go to End (End)" GoToEnd
        ]
    
      -- Timecode Display
    , HH.div 
        [ cls [ "lattice-timecode" ]
        , HP.attr (HH.AttrName "style") timecodeStyle
        ]
        [ HH.text (formatTimecode state.currentFrame state.fps) ]
    
      -- Undo/Redo
    , HH.div [ cls [ "lattice-tool-group", "lattice-undo-redo" ] ]
        [ HH.button
            [ cls [ "lattice-tool-btn", "lattice-undo-btn" ]
            , HP.disabled (not state.canUndo)
            , HP.title "Undo (Ctrl+Z)"
            , HE.onClick \_ -> EmitAction UndoAction
            ]
            [ icon "arrow-counter-clockwise"
            , HH.span [ cls [ "lattice-btn-label" ] ] [ HH.text "Undo" ]
            ]
        , HH.button
            [ cls [ "lattice-tool-btn", "lattice-redo-btn" ]
            , HP.disabled (not state.canRedo)
            , HP.title "Redo (Ctrl+Shift+Z)"
            , HE.onClick \_ -> EmitAction RedoAction
            ]
            [ icon "arrow-clockwise"
            , HH.span [ cls [ "lattice-btn-label" ] ] [ HH.text "Redo" ]
            ]
        ]
    
      -- Spacer
    , HH.div [ cls [ "lattice-toolbar-spacer" ] ] []
    
      -- Action Buttons
    , HH.div [ cls [ "lattice-tool-group", "lattice-action-buttons" ] ]
        [ actionButton "monitor" "Full Resolution Preview (`)" ShowPreview
        , actionButton "package" "Create Template" ShowTemplateBuilder
        , HH.button
            [ cls [ "lattice-tool-btn", "lattice-primary-btn" ]
            , HP.title "Export frame sequence"
            , HE.onClick \_ -> EmitAction ShowExport
            ]
            [ icon "export"
            , HH.text "Export"
            ]
        , actionButton "link" "Send to ComfyUI" ShowComfyUI
        ]
    
    , divider
    
      -- GPU Badge
    , HH.div [ cls [ "lattice-status-group" ] ]
        [ HH.span 
            [ cls [ "lattice-gpu-badge", "lattice-gpu-" <> state.gpuTier ] ]
            [ HH.text (gpuLabel state.gpuTier) ]
        ]
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // helpers
-- ════════════════════════════════════════════════════════════════════════════

toolButton :: forall m. State -> Tool -> String -> String -> H.ComponentHTML Action Slots m
toolButton state tool iconName tooltip =
  HH.button
    [ cls [ "lattice-tool-btn" ]
    , HP.attr (HH.AttrName "data-state") (if state.currentTool == tool then "active" else "inactive")
    , HP.title tooltip
    , HE.onClick \_ -> EmitAction (SetTool tool)
    ]
    [ icon iconName
    , HH.span [ cls [ "lattice-tool-label" ] ] [ HH.text (toolLabel tool) ]
    ]

playbackButton :: forall m. String -> String -> ToolbarAction -> H.ComponentHTML Action Slots m
playbackButton iconName tooltip action =
  HH.button
    [ cls [ "lattice-tool-btn" ]
    , HP.title tooltip
    , HE.onClick \_ -> EmitAction action
    ]
    [ icon iconName ]

actionButton :: forall m. String -> String -> ToolbarAction -> H.ComponentHTML Action Slots m
actionButton iconName tooltip action =
  HH.button
    [ cls [ "lattice-tool-btn" ]
    , HP.title tooltip
    , HE.onClick \_ -> EmitAction action
    ]
    [ icon iconName ]

icon :: forall m. String -> H.ComponentHTML Action Slots m
icon name =
  HH.span 
    [ cls [ "lattice-icon" ]
    , HP.attr (HH.AttrName "data-icon") name
    ]
    []

divider :: forall m. H.ComponentHTML Action Slots m
divider = HH.div [ cls [ "lattice-toolbar-divider" ] ] []

toolLabel :: Tool -> String
toolLabel = case _ of
  ToolSelect -> "Select"
  ToolPen -> "Pen"
  ToolText -> "Text"
  ToolHand -> "Pan"
  ToolZoom -> "Zoom"
  ToolSegment -> "AI Seg"
  ToolRectangle -> "Rect"
  ToolEllipse -> "Ellipse"
  ToolPolygon -> "Polygon"
  ToolStar -> "Star"

gpuLabel :: String -> String
gpuLabel = case _ of
  "cpu" -> "CPU"
  "webgl" -> "WebGL"
  "webgpu" -> "WebGPU"
  "blackwell" -> "BLACKWELL"
  other -> other

formatTimecode :: Int -> Number -> String
formatTimecode frame fps =
  let 
    fpsInt = max 1 (floor fps)
    totalSeconds = toNumber frame / toNumber fpsInt
    minutes = floor (totalSeconds / 60.0)
    seconds = floor totalSeconds `mod` 60
    frames = frame `mod` fpsInt
  in
    padZero minutes <> ":" <> padZero seconds <> ":" <> padZero frames

padZero :: Int -> String
padZero n = 
  if n < 10 
    then "0" <> show n 
    else show n

-- ════════════════════════════════════════════════════════════════════════════
--                                                                    // styles
-- ════════════════════════════════════════════════════════════════════════════

toolbarStyle :: String
toolbarStyle =
  "display: flex; align-items: center; gap: 12px; " <>
  "padding: 10px 12px; min-height: 54px; " <>
  "background: var(--lattice-surface-1); border-radius: 8px;"

timecodeStyle :: String
timecodeStyle =
  "font-family: var(--lattice-font-mono, monospace); " <>
  "font-size: 15px; padding: 8px 18px; " <>
  "background: var(--lattice-surface-2); border-radius: 8px; " <>
  "min-width: 110px; text-align: center; " <>
  "color: var(--lattice-text-primary);"

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // actions
-- ════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action Slots Output m Unit
handleAction = case _ of
  Initialize -> pure unit
  
  Receive input -> 
    H.modify_ _ 
      { currentTool = input.currentTool
      , isPlaying = input.isPlaying
      , currentFrame = input.currentFrame
      , totalFrames = input.totalFrames
      , fps = input.fps
      , canUndo = input.canUndo
      , canRedo = input.canRedo
      , gpuTier = input.gpuTier
      }
  
  EmitAction action -> 
    H.raise (ToolbarActionSelected action)
