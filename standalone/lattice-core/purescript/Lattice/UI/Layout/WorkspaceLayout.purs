-- | Workspace Layout Component
-- |
-- | The main workspace layout for the Lattice Compositor.
-- |
-- | ┌─────────────────────────────────────────────────────────────────────────┐
-- | │ MenuBar (28px)                                                          │
-- | ├─────────────────────────────────────────────────────────────────────────┤
-- | │ Toolbar (54px)                                                          │
-- | ├────────┬────────────────────────────────────────────────┬───────────────┤
-- | │        │  ┌─────────────────┬─────────────────┐         │               │
-- | │  Left  │  │  3D Scene View  │  Render Preview │         │    Right      │
-- | │ Sidebar│  │  (Working)      │  (Final Output) │         │   Sidebar     │
-- | │ (14%)  │  │  Shadowbox      │  Black → Render │         │    (20%)      │
-- | │        │  └─────────────────┴─────────────────┘         │               │
-- | │ Tabs:  │  ┌───────────────────────────────────┐         │  Properties   │
-- | │ -Project│ │           Timeline                │         │  + AI Panel   │
-- | │ -Assets │ │                                   │         │               │
-- | │ -Draw  │  └───────────────────────────────────┘         │               │
-- | └────────┴────────────────────────────────────────────────┴───────────────┘
-- |
-- | ## Viewports:
-- | - **3D Scene View**: Interactive editing, camera rotation, z-space navigation
-- | - **Render Preview**: Displays backend-rendered output, starts black
-- | - **Drawing Canvas**: Tab in left panel for ControlNet brush painting
-- | - **Asset Browser**: Tab in left panel for imported files
module Lattice.UI.Layout.WorkspaceLayout
  ( component
  , Input
  , Output
  , Query
  , Slot
  ) where

import Prelude

import Data.Array ((:))
import Data.Const (Const)
import Data.Either (Either(..))
import Data.Int (floor, toNumber)
import Data.Maybe (Maybe(..))
import Type.Proxy (Proxy(..))
import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Class (liftEffect)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP

import Lattice.UI.Core (cls)
import Lattice.UI.Components.LayerList as LayerList
import Lattice.UI.Components.Timeline as Timeline
import Lattice.UI.Components.PropertiesPanel as PropertiesPanel
import Lattice.Project (LayerBase)
import Lattice.Services.Bridge.Client as Bridge

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                     // types
-- ════════════════════════════════════════════════════════════════════════════

type Input = 
  { bridgeClient :: Maybe Bridge.BridgeClient
  }

type Output = Void

data Query a

type Slot id = H.Slot Query Output id

type CompositionDimensions =
  { width :: Int
  , height :: Int
  }

type State =
  { -- Layout
    leftSidebarWidth :: Number  -- Percentage (default 14%)
  , rightSidebarWidth :: Number -- Percentage (default 20%)
  , timelineHeight :: Number    -- Percentage (default 35%)
  , viewportSplit :: Number     -- Left/Right viewport split (default 50%)
    -- Project
  , layers :: Array LayerBase
  , selectedLayerIds :: Array String
  , currentFrame :: Int
  , totalFrames :: Int
  , fps :: Number
  , isPlaying :: Boolean
    -- Composition
  , compositionDimensions :: CompositionDimensions
    -- Tabs
  , activeLeftTab :: LeftTab
    -- Render state
  , renderPreviewUrl :: Maybe String  -- Base64 or URL of rendered frame
  , isRendering :: Boolean
  , renderError :: Maybe String       -- Error message if render failed
    -- Generation progress
  , generationProgress :: Number      -- 0.0 to 100.0
  , generationStage :: String         -- "idle" | "encoding" | "sampling" | "decoding"
  , generationEta :: Maybe Number     -- Estimated seconds remaining
    -- 3D Scene state
  , sceneCameraRotation :: { x :: Number, y :: Number, z :: Number }
  , sceneCameraPosition :: { x :: Number, y :: Number, z :: Number }
  , sceneCameraZoom :: Number
    -- Bridge
  , bridgeClient :: Maybe Bridge.BridgeClient
    -- AI generation
  , promptText :: String
  , negativePrompt :: String
  , generationMode :: GenerationMode
  , selectedModel :: String
  , sourceImageUrl :: Maybe String  -- For i2v/edit mode
  , maskImageUrl :: Maybe String    -- For edit mode (white = edit, black = keep)
  , numFrames :: Int
  , cfgScale :: Number
  , steps :: Int
  , seed :: Maybe Int               -- Random seed (Nothing = auto)
  }

data LeftTab 
  = TabProject   -- Layer list
  | TabAssets    -- Imported files browser
  | TabDraw      -- Drawing canvas for ControlNet
derive instance eqLeftTab :: Eq LeftTab

-- | Generation mode - determines which models are available
data GenerationMode
  = TextToImage   -- T2I - Generate still image from prompt
  | ImageEdit     -- Edit - Inpaint/outpaint with mask
  | ImageToVideo  -- I2V - Animate an image with prompt
  | TextToVideo   -- T2V - Generate video from prompt
  | TextTo3D      -- 3D  - Generate 3D model from prompt/image
derive instance eqGenerationMode :: Eq GenerationMode

data Action
  = Initialize
  | Receive Input
  | SetLeftTab LeftTab
  | HandleLayerList LayerList.Output
  | HandleTimeline Timeline.Output
  | HandleProperties PropertiesPanel.Output
    -- Viewport actions
  | RotateSceneCamera Number Number
  | PanSceneCamera Number Number
  | ZoomSceneCamera Number
  | ResetSceneCamera
    -- Drawing canvas actions
  | SetBrushSize Number
  | SetBrushColor String
  | SetBrushOpacity Number
  | ClearDrawingCanvas
    -- AI generation actions
  | SetPromptText String
  | SetNegativePrompt String
  | SetGenerationMode GenerationMode
  | SetModel String
  | SetNumFrames Int
  | SetCfgScale Number
  | SetSteps Int
  | SetSourceImage String
  | GenerateFromPrompt
  | ReceiveGenerateProgress Number String  -- percentage, stage
  | ReceiveGenerateResult (Either String Bridge.GenerateResult)

type Slots =
  ( menuBar :: H.Slot (Const Void) Void Unit
  , toolbar :: H.Slot (Const Void) Void Unit
  , leftSidebar :: H.Slot (Const Void) Void Unit
  , sceneViewport :: H.Slot (Const Void) Void Unit
  , renderViewport :: H.Slot (Const Void) Void Unit
  , timeline :: Timeline.Slot Unit
  , rightSidebar :: H.Slot (Const Void) Void Unit
  , layerList :: LayerList.Slot Unit
  , properties :: PropertiesPanel.Slot Unit
  )

_menuBar :: Proxy "menuBar"
_menuBar = Proxy

_toolbar :: Proxy "toolbar"
_toolbar = Proxy

_leftSidebar :: Proxy "leftSidebar"
_leftSidebar = Proxy

_sceneViewport :: Proxy "sceneViewport"
_sceneViewport = Proxy

_renderViewport :: Proxy "renderViewport"
_renderViewport = Proxy

_timeline :: Proxy "timeline"
_timeline = Proxy

_rightSidebar :: Proxy "rightSidebar"
_rightSidebar = Proxy

_layerList :: Proxy "layerList"
_layerList = Proxy

_properties :: Proxy "properties"
_properties = Proxy

-- ════════════════════════════════════════════════════════════════════════════
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
--                                                                    // render
-- ════════════════════════════════════════════════════════════════════════════

render :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
render state =
  HH.div
    [ cls [ "lattice-workspace" ]
    , HP.attr (HH.AttrName "style") workspaceStyle
    ]
    [ -- Menu Bar
      renderMenuBar
    
      -- Toolbar
    , renderToolbar
    
      -- Main content area (3-column split)
    , HH.div
        [ cls [ "lattice-workspace-content" ]
        , HP.attr (HH.AttrName "style") contentStyle
        ]
        [ -- Left Sidebar
          HH.div
            [ cls [ "lattice-sidebar lattice-sidebar-left" ]
            , HP.attr (HH.AttrName "style") (sidebarStyle state.leftSidebarWidth "right")
            ]
            [ renderLeftSidebar state ]
        
          -- Center (Dual Viewports + Timeline)
        , HH.div
            [ cls [ "lattice-center" ]
            , HP.attr (HH.AttrName "style") centerStyle
            ]
            [ -- Dual Viewport Container
              HH.div
                [ cls [ "lattice-viewport-container" ]
                , HP.attr (HH.AttrName "style") viewportContainerStyle
                ]
                [ -- Left: 3D Scene View (Working)
                  renderSceneViewport state
                  -- Right: Render Preview (Final Output)
                , renderRenderViewport state
                ]
            
              -- Timeline
            , HH.div
                [ cls [ "lattice-timeline-container" ]
                , HP.attr (HH.AttrName "style") (timelineStyle state.timelineHeight)
                ]
                [ renderTimeline state ]
            ]
        
          -- Right Sidebar
        , HH.div
            [ cls [ "lattice-sidebar lattice-sidebar-right" ]
            , HP.attr (HH.AttrName "style") (sidebarStyle state.rightSidebarWidth "left")
            ]
            [ renderRightSidebar state ]
        ]
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                            // dual viewports
-- ════════════════════════════════════════════════════════════════════════════

-- | 3D Scene View - Interactive editing viewport
-- | Shows composition with shadowbox for dimensions
-- | User can rotate/pan/zoom camera in z-space
renderSceneViewport :: forall m. State -> H.ComponentHTML Action Slots m
renderSceneViewport state =
  HH.div
    [ cls [ "lattice-scene-viewport" ]
    , HP.attr (HH.AttrName "style") sceneViewportStyle
    ]
    [ -- Header
      HH.div [ cls [ "lattice-viewport-header" ] ]
        [ HH.span [ cls [ "lattice-viewport-title" ] ] 
            [ HH.text "Scene" ]
        , HH.div [ cls [ "lattice-viewport-controls" ] ]
            [ HH.button 
                [ cls [ "lattice-viewport-btn" ]
                , HP.title "Reset Camera"
                , HE.onClick \_ -> ResetSceneCamera
                ]
                [ HH.text "⟲" ]
            ]
        ]
    
      -- Scene canvas with shadowbox
    , HH.div 
        [ cls [ "lattice-scene-canvas" ]
        , HP.attr (HH.AttrName "style") sceneCanvasStyle
        ]
        [ -- Shadowbox overlay showing composition bounds
          HH.div 
            [ cls [ "lattice-shadowbox" ]
            , HP.attr (HH.AttrName "style") (shadowboxStyle state.compositionDimensions)
            ]
            []
        
          -- Scene content area (layers, keyframes, paths)
        , HH.div [ cls [ "lattice-scene-content" ] ]
            [ -- Placeholder for 3D scene rendering
              HH.div [ cls [ "lattice-scene-placeholder" ] ]
                [ HH.text "3D Scene View"
                , HH.br_
                , HH.span [ cls [ "lattice-text-muted" ] ]
                    [ HH.text (show state.compositionDimensions.width <> " × " <> show state.compositionDimensions.height) ]
                ]
            ]
        ]
    
      -- Camera info
    , HH.div [ cls [ "lattice-viewport-footer" ] ]
        [ HH.span_ 
            [ HH.text ("Zoom: " <> show (state.sceneCameraZoom * 100.0) <> "%") ]
        ]
    ]

-- | Render Preview - Final output display
-- | Shows rendered frames from backend
-- | Starts black, updates when render completes
renderRenderViewport :: forall m. State -> H.ComponentHTML Action Slots m
renderRenderViewport state =
  HH.div
    [ cls [ "lattice-render-viewport" ]
    , HP.attr (HH.AttrName "style") renderViewportStyle
    ]
    [ -- Header
      HH.div [ cls [ "lattice-viewport-header" ] ]
        [ HH.span [ cls [ "lattice-viewport-title" ] ] 
            [ HH.text "Preview" ]
        , if state.isRendering
            then HH.span [ cls [ "lattice-rendering-indicator" ] ]
                [ HH.text "Rendering..." ]
            else HH.text ""
        ]
    
      -- Render output area
    , HH.div 
        [ cls [ "lattice-render-canvas" ]
        , HP.attr (HH.AttrName "style") renderCanvasStyle
        ]
        [ case state.renderPreviewUrl of
            Nothing ->
              -- Black placeholder when no render
              HH.div 
                [ cls [ "lattice-render-placeholder" ]
                , HP.attr (HH.AttrName "style") renderPlaceholderStyle
                ]
                [ HH.div [ cls [ "lattice-placeholder-content" ] ]
                    [ HH.span [ cls [ "lattice-text-muted" ] ]
                        [ HH.text "No render" ]
                    , HH.br_
                    , HH.span [ cls [ "lattice-text-xs" ] ]
                        [ HH.text "Generate or import a layer" ]
                    ]
                ]
            Just url ->
              -- Display rendered frame
              HH.img
                [ cls [ "lattice-render-output" ]
                , HP.src url
                , HP.alt "Rendered frame"
                , HP.attr (HH.AttrName "style") renderOutputStyle
                ]
        ]
    
      -- Frame info
    , HH.div [ cls [ "lattice-viewport-footer" ] ]
        [ HH.span_ 
            [ HH.text ("Frame " <> show state.currentFrame <> " / " <> show state.totalFrames) ]
        ]
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                                       // sub
-- ════════════════════════════════════════════════════════════════════════════

renderMenuBar :: forall m. H.ComponentHTML Action Slots m
renderMenuBar =
  HH.div
    [ cls [ "lattice-menubar" ]
    , HP.attr (HH.AttrName "style") menuBarStyle
    ]
    [ HH.div [ cls [ "lattice-menubar-left" ] ]
        [ menuItem "File"
        , menuItem "Edit"
        , menuItem "View"
        , menuItem "Insert"
        , menuItem "Layer"
        , menuItem "Animation"
        , menuItem "Effects"
        , menuItem "Window"
        , menuItem "Help"
        ]
    , HH.div [ cls [ "lattice-menubar-right" ] ]
        [ HH.span [ cls [ "lattice-project-name" ] ] 
            [ HH.text "Untitled Project" ]
        ]
    ]

menuItem :: forall m. String -> H.ComponentHTML Action Slots m
menuItem label =
  HH.button
    [ cls [ "lattice-menu-trigger" ] ]
    [ HH.text label ]

renderToolbar :: forall m. H.ComponentHTML Action Slots m
renderToolbar =
  HH.div
    [ cls [ "lattice-toolbar" ]
    , HP.attr (HH.AttrName "style") toolbarStyle
    ]
    [ -- Tool group: Selection
      HH.div [ cls [ "lattice-tool-group" ] ]
        [ toolButton "select" "Selection Tool" true
        , toolButton "hand" "Pan Tool" false
        , toolButton "zoom" "Zoom Tool" false
        ]
    
      -- Tool group: Transform
    , HH.div [ cls [ "lattice-tool-group" ] ]
        [ toolButton "move" "Move" false
        , toolButton "rotate" "Rotate" false
        , toolButton "scale" "Scale" false
        ]
    
      -- Tool group: Create
    , HH.div [ cls [ "lattice-tool-group" ] ]
        [ toolButton "pen" "Pen Tool" false
        , toolButton "rectangle" "Rectangle" false
        , toolButton "ellipse" "Ellipse" false
        , toolButton "text" "Text Tool" false
        ]
    
      -- Spacer
    , HH.div [ cls [ "lattice-toolbar-spacer" ] ] []
    
      -- Playback controls
    , HH.div [ cls [ "lattice-tool-group lattice-playback" ] ]
        [ toolButton "skip-back" "Go to Start" false
        , toolButton "step-back" "Previous Frame" false
        , toolButton "play" "Play/Pause" false
        , toolButton "step-forward" "Next Frame" false
        , toolButton "skip-forward" "Go to End" false
        ]
    
      -- Time display
    , HH.div [ cls [ "lattice-time-display" ] ]
        [ HH.span_ [ HH.text "00:00:00:00" ] ]
    ]

toolButton :: forall m. String -> String -> Boolean -> H.ComponentHTML Action Slots m
toolButton iconName tooltip active =
  HH.button
    [ cls [ "lattice-tool-btn" ]
    , HP.title tooltip
    , HP.attr (HH.AttrName "data-state") (if active then "active" else "inactive")
    ]
    [ HH.span 
        [ cls [ "lattice-icon" ]
        , HP.attr (HH.AttrName "data-icon") iconName
        ] 
        [] -- Icon rendered via CSS data-icon attribute
    ]

renderLeftSidebar :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
renderLeftSidebar state =
  HH.div [ cls [ "lattice-sidebar-content" ] ]
    [ -- Tabs: Project / Assets / Draw
      HH.div [ cls [ "lattice-sidebar-tabs" ] ]
        [ HH.button 
            [ cls [ "lattice-tabs-trigger" ]
            , HP.attr (HH.AttrName "data-state") (if state.activeLeftTab == TabProject then "active" else "inactive")
            , HE.onClick \_ -> SetLeftTab TabProject
            ]
            [ HH.text "Project" ]
        , HH.button 
            [ cls [ "lattice-tabs-trigger" ]
            , HP.attr (HH.AttrName "data-state") (if state.activeLeftTab == TabAssets then "active" else "inactive")
            , HE.onClick \_ -> SetLeftTab TabAssets
            ]
            [ HH.text "Assets" ]
        , HH.button 
            [ cls [ "lattice-tabs-trigger" ]
            , HP.attr (HH.AttrName "data-state") (if state.activeLeftTab == TabDraw then "active" else "inactive")
            , HE.onClick \_ -> SetLeftTab TabDraw
            ]
            [ HH.text "Draw" ]
        ]
    
      -- Tab content
    , case state.activeLeftTab of
        TabProject -> renderProjectTab state
        TabAssets -> renderAssetsTab
        TabDraw -> renderDrawingTab state
    ]

renderProjectTab :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
renderProjectTab state =
  HH.div [ cls [ "lattice-sidebar-panel" ] ]
    [ HH.div [ cls [ "lattice-panel-header" ] ]
        [ HH.text "Layers" ]
    , HH.slot _layerList unit LayerList.component
        { layers: state.layers
        , selectedIds: state.selectedLayerIds
        }
        HandleLayerList
    ]

renderAssetsTab :: forall m. H.ComponentHTML Action Slots m
renderAssetsTab =
  HH.div [ cls [ "lattice-sidebar-panel" ] ]
    [ HH.div [ cls [ "lattice-panel-header" ] ]
        [ HH.text "Assets" ]
    , HH.div [ cls [ "lattice-panel-content" ] ]
        [ HH.p [ cls [ "lattice-text-muted" ] ] 
            [ HH.text "No assets imported" ]
        , HH.button [ cls [ "lattice-btn lattice-btn-primary" ] ]
            [ HH.text "+ Import" ]
        ]
    ]

-- | Drawing Canvas Tab - For ControlNet mask painting
renderDrawingTab :: forall m. State -> H.ComponentHTML Action Slots m
renderDrawingTab state =
  HH.div [ cls [ "lattice-sidebar-panel lattice-draw-panel" ] ]
    [ HH.div [ cls [ "lattice-panel-header" ] ]
        [ HH.text "Drawing Canvas" ]
    
      -- Brush tools
    , HH.div [ cls [ "lattice-brush-tools" ] ]
        [ HH.div [ cls [ "lattice-brush-control" ] ]
            [ HH.label_ [ HH.text "Size" ]
            , HH.input
                [ HP.type_ HP.InputRange
                , HP.attr (HH.AttrName "min") "1"
                , HP.attr (HH.AttrName "max") "100"
                , HP.attr (HH.AttrName "value") "10"
                ]
            ]
        , HH.div [ cls [ "lattice-brush-control" ] ]
            [ HH.label_ [ HH.text "Opacity" ]
            , HH.input
                [ HP.type_ HP.InputRange
                , HP.attr (HH.AttrName "min") "0"
                , HP.attr (HH.AttrName "max") "100"
                , HP.attr (HH.AttrName "value") "100"
                ]
            ]
        , HH.div [ cls [ "lattice-brush-control" ] ]
            [ HH.label_ [ HH.text "Color" ]
            , HH.input
                [ HP.type_ HP.InputColor
                , HP.attr (HH.AttrName "value") "#FFFFFF"
                ]
            ]
        ]
    
      -- Drawing canvas (scaled to fit sidebar)
    , HH.div 
        [ cls [ "lattice-draw-canvas-container" ]
        , HP.attr (HH.AttrName "style") drawCanvasContainerStyle
        ]
        [ HH.canvas
            [ cls [ "lattice-draw-canvas" ]
            , HP.id "lattice-draw-canvas"
            , HP.width state.compositionDimensions.width
            , HP.height state.compositionDimensions.height
            , HP.attr (HH.AttrName "style") drawCanvasStyle
            ]
        ]
    
      -- Actions
    , HH.div [ cls [ "lattice-draw-actions" ] ]
        [ HH.button 
            [ cls [ "lattice-btn lattice-btn-ghost" ]
            , HE.onClick \_ -> ClearDrawingCanvas
            ]
            [ HH.text "Clear" ]
        , HH.button 
            [ cls [ "lattice-btn lattice-btn-primary" ] ]
            [ HH.text "Use as ControlNet Layer" ]
        ]
    ]

renderTimeline :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
renderTimeline state =
  HH.slot _timeline unit Timeline.component
    { layers: state.layers
    , currentFrame: state.currentFrame
    , totalFrames: state.totalFrames
    , fps: state.fps
    , selectedLayerIds: state.selectedLayerIds
    , isPlaying: state.isPlaying
    }
    HandleTimeline

renderRightSidebar :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
renderRightSidebar state =
  HH.div [ cls [ "lattice-sidebar-content" ] ]
    [ -- Properties panel
      HH.slot _properties unit PropertiesPanel.component
        { selectedLayer: getSelectedLayer state }
        HandleProperties
    
      -- AI section
    , HH.div [ cls [ "lattice-ai-section" ] ]
        [ HH.div [ cls [ "lattice-sidebar-tabs" ] ]
            [ tabButton "Generate" true
            , tabButton "Chat" false
            , tabButton "Flow" false
            ]
        , HH.div [ cls [ "lattice-ai-content" ] ]
            [               -- Generation mode toggle buttons
              HH.div [ cls [ "lattice-mode-toggle" ] ]
                [ modeButton state TextToImage "T2I" "Text to Image"
                , modeButton state ImageEdit "Edit" "Image Edit (Inpaint/Outpaint)"
                , modeButton state ImageToVideo "I2V" "Image to Video"
                , modeButton state TextToVideo "T2V" "Text to Video"
                , modeButton state TextTo3D "3D" "Text/Image to 3D Model"
                ]
            
              -- Model selector (changes based on mode)
            , HH.div [ cls [ "lattice-model-selector" ] ]
                [ HH.label_ [ HH.text "Model" ]
                , HH.select 
                    [ cls [ "lattice-select" ]
                    , HP.value state.selectedModel
                    , HE.onValueChange SetModel
                    ]
                    (modelsForMode state.generationMode)
                ]
            
              -- Source image selector (for I2V, Edit, and 3D modes)
            , case state.generationMode of
                ImageToVideo -> renderSourceImageSelector state
                ImageEdit -> renderSourceImageSelector state
                TextTo3D -> renderSourceImageSelector state  -- Optional reference image
                _ -> HH.text ""
            
              -- Mask controls (only for ImageEdit mode)
            , case state.generationMode of
                ImageEdit ->
                  HH.div [ cls [ "lattice-mask-controls" ] ]
                    [ HH.label_ [ HH.text "Mask" ]
                    , HH.div [ cls [ "lattice-mask-options" ] ]
                        [ HH.button 
                            [ cls [ "lattice-btn lattice-btn-ghost" ]
                            , HP.title "Draw mask in Draw tab"
                            , HE.onClick \_ -> SetLeftTab TabDraw
                            ]
                            [ HH.text "Draw Mask" ]
                        , HH.button 
                            [ cls [ "lattice-btn lattice-btn-ghost" ]
                            , HP.title "Auto-generate mask from selection"
                            ]
                            [ HH.text "Auto Mask" ]
                        ]
                    , HH.div [ cls [ "lattice-mask-info lattice-text-muted" ] ]
                        [ HH.text "White = edit, Black = keep" ]
                    ]
                _ -> HH.text ""
            
              -- Prompt input
            , HH.div [ cls [ "lattice-prompt-container" ] ]
                [ HH.label_ [ HH.text "Prompt" ]
                , HH.textarea
                    [ cls [ "lattice-prompt-input" ]
                    , HP.placeholder "Describe what you want to generate..."
                    , HP.attr (HH.AttrName "rows") "3"
                    , HP.value state.promptText
                    , HE.onValueInput SetPromptText
                    ]
                ]
            
              -- Negative prompt (collapsible)
            , HH.div [ cls [ "lattice-prompt-container" ] ]
                [ HH.label_ [ HH.text "Negative Prompt" ]
                , HH.textarea
                    [ cls [ "lattice-prompt-input lattice-prompt-negative" ]
                    , HP.placeholder "What to avoid..."
                    , HP.attr (HH.AttrName "rows") "2"
                    , HP.value state.negativePrompt
                    , HE.onValueInput SetNegativePrompt
                    ]
                ]
            
              -- Generation parameters
            , HH.div [ cls [ "lattice-gen-params" ] ]
                [ -- Frames (only for video modes)
                  case state.generationMode of
                    TextToImage -> HH.text ""
                    _ -> 
                      HH.div [ cls [ "lattice-param" ] ]
                        [ HH.label_ [ HH.text "Frames" ]
                        , HH.input
                            [ HP.type_ HP.InputNumber
                            , HP.value (show state.numFrames)
                            , HP.attr (HH.AttrName "min") "1"
                            , HP.attr (HH.AttrName "max") "300"
                            ]
                        ]
                , HH.div [ cls [ "lattice-param" ] ]
                    [ HH.label_ [ HH.text "CFG Scale" ]
                    , HH.input
                        [ HP.type_ HP.InputNumber
                        , HP.value (show state.cfgScale)
                        , HP.attr (HH.AttrName "min") "1"
                        , HP.attr (HH.AttrName "max") "20"
                        , HP.attr (HH.AttrName "step") "0.5"
                        ]
                    ]
                , HH.div [ cls [ "lattice-param" ] ]
                    [ HH.label_ [ HH.text "Steps" ]
                    , HH.input
                        [ HP.type_ HP.InputNumber
                        , HP.value (show state.steps)
                        , HP.attr (HH.AttrName "min") "1"
                        , HP.attr (HH.AttrName "max") "100"
                        ]
                    ]
                ]
            
              -- Error display
            , case state.renderError of
                Just err -> 
                  HH.div [ cls [ "lattice-error" ] ] 
                    [ HH.text err ]
                Nothing -> HH.text ""
            
              -- Progress bar (shown during generation)
            , if state.isRendering
                then renderProgressBar state
                else HH.text ""
            
              -- Generate button
            , HH.div [ cls [ "lattice-generate-actions" ] ]
                [ HH.button 
                    [ cls [ "lattice-btn lattice-btn-primary lattice-btn-lg" ]
                    , HP.disabled (state.isRendering || state.promptText == "")
                    , HE.onClick \_ -> GenerateFromPrompt
                    ]
                    [ HH.text (if state.isRendering then "Generating..." else "Generate") ]
                ]
            
              -- Connection status
            , case state.bridgeClient of
                Nothing -> 
                  HH.div [ cls [ "lattice-connection-status lattice-disconnected" ] ]
                    [ HH.text "Backend disconnected" ]
                Just _ ->
                  HH.div [ cls [ "lattice-connection-status lattice-connected" ] ]
                    [ HH.text "Connected" ]
            ]
        ]
    ]

-- | Progress bar for generation
renderProgressBar :: forall m. State -> H.ComponentHTML Action Slots m
renderProgressBar state =
  HH.div [ cls [ "lattice-progress-container" ] ]
    [ -- Stage label
      HH.div [ cls [ "lattice-progress-header" ] ]
        [ HH.span [ cls [ "lattice-progress-stage" ] ]
            [ HH.text (stageLabel state.generationStage) ]
        , HH.span [ cls [ "lattice-progress-percentage" ] ]
            [ HH.text (show (floor state.generationProgress) <> "%") ]
        ]
    
      -- Progress bar track
    , HH.div 
        [ cls [ "lattice-progress-track" ]
        , HP.attr (HH.AttrName "style") progressTrackStyle
        ]
        [ -- Progress bar fill
          HH.div 
            [ cls [ "lattice-progress-fill" ]
            , HP.attr (HH.AttrName "style") (progressFillStyle state.generationProgress)
            ]
            []
        ]
    
      -- ETA display
    , case state.generationEta of
        Just eta -> 
          HH.div [ cls [ "lattice-progress-eta lattice-text-muted" ] ]
            [ HH.text ("~" <> formatEta eta <> " remaining") ]
        Nothing -> HH.text ""
    ]
  where
    stageLabel :: String -> String
    stageLabel = case _ of
      "encoding" -> "Encoding prompt..."
      "sampling" -> "Sampling..."
      "decoding" -> "Decoding frames..."
      "idle" -> "Preparing..."
      other -> other
    
    formatEta :: Number -> String
    formatEta seconds =
      if seconds < 60.0
        then show (floor seconds) <> "s"
        else 
          let mins = floor (seconds / 60.0)
              secs = floor (seconds - (toNumber mins * 60.0))
          in show mins <> "m " <> show secs <> "s"

progressTrackStyle :: String
progressTrackStyle =
  "width: 100%; height: 8px; background: var(--lattice-surface-2); " <>
  "border-radius: 4px; overflow: hidden; margin: 8px 0;"

progressFillStyle :: Number -> String
progressFillStyle percentage =
  "width: " <> show percentage <> "%; height: 100%; " <>
  "background: linear-gradient(90deg, var(--lattice-accent), var(--lattice-accent-bright)); " <>
  "border-radius: 4px; transition: width 0.3s ease-out;"

-- | Mode toggle button helper
modeButton :: forall m. State -> GenerationMode -> String -> String -> H.ComponentHTML Action Slots m
modeButton state mode label title =
  HH.button
    [ cls [ "lattice-mode-btn" ]
    , HP.attr (HH.AttrName "data-state") (if state.generationMode == mode then "active" else "inactive")
    , HE.onClick \_ -> SetGenerationMode mode
    , HP.title title
    ]
    [ HH.text label ]

-- | Source image selector for I2V, Edit, and 3D modes
renderSourceImageSelector :: forall m. State -> H.ComponentHTML Action Slots m
renderSourceImageSelector state =
  HH.div [ cls [ "lattice-source-image" ] ]
    [ HH.label_ [ HH.text "Source Image" ]
    , case state.sourceImageUrl of
        Nothing ->
          HH.div [ cls [ "lattice-source-options" ] ]
            [ HH.button 
                [ cls [ "lattice-btn lattice-btn-ghost" ]
                , HP.title "Select from imported assets"
                ]
                [ HH.text "From Assets" ]
            , HH.button 
                [ cls [ "lattice-btn lattice-btn-ghost" ]
                , HP.title "Use current render preview"
                ]
                [ HH.text "From Preview" ]
            , HH.button 
                [ cls [ "lattice-btn lattice-btn-ghost" ]
                , HP.title "Capture current scene view"
                ]
                [ HH.text "From Scene" ]
            ]
        Just url ->
          HH.div [ cls [ "lattice-source-preview" ] ]
            [ HH.img 
                [ HP.src url
                , HP.alt "Source"
                , HP.attr (HH.AttrName "style") "max-width: 100%; max-height: 80px; object-fit: contain;"
                ]
            , HH.button 
                [ cls [ "lattice-btn-icon" ]
                , HP.title "Clear source image"
                , HE.onClick \_ -> SetSourceImage ""
                ]
                [ HH.text "x" ]
            ]
    ]

-- | Get available models for a generation mode
-- | Models specified by user:
-- | - T2I: flux-1-dev, flux-schnell, flux-2-dev, qwen-image, z-image
-- | - Edit: flux-2-dev, z-image-edit, qwen-image-edit
-- | - I2V: ati, wan-move, ltx-2, hunyuan-video (plus existing exports)
-- | - T2V: wan-2.1, hunyuan-video, ltx-2, mochi
-- | - 3D: trellis-2, hunyuan-3d
modelsForMode :: forall m. GenerationMode -> Array (H.ComponentHTML Action Slots m)
modelsForMode = case _ of
  TextToImage ->
    [ HH.option [ HP.value "flux-1-dev" ] [ HH.text "Flux 1 Dev" ]
    , HH.option [ HP.value "flux-schnell" ] [ HH.text "Flux Schnell" ]
    , HH.option [ HP.value "flux-2-dev" ] [ HH.text "Flux 2 Dev" ]
    , HH.option [ HP.value "qwen-image" ] [ HH.text "Qwen Image" ]
    , HH.option [ HP.value "z-image" ] [ HH.text "Z-Image" ]
    ]
  ImageEdit ->
    [ HH.option [ HP.value "flux-2-dev" ] [ HH.text "Flux 2 Dev" ]
    , HH.option [ HP.value "z-image-edit" ] [ HH.text "Z-Image Edit" ]
    , HH.option [ HP.value "qwen-image-edit" ] [ HH.text "Qwen Image Edit" ]
    ]
  ImageToVideo ->
    [ HH.option [ HP.value "ati" ] [ HH.text "ATI" ]
    , HH.option [ HP.value "wan-move" ] [ HH.text "Wan Move" ]
    , HH.option [ HP.value "ltx-2" ] [ HH.text "LTX 2" ]
    , HH.option [ HP.value "hunyuan-video" ] [ HH.text "Hunyuan Video" ]
    ]
  TextToVideo ->
    [ HH.option [ HP.value "wan-2.1" ] [ HH.text "Wan 2.1" ]
    , HH.option [ HP.value "hunyuan-video" ] [ HH.text "Hunyuan Video" ]
    , HH.option [ HP.value "ltx-2" ] [ HH.text "LTX 2" ]
    , HH.option [ HP.value "mochi" ] [ HH.text "Mochi" ]
    ]
  TextTo3D ->
    [ HH.option [ HP.value "trellis-2" ] [ HH.text "Trellis 2" ]
    , HH.option [ HP.value "hunyuan-3d" ] [ HH.text "Hunyuan 3D" ]
    ]

getSelectedLayer :: State -> Maybe LayerBase
getSelectedLayer state =
  case state.selectedLayerIds of
    [layerId] -> findLayer layerId state.layers
    _ -> Nothing

findLayer :: String -> Array LayerBase -> Maybe LayerBase
findLayer _layerId _layers = Nothing  -- Simplified for now

tabButton :: forall m. String -> Boolean -> H.ComponentHTML Action Slots m
tabButton label active =
  HH.button
    [ cls [ "lattice-tabs-trigger" ]
    , HP.attr (HH.AttrName "data-state") (if active then "active" else "inactive")
    ]
    [ HH.text label ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                          // inline // styles
-- ════════════════════════════════════════════════════════════════════════════

workspaceStyle :: String
workspaceStyle = 
  "display: flex; flex-direction: column; height: 100vh; " <>
  "background: var(--lattice-void); overflow: hidden;"

menuBarStyle :: String
menuBarStyle =
  "height: 28px; min-height: 28px; display: flex; align-items: center; " <>
  "justify-content: space-between; padding: 0 12px; " <>
  "background: var(--lattice-surface-0); border-bottom: 1px solid var(--lattice-border-subtle);"

toolbarStyle :: String
toolbarStyle =
  "min-height: 54px; display: flex; align-items: center; gap: 8px; " <>
  "padding: 8px 12px; background: var(--lattice-surface-1); " <>
  "border-bottom: 1px solid var(--lattice-border-subtle);"

contentStyle :: String
contentStyle =
  "flex: 1; display: flex; overflow: hidden;"

sidebarStyle :: Number -> String -> String
sidebarStyle width borderSide =
  "width: " <> show width <> "%; min-width: 200px; max-width: 400px; " <>
  "background: var(--lattice-surface-1); " <>
  "border-" <> borderSide <> ": 1px solid var(--lattice-border-subtle); " <>
  "overflow-y: auto;"

centerStyle :: String
centerStyle =
  "flex: 1; display: flex; flex-direction: column; overflow: hidden;"

viewportContainerStyle :: String
viewportContainerStyle =
  "flex: 1; display: flex; gap: 2px; min-height: 0; " <>
  "background: var(--lattice-border-subtle);"

sceneViewportStyle :: String
sceneViewportStyle =
  "flex: 1; display: flex; flex-direction: column; " <>
  "background: var(--lattice-surface-0);"

renderViewportStyle :: String
renderViewportStyle =
  "flex: 1; display: flex; flex-direction: column; " <>
  "background: var(--lattice-surface-0);"

sceneCanvasStyle :: String
sceneCanvasStyle =
  "flex: 1; position: relative; display: flex; " <>
  "align-items: center; justify-content: center; " <>
  "background: var(--lattice-void); overflow: hidden;"

renderCanvasStyle :: String
renderCanvasStyle =
  "flex: 1; position: relative; display: flex; " <>
  "align-items: center; justify-content: center; " <>
  "background: #000000; overflow: hidden;"

renderPlaceholderStyle :: String
renderPlaceholderStyle =
  "display: flex; align-items: center; justify-content: center; " <>
  "width: 100%; height: 100%; color: var(--lattice-text-muted);"

renderOutputStyle :: String
renderOutputStyle =
  "max-width: 100%; max-height: 100%; object-fit: contain;"

shadowboxStyle :: CompositionDimensions -> String
shadowboxStyle dims =
  "position: absolute; " <>
  "aspect-ratio: " <> show dims.width <> " / " <> show dims.height <> "; " <>
  "max-width: 90%; max-height: 90%; " <>
  "border: 2px dashed var(--lattice-border-strong); " <>
  "box-shadow: 0 0 0 9999px rgba(0, 0, 0, 0.5); " <>
  "pointer-events: none;"

timelineStyle :: Number -> String
timelineStyle height =
  "height: " <> show height <> "%; min-height: 150px; " <>
  "background: var(--lattice-surface-1); border-top: 1px solid var(--lattice-border-subtle);"

drawCanvasContainerStyle :: String
drawCanvasContainerStyle =
  "flex: 1; display: flex; align-items: center; justify-content: center; " <>
  "padding: 8px; background: var(--lattice-void); overflow: hidden;"

drawCanvasStyle :: String
drawCanvasStyle =
  "max-width: 100%; max-height: 100%; object-fit: contain; " <>
  "background: #000000; cursor: crosshair;"

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
  
  -- Scene camera controls
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
  
  -- Drawing canvas
  SetBrushSize _size -> pure unit  -- Will wire up to canvas
  SetBrushColor _color -> pure unit
  SetBrushOpacity _opacity -> pure unit
  ClearDrawingCanvas -> pure unit  -- Will clear the canvas
  
  -- AI generation
  SetPromptText text -> 
    H.modify_ _ { promptText = text }
  
  SetNegativePrompt text -> 
    H.modify_ _ { negativePrompt = text }
  
  SetGenerationMode mode -> do
    -- When mode changes, select a default model for that mode
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
        -- Reset progress and start rendering
        H.modify_ _ 
          { isRendering = true
          , renderError = Nothing
          , generationProgress = 0.0
          , generationStage = "encoding"
          , generationEta = Nothing
          }
        -- Build generation config
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
              , controlnetImage: state.maskImageUrl  -- Use mask as controlnet for edit mode
              , controlnetType: case state.generationMode of
                  ImageEdit -> Just "inpaint"
                  _ -> Nothing
              , controlnetStrength: Nothing
              }
        -- Call appropriate generation function based on mode
        result <- liftAff $ case state.generationMode of
          TextToImage -> Bridge.generateImage client config
          ImageEdit -> Bridge.generateImage client config
          TextTo3D -> Bridge.generateImage client config  -- 3D returns image for now
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
              -- Take first frame for preview (or last for video)
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

-- | Get last element of array, or first if only one
lastOrFirst :: Array String -> String
lastOrFirst [] = ""
lastOrFirst [x] = x
lastOrFirst arr = case arr of
  [] -> ""
  _ -> go arr
  where
    go [x] = x
    go (_ : xs) = go xs
    go [] = ""

clamp :: Number -> Number -> Number -> Number
clamp minVal maxVal val = max minVal (min maxVal val)
