-- | WebGL Canvas Component
-- | Initializes and manages the WebGL rendering context for the viewport
-- | Uses the GLSL Engine for GPU-accelerated rendering
module Lattice.UI.Components.WebGLCanvas where

import Prelude
import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Events as HE
import Web.HTML.HTMLCanvasElement as Canvas
import Lattice.UI.Core (cls)
import Lattice.Services.GLSL.Engine as GLSL

type Input =
  { width :: Int
  , height :: Int
  , backgroundColor :: String
  }

data Output
  = CanvasReady
  | CanvasResized Int Int
  | RenderFrame Int

data Query a
type Slot id = H.Slot Query Output id

type State =
  { width :: Int
  , height :: Int
  , backgroundColor :: String
  , isInitialized :: Boolean
  , zoom :: Number
  , panX :: Number
  , panY :: Number
  , isDragging :: Boolean
  , glslEngineConfig :: Maybe GLSL.GLSLEngineConfig
  , webglAvailable :: Boolean
  , currentFrame :: Int
  , time :: Number
  }

data Action
  = Initialize
  | Receive Input
  | HandleCanvasRef (Maybe Canvas.HTMLCanvasElement)
  | HandleMouseDown Number Number
  | HandleMouseMove Number Number
  | HandleMouseUp
  | HandleWheel Number
  | ZoomIn
  | ZoomOut
  | ResetView

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
  { width: input.width
  , height: input.height
  , backgroundColor: input.backgroundColor
  , isInitialized: false
  , zoom: 1.0
  , panX: 0.0
  , panY: 0.0
  , isDragging: false
  , glslEngineConfig: Nothing
  , webglAvailable: false
  , currentFrame: 0
  , time: 0.0
  }

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ cls [ "lattice-webgl-container" ]
    , HP.attr (HH.AttrName "style") containerStyle
    ]
    [ renderToolbar state
    , HH.div
        [ cls [ "lattice-canvas-wrapper" ]
        , HP.attr (HH.AttrName "style") wrapperStyle
        ]
        [ HH.canvas
            [ cls [ "lattice-webgl-canvas" ]
            , HP.id "lattice-webgl"
            , HP.width state.width
            , HP.height state.height
            , HP.attr (HH.AttrName "style") (canvasStyle state)
            ]
        , if not state.isInitialized
            then renderPlaceholder state
            else HH.text ""
        ]
    , renderStatusBar state
    ]

renderToolbar :: forall m. State -> H.ComponentHTML Action () m
renderToolbar state =
  HH.div
    [ cls [ "lattice-canvas-toolbar" ]
    , HP.attr (HH.AttrName "style") toolbarStyle
    ]
    [ HH.button
        [ cls [ "lattice-canvas-btn" ]
        , HE.onClick \_ -> ZoomOut
        , HP.title "Zoom Out"
        ]
        [ HH.text "-" ]
    , HH.span [ cls [ "lattice-zoom-level" ] ]
        [ HH.text (show (state.zoom * 100.0) <> "%") ]
    , HH.button
        [ cls [ "lattice-canvas-btn" ]
        , HE.onClick \_ -> ZoomIn
        , HP.title "Zoom In"
        ]
        [ HH.text "+" ]
    , HH.button
        [ cls [ "lattice-canvas-btn" ]
        , HE.onClick \_ -> ResetView
        , HP.title "Reset View"
        ]
        [ HH.text "⟲" ]
    ]

renderPlaceholder :: forall m. State -> H.ComponentHTML Action () m
renderPlaceholder state =
  HH.div
    [ cls [ "lattice-canvas-placeholder" ]
    , HP.attr (HH.AttrName "style") placeholderStyle
    ]
    [ HH.div [ cls [ "lattice-placeholder-content" ] ]
        [ HH.span [ cls [ "lattice-placeholder-icon" ] ] [ HH.text "🎬" ]
        , HH.p_ [ HH.text "Canvas" ]
        , HH.p [ cls [ "lattice-text-muted" ] ]
            [ HH.text (show state.width <> " × " <> show state.height) ]
        ]
    ]

renderStatusBar :: forall m. State -> H.ComponentHTML Action () m
renderStatusBar state =
  HH.div
    [ cls [ "lattice-canvas-status" ]
    , HP.attr (HH.AttrName "style") statusStyle
    ]
    [ HH.span_ [ HH.text (show state.width <> " × " <> show state.height) ]
    , HH.span_ [ HH.text " | " ]
    , HH.span_ [ HH.text ("Zoom: " <> show (state.zoom * 100.0) <> "%") ]
    ]

containerStyle :: String
containerStyle =
  "display: flex; flex-direction: column; flex: 1; " <>
  "background: var(--lattice-void); overflow: hidden;"

toolbarStyle :: String
toolbarStyle =
  "display: flex; align-items: center; gap: var(--lattice-space-2); " <>
  "padding: var(--lattice-space-2); background: var(--lattice-surface-1); " <>
  "border-bottom: 1px solid var(--lattice-border-subtle);"

wrapperStyle :: String
wrapperStyle =
  "flex: 1; position: relative; display: flex; " <>
  "align-items: center; justify-content: center; overflow: hidden;"

canvasStyle :: State -> String
canvasStyle state =
  "transform: scale(" <> show state.zoom <> ") " <>
  "translate(" <> show state.panX <> "px, " <> show state.panY <> "px); " <>
  "transform-origin: center; image-rendering: pixelated; " <>
  "box-shadow: 0 4px 20px rgba(0,0,0,0.5);"

placeholderStyle :: String
placeholderStyle =
  "position: absolute; inset: 0; display: flex; " <>
  "align-items: center; justify-content: center; " <>
  "background: var(--lattice-surface-0); text-align: center;"

statusStyle :: String
statusStyle =
  "display: flex; align-items: center; gap: var(--lattice-space-2); " <>
  "padding: var(--lattice-space-1) var(--lattice-space-2); " <>
  "background: var(--lattice-surface-1); font-size: var(--lattice-text-xs); " <>
  "color: var(--lattice-text-muted); border-top: 1px solid var(--lattice-border-subtle);"

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> do
    -- WebGL availability will be determined by the Haskell backend
    -- For now, assume it's available and use pure configuration
    let config = GLSL.defaultEngineConfig
    H.modify_ _ 
      { glslEngineConfig = Just config
      , webglAvailable = true  -- Backend will verify
      , isInitialized = true 
      }
    H.raise CanvasReady

  Receive input -> do
    H.modify_ _ { width = input.width, height = input.height, backgroundColor = input.backgroundColor }
    state <- H.get
    H.raise (CanvasResized state.width state.height)

  HandleCanvasRef _mbCanvas -> pure unit

  HandleMouseDown _x _y -> H.modify_ _ { isDragging = true }

  HandleMouseMove x y -> do
    state <- H.get
    when state.isDragging do
      H.modify_ _ { panX = state.panX + x, panY = state.panY + y }

  HandleMouseUp -> H.modify_ _ { isDragging = false }

  HandleWheel delta -> do
    state <- H.get
    let newZoom = clamp 0.1 10.0 (state.zoom + delta * 0.001)
    H.modify_ _ { zoom = newZoom }

  ZoomIn -> do
    state <- H.get
    let newZoom = min 10.0 (state.zoom * 1.25)
    H.modify_ _ { zoom = newZoom }

  ZoomOut -> do
    state <- H.get
    let newZoom = max 0.1 (state.zoom / 1.25)
    H.modify_ _ { zoom = newZoom }

  ResetView -> H.modify_ _ { zoom = 1.0, panX = 0.0, panY = 0.0 }

clamp :: Number -> Number -> Number -> Number
clamp minVal maxVal val = max minVal (min maxVal val)
