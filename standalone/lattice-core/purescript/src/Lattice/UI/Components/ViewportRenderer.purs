-- | ViewportRenderer - Multi-view 3D Scene Viewport Component
-- |
-- | Port of: comfyui/ui/src/components/viewport/ViewportRenderer.vue
-- |
-- | Supports 1, 2, or 4 view layouts with orthographic and perspective cameras.
-- | Each view can show: Active Camera, Custom orbit view, or fixed ortho views
-- | (Front, Back, Left, Right, Top, Bottom).
module Lattice.UI.Components.ViewportRenderer
  ( component
  , Input
  , Output(..)
  , Query
  , Slot
  , ViewType(..)
  , ViewLayout(..)
  , Camera3D
  , LayerInfo
  , ViewOptions
  , CustomViewState
  ) where

import Prelude

import Data.Array ((..), length, index, take, mapWithIndex, filter, (:))
import Data.Int (toNumber, floor)
import Data.Maybe (Maybe(..), fromMaybe, isJust)
import Data.Number (isFinite)
import Effect (Effect)
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP

import Lattice.UI.Core (cls)
import Lattice.Services.Render.SceneRenderer as Scene
import Lattice.Services.Math3D.Vec3 (Vec3, vec3)

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | View type for each viewport panel
data ViewType
  = ViewActiveCamera
  | ViewCustom1
  | ViewCustom2
  | ViewCustom3
  | ViewFront
  | ViewBack
  | ViewLeft
  | ViewRight
  | ViewTop
  | ViewBottom

derive instance eqViewType :: Eq ViewType

instance showViewType :: Show ViewType where
  show = case _ of
    ViewActiveCamera -> "active-camera"
    ViewCustom1 -> "custom-1"
    ViewCustom2 -> "custom-2"
    ViewCustom3 -> "custom-3"
    ViewFront -> "front"
    ViewBack -> "back"
    ViewLeft -> "left"
    ViewRight -> "right"
    ViewTop -> "top"
    ViewBottom -> "bottom"

-- | Parse ViewType from string
parseViewType :: String -> Maybe ViewType
parseViewType = case _ of
  "active-camera" -> Just ViewActiveCamera
  "custom-1" -> Just ViewCustom1
  "custom-2" -> Just ViewCustom2
  "custom-3" -> Just ViewCustom3
  "front" -> Just ViewFront
  "back" -> Just ViewBack
  "left" -> Just ViewLeft
  "right" -> Just ViewRight
  "top" -> Just ViewTop
  "bottom" -> Just ViewBottom
  _ -> Nothing

-- | Viewport layout configuration
data ViewLayout
  = Layout1View
  | Layout2ViewHorizontal
  | Layout2ViewVertical
  | Layout4View

derive instance eqViewLayout :: Eq ViewLayout

-- | Custom view orbit state for interactive views
type CustomViewState =
  { orbitCenter :: Vec3
  , orbitDistance :: Number
  , orbitPhi :: Number      -- Vertical angle (1-179 degrees)
  , orbitTheta :: Number    -- Horizontal angle
  , orthoZoom :: Number
  , orthoOffset :: { x :: Number, y :: Number }
  }

-- | Camera data from composition
type Camera3D =
  { position :: Vec3
  , pointOfInterest :: Vec3
  , focalLength :: Number
  , filmSize :: Number
  , nearClip :: Number
  , farClip :: Number
  }

-- | Layer data for visualization
type LayerInfo =
  { id :: String
  , name :: String
  , position :: Vec3
  , selected :: Boolean
  }

-- | View options configuration
type ViewOptions =
  { showGrid :: Boolean
  , show3DReferenceAxes :: Boolean
  , showCompositionBounds :: Boolean
  , showLayerHandles :: Boolean
  , cameraWireframes :: String -- "always" | "selected" | "never"
  , showFocalPlane :: Boolean
  }

type Input =
  { compWidth :: Int
  , compHeight :: Int
  , camera :: Maybe Camera3D
  , layers :: Array LayerInfo
  , viewOptions :: ViewOptions
  }

data Output
  = ViewChanged Int ViewType
  | LayoutChanged ViewLayout
  | CustomViewUpdated String CustomViewState

data Query a

type Slot id = H.Slot Query Output id

type State =
  { -- Input state
    compWidth :: Int
  , compHeight :: Int
  , camera :: Maybe Camera3D
  , layers :: Array LayerInfo
  , viewOptions :: ViewOptions
    -- Viewport state
  , layout :: ViewLayout
  , views :: Array ViewType
  , activeViewIndex :: Int
  , customViews ::
      { custom1 :: CustomViewState
      , custom2 :: CustomViewState
      , custom3 :: CustomViewState
      }
    -- Interaction state
  , isDragging :: Boolean
  , dragStartPos :: { x :: Number, y :: Number }
  , dragViewIndex :: Int
  , dragButton :: Int
  }

data Action
  = Initialize
  | Receive Input
  | SetActiveView Int
  | UpdateViewType Int String
  | SetLayout ViewLayout
  | ResetCustomView ViewType
  | HandleMouseDown Int Int Int Int  -- viewIndex, button, clientX, clientY
  | HandleMouseMove Int Int          -- deltaX, deltaY
  | HandleMouseUp
  | HandleWheel Int Number           -- viewIndex, deltaY
  | RenderFrame

-- ────────────────────────────────────────────────────────────────────────────
-- Component
-- ────────────────────────────────────────────────────────────────────────────

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
  { compWidth: input.compWidth
  , compHeight: input.compHeight
  , camera: input.camera
  , layers: input.layers
  , viewOptions: input.viewOptions
  , layout: Layout1View
  , views: [ViewActiveCamera, ViewTop, ViewFront, ViewRight]
  , activeViewIndex: 0
  , customViews:
      { custom1: defaultCustomView input.compWidth input.compHeight
      , custom2: defaultCustomView input.compWidth input.compHeight
      , custom3: defaultCustomView input.compWidth input.compHeight
      }
  , isDragging: false
  , dragStartPos: { x: 0.0, y: 0.0 }
  , dragViewIndex: 0
  , dragButton: 0
  }

defaultCustomView :: Int -> Int -> CustomViewState
defaultCustomView w h =
  { orbitCenter: vec3 (toNumber w / 2.0) (toNumber h / 2.0) 0.0
  , orbitDistance: 2000.0
  , orbitPhi: 60.0
  , orbitTheta: 45.0
  , orthoZoom: 1.0
  , orthoOffset: { x: 0.0, y: 0.0 }
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Render
-- ────────────────────────────────────────────────────────────────────────────

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ cls [ "viewport-renderer", layoutClass state.layout ]
    , HP.attr (HH.AttrName "style") containerStyle
    ]
    [ renderViewPanels state
    , renderLayoutControls state
    ]

layoutClass :: ViewLayout -> String
layoutClass = case _ of
  Layout1View -> "layout-1-view"
  Layout2ViewHorizontal -> "layout-2-view-horizontal"
  Layout2ViewVertical -> "layout-2-view-vertical"
  Layout4View -> "layout-4-view"

renderViewPanels :: forall m. State -> H.ComponentHTML Action () m
renderViewPanels state =
  HH.div
    [ cls [ "view-panels" ]
    , HP.attr (HH.AttrName "style") panelsStyle
    ]
    (mapWithIndex (renderViewPanel state) (activeViews state))

activeViews :: State -> Array ViewType
activeViews state = case state.layout of
  Layout1View -> take 1 state.views
  Layout2ViewHorizontal -> take 2 state.views
  Layout2ViewVertical -> take 2 state.views
  Layout4View -> take 4 state.views

renderViewPanel :: forall m. State -> Int -> ViewType -> H.ComponentHTML Action () m
renderViewPanel state idx viewType =
  HH.div
    [ cls [ "view-panel", if idx == state.activeViewIndex then "active" else "" ]
    , HP.attr (HH.AttrName "style") viewPanelStyle
    , HE.onClick \_ -> SetActiveView idx
    ]
    [ renderViewHeader state idx viewType
    , renderViewCanvas state idx viewType
    , renderViewInfo state viewType
    ]

renderViewHeader :: forall m. State -> Int -> ViewType -> H.ComponentHTML Action () m
renderViewHeader state idx viewType =
  HH.div
    [ cls [ "view-header" ]
    , HP.attr (HH.AttrName "style") headerStyle
    ]
    [ HH.select
        [ cls [ "view-select" ]
        , HP.attr (HH.AttrName "style") selectStyle
        , HP.value (show viewType)
        , HE.onValueChange (UpdateViewType idx)
        ]
        [ HH.option [ HP.value "active-camera" ] [ HH.text "Active Camera" ]
        , HH.option [ HP.value "custom-1" ] [ HH.text "Custom View 1" ]
        , HH.option [ HP.value "custom-2" ] [ HH.text "Custom View 2" ]
        , HH.option [ HP.value "custom-3" ] [ HH.text "Custom View 3" ]
        , HH.option [ HP.value "front" ] [ HH.text "Front" ]
        , HH.option [ HP.value "back" ] [ HH.text "Back" ]
        , HH.option [ HP.value "left" ] [ HH.text "Left" ]
        , HH.option [ HP.value "right" ] [ HH.text "Right" ]
        , HH.option [ HP.value "top" ] [ HH.text "Top" ]
        , HH.option [ HP.value "bottom" ] [ HH.text "Bottom" ]
        ]
    , if isCustomView viewType
        then HH.button
          [ cls [ "reset-btn" ]
          , HP.title "Reset View"
          , HE.onClick \_ -> ResetCustomView viewType
          ]
          [ HH.text "R" ]
        else HH.text ""
    ]

renderViewCanvas :: forall m. State -> Int -> ViewType -> H.ComponentHTML Action () m
renderViewCanvas state idx viewType =
  HH.canvas
    [ cls [ "view-canvas" ]
    , HP.id ("viewport-canvas-" <> show idx)
    , HP.attr (HH.AttrName "style") canvasStyle
    ]

renderViewInfo :: forall m. State -> ViewType -> H.ComponentHTML Action () m
renderViewInfo state viewType =
  HH.div
    [ cls [ "view-info" ]
    , HP.attr (HH.AttrName "style") infoStyle
    ]
    [ HH.span [ cls [ "view-name" ] ] [ HH.text (viewDisplayName viewType) ]
    , if isCustomView viewType
        then HH.span [ cls [ "view-coords" ] ]
          [ HH.text (customViewCoords state viewType) ]
        else HH.text ""
    ]

renderLayoutControls :: forall m. State -> H.ComponentHTML Action () m
renderLayoutControls state =
  HH.div
    [ cls [ "layout-controls" ]
    , HP.attr (HH.AttrName "style") layoutControlsStyle
    ]
    [ layoutButton state Layout1View "1"
    , layoutButton state Layout2ViewHorizontal "2H"
    , layoutButton state Layout2ViewVertical "2V"
    , layoutButton state Layout4View "4"
    ]

layoutButton :: forall m. State -> ViewLayout -> String -> H.ComponentHTML Action () m
layoutButton state layout label =
  HH.button
    [ cls [ "layout-btn", if state.layout == layout then "active" else "" ]
    , HP.attr (HH.AttrName "style") layoutBtnStyle
    , HE.onClick \_ -> SetLayout layout
    ]
    [ HH.text label ]

-- ────────────────────────────────────────────────────────────────────────────
-- Helpers
-- ────────────────────────────────────────────────────────────────────────────

isCustomView :: ViewType -> Boolean
isCustomView = case _ of
  ViewCustom1 -> true
  ViewCustom2 -> true
  ViewCustom3 -> true
  _ -> false

viewDisplayName :: ViewType -> String
viewDisplayName = case _ of
  ViewActiveCamera -> "Camera"
  ViewCustom1 -> "Custom 1"
  ViewCustom2 -> "Custom 2"
  ViewCustom3 -> "Custom 3"
  ViewFront -> "Front"
  ViewBack -> "Back"
  ViewLeft -> "Left"
  ViewRight -> "Right"
  ViewTop -> "Top"
  ViewBottom -> "Bottom"

customViewCoords :: State -> ViewType -> String
customViewCoords state viewType =
  let
    customState = getCustomViewState state viewType
  in
    "t:" <> show (floor customState.orbitTheta) <>
    " p:" <> show (floor customState.orbitPhi)

getCustomViewState :: State -> ViewType -> CustomViewState
getCustomViewState state = case _ of
  ViewCustom1 -> state.customViews.custom1
  ViewCustom2 -> state.customViews.custom2
  ViewCustom3 -> state.customViews.custom3
  _ -> state.customViews.custom1

-- ────────────────────────────────────────────────────────────────────────────
-- Styles
-- ────────────────────────────────────────────────────────────────────────────

containerStyle :: String
containerStyle =
  "display: flex; flex-direction: column; width: 100%; height: 100%; " <>
  "background: var(--lattice-void, #0a0a0a); position: relative;"

panelsStyle :: String
panelsStyle =
  "display: grid; flex: 1; gap: 2px; " <>
  "grid-template-columns: repeat(auto-fit, minmax(200px, 1fr));"

viewPanelStyle :: String
viewPanelStyle =
  "display: flex; flex-direction: column; position: relative; " <>
  "background: #1a1a1a; border: 1px solid transparent; " <>
  "transition: border-color 0.15s;"

headerStyle :: String
headerStyle =
  "display: flex; align-items: center; gap: 4px; padding: 4px 8px; " <>
  "background: rgba(0,0,0,0.3); border-bottom: 1px solid rgba(255,255,255,0.1);"

selectStyle :: String
selectStyle =
  "flex: 1; background: transparent; color: white; border: none; " <>
  "font-size: 11px; cursor: pointer; outline: none;"

canvasStyle :: String
canvasStyle =
  "flex: 1; width: 100%; display: block; background: #1a1a1a;"

infoStyle :: String
infoStyle =
  "position: absolute; bottom: 4px; left: 8px; display: flex; gap: 8px; " <>
  "font-size: 10px; color: rgba(255,255,255,0.5); pointer-events: none;"

layoutControlsStyle :: String
layoutControlsStyle =
  "position: absolute; top: 4px; right: 4px; display: flex; gap: 2px; z-index: 10;"

layoutBtnStyle :: String
layoutBtnStyle =
  "padding: 2px 6px; background: rgba(0,0,0,0.5); color: white; " <>
  "border: 1px solid rgba(255,255,255,0.2); border-radius: 2px; " <>
  "font-size: 10px; cursor: pointer;"

-- ────────────────────────────────────────────────────────────────────────────
-- Action Handler
-- ────────────────────────────────────────────────────────────────────────────

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> do
    pure unit

  Receive input -> do
    H.modify_ _ 
      { compWidth = input.compWidth
      , compHeight = input.compHeight
      , camera = input.camera
      , layers = input.layers
      , viewOptions = input.viewOptions
      }

  SetActiveView idx -> do
    H.modify_ _ { activeViewIndex = idx }

  UpdateViewType idx valueStr -> do
    case parseViewType valueStr of
      Nothing -> pure unit
      Just newType -> do
        state <- H.get
        let newViews = updateAt idx newType state.views
        H.modify_ _ { views = newViews }
        H.raise (ViewChanged idx newType)

  SetLayout layout -> do
    state <- H.get
    let maxIdx = case layout of
          Layout1View -> 0
          Layout2ViewHorizontal -> 1
          Layout2ViewVertical -> 1
          Layout4View -> 3
    H.modify_ _ 
      { layout = layout
      , activeViewIndex = min state.activeViewIndex maxIdx
      }
    H.raise (LayoutChanged layout)

  ResetCustomView viewType -> do
    state <- H.get
    let newCustom = defaultCustomView state.compWidth state.compHeight
    case viewType of
      ViewCustom1 -> do
        H.modify_ _ { customViews { custom1 = newCustom } }
        H.raise (CustomViewUpdated "custom-1" newCustom)
      ViewCustom2 -> do
        H.modify_ _ { customViews { custom2 = newCustom } }
        H.raise (CustomViewUpdated "custom-2" newCustom)
      ViewCustom3 -> do
        H.modify_ _ { customViews { custom3 = newCustom } }
        H.raise (CustomViewUpdated "custom-3" newCustom)
      _ -> pure unit

  HandleMouseDown viewIdx btn clientX clientY -> do
    H.modify_ _
      { isDragging = true
      , dragStartPos = { x: toNumber clientX, y: toNumber clientY }
      , dragViewIndex = viewIdx
      , dragButton = btn
      }

  HandleMouseMove dx dy -> do
    state <- H.get
    when state.isDragging do
      let views = activeViews state
      case index views state.dragViewIndex of
        Nothing -> pure unit
        Just viewType ->
          when (isCustomView viewType) do
            let customState = getCustomViewState state viewType
            if state.dragButton == 0
              -- Left button: orbit
              then do
                let newTheta = customState.orbitTheta + toNumber dx * 0.5
                    newPhi = clamp 1.0 179.0 (customState.orbitPhi + toNumber dy * 0.5)
                    newCustom = customState { orbitTheta = newTheta, orbitPhi = newPhi }
                updateCustomViewState viewType newCustom
              -- Middle/right button: pan
              else do
                let newOffset =
                      { x: customState.orthoOffset.x + toNumber dx
                      , y: customState.orthoOffset.y + toNumber dy
                      }
                    newCustom = customState { orthoOffset = newOffset }
                updateCustomViewState viewType newCustom

  HandleMouseUp -> do
    H.modify_ _ { isDragging = false }

  HandleWheel viewIdx deltaY -> do
    state <- H.get
    let views = activeViews state
    case index views viewIdx of
      Nothing -> pure unit
      Just viewType ->
        when (isCustomView viewType) do
          let customState = getCustomViewState state viewType
              zoomFactor = if deltaY > 0.0 then 1.1 else 0.9
              newDistance = customState.orbitDistance * zoomFactor
              newCustom = customState { orbitDistance = newDistance }
          updateCustomViewState viewType newCustom

  RenderFrame -> do
    pure unit

-- | Update array at index
updateAt :: forall a. Int -> a -> Array a -> Array a
updateAt idx val arr =
  mapWithIndex (\i v -> if i == idx then val else v) arr

-- | Update custom view state and emit output
updateCustomViewState :: forall m. MonadAff m 
  => ViewType 
  -> CustomViewState 
  -> H.HalogenM State Action () Output m Unit
updateCustomViewState viewType newState = do
  case viewType of
    ViewCustom1 -> do
      H.modify_ _ { customViews { custom1 = newState } }
      H.raise (CustomViewUpdated "custom-1" newState)
    ViewCustom2 -> do
      H.modify_ _ { customViews { custom2 = newState } }
      H.raise (CustomViewUpdated "custom-2" newState)
    ViewCustom3 -> do
      H.modify_ _ { customViews { custom3 = newState } }
      H.raise (CustomViewUpdated "custom-3" newState)
    _ -> pure unit

clamp :: Number -> Number -> Number -> Number
clamp minVal maxVal val = max minVal (min maxVal val)
