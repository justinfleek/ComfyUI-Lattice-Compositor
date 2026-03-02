-- | CurveEditor Component
-- | Bezier curve editor for keyframe interpolation
module Lattice.UI.Components.CurveEditor where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Array (mapWithIndex)
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Lattice.UI.Core (cls)

type BezierHandle = { x :: Number, y :: Number }
type Keyframe = { frame :: Int, value :: Number, inHandle :: BezierHandle, outHandle :: BezierHandle }

type Input =
  { keyframes :: Array Keyframe
  , selectedIndex :: Maybe Int
  , width :: Number
  , height :: Number
  }

data Output
  = KeyframeSelected Int
  | KeyframeMoved Int Number Number
  | HandleMoved Int Boolean Number Number

data Query a
type Slot id = H.Slot Query Output id

type State =
  { keyframes :: Array Keyframe
  , selectedIndex :: Maybe Int
  , width :: Number
  , height :: Number
  , isDragging :: Boolean
  , dragTarget :: DragTarget
  }

data DragTarget = DragNone | DragKeyframe Int | DragInHandle Int | DragOutHandle Int

data Action
  = Initialize
  | Receive Input
  | SelectKeyframe Int
  | StartDragKeyframe Int
  | StartDragInHandle Int
  | StartDragOutHandle Int
  | EndDrag
  | HandleMouseMove Number Number

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
  { keyframes: input.keyframes
  , selectedIndex: input.selectedIndex
  , width: input.width
  , height: input.height
  , isDragging: false
  , dragTarget: DragNone
  }

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ cls [ "lattice-curve-editor" ]
    , HP.attr (HH.AttrName "style") (containerStyle state.width state.height)
    ]
    [ renderGrid state
    , renderCurves state
    , renderKeyframes state
    ]

renderGrid :: forall m. State -> H.ComponentHTML Action () m
renderGrid state =
  HH.svg
    [ HP.attr (HH.AttrName "class") "lattice-curve-grid"
    , HP.attr (HH.AttrName "width") (show state.width)
    , HP.attr (HH.AttrName "height") (show state.height)
    , HP.attr (HH.AttrName "style") gridStyle
    ]
    [ HH.g []
        [ gridLine 0.0 (state.height / 2.0) state.width (state.height / 2.0)
        , gridLine (state.width / 2.0) 0.0 (state.width / 2.0) state.height
        ]
    ]

gridLine :: forall m. Number -> Number -> Number -> Number -> H.ComponentHTML Action () m
gridLine x1 y1 x2 y2 =
  HH.element (HH.ElemName "line")
    [ HP.attr (HH.AttrName "x1") (show x1)
    , HP.attr (HH.AttrName "y1") (show y1)
    , HP.attr (HH.AttrName "x2") (show x2)
    , HP.attr (HH.AttrName "y2") (show y2)
    , HP.attr (HH.AttrName "stroke") "var(--lattice-border-subtle)"
    , HP.attr (HH.AttrName "stroke-width") "1"
    ]
    []

renderCurves :: forall m. State -> H.ComponentHTML Action () m
renderCurves state =
  HH.svg
    [ HP.attr (HH.AttrName "class") "lattice-curve-paths"
    , HP.attr (HH.AttrName "width") (show state.width)
    , HP.attr (HH.AttrName "height") (show state.height)
    , HP.attr (HH.AttrName "style") curvesStyle
    ]
    [ HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") (buildCurvePath state)
        , HP.attr (HH.AttrName "fill") "none"
        , HP.attr (HH.AttrName "stroke") "var(--lattice-accent)"
        , HP.attr (HH.AttrName "stroke-width") "2"
        ]
        []
    ]

buildCurvePath :: State -> String
buildCurvePath state =
  case state.keyframes of
    [] -> ""
    [kf] -> "M " <> show (frameToX state kf.frame) <> " " <> show (valueToY state kf.value)
    kfs -> buildPath state kfs

buildPath :: State -> Array Keyframe -> String
buildPath state kfs =
  case kfs of
    [] -> ""
    (first : _) ->
      "M " <> show (frameToX state first.frame) <> " " <> show (valueToY state first.value)

frameToX :: State -> Int -> Number
frameToX state frame = (toNumber frame / 100.0) * state.width

valueToY :: State -> Number -> Number
valueToY state value = state.height - (value * state.height)

toNumber :: Int -> Number
toNumber n = n * 1.0

renderKeyframes :: forall m. State -> H.ComponentHTML Action () m
renderKeyframes state =
  HH.div [ cls [ "lattice-curve-keyframes" ] ]
    (mapWithIndex (renderKeyframe state) state.keyframes)

renderKeyframe :: forall m. State -> Int -> Keyframe -> H.ComponentHTML Action () m
renderKeyframe state index kf =
  let
    x = frameToX state kf.frame
    y = valueToY state kf.value
    isSelected = state.selectedIndex == Just index
  in
  HH.div
    [ cls [ "lattice-curve-keyframe" ]
    , HP.attr (HH.AttrName "style") (keyframeStyle x y isSelected)
    , HE.onClick \_ -> SelectKeyframe index
    ]
    [ if isSelected then renderHandles state index kf else HH.text "" ]

renderHandles :: forall m. State -> Int -> Keyframe -> H.ComponentHTML Action () m
renderHandles state _index kf =
  let
    kfX = frameToX state kf.frame
    kfY = valueToY state kf.value
    inX = kfX + kf.inHandle.x * 50.0
    inY = kfY - kf.inHandle.y * 50.0
    outX = kfX + kf.outHandle.x * 50.0
    outY = kfY - kf.outHandle.y * 50.0
  in
  HH.g []
    [ HH.div
        [ cls [ "lattice-curve-handle-line" ]
        , HP.attr (HH.AttrName "style") (handleLineStyle kfX kfY inX inY)
        ]
        []
    , HH.div
        [ cls [ "lattice-curve-handle" ]
        , HP.attr (HH.AttrName "style") (handleStyle inX inY)
        ]
        []
    , HH.div
        [ cls [ "lattice-curve-handle-line" ]
        , HP.attr (HH.AttrName "style") (handleLineStyle kfX kfY outX outY)
        ]
        []
    , HH.div
        [ cls [ "lattice-curve-handle" ]
        , HP.attr (HH.AttrName "style") (handleStyle outX outY)
        ]
        []
    ]

containerStyle :: Number -> Number -> String
containerStyle w h =
  "position: relative; width: " <> show w <> "px; height: " <> show h <> "px; " <>
  "background: var(--lattice-surface-2); border-radius: var(--lattice-radius-md); " <>
  "border: 1px solid var(--lattice-border-subtle); overflow: hidden;"

gridStyle :: String
gridStyle = "position: absolute; top: 0; left: 0;"

curvesStyle :: String
curvesStyle = "position: absolute; top: 0; left: 0; pointer-events: none;"

keyframeStyle :: Number -> Number -> Boolean -> String
keyframeStyle x y selected =
  "position: absolute; left: " <> show (x - 6.0) <> "px; top: " <> show (y - 6.0) <> "px; " <>
  "width: 12px; height: 12px; border-radius: 2px; cursor: pointer; " <>
  "background: " <> (if selected then "var(--lattice-accent)" else "var(--lattice-surface-3)") <> "; " <>
  "border: 2px solid var(--lattice-accent);"

handleStyle :: Number -> Number -> String
handleStyle x y =
  "position: absolute; left: " <> show (x - 4.0) <> "px; top: " <> show (y - 4.0) <> "px; " <>
  "width: 8px; height: 8px; border-radius: 50%; cursor: pointer; " <>
  "background: var(--lattice-accent-vivid);"

handleLineStyle :: Number -> Number -> Number -> Number -> String
handleLineStyle _x1 _y1 _x2 _y2 =
  "position: absolute; background: var(--lattice-accent-muted); height: 1px;"

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> pure unit
  Receive input -> H.modify_ _ 
    { keyframes = input.keyframes
    , selectedIndex = input.selectedIndex
    , width = input.width
    , height = input.height
    }
  SelectKeyframe index -> do
    H.modify_ _ { selectedIndex = Just index }
    H.raise (KeyframeSelected index)
  StartDragKeyframe index -> H.modify_ _ { isDragging = true, dragTarget = DragKeyframe index }
  StartDragInHandle index -> H.modify_ _ { isDragging = true, dragTarget = DragInHandle index }
  StartDragOutHandle index -> H.modify_ _ { isDragging = true, dragTarget = DragOutHandle index }
  EndDrag -> H.modify_ _ { isDragging = false, dragTarget = DragNone }
  HandleMouseMove _x _y -> pure unit
