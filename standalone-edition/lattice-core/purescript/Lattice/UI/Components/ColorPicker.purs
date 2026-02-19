-- | ColorPicker Component
module Lattice.UI.Components.ColorPicker where

import Prelude
import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Lattice.UI.Core (cls)

type Input = { color :: String, label :: String }
data Output = ColorChanged String
data Query a
type Slot id = H.Slot Query Output id

type State =
  { color :: String
  , label :: String
  , isOpen :: Boolean
  , hue :: Number
  , saturation :: Number
  , lightness :: Number
  }

data Action
  = Initialize
  | Receive Input
  | ToggleOpen
  | SetHue Number
  | SetSaturation Number
  | SetLightness Number
  | SetHex String

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
  { color: input.color
  , label: input.label
  , isOpen: false
  , hue: 0.0
  , saturation: 100.0
  , lightness: 50.0
  }

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ cls [ "lattice-color-picker" ]
    , HP.attr (HH.AttrName "style") containerStyle
    ]
    [ HH.span [ cls [ "lattice-color-label" ] ] [ HH.text state.label ]
    , HH.button
        [ cls [ "lattice-color-swatch" ]
        , HP.attr (HH.AttrName "style") (swatchStyle state.color)
        , HE.onClick \_ -> ToggleOpen
        ]
        []
    , if state.isOpen then renderPopover state else HH.text ""
    ]

renderPopover :: forall m. State -> H.ComponentHTML Action () m
renderPopover state =
  HH.div
    [ cls [ "lattice-color-popover" ]
    , HP.attr (HH.AttrName "style") popoverStyle
    ]
    [ HH.div [ cls [ "lattice-color-gradient" ] ]
        [ HH.div
            [ cls [ "lattice-color-saturation" ]
            , HP.attr (HH.AttrName "style") (gradientStyle state.hue)
            ]
            []
        ]
    , HH.div [ cls [ "lattice-color-hue-slider" ] ]
        [ HH.input
            [ HP.type_ HP.InputRange
            , HP.min 0.0
            , HP.max 360.0
            , HP.value (show state.hue)
            , HE.onValueInput \v -> SetHue (parseNumber v)
            ]
        ]
    , HH.div [ cls [ "lattice-color-hex" ] ]
        [ HH.input
            [ cls [ "lattice-input" ]
            , HP.value state.color
            , HE.onValueInput SetHex
            ]
        ]
    ]

containerStyle :: String
containerStyle = "display: flex; align-items: center; gap: var(--lattice-space-2);"

swatchStyle :: String -> String
swatchStyle color =
  "width: 24px; height: 24px; border-radius: var(--lattice-radius-sm); " <>
  "background: " <> color <> "; border: 1px solid var(--lattice-border-subtle); cursor: pointer;"

popoverStyle :: String
popoverStyle =
  "position: absolute; top: 100%; left: 0; z-index: 100; " <>
  "background: var(--lattice-surface-2); border-radius: var(--lattice-radius-md); " <>
  "padding: var(--lattice-space-3); box-shadow: var(--lattice-shadow-lg);"

gradientStyle :: Number -> String
gradientStyle hue =
  "width: 200px; height: 150px; " <>
  "background: linear-gradient(to right, #fff, hsl(" <> show hue <> ", 100%, 50%));"

parseNumber :: String -> Number
parseNumber s = case s of
  _ -> 0.0

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> pure unit
  Receive input -> H.modify_ _ { color = input.color, label = input.label }
  ToggleOpen -> H.modify_ \s -> s { isOpen = not s.isOpen }
  SetHue h -> do
    H.modify_ _ { hue = h }
    state <- H.get
    let newColor = hslToHex state.hue state.saturation state.lightness
    H.modify_ _ { color = newColor }
    H.raise (ColorChanged newColor)
  SetSaturation s -> do
    H.modify_ _ { saturation = s }
    state <- H.get
    let newColor = hslToHex state.hue state.saturation state.lightness
    H.modify_ _ { color = newColor }
    H.raise (ColorChanged newColor)
  SetLightness l -> do
    H.modify_ _ { lightness = l }
    state <- H.get
    let newColor = hslToHex state.hue state.saturation state.lightness
    H.modify_ _ { color = newColor }
    H.raise (ColorChanged newColor)
  SetHex hex -> do
    H.modify_ _ { color = hex }
    H.raise (ColorChanged hex)

hslToHex :: Number -> Number -> Number -> String
hslToHex _h _s _l = "#808080"
