-- | Transform Properties Component
-- |
-- | Displays and edits the transform properties of a layer:
-- | - Position (X, Y, Z if 3D)
-- | - Scale (X, Y, Z if 3D)
-- | - Rotation (Z, and X, Y if 3D)
-- | - Anchor Point (X, Y, Z if 3D)
-- | - Opacity
module Lattice.UI.Components.TransformProperties
  ( component
  , Transform
  , Input
  , Output(..)
  , Query
  , Slot
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Type.Proxy (Proxy(..))
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP

import Lattice.UI.Core (cls, collapsibleHeader)
import Lattice.UI.Components.NumericInput as NumericInput

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                     // types
-- ════════════════════════════════════════════════════════════════════════════

type Transform =
  { positionX :: Number
  , positionY :: Number
  , positionZ :: Number
  , scaleX :: Number
  , scaleY :: Number
  , scaleZ :: Number
  , rotation :: Number
  , rotationX :: Number
  , rotationY :: Number
  , rotationZ :: Number
  , anchorX :: Number
  , anchorY :: Number
  , anchorZ :: Number
  , opacity :: Number
  }

type Input =
  { transform :: Transform
  , is3D :: Boolean
  , layerId :: String
  }

data Output
  = TransformChanged String Transform

data Query a

type Slot id = H.Slot Query Output id

type State =
  { transform :: Transform
  , is3D :: Boolean
  , layerId :: String
  , positionExpanded :: Boolean
  , scaleExpanded :: Boolean
  , rotationExpanded :: Boolean
  , anchorExpanded :: Boolean
  }

data Action
  = Initialize
  | Receive Input
  | TogglePosition
  | ToggleScale
  | ToggleRotation
  | ToggleAnchor
  | HandleNumeric Property Number

data Property
  = PositionX | PositionY | PositionZ
  | ScaleX | ScaleY | ScaleZ
  | Rotation | RotationX | RotationY | RotationZ
  | AnchorX | AnchorY | AnchorZ
  | Opacity

type Slots =
  ( posX :: NumericInput.Slot Unit
  , posY :: NumericInput.Slot Unit
  , posZ :: NumericInput.Slot Unit
  , scaleX :: NumericInput.Slot Unit
  , scaleY :: NumericInput.Slot Unit
  , scaleZ :: NumericInput.Slot Unit
  , rotation :: NumericInput.Slot Unit
  , rotX :: NumericInput.Slot Unit
  , rotY :: NumericInput.Slot Unit
  , rotZ :: NumericInput.Slot Unit
  , anchorX :: NumericInput.Slot Unit
  , anchorY :: NumericInput.Slot Unit
  , anchorZ :: NumericInput.Slot Unit
  , opacity :: NumericInput.Slot Unit
  )

_posX :: Proxy "posX"
_posX = Proxy

_posY :: Proxy "posY"
_posY = Proxy

_posZ :: Proxy "posZ"
_posZ = Proxy

_scaleX :: Proxy "scaleX"
_scaleX = Proxy

_scaleY :: Proxy "scaleY"
_scaleY = Proxy

_scaleZ :: Proxy "scaleZ"
_scaleZ = Proxy

_rotation :: Proxy "rotation"
_rotation = Proxy

_rotX :: Proxy "rotX"
_rotX = Proxy

_rotY :: Proxy "rotY"
_rotY = Proxy

_rotZ :: Proxy "rotZ"
_rotZ = Proxy

_anchorX :: Proxy "anchorX"
_anchorX = Proxy

_anchorY :: Proxy "anchorY"
_anchorY = Proxy

_anchorZ :: Proxy "anchorZ"
_anchorZ = Proxy

_opacity :: Proxy "opacity"
_opacity = Proxy

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
  { transform: input.transform
  , is3D: input.is3D
  , layerId: input.layerId
  , positionExpanded: true
  , scaleExpanded: true
  , rotationExpanded: true
  , anchorExpanded: false
  }

-- ════════════════════════════════════════════════════════════════════════════
--                                                                    // render
-- ════════════════════════════════════════════════════════════════════════════

render :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
render state =
  HH.div
    [ cls [ "lattice-transform-properties" ]
    , HP.attr (HH.AttrName "style") containerStyle
    ]
    [ -- Position section
      renderSection "Position" state.positionExpanded TogglePosition
        (renderPositionInputs state)
    
      -- Scale section
    , renderSection "Scale" state.scaleExpanded ToggleScale
        (renderScaleInputs state)
    
      -- Rotation section
    , renderSection "Rotation" state.rotationExpanded ToggleRotation
        (renderRotationInputs state)
    
      -- Anchor section
    , renderSection "Anchor Point" state.anchorExpanded ToggleAnchor
        (renderAnchorInputs state)
    
      -- Opacity (always visible)
    , renderOpacityInput state
    ]

renderSection :: forall m. MonadAff m 
  => String 
  -> Boolean 
  -> Action 
  -> Array (H.ComponentHTML Action Slots m) 
  -> H.ComponentHTML Action Slots m
renderSection title expanded toggleAction content =
  HH.div [ cls [ "lattice-transform-section" ] ]
    [ HH.div 
        [ cls [ "lattice-transform-header" ]
        , HP.attr (HH.AttrName "style") headerStyle
        , HE.onClick \_ -> toggleAction
        ]
        [ collapsibleHeader title expanded ]
    , if expanded
        then HH.div 
          [ cls [ "lattice-transform-content" ]
          , HP.attr (HH.AttrName "style") contentStyle
          ] 
          content
        else HH.text ""
    ]

renderPositionInputs :: forall m. MonadAff m => State -> Array (H.ComponentHTML Action Slots m)
renderPositionInputs state =
  [ numericRow _posX "X" state.transform.positionX PositionX
  , numericRow _posY "Y" state.transform.positionY PositionY
  ] <> if state.is3D 
    then [ numericRow _posZ "Z" state.transform.positionZ PositionZ ]
    else []

renderScaleInputs :: forall m. MonadAff m => State -> Array (H.ComponentHTML Action Slots m)
renderScaleInputs state =
  [ numericRow _scaleX "X" (state.transform.scaleX * 100.0) ScaleX
  , numericRow _scaleY "Y" (state.transform.scaleY * 100.0) ScaleY
  ] <> if state.is3D 
    then [ numericRow _scaleZ "Z" (state.transform.scaleZ * 100.0) ScaleZ ]
    else []

renderRotationInputs :: forall m. MonadAff m => State -> Array (H.ComponentHTML Action Slots m)
renderRotationInputs state =
  if state.is3D
    then
      [ numericRow _rotX "X" state.transform.rotationX RotationX
      , numericRow _rotY "Y" state.transform.rotationY RotationY
      , numericRow _rotZ "Z" state.transform.rotationZ RotationZ
      ]
    else
      [ numericRow _rotation "°" state.transform.rotation Rotation
      ]

renderAnchorInputs :: forall m. MonadAff m => State -> Array (H.ComponentHTML Action Slots m)
renderAnchorInputs state =
  [ numericRow _anchorX "X" state.transform.anchorX AnchorX
  , numericRow _anchorY "Y" state.transform.anchorY AnchorY
  ] <> if state.is3D 
    then [ numericRow _anchorZ "Z" state.transform.anchorZ AnchorZ ]
    else []

renderOpacityInput :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
renderOpacityInput state =
  HH.div 
    [ cls [ "lattice-transform-opacity" ]
    , HP.attr (HH.AttrName "style") opacityStyle
    ]
    [ HH.span [ cls [ "lattice-label" ] ] [ HH.text "Opacity" ]
    , HH.slot _opacity unit NumericInput.component
        { value: state.transform.opacity
        , label: ""
        , min: Just 0.0
        , max: Just 100.0
        , step: 1.0
        , precision: 1
        , suffix: "%"
        }
        (handleNumericOutput Opacity)
    ]

numericRow :: forall m label. MonadAff m 
  => Proxy label 
  -> String 
  -> Number 
  -> Property 
  -> H.ComponentHTML Action Slots m
numericRow _ label value _ =
  HH.div 
    [ cls [ "lattice-transform-row" ]
    , HP.attr (HH.AttrName "style") rowStyle
    ]
    [ HH.text (label <> ": " <> show value) ]

handleNumericOutput :: Property -> NumericInput.Output -> Action
handleNumericOutput prop (NumericInput.ValueChanged value) = 
  HandleNumeric prop value

-- ════════════════════════════════════════════════════════════════════════════
--                                                          // inline // styles
-- ════════════════════════════════════════════════════════════════════════════

containerStyle :: String
containerStyle =
  "display: flex; flex-direction: column; gap: var(--lattice-space-1);"

headerStyle :: String
headerStyle =
  "cursor: pointer; user-select: none;"

contentStyle :: String
contentStyle =
  "display: flex; flex-direction: column; gap: var(--lattice-space-2); " <>
  "padding: var(--lattice-space-2) 0 var(--lattice-space-2) var(--lattice-space-4);"

rowStyle :: String
rowStyle =
  "display: flex; align-items: center; gap: var(--lattice-space-2);"

opacityStyle :: String
opacityStyle =
  "display: flex; align-items: center; justify-content: space-between; " <>
  "padding: var(--lattice-space-2) 0; " <>
  "border-top: 1px solid var(--lattice-border-subtle);"

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // actions
-- ════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action Slots Output m Unit
handleAction = case _ of
  Initialize -> pure unit
  
  Receive input -> do
    H.modify_ _ 
      { transform = input.transform
      , is3D = input.is3D
      , layerId = input.layerId
      }
  
  TogglePosition -> do
    H.modify_ \s -> s { positionExpanded = not s.positionExpanded }
  
  ToggleScale -> do
    H.modify_ \s -> s { scaleExpanded = not s.scaleExpanded }
  
  ToggleRotation -> do
    H.modify_ \s -> s { rotationExpanded = not s.rotationExpanded }
  
  ToggleAnchor -> do
    H.modify_ \s -> s { anchorExpanded = not s.anchorExpanded }
  
  HandleNumeric prop value -> do
    state <- H.get
    let
      newTransform = updateTransform state.transform prop value
    H.modify_ _ { transform = newTransform }
    H.raise (TransformChanged state.layerId newTransform)

updateTransform :: Transform -> Property -> Number -> Transform
updateTransform t prop value = case prop of
  PositionX -> t { positionX = value }
  PositionY -> t { positionY = value }
  PositionZ -> t { positionZ = value }
  ScaleX -> t { scaleX = value / 100.0 }
  ScaleY -> t { scaleY = value / 100.0 }
  ScaleZ -> t { scaleZ = value / 100.0 }
  Rotation -> t { rotation = value }
  RotationX -> t { rotationX = value }
  RotationY -> t { rotationY = value }
  RotationZ -> t { rotationZ = value }
  AnchorX -> t { anchorX = value }
  AnchorY -> t { anchorY = value }
  AnchorZ -> t { anchorZ = value }
  Opacity -> t { opacity = value }
