-- | Numeric Input Component
-- |
-- | A numeric input field with drag-to-adjust functionality.
-- | Supports scrubbing (drag horizontally to change value),
-- | direct text input, and keyboard increment/decrement.
module Lattice.UI.Components.NumericInput
  ( component
  , Input
  , Output(..)
  , Query
  , Slot
  ) where

import Prelude

import Data.Int (round, toNumber)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Number (fromString)
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP

import Lattice.UI.Core (cls)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                     // types
-- ════════════════════════════════════════════════════════════════════════════

type Input =
  { value :: Number
  , label :: String
  , min :: Maybe Number
  , max :: Maybe Number
  , step :: Number
  , precision :: Int
  , suffix :: String
  }

data Output = ValueChanged Number

data Query a

type Slot id = H.Slot Query Output id

type State =
  { value :: Number
  , label :: String
  , min :: Maybe Number
  , max :: Maybe Number
  , step :: Number
  , precision :: Int
  , suffix :: String
  , isDragging :: Boolean
  , isEditing :: Boolean
  , editValue :: String
  , dragStartX :: Number
  , dragStartValue :: Number
  }

data Action
  = Initialize
  | Receive Input
  | StartDrag Number
  | Drag Number
  | EndDrag
  | StartEdit
  | UpdateEditValue String
  | CommitEdit
  | CancelEdit
  | Increment
  | Decrement

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
  { value: input.value
  , label: input.label
  , min: input.min
  , max: input.max
  , step: input.step
  , precision: input.precision
  , suffix: input.suffix
  , isDragging: false
  , isEditing: false
  , editValue: ""
  , dragStartX: 0.0
  , dragStartValue: 0.0
  }

-- ════════════════════════════════════════════════════════════════════════════
--                                                                    // render
-- ════════════════════════════════════════════════════════════════════════════

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ cls [ "lattice-numeric-input" ]
    , HP.attr (HH.AttrName "style") containerStyle
    ]
    [ -- Label
      HH.span
        [ cls [ "lattice-numeric-label" ]
        , HP.attr (HH.AttrName "style") labelStyle
        ]
        [ HH.text state.label ]
    
      -- Value display / input
    , if state.isEditing
        then renderEditMode state
        else renderDisplayMode state
    ]

renderDisplayMode :: forall m. State -> H.ComponentHTML Action () m
renderDisplayMode state =
  HH.div
    [ cls [ "lattice-numeric-display" ]
    , HP.attr (HH.AttrName "style") displayStyle
    , HE.onDoubleClick \_ -> StartEdit
    ]
    [ HH.span
        [ cls [ "lattice-numeric-value" ]
        , HP.attr (HH.AttrName "style") valueStyle
        ]
        [ HH.text (formatValue state.value state.precision <> state.suffix) ]
    ]

renderEditMode :: forall m. State -> H.ComponentHTML Action () m
renderEditMode state =
  HH.input
    [ cls [ "lattice-numeric-edit" ]
    , HP.attr (HH.AttrName "style") editStyle
    , HP.type_ HP.InputText
    , HP.value state.editValue
    , HP.autofocus true
    , HE.onValueInput UpdateEditValue
    , HE.onBlur \_ -> CommitEdit
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                          // inline // styles
-- ════════════════════════════════════════════════════════════════════════════

containerStyle :: String
containerStyle =
  "display: flex; align-items: center; gap: var(--lattice-space-2); " <>
  "min-width: 120px;"

labelStyle :: String
labelStyle =
  "color: var(--lattice-text-secondary); font-size: var(--lattice-text-xs); " <>
  "min-width: 24px; text-transform: uppercase;"

displayStyle :: String
displayStyle =
  "flex: 1; display: flex; align-items: center; " <>
  "background: var(--lattice-surface-2); border-radius: var(--lattice-radius-sm); " <>
  "padding: var(--lattice-space-1) var(--lattice-space-2); " <>
  "cursor: ew-resize; user-select: none;"

valueStyle :: String
valueStyle =
  "font-family: var(--lattice-font-mono); font-size: var(--lattice-text-sm); " <>
  "color: var(--lattice-text-primary);"

editStyle :: String
editStyle =
  "flex: 1; background: var(--lattice-surface-3); " <>
  "border: 1px solid var(--lattice-accent); border-radius: var(--lattice-radius-sm); " <>
  "padding: var(--lattice-space-1) var(--lattice-space-2); " <>
  "font-family: var(--lattice-font-mono); font-size: var(--lattice-text-sm); " <>
  "color: var(--lattice-text-primary); outline: none;"

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // helpers
-- ════════════════════════════════════════════════════════════════════════════

formatValue :: Number -> Int -> String
formatValue value precision =
  let
    multiplier = toNumber (pow 10 precision)
    rounded = toNumber (round (value * multiplier)) / multiplier
  in
  show rounded
  where
    pow :: Int -> Int -> Int
    pow base exp = 
      if exp <= 0 then 1
      else base * pow base (exp - 1)

clampValue :: State -> Number -> Number
clampValue state value =
  let
    minClamped = case state.min of
      Just m -> max m value
      Nothing -> value
  in
  case state.max of
    Just m -> min m minClamped
    Nothing -> minClamped

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // actions
-- ════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> pure unit
  
  Receive input -> do
    H.modify_ _ 
      { value = input.value
      , label = input.label
      , min = input.min
      , max = input.max
      , step = input.step
      , precision = input.precision
      , suffix = input.suffix
      }
  
  StartDrag x -> do
    state <- H.get
    H.modify_ _ 
      { isDragging = true
      , dragStartX = x
      , dragStartValue = state.value
      }
  
  Drag x -> do
    state <- H.get
    when state.isDragging do
      let
        delta = (x - state.dragStartX) * state.step * 0.1
        newValue = clampValue state (state.dragStartValue + delta)
      H.modify_ _ { value = newValue }
      H.raise (ValueChanged newValue)
  
  EndDrag -> do
    H.modify_ _ { isDragging = false }
  
  StartEdit -> do
    state <- H.get
    H.modify_ _ 
      { isEditing = true
      , editValue = formatValue state.value state.precision
      }
  
  UpdateEditValue str -> do
    H.modify_ _ { editValue = str }
  
  CommitEdit -> do
    state <- H.get
    let
      parsed = fromString state.editValue
      newValue = clampValue state (fromMaybe state.value parsed)
    H.modify_ _ { isEditing = false, value = newValue }
    H.raise (ValueChanged newValue)
  
  CancelEdit -> do
    H.modify_ _ { isEditing = false }
  
  Increment -> do
    state <- H.get
    let newValue = clampValue state (state.value + state.step)
    H.modify_ _ { value = newValue }
    H.raise (ValueChanged newValue)
  
  Decrement -> do
    state <- H.get
    let newValue = clampValue state (state.value - state.step)
    H.modify_ _ { value = newValue }
    H.raise (ValueChanged newValue)
