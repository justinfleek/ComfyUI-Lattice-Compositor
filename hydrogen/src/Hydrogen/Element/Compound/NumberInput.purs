-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // element // number-input
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Pure Hydrogen NumberInput Component
-- |
-- | A specialized input for numeric values with increment/decrement controls.
-- | Pure Element — no Halogen dependency.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.NumberInput as NumberInput
-- | import Hydrogen.Render.Element as E
-- |
-- | -- Basic number input
-- | NumberInput.numberInput
-- |   [ NumberInput.value 10.0
-- |   , NumberInput.onChange HandleChange
-- |   ]
-- |
-- | -- With min/max bounds and step
-- | NumberInput.numberInput
-- |   [ NumberInput.value state.rating
-- |   , NumberInput.minValue 1.0
-- |   , NumberInput.maxValue 5.0
-- |   , NumberInput.step 0.5
-- |   , NumberInput.onChange HandleRating
-- |   ]
-- |
-- | -- With buttons
-- | NumberInput.numberInputWithButtons
-- |   [ NumberInput.value state.quantity
-- |   , NumberInput.buttonPosition NumberInput.Sides
-- |   , NumberInput.onIncrement Increment
-- |   , NumberInput.onDecrement Decrement
-- |   ]
-- |
-- | -- With prefix/suffix
-- | NumberInput.numberInput
-- |   [ NumberInput.value state.price
-- |   , NumberInput.inputPrefix "$"
-- |   , NumberInput.inputSuffix ".00"
-- |   ]
-- | ```
module Hydrogen.Element.Compound.NumberInput
  ( -- * NumberInput Component
    numberInput
  , numberInputWithButtons
    -- * Props
  , NumberInputProps
  , NumberInputProp
  , defaultProps
    -- * Prop Builders
  , value
  , minValue
  , maxValue
  , step
  , inputPrefix
  , inputSuffix
  , inputDisabled
  , inputReadOnly
  , buttonPosition
  , className
  , inputId
  , inputName
  , placeholder
  , inputAriaLabel
  , onChange
  , onIncrement
  , onDecrement
    -- * Types
  , ButtonPosition(Sides, Stacked, NoButtons)
  ) where

import Prelude
  ( class Eq
  , show
  , (<>)
  , (<=)
  , (>=)
  , (||)
  )

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just))
import Hydrogen.Render.Element as E

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Position of increment/decrement buttons
data ButtonPosition
  = Sides      -- Buttons on left and right
  | Stacked    -- Both buttons stacked on right
  | NoButtons  -- No buttons

derive instance eqButtonPosition :: Eq ButtonPosition

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | NumberInput properties
type NumberInputProps msg =
  { value :: Number
  , min :: Maybe Number
  , max :: Maybe Number
  , step :: Number
  , prefix :: Maybe String
  , suffix :: Maybe String
  , disabled :: Boolean
  , readOnly :: Boolean
  , buttonPosition :: ButtonPosition
  , className :: String
  , id :: Maybe String
  , name :: Maybe String
  , placeholder :: String
  , ariaLabel :: Maybe String
  , onChange :: Maybe (String -> msg)
  , onIncrement :: Maybe msg
  , onDecrement :: Maybe msg
  }

-- | Property modifier
type NumberInputProp msg = NumberInputProps msg -> NumberInputProps msg

-- | Default properties
defaultProps :: forall msg. NumberInputProps msg
defaultProps =
  { value: 0.0
  , min: Nothing
  , max: Nothing
  , step: 1.0
  , prefix: Nothing
  , suffix: Nothing
  , disabled: false
  , readOnly: false
  , buttonPosition: NoButtons
  , className: ""
  , id: Nothing
  , name: Nothing
  , placeholder: "0"
  , ariaLabel: Nothing
  , onChange: Nothing
  , onIncrement: Nothing
  , onDecrement: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set current value
value :: forall msg. Number -> NumberInputProp msg
value v props = props { value = v }

-- | Set minimum value
minValue :: forall msg. Number -> NumberInputProp msg
minValue m props = props { min = Just m }

-- | Set maximum value
maxValue :: forall msg. Number -> NumberInputProp msg
maxValue m props = props { max = Just m }

-- | Set step increment
step :: forall msg. Number -> NumberInputProp msg
step s props = props { step = s }

-- | Set prefix (e.g., "$")
inputPrefix :: forall msg. String -> NumberInputProp msg
inputPrefix p props = props { prefix = Just p }

-- | Set suffix (e.g., "%")
inputSuffix :: forall msg. String -> NumberInputProp msg
inputSuffix s props = props { suffix = Just s }

-- | Set disabled state
inputDisabled :: forall msg. Boolean -> NumberInputProp msg
inputDisabled d props = props { disabled = d }

-- | Set read-only state
inputReadOnly :: forall msg. Boolean -> NumberInputProp msg
inputReadOnly r props = props { readOnly = r }

-- | Set button position
buttonPosition :: forall msg. ButtonPosition -> NumberInputProp msg
buttonPosition p props = props { buttonPosition = p }

-- | Add custom class
className :: forall msg. String -> NumberInputProp msg
className c props = props { className = props.className <> " " <> c }

-- | Set id
inputId :: forall msg. String -> NumberInputProp msg
inputId i props = props { id = Just i }

-- | Set name
inputName :: forall msg. String -> NumberInputProp msg
inputName n props = props { name = Just n }

-- | Set placeholder
placeholder :: forall msg. String -> NumberInputProp msg
placeholder p props = props { placeholder = p }

-- | Set aria label
inputAriaLabel :: forall msg. String -> NumberInputProp msg
inputAriaLabel l props = props { ariaLabel = Just l }

-- | Set change handler (receives the input string)
onChange :: forall msg. (String -> msg) -> NumberInputProp msg
onChange handler props = props { onChange = Just handler }

-- | Set increment handler
onIncrement :: forall msg. msg -> NumberInputProp msg
onIncrement handler props = props { onIncrement = Just handler }

-- | Set decrement handler
onDecrement :: forall msg. msg -> NumberInputProp msg
onDecrement handler props = props { onDecrement = Just handler }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // styling
-- ═════════════════════════════════════════════════════════════════════════════

-- | Container classes
containerClasses :: String
containerClasses =
  "relative flex items-center"

-- | Input base classes
inputClasses :: String
inputClasses =
  "flex h-10 w-full rounded-md border border-input bg-background px-3 py-2 text-sm ring-offset-background placeholder:text-muted-foreground focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring focus-visible:ring-offset-2 disabled:cursor-not-allowed disabled:opacity-50"

-- | Input classes when buttons on right
inputWithButtonsClasses :: String
inputWithButtonsClasses =
  "rounded-r-none border-r-0"

-- | Input classes when buttons on sides
inputWithSideButtonsClasses :: String
inputWithSideButtonsClasses =
  "rounded-none border-x-0 text-center"

-- | Button base classes
buttonClasses :: String
buttonClasses =
  "flex items-center justify-center h-10 w-8 border border-input bg-background text-foreground hover:bg-accent hover:text-accent-foreground focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring disabled:cursor-not-allowed disabled:opacity-50 transition-colors"

-- | Stacked button classes (right position)
stackedButtonClasses :: String
stackedButtonClasses =
  "flex items-center justify-center h-5 w-8 border border-input bg-background text-foreground hover:bg-accent hover:text-accent-foreground focus-visible:outline-none focus-visible:ring-1 focus-visible:ring-ring disabled:cursor-not-allowed disabled:opacity-50 transition-colors"

-- | Prefix/suffix addon classes
addonClasses :: String
addonClasses =
  "flex items-center justify-center h-10 px-3 border border-input bg-muted text-muted-foreground text-sm"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // components
-- ═════════════════════════════════════════════════════════════════════════════

-- | Basic number input (no buttons)
-- |
-- | A numeric input field with optional prefix/suffix.
-- | Pure Element — can be rendered to DOM, Halogen, Static HTML, or any target.
numberInput :: forall msg. Array (NumberInputProp msg) -> E.Element msg
numberInput propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    changeHandler = case props.onChange of
      Just handler -> [ E.onInput handler ]
      Nothing -> []
    
    idAttr = case props.id of
      Just i -> [ E.id_ i ]
      Nothing -> []
    
    nameAttr = case props.name of
      Just n -> [ E.name n ]
      Nothing -> []
    
    ariaLabelAttr = case props.ariaLabel of
      Just l -> [ E.ariaLabel l ]
      Nothing -> []
    
    minAttr = case props.min of
      Just m -> [ E.attr "min" (show m) ]
      Nothing -> []
    
    maxAttr = case props.max of
      Just m -> [ E.attr "max" (show m) ]
      Nothing -> []
    
    prefixEl = case props.prefix of
      Just p -> 
        [ E.span_ 
            [ E.classes [ addonClasses, "rounded-l-md border-r-0" ] ] 
            [ E.text p ] 
        ]
      Nothing -> []
    
    suffixEl = case props.suffix of
      Just s -> 
        [ E.span_ 
            [ E.classes [ addonClasses, "rounded-r-md border-l-0" ] ] 
            [ E.text s ] 
        ]
      Nothing -> []
    
    inputEl =
      E.input_
        ( [ E.class_ inputClasses
          , E.attr "type" "number"
          , E.value (show props.value)
          , E.placeholder props.placeholder
          , E.disabled props.disabled
          , E.attr "step" (show props.step)
          ] 
          <> (if props.readOnly then [ E.attr "readonly" "readonly" ] else [])
          <> idAttr 
          <> nameAttr 
          <> ariaLabelAttr
          <> minAttr
          <> maxAttr
          <> changeHandler
        )
  in
    E.div_
      [ E.classes [ containerClasses, props.className ] ]
      ( prefixEl <> [ inputEl ] <> suffixEl )

-- | Number input with increment/decrement buttons
-- |
-- | A numeric input field with +/- buttons.
-- | Pure Element — can be rendered to DOM, Halogen, Static HTML, or any target.
numberInputWithButtons :: forall msg. Array (NumberInputProp msg) -> E.Element msg
numberInputWithButtons propMods =
  let
    props = foldl (\p f -> f p) (defaultProps { buttonPosition = Stacked }) propMods
    
    atMin = case props.min of
      Just m -> props.value <= m
      Nothing -> false
    
    atMax = case props.max of
      Just m -> props.value >= m
      Nothing -> false
    
    changeHandler = case props.onChange of
      Just handler -> [ E.onInput handler ]
      Nothing -> []
    
    decrementHandler = case props.onDecrement of
      Just handler -> [ E.onClick handler ]
      Nothing -> []
    
    incrementHandler = case props.onIncrement of
      Just handler -> [ E.onClick handler ]
      Nothing -> []
    
    idAttr = case props.id of
      Just i -> [ E.id_ i ]
      Nothing -> []
    
    nameAttr = case props.name of
      Just n -> [ E.name n ]
      Nothing -> []
    
    minAttr = case props.min of
      Just m -> [ E.attr "min" (show m) ]
      Nothing -> []
    
    maxAttr = case props.max of
      Just m -> [ E.attr "max" (show m) ]
      Nothing -> []
    
    decrementButton =
      E.button_
        ( [ E.classes [ buttonClasses, "rounded-l-md" ]
          , E.attr "type" "button"
          , E.disabled (props.disabled || atMin)
          , E.ariaLabel "Decrease value"
          ] <> decrementHandler
        )
        [ minusIcon ]
    
    incrementButton =
      E.button_
        ( [ E.classes [ buttonClasses, "rounded-r-md" ]
          , E.attr "type" "button"
          , E.disabled (props.disabled || atMax)
          , E.ariaLabel "Increase value"
          ] <> incrementHandler
        )
        [ plusIcon ]
    
    stackedButtons =
      E.div_
        [ E.class_ "flex flex-col" ]
        [ E.button_
            ( [ E.classes [ stackedButtonClasses, "rounded-tr-md border-b-0" ]
              , E.attr "type" "button"
              , E.disabled (props.disabled || atMax)
              , E.ariaLabel "Increase value"
              ] <> incrementHandler
            )
            [ chevronUpIcon ]
        , E.button_
            ( [ E.classes [ stackedButtonClasses, "rounded-br-md" ]
              , E.attr "type" "button"
              , E.disabled (props.disabled || atMin)
              , E.ariaLabel "Decrease value"
              ] <> decrementHandler
            )
            [ chevronDownIcon ]
        ]
    
    inputCls = case props.buttonPosition of
      Sides -> inputWithSideButtonsClasses
      Stacked -> inputWithButtonsClasses
      NoButtons -> ""
    
    inputEl =
      E.input_
        ( [ E.classes [ inputClasses, inputCls ]
          , E.attr "type" "number"
          , E.value (show props.value)
          , E.placeholder props.placeholder
          , E.disabled props.disabled
          , E.attr "step" (show props.step)
          ] 
          <> (if props.readOnly then [ E.attr "readonly" "readonly" ] else [])
          <> idAttr 
          <> nameAttr
          <> minAttr
          <> maxAttr
          <> changeHandler
        )
  in
    E.div_
      [ E.classes [ containerClasses, props.className ]
      , E.role "group"
      ]
      ( case props.buttonPosition of
          Sides ->
            [ decrementButton, inputEl, incrementButton ]
          Stacked ->
            [ inputEl, stackedButtons ]
          NoButtons ->
            [ inputEl ]
      )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // icons
-- ═════════════════════════════════════════════════════════════════════════════

-- | Plus icon
plusIcon :: forall msg. E.Element msg
plusIcon =
  E.svg_
    [ E.class_ "h-4 w-4"
    , E.attr "xmlns" "http://www.w3.org/2000/svg"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "fill" "none"
    , E.attr "stroke" "currentColor"
    , E.attr "stroke-width" "2"
    , E.attr "stroke-linecap" "round"
    , E.attr "stroke-linejoin" "round"
    ]
    [ E.line_ [ E.attr "x1" "12", E.attr "y1" "5", E.attr "x2" "12", E.attr "y2" "19" ]
    , E.line_ [ E.attr "x1" "5", E.attr "y1" "12", E.attr "x2" "19", E.attr "y2" "12" ]
    ]

-- | Minus icon
minusIcon :: forall msg. E.Element msg
minusIcon =
  E.svg_
    [ E.class_ "h-4 w-4"
    , E.attr "xmlns" "http://www.w3.org/2000/svg"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "fill" "none"
    , E.attr "stroke" "currentColor"
    , E.attr "stroke-width" "2"
    , E.attr "stroke-linecap" "round"
    , E.attr "stroke-linejoin" "round"
    ]
    [ E.line_ [ E.attr "x1" "5", E.attr "y1" "12", E.attr "x2" "19", E.attr "y2" "12" ] ]

-- | Chevron up icon (for stacked buttons)
chevronUpIcon :: forall msg. E.Element msg
chevronUpIcon =
  E.svg_
    [ E.class_ "h-3 w-3"
    , E.attr "xmlns" "http://www.w3.org/2000/svg"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "fill" "none"
    , E.attr "stroke" "currentColor"
    , E.attr "stroke-width" "2"
    , E.attr "stroke-linecap" "round"
    , E.attr "stroke-linejoin" "round"
    ]
    [ E.polyline_ [ E.attr "points" "18 15 12 9 6 15" ] ]

-- | Chevron down icon (for stacked buttons)
chevronDownIcon :: forall msg. E.Element msg
chevronDownIcon =
  E.svg_
    [ E.class_ "h-3 w-3"
    , E.attr "xmlns" "http://www.w3.org/2000/svg"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "fill" "none"
    , E.attr "stroke" "currentColor"
    , E.attr "stroke-width" "2"
    , E.attr "stroke-linecap" "round"
    , E.attr "stroke-linejoin" "round"
    ]
    [ E.polyline_ [ E.attr "points" "6 9 12 15 18 9" ] ]
