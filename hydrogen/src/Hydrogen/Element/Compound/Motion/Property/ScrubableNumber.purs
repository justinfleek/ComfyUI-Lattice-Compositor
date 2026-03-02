-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // motion // property // scrubable
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ScrubableNumber — Motion Graphics Numeric Input Control
-- |
-- | The defining control of professional motion graphics software.
-- | Drag on the label to scrub values. Click to type directly.
-- | Modifier keys adjust precision (Shift=10x, Ctrl/Cmd=0.1x).
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.Motion.Property.ScrubableNumber as Scrub
-- |
-- | -- Basic scrubable number
-- | Scrub.scrubableNumber
-- |   [ Scrub.value 100.0
-- |   , Scrub.label "Position X"
-- |   , Scrub.onChange HandlePositionX
-- |   ]
-- |
-- | -- With bounds and unit
-- | Scrub.scrubableNumber
-- |   [ Scrub.value state.opacity
-- |   , Scrub.label "Opacity"
-- |   , Scrub.minValue 0.0
-- |   , Scrub.maxValue 100.0
-- |   , Scrub.unit "%"
-- |   , Scrub.onChange HandleOpacity
-- |   ]
-- | ```

module Hydrogen.Element.Compound.Motion.Property.ScrubableNumber
  ( -- * Component
    scrubableNumber
    
  -- * Props
  , ScrubableNumberProps
  , ScrubableNumberProp
  , defaultProps
  
  -- * Prop Builders
  , value
  , label
  , minValue
  , maxValue
  , step
  , precision
  , unit
  , sensitivity
  , defaultValue
  , scrubDisabled
  , showReset
  , onChange
  , onScrubStart
  , onScrubEnd
  
  -- * Types (for runtime implementations)
  , ScrubState(Idle, Scrubbing)
  
  -- * Helpers (for runtime implementations)
  , clamp
  , roundTo
  , formatValue
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , show
  , (<>)
  , (-)
  , (*)
  , (/)
  , (==)
  , (/=)
  , (&&)
  , (<)
  , (>)
  , negate
  )

import Data.Array (foldl)
import Data.Int (toNumber, round) as Int
import Data.Maybe (Maybe(Nothing, Just))
import Data.Number (floor) as Number

import Hydrogen.Render.Element as E

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Scrub state for tracking drag interaction
-- | Pure data — runtime interprets this via event handlers
data ScrubState
  = Idle
  | Scrubbing
    { startX :: Number
    , startValue :: Number
    }

derive instance eqScrubState :: Eq ScrubState

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | ScrubableNumber properties
-- |
-- | Core motion graphics numeric input with scrub-to-adjust behavior.
-- | Modifier keys affect scrub sensitivity:
-- | - Shift: 10x multiplier (coarse adjustment)
-- | - Ctrl/Cmd: 0.1x multiplier (fine adjustment)
-- | - Shift+Ctrl: 1x (normal, overrides both)
type ScrubableNumberProps msg =
  { value :: Number
  , label :: Maybe String
  , min :: Maybe Number
  , max :: Maybe Number
  , step :: Number
  , precision :: Int
  , unit :: Maybe String
  , sensitivity :: Number
  , defaultVal :: Maybe Number
  , disabled :: Boolean
  , showReset :: Boolean
  , onChange :: Maybe (Number -> msg)
  , onScrubStart :: Maybe msg
  , onScrubEnd :: Maybe msg
  }

-- | Property modifier function
type ScrubableNumberProp msg = ScrubableNumberProps msg -> ScrubableNumberProps msg

-- | Default properties
-- |
-- | Sensible defaults for motion graphics workflows:
-- | - Step of 1.0 (integer-friendly)
-- | - Precision of 2 decimal places
-- | - Sensitivity of 1.0 (1 pixel = 1 step unit)
defaultProps :: forall msg. ScrubableNumberProps msg
defaultProps =
  { value: 0.0
  , label: Nothing
  , min: Nothing
  , max: Nothing
  , step: 1.0
  , precision: 2
  , unit: Nothing
  , sensitivity: 1.0
  , defaultVal: Nothing
  , disabled: false
  , showReset: false
  , onChange: Nothing
  , onScrubStart: Nothing
  , onScrubEnd: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set current value
value :: forall msg. Number -> ScrubableNumberProp msg
value v props = props { value = v }

-- | Set label (displayed left of input, draggable for scrub)
label :: forall msg. String -> ScrubableNumberProp msg
label l props = props { label = Just l }

-- | Set minimum bound
minValue :: forall msg. Number -> ScrubableNumberProp msg
minValue m props = props { min = Just m }

-- | Set maximum bound
maxValue :: forall msg. Number -> ScrubableNumberProp msg
maxValue m props = props { max = Just m }

-- | Set step increment (used for arrow keys and scrub calculation)
step :: forall msg. Number -> ScrubableNumberProp msg
step s props = props { step = s }

-- | Set display precision (decimal places)
precision :: forall msg. Int -> ScrubableNumberProp msg
precision p props = props { precision = p }

-- | Set unit suffix (e.g., "%", "px", "°")
unit :: forall msg. String -> ScrubableNumberProp msg
unit u props = props { unit = Just u }

-- | Set scrub sensitivity (1.0 = 1 pixel per step unit)
sensitivity :: forall msg. Number -> ScrubableNumberProp msg
sensitivity s props = props { sensitivity = s }

-- | Set default value (for reset button)
defaultValue :: forall msg. Number -> ScrubableNumberProp msg
defaultValue d props = props { defaultVal = Just d, showReset = true }

-- | Set disabled state
scrubDisabled :: forall msg. Boolean -> ScrubableNumberProp msg
scrubDisabled d props = props { disabled = d }

-- | Show reset button (auto-enabled when defaultValue is set)
showReset :: forall msg. Boolean -> ScrubableNumberProp msg
showReset s props = props { showReset = s }

-- | Set change handler (called with new value)
onChange :: forall msg. (Number -> msg) -> ScrubableNumberProp msg
onChange handler props = props { onChange = Just handler }

-- | Called when scrub begins
onScrubStart :: forall msg. msg -> ScrubableNumberProp msg
onScrubStart handler props = props { onScrubStart = Just handler }

-- | Called when scrub ends
onScrubEnd :: forall msg. msg -> ScrubableNumberProp msg
onScrubEnd handler props = props { onScrubEnd = Just handler }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp value to bounds
clamp :: Maybe Number -> Maybe Number -> Number -> Number
clamp maybeMin maybeMax val =
  let
    withMin = case maybeMin of
      Just m -> if val < m then m else val
      Nothing -> val
    withMax = case maybeMax of
      Just m -> if withMin > m then m else withMin
      Nothing -> withMin
  in
    withMax

-- | Round to precision
roundTo :: Int -> Number -> Number
roundTo prec val =
  let
    factor = power 10.0 prec
    rounded = Int.toNumber (Int.round (val * factor))
  in
    rounded / factor

-- | Power function for precision rounding
power :: Number -> Int -> Number
power base exp =
  if exp == 0 then 1.0
  else if exp > 0 then base * power base (exp - 1)
  else 1.0 / power base (negate exp)

-- | Format display value with precision
formatValue :: Int -> Number -> String
formatValue prec val =
  let
    rounded = roundTo prec val
    floored = Number.floor rounded
  in
    if prec == 0 && rounded == floored
      then show (Int.round rounded)
      else show rounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // component
-- ═════════════════════════════════════════════════════════════════════════════

-- | ScrubableNumber component
-- |
-- | A motion graphics numeric input with drag-to-scrub behavior.
-- | Pure Element — renders to DOM, Halogen, Static HTML, or any target.
-- |
-- | The component consists of:
-- | - Optional label (draggable to scrub)
-- | - Scrub handle (visible when no label, draggable to scrub)  
-- | - Numeric input field (click to type, drag to scrub)
-- | - Optional unit suffix
-- | - Optional reset button
scrubableNumber :: forall msg. Array (ScrubableNumberProp msg) -> E.Element msg
scrubableNumber propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    displayVal = formatValue props.precision props.value
    
    -- Check if value differs from default (for reset button visibility)
    showResetBtn = props.showReset && case props.defaultVal of
      Just d -> props.value /= d
      Nothing -> false
    
    -- Container styles
    containerStyles =
      [ E.style "display" "flex"
      , E.style "align-items" "center"
      , E.style "gap" "4px"
      ]
    
    disabledStyles = if props.disabled
      then [ E.style "opacity" "0.5", E.style "pointer-events" "none" ]
      else []
    
    -- Label element (scrub target)
    labelEl = case props.label of
      Just l ->
        [ E.label_
            [ E.class_ "scrub-label"
            , E.style "min-width" "70px"
            , E.style "font-size" "13px"
            , E.style "color" "#888"
            , E.style "cursor" "ew-resize"
            , E.style "user-select" "none"
            , E.style "transition" "color 0.1s"
            ]
            [ E.text l ]
        ]
      Nothing ->
        -- Scrub handle when no label
        [ E.div_
            [ E.class_ "scrub-handle"
            , E.style "display" "flex"
            , E.style "align-items" "center"
            , E.style "justify-content" "center"
            , E.style "width" "12px"
            , E.style "height" "20px"
            , E.style "color" "#555"
            , E.style "cursor" "ew-resize"
            , E.style "user-select" "none"
            , E.style "font-size" "10px"
            , E.style "letter-spacing" "-2px"
            , E.style "transition" "color 0.1s, background 0.1s"
            , E.style "border-radius" "2px"
            , E.style "flex-shrink" "0"
            , E.title "Drag to scrub value"
            ]
            [ E.text "⋮⋮" ]
        ]
    
    -- Min attribute
    minAttr = case props.min of
      Just m -> [ E.attr "min" (show m) ]
      Nothing -> []
    
    -- Max attribute  
    maxAttr = case props.max of
      Just m -> [ E.attr "max" (show m) ]
      Nothing -> []
    
    -- Step attribute
    stepAttr = [ E.attr "step" (show props.step) ]
    
    -- Input element
    inputEl =
      E.input_
        ( [ E.class_ "scrub-input"
          , E.attr "type" "number"
          , E.value displayVal
          , E.style "width" "60px"
          , E.style "padding" "4px 6px"
          , E.style "border" "1px solid #3d3d3d"
          , E.style "border-radius" "3px"
          , E.style "background" "#2a2a2a"
          , E.style "color" "#3498db"
          , E.style "font-size" "13px"
          , E.style "text-align" "right"
          , E.style "cursor" "ew-resize"
          , E.style "transition" "border-color 0.1s"
          , E.disabled props.disabled
          ] <> minAttr <> maxAttr <> stepAttr
        )
    
    -- Unit suffix
    unitEl = case props.unit of
      Just u ->
        [ E.span_
            [ E.class_ "scrub-unit"
            , E.style "font-size" "12px"
            , E.style "color" "#666"
            , E.style "min-width" "16px"
            ]
            [ E.text u ]
        ]
      Nothing -> []
    
    -- Reset button
    resetEl = if showResetBtn
      then
        [ E.button_
            [ E.class_ "reset-btn"
            , E.style "width" "18px"
            , E.style "height" "18px"
            , E.style "padding" "0"
            , E.style "border" "none"
            , E.style "border-radius" "3px"
            , E.style "background" "transparent"
            , E.style "color" "#666"
            , E.style "cursor" "pointer"
            , E.style "display" "flex"
            , E.style "align-items" "center"
            , E.style "justify-content" "center"
            , E.title "Reset to default"
            ]
            [ resetIcon ]
        ]
      else []
  in
    E.div_
      (containerStyles <> disabledStyles <> [ E.class_ "scrubable-number" ])
      (labelEl <> [ inputEl ] <> unitEl <> resetEl)

-- | Reset icon (refresh symbol)
resetIcon :: forall msg. E.Element msg
resetIcon =
  E.svg_
    [ E.class_ "reset-icon"
    , E.attr "xmlns" "http://www.w3.org/2000/svg"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "fill" "none"
    , E.attr "stroke" "currentColor"
    , E.attr "stroke-width" "2"
    , E.attr "stroke-linecap" "round"
    , E.attr "stroke-linejoin" "round"
    , E.style "width" "12px"
    , E.style "height" "12px"
    ]
    [ E.path_ [ E.attr "d" "M3 12a9 9 0 1 0 9-9 9.75 9.75 0 0 0-6.74 2.74L3 8" ]
    , E.path_ [ E.attr "d" "M3 3v5h5" ]
    ]
