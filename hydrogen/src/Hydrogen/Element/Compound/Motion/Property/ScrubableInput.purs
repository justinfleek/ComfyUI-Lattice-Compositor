-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // motion // property // scrubable-input
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ScrubableInput — Schema-native Motion Graphics Numeric Control
-- |
-- | This is the defining control of professional motion graphics software.
-- | Drag on the label to scrub values. Click to type directly.
-- | Modifier keys adjust precision (Shift=10x, Ctrl/Cmd=0.1x).
-- |
-- | ## Design Philosophy
-- |
-- | Unlike raw `Number` inputs, ScrubableInput works with ANY bounded Schema
-- | atom via the `ScrubableValue` typeclass. A HueInput (0-359°, wrapping)
-- | uses the same rendering code as an OpacityInput (0-100%, clamping) —
-- | the TYPE determines the behavior.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.Motion.Property.ScrubableInput as Scrub
-- | import Hydrogen.Schema.Color.Hue (Hue)
-- | import Hydrogen.Schema.Color.Opacity (Opacity)
-- |
-- | -- Same function, different types, different bounds
-- | hueInput :: Hue -> Element Msg
-- | hueInput h = Scrub.scrubableInput h
-- |   [ Scrub.label "Hue"
-- |   , Scrub.onChange SetHue
-- |   ]
-- |
-- | opacityInput :: Opacity -> Element Msg
-- | opacityInput o = Scrub.scrubableInput o
-- |   [ Scrub.label "Opacity"
-- |   , Scrub.onChange SetOpacity
-- |   ]
-- | ```

module Hydrogen.Element.Compound.Motion.Property.ScrubableInput
  ( -- * Component
    scrubableInput
    
  -- * ScrubableValue Typeclass
  , class ScrubableValue
  , scrubMin
  , scrubMax
  , scrubStep
  , scrubPrecision
  , scrubUnit
  , scrubFormat
  , scrubFromNumber
  , scrubToNumber
  
  -- * Props
  , ScrubableInputProps
  , ScrubableInputProp
  , defaultProps
  
  -- * Prop Builders
  , value
  , label
  , sensitivity
  , defaultValue
  , scrubDisabled
  , showReset
  , onChange
  , onScrubStart
  , onScrubEnd
  
  -- * Types
  , ScrubState(Idle, Scrubbing)
  
  -- * Helpers (for runtime implementations)
  , clamp
  , roundTo
  , power
  , formatValue
  , calculateScrubValue
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , show
  , negate
  , (<>)
  , (+)
  , (-)
  , (*)
  , (/)
  , (==)
  , (/=)
  , (<)
  , (>)
  , (&&)
  )

import Data.Array (foldl)
import Data.Int (toNumber, round) as Int
import Data.Maybe (Maybe(Nothing, Just))
import Data.Number (floor) as Number

import Hydrogen.Render.Element as E

-- Schema atoms for ScrubableValue instances
import Hydrogen.Schema.Color.Hue as Hue
import Hydrogen.Schema.Color.Opacity as Opacity
import Hydrogen.Schema.Geometry.Angle as Angle
import Hydrogen.Schema.Dimension.Device as Device

-- ═══���═════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Scrub state for tracking drag interaction
-- | Pure data — runtime interprets this via event handlers
data ScrubState a
  = Idle
  | Scrubbing
    { startX :: Number
    , startValue :: a
    }

derive instance eqScrubStateA :: Eq a => Eq (ScrubState a)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // scrubable typeclass
-- ═════════════════════════════════════════════════════════════════════════════

-- | Typeclass for values that can be scrubbed in motion graphics UI.
-- |
-- | Provides display formatting, unit information, and bounds for rendering
-- | a professional scrubable control. Unlike BoundedValue, this supports
-- | types with practical (rather than absolute) bounds like Pixel.
-- |
-- | ## Laws
-- |
-- | - `scrubFromNumber (scrubToNumber a) = a` (within precision)
-- | - `scrubMin` and `scrubMax` represent practical UI bounds
class ScrubableValue a where
  -- | Minimum value for display (from type bounds)
  scrubMin :: a -> Number
  
  -- | Maximum value for display (from type bounds)
  scrubMax :: a -> Number
  
  -- | Step increment for this type
  scrubStep :: a -> Number
  
  -- | Display precision (decimal places)
  scrubPrecision :: a -> Int
  
  -- | Unit suffix for display (e.g., "°", "%", "px")
  scrubUnit :: a -> String
  
  -- | Format value for display
  scrubFormat :: a -> String
  
  -- | Convert from raw Number (with clamping/wrapping)
  scrubFromNumber :: Number -> a
  
  -- | Convert to raw Number for calculations
  scrubToNumber :: a -> Number

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | ScrubableInput properties
-- |
-- | Core motion graphics numeric input with scrub-to-adjust behavior.
-- | Modifier keys affect scrub sensitivity:
-- | - Shift: 10x multiplier (coarse adjustment)
-- | - Ctrl/Cmd: 0.1x multiplier (fine adjustment)
-- | - Shift+Ctrl: 1x (normal, overrides both)
type ScrubableInputProps a msg =
  { value :: a
  , label :: Maybe String
  , sensitivity :: Number
  , defaultVal :: Maybe a
  , disabled :: Boolean
  , showReset :: Boolean
  , onChange :: Maybe (a -> msg)
  , onScrubStart :: Maybe msg
  , onScrubEnd :: Maybe msg
  }

-- | Property modifier function
type ScrubableInputProp a msg = ScrubableInputProps a msg -> ScrubableInputProps a msg

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set current value
value :: forall a msg. a -> ScrubableInputProp a msg
value v props = props { value = v }

-- | Set label (displayed left of input, draggable for scrub)
label :: forall a msg. String -> ScrubableInputProp a msg
label l props = props { label = Just l }

-- | Set scrub sensitivity (1.0 = 1 pixel per step unit)
sensitivity :: forall a msg. Number -> ScrubableInputProp a msg
sensitivity s props = props { sensitivity = s }

-- | Set default value (for reset button)
defaultValue :: forall a msg. a -> ScrubableInputProp a msg
defaultValue d props = props { defaultVal = Just d, showReset = true }

-- | Set disabled state
scrubDisabled :: forall a msg. Boolean -> ScrubableInputProp a msg
scrubDisabled d props = props { disabled = d }

-- | Show reset button (auto-enabled when defaultValue is set)
showReset :: forall a msg. Boolean -> ScrubableInputProp a msg
showReset s props = props { showReset = s }

-- | Set change handler (called with new value)
onChange :: forall a msg. (a -> msg) -> ScrubableInputProp a msg
onChange handler props = props { onChange = Just handler }

-- | Called when scrub begins
onScrubStart :: forall a msg. msg -> ScrubableInputProp a msg
onScrubStart handler props = props { onScrubStart = Just handler }

-- | Called when scrub ends
onScrubEnd :: forall a msg. msg -> ScrubableInputProp a msg
onScrubEnd handler props = props { onScrubEnd = Just handler }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp value to bounds
-- |
-- | Used for constraining scrubbed values to valid ranges.
-- | Handles optional min/max bounds independently.
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

-- | Round to specified precision (decimal places)
-- |
-- | Essential for display formatting and step-based value adjustment.
-- | ```purescript
-- | roundTo 2 3.14159  -- 3.14
-- | roundTo 0 3.7      -- 4.0
-- | ```
roundTo :: Int -> Number -> Number
roundTo prec val =
  let
    factor = power 10.0 prec
    rounded = Int.toNumber (Int.round (val * factor))
  in
    rounded / factor

-- | Power function for precision rounding
-- |
-- | Computes base^exp for both positive and negative exponents.
-- | Used by roundTo to calculate decimal place factors.
power :: Number -> Int -> Number
power base exp =
  if exp == 0 then 1.0
  else if exp > 0 then base * power base (exp - 1)
  else 1.0 / power base (negate exp)

-- | Format display value with precision
-- |
-- | Intelligently formats numbers for display:
-- | - Removes unnecessary decimal points for whole numbers at precision 0
-- | - Rounds to specified precision for decimal values
formatValue :: Int -> Number -> String
formatValue prec val =
  let
    rounded = roundTo prec val
    floored = Number.floor rounded
  in
    if prec == 0 && rounded == floored
      then show (Int.round rounded)
      else show rounded

-- | Calculate new value from scrub delta
-- |
-- | Converts pixel movement to value change based on:
-- | - Sensitivity (pixels per unit)
-- | - Step size (minimum value increment)
-- | - Bounds (min/max constraints)
calculateScrubValue 
  :: Number  -- ^ Start value
  -> Number  -- ^ Delta X (pixels moved)
  -> Number  -- ^ Sensitivity (pixels per step)
  -> Number  -- ^ Step size
  -> Maybe Number  -- ^ Min bound
  -> Maybe Number  -- ^ Max bound
  -> Number
calculateScrubValue startVal deltaX sens step minBound maxBound =
  let
    -- Calculate raw delta in value units
    rawDelta = (deltaX / sens) * step
    newVal = startVal + rawDelta
    -- Clamp to bounds
  in
    clamp minBound maxBound newVal

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // component
-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default properties for a scrubable value
-- |
-- | Creates default props using the type's inherent bounds.
defaultProps :: forall a msg. ScrubableValue a => a -> ScrubableInputProps a msg
defaultProps initialValue =
  { value: initialValue
  , label: Nothing
  , sensitivity: 1.0
  , defaultVal: Nothing
  , disabled: false
  , showReset: false
  , onChange: Nothing
  , onScrubStart: Nothing
  , onScrubEnd: Nothing
  }

-- | ScrubableInput component
-- |
-- | A motion graphics numeric input with drag-to-scrub behavior.
-- | Pure Element — renders to DOM, Halogen, Static HTML, or any target.
-- |
-- | The component consists of:
-- | - Optional label (draggable to scrub)
-- | - Scrub handle (visible when no label, draggable to scrub)  
-- | - Numeric input field (click to type, drag to scrub)
-- | - Unit suffix (derived from type)
-- | - Optional reset button
scrubableInput 
  :: forall a msg
   . ScrubableValue a 
  => a 
  -> Array (ScrubableInputProp a msg) 
  -> E.Element msg
scrubableInput initialValue propMods =
  let
    props = foldl (\p f -> f p) (defaultProps initialValue) propMods
    
    -- Get type-specific display info
    displayVal = scrubFormat props.value
    unitSuffix = scrubUnit props.value
    minVal = scrubMin props.value
    maxVal = scrubMax props.value
    stepVal = scrubStep props.value
    
    -- Check if value differs from default (for reset button visibility)
    showResetBtn = props.showReset && case props.defaultVal of
      Just d -> scrubToNumber props.value /= scrubToNumber d
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
    
    -- Input element with type-derived bounds
    inputEl =
      E.input_
        [ E.class_ "scrub-input"
        , E.attr "type" "number"
        , E.value displayVal
        , E.attr "min" (show minVal)
        , E.attr "max" (show maxVal)
        , E.attr "step" (show stepVal)
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
        ]
    
    -- Unit suffix (from type)
    unitEl = if unitSuffix /= ""
      then
        [ E.span_
            [ E.class_ "scrub-unit"
            , E.style "font-size" "12px"
            , E.style "color" "#666"
            , E.style "min-width" "16px"
            ]
            [ E.text unitSuffix ]
        ]
      else []
    
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
      (containerStyles <> disabledStyles <> [ E.class_ "scrubable-input" ])
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

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // scrubable value instances
-- ═════════════════════════════════════════════════════════════════════════════

-- | ScrubableValue instance for Hue (0-359°, wrapping)
-- |
-- | Color wheel position. 0° = Red, 120° = Green, 240° = Blue.
-- | Values wrap at 360° (360 becomes 0).
instance scrubableValueHue :: ScrubableValue Hue.Hue where
  scrubMin _ = 0.0
  scrubMax _ = 359.0
  scrubStep _ = 1.0
  scrubPrecision _ = 0
  scrubUnit _ = "°"
  scrubFormat h = show (Hue.unwrap h)
  scrubFromNumber n = Hue.hueWrap (Int.round n)
  scrubToNumber h = Int.toNumber (Hue.unwrap h)

-- | ScrubableValue instance for Opacity (0-100%, clamping)
-- |
-- | Alpha transparency as percentage. 0% = transparent, 100% = opaque.
instance scrubableValueOpacity :: ScrubableValue Opacity.Opacity where
  scrubMin _ = 0.0
  scrubMax _ = 100.0
  scrubStep _ = 1.0
  scrubPrecision _ = 0
  scrubUnit _ = "%"
  scrubFormat o = show (Opacity.unwrap o)
  scrubFromNumber n = Opacity.opacity (Int.round n)
  scrubToNumber o = Int.toNumber (Opacity.unwrap o)

-- | ScrubableValue instance for Degrees (0-360°, wrapping)
-- |
-- | Angular measurement. 0° = right, 90° = up, 180° = left, 270° = down.
-- | Values wrap at 360° (360 becomes 0).
instance scrubableValueDegrees :: ScrubableValue Angle.Degrees where
  scrubMin _ = 0.0
  scrubMax _ = 360.0
  scrubStep _ = 1.0
  scrubPrecision _ = 1
  scrubUnit _ = "°"
  scrubFormat d = show (Angle.unwrapDegrees d)
  scrubFromNumber n = Angle.degrees n
  scrubToNumber d = Angle.unwrapDegrees d

-- | ScrubableValue instance for Pixel (unbounded, but practical range)
-- |
-- | Device-independent pixels. Range is ±10000 for practical UI limits.
instance scrubableValuePixel :: ScrubableValue Device.Pixel where
  scrubMin _ = -10000.0
  scrubMax _ = 10000.0
  scrubStep _ = 1.0
  scrubPrecision _ = 1
  scrubUnit _ = "px"
  scrubFormat p = show (Device.unwrapPixel p)
  scrubFromNumber n = Device.px n
  scrubToNumber p = Device.unwrapPixel p

