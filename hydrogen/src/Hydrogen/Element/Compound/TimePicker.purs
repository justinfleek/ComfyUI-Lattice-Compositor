-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // element // time-picker
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TimePicker — Schema-native time selection component.
-- |
-- | A time picker with hour/minute/second inputs, supporting both 12-hour and
-- | 24-hour formats. Pure PureScript implementation with no JavaScript FFI.
-- |
-- | ## Design Philosophy
-- |
-- | This component accepts **concrete Schema atoms** for ALL visual properties.
-- | No hardcoded CSS strings. No Tailwind classes. No JavaScript FFI.
-- |
-- | ## Schema Atoms Accepted
-- |
-- | | Property           | Pillar    | Type                  | CSS Output      |
-- | |--------------------|-----------|----------------------|-----------------|
-- | | backgroundColor    | Color     | Color.RGB            | background      |
-- | | borderColor        | Color     | Color.RGB            | border-color    |
-- | | textColor          | Color     | Color.RGB            | color           |
-- | | mutedColor         | Color     | Color.RGB            | muted text      |
-- | | primaryColor       | Color     | Color.RGB            | active state    |
-- | | primaryTextColor   | Color     | Color.RGB            | active text     |
-- | | borderRadius       | Geometry  | Geometry.Corners     | border-radius   |
-- | | padding            | Dimension | Device.Pixel         | padding         |
-- | | fontSize           | Typography| FontSize.FontSize    | font-size       |
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.TimePicker as TimePicker
-- | import Hydrogen.Schema.Temporal.TimeOfDay as TimeOfDay
-- |
-- | -- Basic time picker (24h format)
-- | TimePicker.timePicker
-- |   [ TimePicker.value state.time
-- |   , TimePicker.onChange HandleTimeChange
-- |   ]
-- |
-- | -- 12-hour format with AM/PM
-- | TimePicker.timePicker
-- |   [ TimePicker.value state.time
-- |   , TimePicker.hourFormat TimePicker.Hour12
-- |   , TimePicker.onChange HandleTimeChange
-- |   ]
-- | ```

module Hydrogen.Element.Compound.TimePicker
  ( -- * Component
    timePicker
  , timePickerInline
  
  -- * Re-exports from Types
  , module Hydrogen.Element.Compound.TimePicker.Types
  
  -- * Re-exports from Format
  , module Hydrogen.Element.Compound.TimePicker.Format
  
  -- * Props
  , TimePickerProps
  , TimePickerProp
  , defaultProps
  
  -- * Prop Builders: State
  , value
  , hourFormat
  , showSeconds
  , minuteStep
  , secondStep
  , disabled
  , readOnly
  , showIncrementButtons
  
  -- * Prop Builders: Constraints
  , minTime
  , maxTime
  
  -- * Prop Builders: Color Atoms
  , backgroundColor
  , borderColor
  , textColor
  , mutedColor
  , primaryColor
  , primaryTextColor
  
  -- * Prop Builders: Geometry Atoms
  , borderRadius
  
  -- * Prop Builders: Dimension Atoms
  , padding
  , borderWidth
  
  -- * Prop Builders: Typography Atoms
  , fontSize
  
  -- * Prop Builders: Behavior
  , onChange
  , onHourChange
  , onMinuteChange
  , onSecondChange
  , onPeriodChange
  ) where

import Prelude
  ( not
  , (&&)
  , (==)
  , max
  )

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just))

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Typography.FontSize as FontSize
import Hydrogen.Schema.Temporal.TimeOfDay as TimeOfDay

import Hydrogen.Element.Compound.TimePicker.Types
  ( HourFormat(Hour12, Hour24)
  , Period(AM, PM)
  , ValidationError(InvalidFormat, TimeOutOfRange, EmptyValue)
  , is12Hour
  , togglePeriod
  , validationErrorMessage
  )
import Hydrogen.Element.Compound.TimePicker.Format
  ( formatTime
  , format24H
  , format12H
  , parseTime
  , hourTo12
  , periodFromHour
  , padZero
  )
import Hydrogen.Element.Compound.TimePicker.Render as Render

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | TimePicker properties
type TimePickerProps msg =
  { -- State
    value :: Maybe TimeOfDay.TimeOfDay
  , hourFormat :: HourFormat
  , showSeconds :: Boolean
  , minuteStep :: Int
  , secondStep :: Int
  , disabled :: Boolean
  , readOnly :: Boolean
  , showIncrementButtons :: Boolean
  
  -- Constraints
  , minTime :: Maybe TimeOfDay.TimeOfDay
  , maxTime :: Maybe TimeOfDay.TimeOfDay
  
  -- Color atoms
  , backgroundColor :: Maybe Color.RGB
  , borderColor :: Maybe Color.RGB
  , textColor :: Maybe Color.RGB
  , mutedColor :: Maybe Color.RGB
  , primaryColor :: Maybe Color.RGB
  , primaryTextColor :: Maybe Color.RGB
  
  -- Geometry atoms
  , borderRadius :: Maybe Geometry.Corners
  
  -- Dimension atoms
  , padding :: Maybe Device.Pixel
  , borderWidth :: Maybe Device.Pixel
  
  -- Typography atoms
  , fontSize :: Maybe FontSize.FontSize
  
  -- Behavior
  , onChange :: Maybe (TimeOfDay.TimeOfDay -> msg)
  , onHourChange :: Maybe (Int -> msg)
  , onMinuteChange :: Maybe (Int -> msg)
  , onSecondChange :: Maybe (Int -> msg)
  , onPeriodChange :: Maybe (Period -> msg)
  }

-- | Property modifier
type TimePickerProp msg = TimePickerProps msg -> TimePickerProps msg

-- | Default properties
defaultProps :: forall msg. TimePickerProps msg
defaultProps =
  { value: Nothing
  , hourFormat: Hour24
  , showSeconds: false
  , minuteStep: 1
  , secondStep: 1
  , disabled: false
  , readOnly: false
  , showIncrementButtons: true
  , minTime: Nothing
  , maxTime: Nothing
  , backgroundColor: Nothing
  , borderColor: Nothing
  , textColor: Nothing
  , mutedColor: Nothing
  , primaryColor: Nothing
  , primaryTextColor: Nothing
  , borderRadius: Nothing
  , padding: Nothing
  , borderWidth: Nothing
  , fontSize: Nothing
  , onChange: Nothing
  , onHourChange: Nothing
  , onMinuteChange: Nothing
  , onSecondChange: Nothing
  , onPeriodChange: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set time value
value :: forall msg. Maybe TimeOfDay.TimeOfDay -> TimePickerProp msg
value v props = props { value = v }

-- | Set hour format (12h or 24h)
hourFormat :: forall msg. HourFormat -> TimePickerProp msg
hourFormat f props = props { hourFormat = f }

-- | Show seconds field
showSeconds :: forall msg. Boolean -> TimePickerProp msg
showSeconds s props = props { showSeconds = s }

-- | Set minute step interval (minimum 1)
minuteStep :: forall msg. Int -> TimePickerProp msg
minuteStep s props = props { minuteStep = max 1 s }

-- | Set second step interval (minimum 1)
secondStep :: forall msg. Int -> TimePickerProp msg
secondStep s props = props { secondStep = max 1 s }

-- | Set disabled state
disabled :: forall msg. Boolean -> TimePickerProp msg
disabled d props = props { disabled = d }

-- | Set read-only state
readOnly :: forall msg. Boolean -> TimePickerProp msg
readOnly r props = props { readOnly = r }

-- | Show increment/decrement buttons
showIncrementButtons :: forall msg. Boolean -> TimePickerProp msg
showIncrementButtons s props = props { showIncrementButtons = s }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                 // prop builders: constraints
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set minimum time
minTime :: forall msg. TimeOfDay.TimeOfDay -> TimePickerProp msg
minTime t props = props { minTime = Just t }

-- | Set maximum time
maxTime :: forall msg. TimeOfDay.TimeOfDay -> TimePickerProp msg
maxTime t props = props { maxTime = Just t }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: color
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set background color (Color.RGB atom)
backgroundColor :: forall msg. Color.RGB -> TimePickerProp msg
backgroundColor c props = props { backgroundColor = Just c }

-- | Set border color (Color.RGB atom)
borderColor :: forall msg. Color.RGB -> TimePickerProp msg
borderColor c props = props { borderColor = Just c }

-- | Set text color (Color.RGB atom)
textColor :: forall msg. Color.RGB -> TimePickerProp msg
textColor c props = props { textColor = Just c }

-- | Set muted text color (Color.RGB atom)
mutedColor :: forall msg. Color.RGB -> TimePickerProp msg
mutedColor c props = props { mutedColor = Just c }

-- | Set primary/active color (Color.RGB atom)
primaryColor :: forall msg. Color.RGB -> TimePickerProp msg
primaryColor c props = props { primaryColor = Just c }

-- | Set primary text color (Color.RGB atom)
primaryTextColor :: forall msg. Color.RGB -> TimePickerProp msg
primaryTextColor c props = props { primaryTextColor = Just c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: geometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set border radius (Geometry.Corners atom)
borderRadius :: forall msg. Geometry.Corners -> TimePickerProp msg
borderRadius r props = props { borderRadius = Just r }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // prop builders: dimension
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set padding (Device.Pixel atom)
padding :: forall msg. Device.Pixel -> TimePickerProp msg
padding p props = props { padding = Just p }

-- | Set border width (Device.Pixel atom)
borderWidth :: forall msg. Device.Pixel -> TimePickerProp msg
borderWidth w props = props { borderWidth = Just w }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // prop builders: typography
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set font size (FontSize atom)
fontSize :: forall msg. FontSize.FontSize -> TimePickerProp msg
fontSize s props = props { fontSize = Just s }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: behavior
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set change handler (fires when time changes)
onChange :: forall msg. (TimeOfDay.TimeOfDay -> msg) -> TimePickerProp msg
onChange handler props = props { onChange = Just handler }

-- | Set hour change handler
onHourChange :: forall msg. (Int -> msg) -> TimePickerProp msg
onHourChange handler props = props { onHourChange = Just handler }

-- | Set minute change handler
onMinuteChange :: forall msg. (Int -> msg) -> TimePickerProp msg
onMinuteChange handler props = props { onMinuteChange = Just handler }

-- | Set second change handler
onSecondChange :: forall msg. (Int -> msg) -> TimePickerProp msg
onSecondChange handler props = props { onSecondChange = Just handler }

-- | Set period change handler (for 12-hour format)
onPeriodChange :: forall msg. (Period -> msg) -> TimePickerProp msg
onPeriodChange handler props = props { onPeriodChange = Just handler }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // main component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a time picker
-- |
-- | Pure Element — renders to DOM, Static HTML, or any target.
-- | No JavaScript FFI. Pure PureScript time handling.
timePicker :: forall msg. Array (TimePickerProp msg) -> E.Element msg
timePicker propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    config = resolveConfigFromProps props
    time = getTimeOrDefault props.value
    rec = TimeOfDay.toRecord time
    
    -- Determine display hour based on format
    displayHour = case props.hourFormat of
      Hour12 -> hourTo12 rec.hour
      Hour24 -> rec.hour
    
    -- Determine period for 12-hour format
    period = periodFromHour rec.hour
  in
    E.div_
      [ E.style "display" "inline-flex"
      , E.style "align-items" "center"
      , E.style "gap" "4px"
      , E.style "border-style" "solid"
      , E.style "border-width" config.borderWidthVal
      , E.style "border-color" (Color.toLegacyCss config.borderCol)
      , E.style "border-radius" config.radius
      , E.style "padding" "4px 8px"
      , E.style "background-color" (Color.toLegacyCss config.bgColor)
      , E.role "group"
      , E.ariaLabel "Time picker"
      ]
      [ -- Hour segment
        Render.renderTimeSegment config
          { value: displayHour
          , label: "Hour"
          , disabled: props.disabled
          , readOnly: props.readOnly
          , showButtons: props.showIncrementButtons && not props.disabled
          , onIncrement: Nothing
          , onDecrement: Nothing
          , onInputChange: Nothing
          }
      
      , -- Separator
        Render.renderSeparator config
      
      , -- Minute segment
        Render.renderTimeSegment config
          { value: rec.minute
          , label: "Minute"
          , disabled: props.disabled
          , readOnly: props.readOnly
          , showButtons: props.showIncrementButtons && not props.disabled
          , onIncrement: Nothing
          , onDecrement: Nothing
          , onInputChange: Nothing
          }
      
      , -- Seconds segment (optional)
        if props.showSeconds
          then renderSecondsSection config props rec.second
          else E.text ""
      
      , -- AM/PM toggle (for 12-hour format)
        if props.hourFormat == Hour12
          then Render.renderPeriodToggle (toRenderProps props) config period
          else E.text ""
      ]

-- | Render inline time picker (larger, for embedded use)
timePickerInline :: forall msg. Array (TimePickerProp msg) -> E.Element msg
timePickerInline propMods =
  let
    propsWithButtons = propMods
  in
    E.div_
      [ E.style "display" "inline-flex"
      , E.style "flex-direction" "column"
      , E.style "align-items" "center"
      , E.style "gap" "8px"
      , E.style "padding" "16px"
      ]
      [ timePicker propsWithButtons ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // internal helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render the seconds section (separator + segment)
renderSecondsSection :: forall msg. Render.ResolvedConfig -> TimePickerProps msg -> Int -> E.Element msg
renderSecondsSection config props secondVal =
  E.span_
    [ E.style "display" "inline-flex"
    , E.style "align-items" "center"
    , E.style "gap" "4px"
    ]
    [ Render.renderSeparator config
    , Render.renderTimeSegment config
        { value: secondVal
        , label: "Second"
        , disabled: props.disabled
        , readOnly: props.readOnly
        , showButtons: props.showIncrementButtons && not props.disabled
        , onIncrement: Nothing
        , onDecrement: Nothing
        , onInputChange: Nothing
        }
    ]

-- | Get time value or midnight as default
getTimeOrDefault :: Maybe TimeOfDay.TimeOfDay -> TimeOfDay.TimeOfDay
getTimeOrDefault maybeTime = case maybeTime of
  Just t -> t
  Nothing -> TimeOfDay.midnight

-- | Convert main props to Render.TimePickerProps
toRenderProps :: forall msg. TimePickerProps msg -> Render.TimePickerProps msg
toRenderProps props =
  { disabled: props.disabled
  , readOnly: props.readOnly
  , showIncrementButtons: props.showIncrementButtons
  , backgroundColor: props.backgroundColor
  , borderColor: props.borderColor
  , textColor: props.textColor
  , mutedColor: props.mutedColor
  , primaryColor: props.primaryColor
  , primaryTextColor: props.primaryTextColor
  , borderRadius: props.borderRadius
  , padding: props.padding
  , borderWidth: props.borderWidth
  , fontSize: props.fontSize
  , onPeriodChange: props.onPeriodChange
  , onHourIncrement: Nothing
  , onHourDecrement: Nothing
  , onMinuteIncrement: Nothing
  , onMinuteDecrement: Nothing
  , onSecondIncrement: Nothing
  , onSecondDecrement: Nothing
  }

-- | Resolve config from props (adapter for Render.resolveConfig)
resolveConfigFromProps :: forall msg. TimePickerProps msg -> Render.ResolvedConfig
resolveConfigFromProps props = Render.resolveConfig (toRenderProps props)
