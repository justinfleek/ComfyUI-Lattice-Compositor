-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // element // date-picker
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | DatePicker — Schema-native date selection component.
-- |
-- | A date picker combining a text input for direct date entry with a calendar
-- | popup for visual selection. Pure PureScript implementation with no
-- | JavaScript FFI.
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
-- | | placeholderColor   | Color     | Color.RGB            | placeholder     |
-- | | errorColor         | Color     | Color.RGB            | error indicator |
-- | | borderRadius       | Geometry  | Geometry.Corners     | border-radius   |
-- | | padding            | Dimension | Device.Pixel         | padding         |
-- | | fontSize           | Typography| FontSize.FontSize    | font-size       |
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.DatePicker as DatePicker
-- | import Hydrogen.Schema.Color.RGB as Color
-- |
-- | -- Basic date picker
-- | DatePicker.datePicker
-- |   [ DatePicker.value state.date
-- |   , DatePicker.onSelect HandleDateSelect
-- |   ]
-- |
-- | -- With brand atoms
-- | DatePicker.datePicker
-- |   [ DatePicker.value state.date
-- |   , DatePicker.onSelect HandleDateSelect
-- |   , DatePicker.backgroundColor brand.surfaceColor
-- |   , DatePicker.borderRadius brand.corners
-- |   ]
-- | ```

module Hydrogen.Element.Compound.DatePicker
  ( -- * Component
    datePicker
  
  -- * Re-exports from Types
  , module Hydrogen.Element.Compound.DatePicker.Types
  
  -- * Re-exports from Format
  , module Hydrogen.Element.Compound.DatePicker.Format
  
  -- * Props
  , DatePickerProps
  , DatePickerProp
  , defaultProps
  
  -- * Prop Builders: State
  , value
  , inputValue
  , dateFormat
  , placeholder
  , disabled
  , readOnly
  , required
  , isOpen
  , hasError
  , errorMessage
  
  -- * Prop Builders: Constraints
  , minDate
  , maxDate
  , disabledDates
  , weekStartsOn
  
  -- * Prop Builders: Display
  , showTodayButton
  , showClearButton
  , showCalendarIcon
  
  -- * Prop Builders: Color Atoms
  , backgroundColor
  , borderColor
  , textColor
  , placeholderColor
  , errorColor
  , focusColor
  
  -- * Prop Builders: Geometry Atoms
  , borderRadius
  
  -- * Prop Builders: Dimension Atoms
  , padding
  , borderWidth
  
  -- * Prop Builders: Typography Atoms
  , fontSize
  
  -- * Prop Builders: Behavior
  , onSelect
  , onInputChange
  , onOpen
  , onClose
  , onClear
  , onToday
  ) where

import Prelude
  ( const
  , not
  , (&&)
  )

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just), isJust)

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Typography.FontSize as FontSize

import Hydrogen.Element.Compound.Calendar as Calendar
import Hydrogen.Element.Compound.DatePicker.Types
  ( DateFormat(ISO, USShort, USLong, EUShort, EULong, Custom)
  , ValidationError(InvalidFormat, DateOutOfRange, DateDisabled, EmptyValue)
  , validationErrorMessage
  )
import Hydrogen.Element.Compound.DatePicker.Format
  ( formatDate
  , formatDateISO
  , formatDateUSShort
  , formatDateUSLong
  , formatDateEUShort
  , formatDateEULong
  , parseDate
  , parseISO
  , parseUSShort
  , parseEUShort
  , monthNameLong
  , padZero
  )
import Hydrogen.Element.Compound.DatePicker.Render as Render

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | DatePicker properties
type DatePickerProps msg =
  { -- State
    value :: Maybe Calendar.CalendarDate
  , inputValue :: String
  , dateFormat :: DateFormat
  , placeholder :: String
  , disabled :: Boolean
  , readOnly :: Boolean
  , required :: Boolean
  , isOpen :: Boolean
  , hasError :: Boolean
  , errorMessage :: Maybe String
  
  -- Constraints
  , minDate :: Maybe Calendar.CalendarDate
  , maxDate :: Maybe Calendar.CalendarDate
  , disabledDates :: Calendar.CalendarDate -> Boolean
  , weekStartsOn :: Calendar.WeekStart
  
  -- Display
  , showTodayButton :: Boolean
  , showClearButton :: Boolean
  , showCalendarIcon :: Boolean
  
  -- Color atoms
  , backgroundColor :: Maybe Color.RGB
  , borderColor :: Maybe Color.RGB
  , textColor :: Maybe Color.RGB
  , placeholderColor :: Maybe Color.RGB
  , errorColor :: Maybe Color.RGB
  , focusColor :: Maybe Color.RGB
  
  -- Geometry atoms
  , borderRadius :: Maybe Geometry.Corners
  
  -- Dimension atoms
  , padding :: Maybe Device.Pixel
  , borderWidth :: Maybe Device.Pixel
  
  -- Typography atoms
  , fontSize :: Maybe FontSize.FontSize
  
  -- Behavior
  , onSelect :: Maybe (Calendar.CalendarDate -> msg)
  , onInputChange :: Maybe (String -> msg)
  , onOpen :: Maybe msg
  , onClose :: Maybe msg
  , onClear :: Maybe msg
  , onToday :: Maybe msg
  }

-- | Property modifier
type DatePickerProp msg = DatePickerProps msg -> DatePickerProps msg

-- | Default properties
defaultProps :: forall msg. DatePickerProps msg
defaultProps =
  { value: Nothing
  , inputValue: ""
  , dateFormat: ISO
  , placeholder: "Select date..."
  , disabled: false
  , readOnly: false
  , required: false
  , isOpen: false
  , hasError: false
  , errorMessage: Nothing
  , minDate: Nothing
  , maxDate: Nothing
  , disabledDates: const false
  , weekStartsOn: Calendar.Sunday
  , showTodayButton: false
  , showClearButton: false
  , showCalendarIcon: true
  , backgroundColor: Nothing
  , borderColor: Nothing
  , textColor: Nothing
  , placeholderColor: Nothing
  , errorColor: Nothing
  , focusColor: Nothing
  , borderRadius: Nothing
  , padding: Nothing
  , borderWidth: Nothing
  , fontSize: Nothing
  , onSelect: Nothing
  , onInputChange: Nothing
  , onOpen: Nothing
  , onClose: Nothing
  , onClear: Nothing
  , onToday: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set the selected date value
value :: forall msg. Maybe Calendar.CalendarDate -> DatePickerProp msg
value v props = props { value = v }

-- | Set the raw input value
inputValue :: forall msg. String -> DatePickerProp msg
inputValue v props = props { inputValue = v }

-- | Set date format for display/parsing
dateFormat :: forall msg. DateFormat -> DatePickerProp msg
dateFormat f props = props { dateFormat = f }

-- | Set placeholder text
placeholder :: forall msg. String -> DatePickerProp msg
placeholder p props = props { placeholder = p }

-- | Set disabled state
disabled :: forall msg. Boolean -> DatePickerProp msg
disabled d props = props { disabled = d }

-- | Set read-only state
readOnly :: forall msg. Boolean -> DatePickerProp msg
readOnly r props = props { readOnly = r }

-- | Set required state
required :: forall msg. Boolean -> DatePickerProp msg
required r props = props { required = r }

-- | Set open state
isOpen :: forall msg. Boolean -> DatePickerProp msg
isOpen o props = props { isOpen = o }

-- | Set error state
hasError :: forall msg. Boolean -> DatePickerProp msg
hasError e props = props { hasError = e }

-- | Set error message
errorMessage :: forall msg. String -> DatePickerProp msg
errorMessage msg props = props { errorMessage = Just msg }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                 // prop builders: constraints
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set minimum selectable date
minDate :: forall msg. Calendar.CalendarDate -> DatePickerProp msg
minDate d props = props { minDate = Just d }

-- | Set maximum selectable date
maxDate :: forall msg. Calendar.CalendarDate -> DatePickerProp msg
maxDate d props = props { maxDate = Just d }

-- | Set disabled dates predicate
disabledDates :: forall msg. (Calendar.CalendarDate -> Boolean) -> DatePickerProp msg
disabledDates pred props = props { disabledDates = pred }

-- | Set week start day
weekStartsOn :: forall msg. Calendar.WeekStart -> DatePickerProp msg
weekStartsOn ws props = props { weekStartsOn = ws }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // prop builders: display
-- ═════════════════════════════════════════════════════════════════════════════

-- | Show "Today" button in calendar
showTodayButton :: forall msg. Boolean -> DatePickerProp msg
showTodayButton s props = props { showTodayButton = s }

-- | Show clear button
showClearButton :: forall msg. Boolean -> DatePickerProp msg
showClearButton s props = props { showClearButton = s }

-- | Show calendar icon
showCalendarIcon :: forall msg. Boolean -> DatePickerProp msg
showCalendarIcon s props = props { showCalendarIcon = s }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: color
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set background color (Color.RGB atom)
backgroundColor :: forall msg. Color.RGB -> DatePickerProp msg
backgroundColor c props = props { backgroundColor = Just c }

-- | Set border color (Color.RGB atom)
borderColor :: forall msg. Color.RGB -> DatePickerProp msg
borderColor c props = props { borderColor = Just c }

-- | Set text color (Color.RGB atom)
textColor :: forall msg. Color.RGB -> DatePickerProp msg
textColor c props = props { textColor = Just c }

-- | Set placeholder text color (Color.RGB atom)
placeholderColor :: forall msg. Color.RGB -> DatePickerProp msg
placeholderColor c props = props { placeholderColor = Just c }

-- | Set error indicator color (Color.RGB atom)
errorColor :: forall msg. Color.RGB -> DatePickerProp msg
errorColor c props = props { errorColor = Just c }

-- | Set focus ring color (Color.RGB atom)
focusColor :: forall msg. Color.RGB -> DatePickerProp msg
focusColor c props = props { focusColor = Just c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: geometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set border radius (Geometry.Corners atom)
borderRadius :: forall msg. Geometry.Corners -> DatePickerProp msg
borderRadius r props = props { borderRadius = Just r }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // prop builders: dimension
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set padding (Device.Pixel atom)
padding :: forall msg. Device.Pixel -> DatePickerProp msg
padding p props = props { padding = Just p }

-- | Set border width (Device.Pixel atom)
borderWidth :: forall msg. Device.Pixel -> DatePickerProp msg
borderWidth w props = props { borderWidth = Just w }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // prop builders: typography
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set font size (FontSize atom)
fontSize :: forall msg. FontSize.FontSize -> DatePickerProp msg
fontSize s props = props { fontSize = Just s }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: behavior
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set date select handler
onSelect :: forall msg. (Calendar.CalendarDate -> msg) -> DatePickerProp msg
onSelect handler props = props { onSelect = Just handler }

-- | Set input change handler
onInputChange :: forall msg. (String -> msg) -> DatePickerProp msg
onInputChange handler props = props { onInputChange = Just handler }

-- | Set open handler
onOpen :: forall msg. msg -> DatePickerProp msg
onOpen msg props = props { onOpen = Just msg }

-- | Set close handler
onClose :: forall msg. msg -> DatePickerProp msg
onClose msg props = props { onClose = Just msg }

-- | Set clear handler
onClear :: forall msg. msg -> DatePickerProp msg
onClear msg props = props { onClear = Just msg }

-- | Set today handler
onToday :: forall msg. msg -> DatePickerProp msg
onToday msg props = props { onToday = Just msg }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // main component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a date picker
-- |
-- | Pure Element — renders to DOM, Static HTML, or any target.
-- | No JavaScript FFI. Pure PureScript date formatting and parsing.
datePicker :: forall msg. Array (DatePickerProp msg) -> E.Element msg
datePicker propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    config = Render.resolveConfig props
    displayValue = case props.value of
      Just d -> formatDate props.dateFormat d
      Nothing -> props.inputValue
    currentBorderColor = if props.hasError
      then Color.toLegacyCss config.errorCol
      else Color.toLegacyCss config.borderCol
  in
    E.div_
      [ E.style "position" "relative"
      , E.style "display" "inline-block"
      ]
      [ -- Input wrapper
        E.div_
          [ E.style "position" "relative" ]
          [ -- Calendar icon (left)
            if props.showCalendarIcon
              then Render.renderCalendarIcon config
              else E.text ""
          
          , -- Input field
            Render.renderInput props config displayValue currentBorderColor
          
          , -- Clear button (right)
            if props.showClearButton && isJust props.value && not props.disabled
              then Render.renderClearButton props config
              else E.text ""
          ]
      
      , -- Error message
        case props.errorMessage of
          Just msg -> Render.renderErrorMessage config msg
          Nothing -> E.text ""
      
      , -- Calendar popup
        if props.isOpen
          then Render.renderCalendarPopup props config
          else E.text ""
      ]
