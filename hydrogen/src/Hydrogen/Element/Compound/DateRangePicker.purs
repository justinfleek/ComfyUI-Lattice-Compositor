-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // element // date-range-picker
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | DateRangePicker — Schema-native date range selection component.
-- |
-- | A date range picker with two side-by-side calendars, preset ranges,
-- | and optional comparison mode for analytics and reporting use cases.
-- |
-- | ## Design Philosophy
-- |
-- | This component accepts **concrete Schema atoms** for ALL visual properties.
-- | No hardcoded CSS strings. No Tailwind classes. No JavaScript FFI.
-- |
-- | Presets are **pure functions** that take "today" as a parameter, making
-- | them deterministic and testable. The caller provides the current date
-- | from the runtime boundary.
-- |
-- | ## Schema Atoms Accepted
-- |
-- | | Property           | Pillar    | Type                  | CSS Output      |
-- | |--------------------|-----------|----------------------|-----------------|
-- | | backgroundColor    | Color     | Color.RGB            | background      |
-- | | borderColor        | Color     | Color.RGB            | border-color    |
-- | | textColor          | Color     | Color.RGB            | color           |
-- | | mutedColor         | Color     | Color.RGB            | muted text      |
-- | | primaryColor       | Color     | Color.RGB            | primary actions |
-- | | primaryTextColor   | Color     | Color.RGB            | primary text    |
-- | | borderRadius       | Geometry  | Geometry.Corners     | border-radius   |
-- | | padding            | Dimension | Device.Pixel         | padding         |
-- | | fontSize           | Typography| FontSize.FontSize    | font-size       |
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.DateRangePicker as DateRangePicker
-- | import Hydrogen.Schema.Attestation.Timestamp as Timestamp
-- |
-- | -- Basic range picker (today and timestamp are required)
-- | DateRangePicker.dateRangePicker
-- |   state.today          -- CalendarDate: current date for presets
-- |   state.utcTimestamp   -- Timestamp: current UTC time for attestation
-- |   [ DateRangePicker.startDate state.start
-- |   , DateRangePicker.endDate state.end
-- |   , DateRangePicker.onApply HandleApply
-- |   ]
-- |
-- | -- With presets
-- | DateRangePicker.dateRangePicker
-- |   state.today
-- |   state.utcTimestamp
-- |   [ DateRangePicker.startDate state.start
-- |   , DateRangePicker.endDate state.end
-- |   , DateRangePicker.showPresets true
-- |   , DateRangePicker.presets DateRangePicker.analyticsPresets
-- |   , DateRangePicker.onApply HandleApply
-- |   ]
-- |
-- | -- With comparison mode
-- | DateRangePicker.dateRangePicker
-- |   state.today
-- |   state.utcTimestamp
-- |   [ DateRangePicker.startDate state.start
-- |   , DateRangePicker.endDate state.end
-- |   , DateRangePicker.enableComparison true
-- |   , DateRangePicker.comparisonMode DateRangePicker.PreviousPeriod
-- |   , DateRangePicker.onApply HandleApply
-- |   ]
-- | ```

module Hydrogen.Element.Compound.DateRangePicker
  ( -- * Component
    dateRangePicker
  , dateRangePickerWithLabel
  
  -- * Re-exports from Types
  , module Hydrogen.Element.Compound.DateRangePicker.Types
  
  -- * Re-exports from Presets
  , module Hydrogen.Element.Compound.DateRangePicker.Presets
  
  -- * Props
  , DateRangePickerProps
  , DateRangePickerProp
  , defaultProps
  
  -- * Prop Builders: State
  , startDate
  , endDate
  , isOpen
  , disabled
  , placeholder
  
  -- * Prop Builders: Calendar View
  , leftMonth
  , leftYear
  , rightMonth
  , rightYear
  , weekStartsOn
  
  -- * Prop Builders: Constraints
  , minDate
  , maxDate
  , disabledDates
  
  -- * Prop Builders: Presets
  , showPresets
  , presets
  
  -- * Prop Builders: Comparison
  , enableComparison
  , comparisonMode
  , comparisonStart
  , comparisonEnd
  
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
  , onOpen
  , onClose
  , onApply
  , onStartDateChange
  , onEndDateChange
  , onPresetSelect
  , onComparisonModeChange
  ) where

import Prelude
  ( const
  )

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just))

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Typography.FontSize as FontSize

import Hydrogen.Element.Compound.Calendar (CalendarDate, WeekStart(Sunday))
import Hydrogen.Schema.Attestation.Timestamp (Timestamp)
import Hydrogen.Schema.Attestation.Timestamp as Timestamp
import Hydrogen.Element.Compound.DateRangePicker.Types
  ( ComparisonMode(PreviousPeriod, PreviousYear, Custom)
  , SelectionState(SelectingStart, SelectingEnd, Complete)
  , comparisonModeLabel
  , mkDateRange
  , rangeStart
  , rangeEnd
  , rangeDays
  , isValidRange
  )
import Hydrogen.Element.Compound.DateRangePicker.Presets
  ( PresetDef
  , defaultPresets
  , analyticsPresets
  , todayPreset
  , yesterdayPreset
  , last7DaysPreset
  , last30DaysPreset
  , thisWeekPreset
  , lastWeekPreset
  , thisMonthPreset
  , lastMonthPreset
  , thisYearPreset
  , presetRange
  )
import Hydrogen.Element.Compound.DateRangePicker.Render as Render

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | DateRangePicker properties
type DateRangePickerProps msg =
  { -- State
    startDate :: Maybe CalendarDate
  , endDate :: Maybe CalendarDate
  , isOpen :: Boolean
  , disabled :: Boolean
  , placeholder :: String
  , today :: CalendarDate
  , utcTimestamp :: Timestamp
  
  -- Calendar view state
  , leftMonth :: Int
  , leftYear :: Int
  , rightMonth :: Int
  , rightYear :: Int
  , weekStartsOn :: WeekStart
  
  -- Constraints
  , minDate :: Maybe CalendarDate
  , maxDate :: Maybe CalendarDate
  , disabledDates :: CalendarDate -> Boolean
  
  -- Presets
  , showPresets :: Boolean
  , presets :: Array PresetDef
  
  -- Comparison
  , enableComparison :: Boolean
  , comparisonMode :: ComparisonMode
  , comparisonStart :: Maybe CalendarDate
  , comparisonEnd :: Maybe CalendarDate
  
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
  , onOpen :: Maybe msg
  , onClose :: Maybe msg
  , onApply :: Maybe msg
  , onStartDateChange :: Maybe (CalendarDate -> msg)
  , onEndDateChange :: Maybe (CalendarDate -> msg)
  , onPresetSelect :: Maybe (String -> msg)
  , onComparisonModeChange :: Maybe (ComparisonMode -> msg)
  }

-- | Property modifier
type DateRangePickerProp msg = DateRangePickerProps msg -> DateRangePickerProps msg

-- | Default properties
defaultProps :: forall msg. DateRangePickerProps msg
defaultProps =
  { startDate: Nothing
  , endDate: Nothing
  , isOpen: false
  , disabled: false
  , placeholder: "Select date range..."
  -- today and utcTimestamp are required parameters to the component,
  -- not optional props. They are set by mkProps, not defaultProps.
  , today: { year: 1970, month: 1, day: 1 }  -- Placeholder, overwritten by mkProps
  , utcTimestamp: Timestamp.epoch            -- Placeholder, overwritten by mkProps
  , leftMonth: 1
  , leftYear: 2026
  , rightMonth: 2
  , rightYear: 2026
  , weekStartsOn: Sunday
  , minDate: Nothing
  , maxDate: Nothing
  , disabledDates: const false
  , showPresets: true
  , presets: defaultPresets
  , enableComparison: false
  , comparisonMode: PreviousPeriod
  , comparisonStart: Nothing
  , comparisonEnd: Nothing
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
  , onOpen: Nothing
  , onClose: Nothing
  , onApply: Nothing
  , onStartDateChange: Nothing
  , onEndDateChange: Nothing
  , onPresetSelect: Nothing
  , onComparisonModeChange: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set start date
startDate :: forall msg. Maybe CalendarDate -> DateRangePickerProp msg
startDate d props = props { startDate = d }

-- | Set end date
endDate :: forall msg. Maybe CalendarDate -> DateRangePickerProp msg
endDate d props = props { endDate = d }

-- | Set open state
isOpen :: forall msg. Boolean -> DateRangePickerProp msg
isOpen o props = props { isOpen = o }

-- | Set disabled state
disabled :: forall msg. Boolean -> DateRangePickerProp msg
disabled d props = props { disabled = d }

-- | Set placeholder text
placeholder :: forall msg. String -> DateRangePickerProp msg
placeholder p props = props { placeholder = p }



-- ═════════════════════════════════════════════════════════════════════════════
--                                               // prop builders: calendar view
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set left calendar month (1-12)
leftMonth :: forall msg. Int -> DateRangePickerProp msg
leftMonth m props = props { leftMonth = m }

-- | Set left calendar year
leftYear :: forall msg. Int -> DateRangePickerProp msg
leftYear y props = props { leftYear = y }

-- | Set right calendar month (1-12)
rightMonth :: forall msg. Int -> DateRangePickerProp msg
rightMonth m props = props { rightMonth = m }

-- | Set right calendar year
rightYear :: forall msg. Int -> DateRangePickerProp msg
rightYear y props = props { rightYear = y }

-- | Set week start day
weekStartsOn :: forall msg. WeekStart -> DateRangePickerProp msg
weekStartsOn ws props = props { weekStartsOn = ws }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                 // prop builders: constraints
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set minimum selectable date
minDate :: forall msg. CalendarDate -> DateRangePickerProp msg
minDate d props = props { minDate = Just d }

-- | Set maximum selectable date
maxDate :: forall msg. CalendarDate -> DateRangePickerProp msg
maxDate d props = props { maxDate = Just d }

-- | Set disabled dates predicate
disabledDates :: forall msg. (CalendarDate -> Boolean) -> DateRangePickerProp msg
disabledDates pred props = props { disabledDates = pred }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // prop builders: presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Show presets sidebar
showPresets :: forall msg. Boolean -> DateRangePickerProp msg
showPresets s props = props { showPresets = s }

-- | Set custom presets
presets :: forall msg. Array PresetDef -> DateRangePickerProp msg
presets p props = props { presets = p }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // prop builders: comparison
-- ═════════════════════════════════════════════════════════════════════════════

-- | Enable comparison mode
enableComparison :: forall msg. Boolean -> DateRangePickerProp msg
enableComparison e props = props { enableComparison = e }

-- | Set comparison mode
comparisonMode :: forall msg. ComparisonMode -> DateRangePickerProp msg
comparisonMode m props = props { comparisonMode = m }

-- | Set comparison start date
comparisonStart :: forall msg. Maybe CalendarDate -> DateRangePickerProp msg
comparisonStart d props = props { comparisonStart = d }

-- | Set comparison end date
comparisonEnd :: forall msg. Maybe CalendarDate -> DateRangePickerProp msg
comparisonEnd d props = props { comparisonEnd = d }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: color
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set background color (Color.RGB atom)
backgroundColor :: forall msg. Color.RGB -> DateRangePickerProp msg
backgroundColor c props = props { backgroundColor = Just c }

-- | Set border color (Color.RGB atom)
borderColor :: forall msg. Color.RGB -> DateRangePickerProp msg
borderColor c props = props { borderColor = Just c }

-- | Set text color (Color.RGB atom)
textColor :: forall msg. Color.RGB -> DateRangePickerProp msg
textColor c props = props { textColor = Just c }

-- | Set muted text color (Color.RGB atom)
mutedColor :: forall msg. Color.RGB -> DateRangePickerProp msg
mutedColor c props = props { mutedColor = Just c }

-- | Set primary color (Color.RGB atom)
primaryColor :: forall msg. Color.RGB -> DateRangePickerProp msg
primaryColor c props = props { primaryColor = Just c }

-- | Set primary text color (Color.RGB atom)
primaryTextColor :: forall msg. Color.RGB -> DateRangePickerProp msg
primaryTextColor c props = props { primaryTextColor = Just c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: geometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set border radius (Geometry.Corners atom)
borderRadius :: forall msg. Geometry.Corners -> DateRangePickerProp msg
borderRadius r props = props { borderRadius = Just r }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // prop builders: dimension
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set padding (Device.Pixel atom)
padding :: forall msg. Device.Pixel -> DateRangePickerProp msg
padding p props = props { padding = Just p }

-- | Set border width (Device.Pixel atom)
borderWidth :: forall msg. Device.Pixel -> DateRangePickerProp msg
borderWidth w props = props { borderWidth = Just w }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // prop builders: typography
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set font size (FontSize atom)
fontSize :: forall msg. FontSize.FontSize -> DateRangePickerProp msg
fontSize s props = props { fontSize = Just s }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: behavior
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set open handler
onOpen :: forall msg. msg -> DateRangePickerProp msg
onOpen m props = props { onOpen = Just m }

-- | Set close handler
onClose :: forall msg. msg -> DateRangePickerProp msg
onClose m props = props { onClose = Just m }

-- | Set apply handler (fires when user confirms selection)
onApply :: forall msg. msg -> DateRangePickerProp msg
onApply m props = props { onApply = Just m }

-- | Set start date change handler
onStartDateChange :: forall msg. (CalendarDate -> msg) -> DateRangePickerProp msg
onStartDateChange handler props = props { onStartDateChange = Just handler }

-- | Set end date change handler
onEndDateChange :: forall msg. (CalendarDate -> msg) -> DateRangePickerProp msg
onEndDateChange handler props = props { onEndDateChange = Just handler }

-- | Set preset select handler
onPresetSelect :: forall msg. (String -> msg) -> DateRangePickerProp msg
onPresetSelect handler props = props { onPresetSelect = Just handler }

-- | Set comparison mode change handler
onComparisonModeChange :: forall msg. (ComparisonMode -> msg) -> DateRangePickerProp msg
onComparisonModeChange handler props = props { onComparisonModeChange = Just handler }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // main component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a date range picker
-- |
-- | Pure Element — renders to DOM, Static HTML, or any target.
-- | No JavaScript FFI. Pure PureScript.
-- |
-- | Required parameters:
-- | - `today` — Current date for preset calculations (e.g., "Last 7 days")
-- | - `utcTimestamp` — Current UTC timestamp for attestation
-- |
-- | These are required because every selection is attested with a timestamp,
-- | and presets need a reference date to calculate ranges.
dateRangePicker 
  :: forall msg
   . CalendarDate 
  -> Timestamp 
  -> Array (DateRangePickerProp msg) 
  -> E.Element msg
dateRangePicker todayDate ts propMods =
  let
    baseProps = foldl (\p f -> f p) defaultProps propMods
    props = baseProps { today = todayDate, utcTimestamp = ts }
    renderProps = toRenderProps props
    config = Render.resolveConfig renderProps
  in
    E.div_
      [ E.style "position" "relative"
      , E.style "display" "inline-block"
      ]
      [ -- Trigger button
        Render.renderTrigger renderProps config
      
      , -- Popup panel (if open)
        if props.isOpen
          then Render.renderPopup renderProps config
          else E.text ""
      ]

-- | Render a date range picker with label
-- |
-- | Same as `dateRangePicker` but with a label above.
-- |
-- | Required parameters:
-- | - `labelText` — Label to display above the picker
-- | - `today` — Current date for preset calculations
-- | - `utcTimestamp` — Current UTC timestamp for attestation
dateRangePickerWithLabel 
  :: forall msg
   . String 
  -> CalendarDate 
  -> Timestamp 
  -> Array (DateRangePickerProp msg) 
  -> E.Element msg
dateRangePickerWithLabel labelText todayDate ts propMods =
  let
    baseProps = foldl (\p f -> f p) defaultProps propMods
    props = baseProps { today = todayDate, utcTimestamp = ts }
    renderProps = toRenderProps props
    config = Render.resolveConfig renderProps
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "gap" "8px"
      ]
      [ E.label_
          [ E.style "font-size" "14px"
          , E.style "font-weight" "500"
          , E.style "color" (Color.toLegacyCss config.textCol)
          ]
          [ E.text labelText ]
      , E.div_
          [ E.style "position" "relative"
          , E.style "display" "inline-block"
          ]
          [ Render.renderTrigger renderProps config
          , if props.isOpen
              then Render.renderPopup renderProps config
              else E.text ""
          ]
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // internal helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert main props to Render.DateRangePickerProps
toRenderProps :: forall msg. DateRangePickerProps msg -> Render.DateRangePickerProps msg
toRenderProps props =
  { startDate: props.startDate
  , endDate: props.endDate
  , isOpen: props.isOpen
  , disabled: props.disabled
  , placeholder: props.placeholder
  , today: props.today
  , utcTimestamp: props.utcTimestamp
  , leftMonth: props.leftMonth
  , leftYear: props.leftYear
  , rightMonth: props.rightMonth
  , rightYear: props.rightYear
  , showPresets: props.showPresets
  , presets: props.presets
  , enableComparison: props.enableComparison
  , comparisonMode: props.comparisonMode
  , comparisonStart: props.comparisonStart
  , comparisonEnd: props.comparisonEnd
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
  , onOpen: props.onOpen
  , onClose: props.onClose
  , onPresetSelect: props.onPresetSelect
  , onApply: props.onApply
  }
