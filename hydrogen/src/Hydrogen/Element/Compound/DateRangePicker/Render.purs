-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                           // hydrogen // element // daterangepicker // render
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | DateRangePicker Render — Rendering helpers for DateRangePicker component.
-- |
-- | Internal module containing render functions. Pure PureScript, no FFI.
-- | Uses Schema atoms for all visual properties.

module Hydrogen.Element.Compound.DateRangePicker.Render
  ( -- * Render Functions
    renderTrigger
  , renderPopup
  , renderPresetsSidebar
  , renderDualCalendars
  , renderComparisonSection
  , renderFooter
  , renderCalendarIcon
  
  -- * Configuration
  , ResolvedConfig
  , resolveConfig
  
  -- * Props Type
  , DateRangePickerProps
  ) where

import Prelude
  ( show
  , map
  , (<>)
  , ($)
  )

import Data.Maybe (Maybe(Nothing, Just), maybe)

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Typography.FontSize as FontSize

import Hydrogen.Element.Compound.Calendar as Calendar
import Hydrogen.Element.Compound.DateRangePicker.Types 
  ( CalendarDate
  , ComparisonMode
  , comparisonModeLabel
  )
import Hydrogen.Schema.Attestation.Timestamp (Timestamp)
import Hydrogen.Schema.Attestation.Timestamp as Timestamp
import Hydrogen.Element.Compound.DateRangePicker.Presets (PresetDef, presetId, presetLabel)
import Hydrogen.Element.Compound.DatePicker.Format (formatDate)
import Hydrogen.Element.Compound.DatePicker.Types (DateFormat(ISO))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | DateRangePicker properties for rendering
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
  
  -- Handlers
  , onOpen :: Maybe msg
  , onClose :: Maybe msg
  , onPresetSelect :: Maybe (String -> msg)
  , onApply :: Maybe msg
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // resolved config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Resolved configuration with defaults applied
type ResolvedConfig =
  { bgColor :: Color.RGB
  , borderCol :: Color.RGB
  , textCol :: Color.RGB
  , mutedCol :: Color.RGB
  , primaryCol :: Color.RGB
  , primaryTextCol :: Color.RGB
  , radius :: String
  , paddingVal :: String
  , borderWidthVal :: String
  , fontSizeVal :: String
  }

-- | Resolve props to config with defaults
resolveConfig :: forall msg. DateRangePickerProps msg -> ResolvedConfig
resolveConfig props =
  { bgColor: maybe (Color.rgb 30 30 30) (\c -> c) props.backgroundColor
  , borderCol: maybe (Color.rgb 60 60 60) (\c -> c) props.borderColor
  , textCol: maybe (Color.rgb 220 220 220) (\c -> c) props.textColor
  , mutedCol: maybe (Color.rgb 120 120 120) (\c -> c) props.mutedColor
  , primaryCol: maybe (Color.rgb 59 130 246) (\c -> c) props.primaryColor
  , primaryTextCol: maybe (Color.rgb 255 255 255) (\c -> c) props.primaryTextColor
  , radius: maybe "6px" Geometry.cornersToLegacyCss props.borderRadius
  , paddingVal: maybe "16px" show props.padding
  , borderWidthVal: maybe "1px" show props.borderWidth
  , fontSizeVal: maybe "14px" FontSize.toLegacyCss props.fontSize
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // render helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render the trigger button
renderTrigger :: forall msg. DateRangePickerProps msg -> ResolvedConfig -> E.Element msg
renderTrigger props config =
  let
    displayText = case props.startDate, props.endDate of
      Just start, Just end ->
        formatDate ISO start <> " - " <> formatDate ISO end
      Just start, Nothing ->
        formatDate ISO start <> " - ..."
      Nothing, Just end ->
        "... - " <> formatDate ISO end
      Nothing, Nothing ->
        props.placeholder
    
    clickHandler = case props.onOpen of
      Just msg -> [ E.onClick msg ]
      Nothing -> []
  in
    E.button_
      ( [ E.type_ "button"
        , E.disabled props.disabled
        , E.attr "aria-haspopup" "dialog"
        , E.attr "aria-expanded" (show props.isOpen)
        , E.style "display" "flex"
        , E.style "align-items" "center"
        , E.style "height" "40px"
        , E.style "padding" "8px 12px"
        , E.style "background-color" (Color.toLegacyCss config.bgColor)
        , E.style "color" (Color.toLegacyCss config.textCol)
        , E.style "border-style" "solid"
        , E.style "border-width" config.borderWidthVal
        , E.style "border-color" (Color.toLegacyCss config.borderCol)
        , E.style "border-radius" config.radius
        , E.style "font-size" config.fontSizeVal
        , E.style "cursor" (if props.disabled then "not-allowed" else "pointer")
        ] <> clickHandler
      )
      [ renderCalendarIcon config
      , E.span_
          [ E.style "margin-left" "8px" ]
          [ E.text displayText ]
      ]

-- | Render the popup panel
renderPopup :: forall msg. DateRangePickerProps msg -> ResolvedConfig -> E.Element msg
renderPopup props config =
  E.div_
    [ E.style "position" "absolute"
    , E.style "z-index" "50"
    , E.style "margin-top" "4px"
    , E.style "background-color" (Color.toLegacyCss config.bgColor)
    , E.style "border-style" "solid"
    , E.style "border-width" "1px"
    , E.style "border-color" (Color.toLegacyCss config.borderCol)
    , E.style "border-radius" config.radius
    , E.style "box-shadow" "0 4px 6px -1px rgba(0,0,0,0.1)"
    , E.style "padding" config.paddingVal
    , E.role "dialog"
    , E.attr "aria-modal" "true"
    ]
    [ E.div_
        [ E.style "display" "flex"
        , E.style "gap" "16px"
        ]
        [ if props.showPresets
            then renderPresetsSidebar props config
            else E.text ""
        , renderDualCalendars props config
        ]
    , if props.enableComparison
        then renderComparisonSection props config
        else E.text ""
    , renderFooter props config
    ]

-- | Render presets sidebar
renderPresetsSidebar :: forall msg. DateRangePickerProps msg -> ResolvedConfig -> E.Element msg
renderPresetsSidebar props config =
  let
    presetsToUse = props.presets
  in
    E.div_
      [ E.style "border-right" ("1px solid " <> Color.toLegacyCss config.borderCol)
      , E.style "padding-right" "16px"
      , E.style "min-width" "140px"
      ]
      [ E.div_
          [ E.style "font-size" "14px"
          , E.style "font-weight" "500"
          , E.style "margin-bottom" "8px"
          , E.style "color" (Color.toLegacyCss config.textCol)
          ]
          [ E.text "Quick select" ]
      , E.div_
          [ E.style "display" "flex"
          , E.style "flex-direction" "column"
          , E.style "gap" "4px"
          ]
          (map (renderPresetButton props config) presetsToUse)
      ]

-- | Render a single preset button
renderPresetButton :: forall msg. DateRangePickerProps msg -> ResolvedConfig -> PresetDef -> E.Element msg
renderPresetButton props config preset =
  let
    clickHandler = case props.onPresetSelect of
      Just handler -> [ E.onClick (handler (presetId preset)) ]
      Nothing -> []
  in
    E.button_
      ( [ E.type_ "button"
        , E.style "text-align" "left"
        , E.style "padding" "6px 8px"
        , E.style "border-radius" "4px"
        , E.style "border" "none"
        , E.style "background" "transparent"
        , E.style "color" (Color.toLegacyCss config.textCol)
        , E.style "font-size" "14px"
        , E.style "cursor" "pointer"
        ] <> clickHandler
      )
      [ E.text (presetLabel preset) ]

-- | Render dual calendars side by side
renderDualCalendars :: forall msg. DateRangePickerProps msg -> ResolvedConfig -> E.Element msg
renderDualCalendars props config =
  E.div_
    [ E.style "display" "flex"
    , E.style "gap" "16px"
    ]
    [ -- Left calendar
      E.div_
        []
        [ E.div_
            [ E.style "font-size" "14px"
            , E.style "font-weight" "500"
            , E.style "text-align" "center"
            , E.style "margin-bottom" "8px"
            , E.style "color" (Color.toLegacyCss config.textCol)
            ]
            [ E.text $ Calendar.monthName Calendar.EnUS props.leftMonth <> " " <> show props.leftYear ]
        , Calendar.calendar
            [ Calendar.selectionMode Calendar.Range
            , Calendar.rangeStart props.startDate
            , Calendar.rangeEnd props.endDate
            , Calendar.viewMonth props.leftMonth
            , Calendar.viewYear props.leftYear
            ]
        ]
    , -- Right calendar
      E.div_
        []
        [ E.div_
            [ E.style "font-size" "14px"
            , E.style "font-weight" "500"
            , E.style "text-align" "center"
            , E.style "margin-bottom" "8px"
            , E.style "color" (Color.toLegacyCss config.textCol)
            ]
            [ E.text $ Calendar.monthName Calendar.EnUS props.rightMonth <> " " <> show props.rightYear ]
        , Calendar.calendar
            [ Calendar.selectionMode Calendar.Range
            , Calendar.rangeStart props.startDate
            , Calendar.rangeEnd props.endDate
            , Calendar.viewMonth props.rightMonth
            , Calendar.viewYear props.rightYear
            ]
        ]
    ]

-- | Render comparison section
renderComparisonSection :: forall msg. DateRangePickerProps msg -> ResolvedConfig -> E.Element msg
renderComparisonSection props config =
  E.div_
    [ E.style "border-top" ("1px solid " <> Color.toLegacyCss config.borderCol)
    , E.style "margin-top" "16px"
    , E.style "padding-top" "16px"
    ]
    [ E.div_
        [ E.style "display" "flex"
        , E.style "align-items" "center"
        , E.style "gap" "16px"
        ]
        [ E.label_
            [ E.style "font-size" "14px"
            , E.style "font-weight" "500"
            , E.style "color" (Color.toLegacyCss config.textCol)
            ]
            [ E.text "Compare to:" ]
        , E.span_
            [ E.style "font-size" "14px"
            , E.style "color" (Color.toLegacyCss config.mutedCol)
            ]
            [ E.text (comparisonModeLabel props.comparisonMode) ]
        , case props.comparisonStart, props.comparisonEnd of
            Just start, Just end ->
              E.span_
                [ E.style "font-size" "14px"
                , E.style "color" (Color.toLegacyCss config.mutedCol)
                ]
                [ E.text $ formatDate ISO start <> " - " <> formatDate ISO end ]
            _, _ -> E.text ""
        ]
    ]

-- | Render footer with inputs and buttons
-- |
-- | When utcTimestamp is provided, displays the current UTC time for attestation
-- | transparency. Users see exactly when their selection will be timestamped.
renderFooter :: forall msg. DateRangePickerProps msg -> ResolvedConfig -> E.Element msg
renderFooter props config =
  let
    cancelHandler = case props.onClose of
      Just msg -> [ E.onClick msg ]
      Nothing -> []
    
    applyHandler = case props.onApply of
      Just msg -> [ E.onClick msg ]
      Nothing -> []
  in
    E.div_
      [ E.style "border-top" ("1px solid " <> Color.toLegacyCss config.borderCol)
      , E.style "margin-top" "16px"
      , E.style "padding-top" "16px"
      , E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "gap" "12px"
      ]
      [ -- Date inputs and action buttons row
        E.div_
          [ E.style "display" "flex"
          , E.style "align-items" "center"
          , E.style "justify-content" "space-between"
          ]
          [ -- Date inputs display
            E.div_
              [ E.style "display" "flex"
              , E.style "align-items" "center"
              , E.style "gap" "8px"
              ]
              [ E.input_
                  [ E.type_ "text"
                  , E.placeholder "Start date"
                  , E.value $ maybe "" (formatDate ISO) props.startDate
                  , E.attr "readonly" "true"
                  , E.style "width" "120px"
                  , E.style "padding" "4px 8px"
                  , E.style "border-style" "solid"
                  , E.style "border-width" "1px"
                  , E.style "border-color" (Color.toLegacyCss config.borderCol)
                  , E.style "border-radius" "4px"
                  , E.style "font-size" "14px"
                  , E.style "background-color" (Color.toLegacyCss config.bgColor)
                  , E.style "color" (Color.toLegacyCss config.textCol)
                  ]
              , E.span_
                  [ E.style "color" (Color.toLegacyCss config.mutedCol) ]
                  [ E.text "-" ]
              , E.input_
                  [ E.type_ "text"
                  , E.placeholder "End date"
                  , E.value $ maybe "" (formatDate ISO) props.endDate
                  , E.attr "readonly" "true"
                  , E.style "width" "120px"
                  , E.style "padding" "4px 8px"
                  , E.style "border-style" "solid"
                  , E.style "border-width" "1px"
                  , E.style "border-color" (Color.toLegacyCss config.borderCol)
                  , E.style "border-radius" "4px"
                  , E.style "font-size" "14px"
                  , E.style "background-color" (Color.toLegacyCss config.bgColor)
                  , E.style "color" (Color.toLegacyCss config.textCol)
                  ]
              ]
          , -- Action buttons
            E.div_
              [ E.style "display" "flex"
              , E.style "gap" "8px"
              ]
              [ E.button_
                  ( [ E.type_ "button"
                    , E.style "padding" "6px 12px"
                    , E.style "border-style" "solid"
                    , E.style "border-width" "1px"
                    , E.style "border-color" (Color.toLegacyCss config.borderCol)
                    , E.style "border-radius" "4px"
                    , E.style "background-color" "transparent"
                    , E.style "color" (Color.toLegacyCss config.textCol)
                    , E.style "font-size" "14px"
                    , E.style "cursor" "pointer"
                    ] <> cancelHandler
                  )
                  [ E.text "Cancel" ]
              , E.button_
                  ( [ E.type_ "button"
                    , E.style "padding" "6px 12px"
                    , E.style "border" "none"
                    , E.style "border-radius" "4px"
                    , E.style "background-color" (Color.toLegacyCss config.primaryCol)
                    , E.style "color" (Color.toLegacyCss config.primaryTextCol)
                    , E.style "font-size" "14px"
                    , E.style "cursor" "pointer"
                    ] <> applyHandler
                  )
                  [ E.text "Apply" ]
              ]
          ]
      , -- UTC timestamp display (for attestation transparency)
        renderTimestampDisplay props config
      ]

-- | Render UTC timestamp display
-- |
-- | Shows the current UTC time. Every selection is attested —
-- | users see exactly when their selection will be recorded.
renderTimestampDisplay :: forall msg. DateRangePickerProps msg -> ResolvedConfig -> E.Element msg
renderTimestampDisplay props config =
  E.div_
    [ E.style "display" "flex"
    , E.style "align-items" "center"
    , E.style "gap" "4px"
    , E.style "font-size" "12px"
    , E.style "color" (Color.toLegacyCss config.mutedCol)
    ]
    [ E.span_
        []
        [ E.text "Selection timestamp:" ]
    , E.span_
        [ E.style "font-family" "monospace" ]
        [ E.text (Timestamp.toISO8601 props.utcTimestamp) ]
    ]

-- | Render calendar icon
renderCalendarIcon :: forall msg. ResolvedConfig -> E.Element msg
renderCalendarIcon config =
  E.element "svg"
    [ E.attr "width" "16"
    , E.attr "height" "16"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "fill" "none"
    , E.attr "stroke" (Color.toLegacyCss config.mutedCol)
    , E.attr "stroke-width" "2"
    , E.attr "stroke-linecap" "round"
    , E.attr "stroke-linejoin" "round"
    ]
    [ E.element "rect"
        [ E.attr "width" "18"
        , E.attr "height" "18"
        , E.attr "x" "3"
        , E.attr "y" "4"
        , E.attr "rx" "2"
        ]
        []
    , E.element "line"
        [ E.attr "x1" "16"
        , E.attr "x2" "16"
        , E.attr "y1" "2"
        , E.attr "y2" "6"
        ]
        []
    , E.element "line"
        [ E.attr "x1" "8"
        , E.attr "x2" "8"
        , E.attr "y1" "2"
        , E.attr "y2" "6"
        ]
        []
    , E.element "line"
        [ E.attr "x1" "3"
        , E.attr "x2" "21"
        , E.attr "y1" "10"
        , E.attr "y2" "10"
        ]
        []
    ]
