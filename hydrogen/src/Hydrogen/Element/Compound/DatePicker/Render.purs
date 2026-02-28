-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // element // datepicker // render
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | DatePicker Render — Rendering helpers for DatePicker component.
-- |
-- | Internal module containing render functions. Pure PureScript, no FFI.

module Hydrogen.Element.Compound.DatePicker.Render
  ( -- * Render Functions
    renderInput
  , renderCalendarIcon
  , renderClearButton
  , renderErrorMessage
  , renderCalendarPopup
  , renderFooter
  , renderTodayButton
  , renderClearButtonFooter
  
  -- * Types (re-exported for internal use)
  , ResolvedConfig
  , resolveConfig
  ) where

import Prelude
  ( show
  , map
  , (<>)
  , (&&)
  , (||)
  )

import Data.Maybe (Maybe(Nothing, Just), maybe, isJust)

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Typography.FontSize as FontSize

import Hydrogen.Element.Compound.Calendar as Calendar
import Hydrogen.Element.Compound.DatePicker.Types (DateFormat)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | DatePicker properties (duplicated here for internal use)
-- | The main module re-exports this.
type DatePickerProps msg =
  { value :: Maybe Calendar.CalendarDate
  , inputValue :: String
  , dateFormat :: DateFormat
  , placeholder :: String
  , disabled :: Boolean
  , readOnly :: Boolean
  , required :: Boolean
  , isOpen :: Boolean
  , hasError :: Boolean
  , errorMessage :: Maybe String
  , minDate :: Maybe Calendar.CalendarDate
  , maxDate :: Maybe Calendar.CalendarDate
  , disabledDates :: Calendar.CalendarDate -> Boolean
  , weekStartsOn :: Calendar.WeekStart
  , showTodayButton :: Boolean
  , showClearButton :: Boolean
  , showCalendarIcon :: Boolean
  , backgroundColor :: Maybe Color.RGB
  , borderColor :: Maybe Color.RGB
  , textColor :: Maybe Color.RGB
  , placeholderColor :: Maybe Color.RGB
  , errorColor :: Maybe Color.RGB
  , focusColor :: Maybe Color.RGB
  , borderRadius :: Maybe Geometry.Corners
  , padding :: Maybe Device.Pixel
  , borderWidth :: Maybe Device.Pixel
  , fontSize :: Maybe FontSize.FontSize
  , onSelect :: Maybe (Calendar.CalendarDate -> msg)
  , onInputChange :: Maybe (String -> msg)
  , onOpen :: Maybe msg
  , onClose :: Maybe msg
  , onClear :: Maybe msg
  , onToday :: Maybe msg
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // resolved config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Resolved configuration with defaults applied
type ResolvedConfig =
  { bgColor :: Color.RGB
  , borderCol :: Color.RGB
  , textCol :: Color.RGB
  , placeholderCol :: Color.RGB
  , errorCol :: Color.RGB
  , focusCol :: Color.RGB
  , radius :: String
  , paddingVal :: String
  , borderWidthVal :: String
  , fontSizeVal :: String
  }

-- | Resolve props to config with defaults
resolveConfig :: forall msg. DatePickerProps msg -> ResolvedConfig
resolveConfig props =
  { bgColor: maybe (Color.rgb 30 30 30) (\c -> c) props.backgroundColor
  , borderCol: maybe (Color.rgb 60 60 60) (\c -> c) props.borderColor
  , textCol: maybe (Color.rgb 220 220 220) (\c -> c) props.textColor
  , placeholderCol: maybe (Color.rgb 120 120 120) (\c -> c) props.placeholderColor
  , errorCol: maybe (Color.rgb 239 68 68) (\c -> c) props.errorColor
  , focusCol: maybe (Color.rgb 59 130 246) (\c -> c) props.focusColor
  , radius: maybe "6px" Geometry.cornersToLegacyCss props.borderRadius
  , paddingVal: maybe "8px 12px" show props.padding
  , borderWidthVal: maybe "1px" show props.borderWidth
  , fontSizeVal: maybe "14px" FontSize.toLegacyCss props.fontSize
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // render helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render the input field
renderInput :: forall msg. DatePickerProps msg -> ResolvedConfig -> String -> String -> E.Element msg
renderInput props config displayValue currentBorderColor =
  let
    paddingLeft = if props.showCalendarIcon then "36px" else config.paddingVal
    paddingRight = if props.showClearButton && isJust props.value then "36px" else config.paddingVal
    inputHandler = case props.onInputChange of
      Just handler -> [ E.onInput handler ]
      Nothing -> []
  in
    E.input_
      ( [ E.type_ "text"
        , E.value displayValue
        , E.placeholder props.placeholder
        , E.disabled props.disabled
        , E.attr "readonly" (if props.readOnly then "true" else "")
        , E.style "width" "100%"
        , E.style "height" "40px"
        , E.style "padding-left" paddingLeft
        , E.style "padding-right" paddingRight
        , E.style "background-color" (Color.toLegacyCss config.bgColor)
        , E.style "color" (Color.toLegacyCss config.textCol)
        , E.style "border-style" "solid"
        , E.style "border-width" config.borderWidthVal
        , E.style "border-color" currentBorderColor
        , E.style "border-radius" config.radius
        , E.style "font-size" config.fontSizeVal
        , E.style "outline" "none"
        , E.role "combobox"
        , E.ariaLabel "Date input"
        , E.attr "aria-expanded" (show props.isOpen)
        ] <> inputHandler
      )

-- | Render calendar icon
renderCalendarIcon :: forall msg. ResolvedConfig -> E.Element msg
renderCalendarIcon config =
  E.div_
    [ E.style "position" "absolute"
    , E.style "left" "12px"
    , E.style "top" "50%"
    , E.style "transform" "translateY(-50%)"
    , E.style "color" (Color.toLegacyCss config.placeholderCol)
    , E.style "pointer-events" "none"
    ]
    [ E.text "📅" ]

-- | Render clear button
renderClearButton :: forall msg. DatePickerProps msg -> ResolvedConfig -> E.Element msg
renderClearButton props config =
  let
    clickHandler = case props.onClear of
      Just msg -> [ E.onClick msg ]
      Nothing -> []
  in
    E.button_
      ( [ E.type_ "button"
        , E.style "position" "absolute"
        , E.style "right" "8px"
        , E.style "top" "50%"
        , E.style "transform" "translateY(-50%)"
        , E.style "background" "none"
        , E.style "border" "none"
        , E.style "color" (Color.toLegacyCss config.placeholderCol)
        , E.style "cursor" "pointer"
        , E.style "padding" "4px"
        , E.ariaLabel "Clear date"
        ] <> clickHandler
      )
      [ E.text "✕" ]

-- | Render error message
renderErrorMessage :: forall msg. ResolvedConfig -> String -> E.Element msg
renderErrorMessage config msg =
  E.p_
    [ E.style "margin-top" "4px"
    , E.style "font-size" "12px"
    , E.style "color" (Color.toLegacyCss config.errorCol)
    ]
    [ E.text msg ]

-- | Render calendar popup
renderCalendarPopup :: forall msg. DatePickerProps msg -> ResolvedConfig -> E.Element msg
renderCalendarPopup props config =
  let
    calendarSelectHandler = map (\handler -> Calendar.onSelect handler) props.onSelect
    calendarProps = case calendarSelectHandler of
      Just h -> [ h ]
      Nothing -> []
  in
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
      , E.role "dialog"
      , E.attr "aria-modal" "true"
      ]
      [ Calendar.calendar
          ( [ Calendar.selected props.value
            , Calendar.weekStartsOn props.weekStartsOn
            , Calendar.disabledDates props.disabledDates
            ] <> calendarProps
            <> (case props.minDate of
                  Just d -> [ Calendar.minDate d ]
                  Nothing -> [])
            <> (case props.maxDate of
                  Just d -> [ Calendar.maxDate d ]
                  Nothing -> [])
          )
      , if props.showTodayButton || props.showClearButton
          then renderFooter props config
          else E.text ""
      ]

-- | Render calendar footer with action buttons
renderFooter :: forall msg. DatePickerProps msg -> ResolvedConfig -> E.Element msg
renderFooter props config =
  E.div_
    [ E.style "border-top" ("1px solid " <> Color.toLegacyCss config.borderCol)
    , E.style "padding" "8px 12px"
    , E.style "display" "flex"
    , E.style "justify-content" "space-between"
    ]
    [ if props.showTodayButton
        then renderTodayButton props config
        else E.text ""
    , if props.showClearButton
        then renderClearButtonFooter props config
        else E.text ""
    ]

-- | Render Today button in footer
renderTodayButton :: forall msg. DatePickerProps msg -> ResolvedConfig -> E.Element msg
renderTodayButton props config =
  let
    clickHandler = case props.onToday of
      Just msg -> [ E.onClick msg ]
      Nothing -> []
  in
    E.button_
      ( [ E.type_ "button"
        , E.style "font-size" "14px"
        , E.style "color" (Color.toLegacyCss config.focusCol)
        , E.style "background" "none"
        , E.style "border" "none"
        , E.style "cursor" "pointer"
        , E.style "text-decoration" "underline"
        ] <> clickHandler
      )
      [ E.text "Today" ]

-- | Render Clear button in footer
renderClearButtonFooter :: forall msg. DatePickerProps msg -> ResolvedConfig -> E.Element msg
renderClearButtonFooter props config =
  let
    clickHandler = case props.onClear of
      Just msg -> [ E.onClick msg ]
      Nothing -> []
  in
    E.button_
      ( [ E.type_ "button"
        , E.style "font-size" "14px"
        , E.style "color" (Color.toLegacyCss config.placeholderCol)
        , E.style "background" "none"
        , E.style "border" "none"
        , E.style "cursor" "pointer"
        ] <> clickHandler
      )
      [ E.text "Clear" ]
