-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // element // timepicker // render
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TimePicker Render — Rendering helpers for TimePicker component.
-- |
-- | Internal module containing render functions. Pure PureScript, no FFI.
-- | Uses Schema atoms for all visual properties.

module Hydrogen.Element.Compound.TimePicker.Render
  ( -- * Render Functions
    renderTimeSegment
  , renderSeparator
  , renderPeriodToggle
  , renderIncrementButton
  , renderDecrementButton
  , renderChevronUp
  , renderChevronDown
  
  -- * Props Type (for internal use)
  , TimePickerProps
  
  -- * Configuration
  , ResolvedConfig
  , resolveConfig
  
  -- * Segment Configuration
  , SegmentConfig
  ) where

import Prelude
  ( show
  , not
  , (<>)
  , (==)
  , (&&)
  )

import Data.Maybe (Maybe(Nothing, Just), maybe)

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Typography.FontSize as FontSize

import Hydrogen.Element.Compound.TimePicker.Types (Period(AM, PM))
import Hydrogen.Element.Compound.TimePicker.Format (padZero)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | TimePicker properties (duplicated here for internal use)
-- | The main module re-exports this.
type TimePickerProps msg =
  { disabled :: Boolean
  , readOnly :: Boolean
  , showIncrementButtons :: Boolean
  
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
  , onPeriodChange :: Maybe (Period -> msg)
  , onHourIncrement :: Maybe msg
  , onHourDecrement :: Maybe msg
  , onMinuteIncrement :: Maybe msg
  , onMinuteDecrement :: Maybe msg
  , onSecondIncrement :: Maybe msg
  , onSecondDecrement :: Maybe msg
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
resolveConfig :: forall msg. TimePickerProps msg -> ResolvedConfig
resolveConfig props =
  { bgColor: maybe (Color.rgb 30 30 30) (\c -> c) props.backgroundColor
  , borderCol: maybe (Color.rgb 60 60 60) (\c -> c) props.borderColor
  , textCol: maybe (Color.rgb 220 220 220) (\c -> c) props.textColor
  , mutedCol: maybe (Color.rgb 120 120 120) (\c -> c) props.mutedColor
  , primaryCol: maybe (Color.rgb 59 130 246) (\c -> c) props.primaryColor
  , primaryTextCol: maybe (Color.rgb 255 255 255) (\c -> c) props.primaryTextColor
  , radius: maybe "6px" Geometry.cornersToLegacyCss props.borderRadius
  , paddingVal: maybe "8px" show props.padding
  , borderWidthVal: maybe "1px" show props.borderWidth
  , fontSizeVal: maybe "14px" FontSize.toLegacyCss props.fontSize
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // segment configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for a time segment (hour, minute, second)
type SegmentConfig msg =
  { value :: Int
  , label :: String
  , disabled :: Boolean
  , readOnly :: Boolean
  , showButtons :: Boolean
  , onIncrement :: Maybe msg
  , onDecrement :: Maybe msg
  , onInputChange :: Maybe (String -> msg)
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // render helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a time segment (hour, minute, or second)
renderTimeSegment :: forall msg. ResolvedConfig -> SegmentConfig msg -> E.Element msg
renderTimeSegment config segment =
  E.div_
    [ E.style "display" "flex"
    , E.style "flex-direction" "column"
    , E.style "align-items" "center"
    ]
    [ -- Increment button
      if segment.showButtons && not segment.disabled
        then renderIncrementButton config segment
        else E.text ""
    
    , -- Input field
      renderSegmentInput config segment
    
    , -- Decrement button
      if segment.showButtons && not segment.disabled
        then renderDecrementButton config segment
        else E.text ""
    ]

-- | Render segment input field
renderSegmentInput :: forall msg. ResolvedConfig -> SegmentConfig msg -> E.Element msg
renderSegmentInput config segment =
  let
    inputHandler = case segment.onInputChange of
      Just handler -> [ E.onInput handler ]
      Nothing -> []
  in
    E.input_
      ( [ E.type_ "text"
        , E.value (padZero segment.value)
        , E.disabled segment.disabled
        , E.attr "readonly" (if segment.readOnly then "true" else "")
        , E.attr "inputmode" "numeric"
        , E.attr "pattern" "[0-9]*"
        , E.style "width" "40px"
        , E.style "height" "36px"
        , E.style "text-align" "center"
        , E.style "font-size" config.fontSizeVal
        , E.style "background-color" "transparent"
        , E.style "border" "none"
        , E.style "color" (Color.toLegacyCss config.textCol)
        , E.style "outline" "none"
        , E.ariaLabel segment.label
        ] <> inputHandler
      )

-- | Render increment button (chevron up)
renderIncrementButton :: forall msg. ResolvedConfig -> SegmentConfig msg -> E.Element msg
renderIncrementButton config segment =
  let
    clickHandler = case segment.onIncrement of
      Just msg -> [ E.onClick msg ]
      Nothing -> []
  in
    E.button_
      ( [ E.type_ "button"
        , E.attr "tabindex" "-1"
        , E.disabled segment.disabled
        , E.ariaLabel ("Increase " <> segment.label)
        , E.style "width" "24px"
        , E.style "height" "24px"
        , E.style "display" "flex"
        , E.style "align-items" "center"
        , E.style "justify-content" "center"
        , E.style "background" "none"
        , E.style "border" "none"
        , E.style "color" (Color.toLegacyCss config.mutedCol)
        , E.style "cursor" "pointer"
        , E.style "border-radius" "4px"
        ] <> clickHandler
      )
      [ renderChevronUp ]

-- | Render decrement button (chevron down)
renderDecrementButton :: forall msg. ResolvedConfig -> SegmentConfig msg -> E.Element msg
renderDecrementButton config segment =
  let
    clickHandler = case segment.onDecrement of
      Just msg -> [ E.onClick msg ]
      Nothing -> []
  in
    E.button_
      ( [ E.type_ "button"
        , E.attr "tabindex" "-1"
        , E.disabled segment.disabled
        , E.ariaLabel ("Decrease " <> segment.label)
        , E.style "width" "24px"
        , E.style "height" "24px"
        , E.style "display" "flex"
        , E.style "align-items" "center"
        , E.style "justify-content" "center"
        , E.style "background" "none"
        , E.style "border" "none"
        , E.style "color" (Color.toLegacyCss config.mutedCol)
        , E.style "cursor" "pointer"
        , E.style "border-radius" "4px"
        ] <> clickHandler
      )
      [ renderChevronDown ]

-- | Render separator (colon between segments)
renderSeparator :: forall msg. ResolvedConfig -> E.Element msg
renderSeparator config =
  E.span_
    [ E.style "color" (Color.toLegacyCss config.mutedCol)
    , E.style "font-weight" "500"
    , E.style "font-size" config.fontSizeVal
    ]
    [ E.text ":" ]

-- | Render AM/PM toggle
renderPeriodToggle :: forall msg. TimePickerProps msg -> ResolvedConfig -> Period -> E.Element msg
renderPeriodToggle props config period =
  E.div_
    [ E.style "display" "flex"
    , E.style "flex-direction" "column"
    , E.style "margin-left" "8px"
    , E.style "font-size" "12px"
    ]
    [ renderPeriodButton props config AM (period == AM)
    , renderPeriodButton props config PM (period == PM)
    ]

-- | Render a single period button (AM or PM)
renderPeriodButton :: forall msg. TimePickerProps msg -> ResolvedConfig -> Period -> Boolean -> E.Element msg
renderPeriodButton props config targetPeriod isActive =
  let
    clickHandler = case props.onPeriodChange of
      Just handler -> [ E.onClick (handler targetPeriod) ]
      Nothing -> []
    
    bgColor = if isActive
      then Color.toLegacyCss config.primaryCol
      else Color.toLegacyCss config.bgColor
    
    textColor = if isActive
      then Color.toLegacyCss config.primaryTextCol
      else Color.toLegacyCss config.mutedCol
    
    borderRadiusTop = if targetPeriod == AM then config.radius else "0"
    borderRadiusBottom = if targetPeriod == PM then config.radius else "0"
    
    label = case targetPeriod of
      AM -> "AM"
      PM -> "PM"
  in
    E.button_
      ( [ E.type_ "button"
        , E.disabled props.disabled
        , E.attr "aria-pressed" (show isActive)
        , E.style "padding" "4px 8px"
        , E.style "background-color" bgColor
        , E.style "color" textColor
        , E.style "border" "none"
        , E.style "cursor" (if props.disabled then "default" else "pointer")
        , E.style "border-top-left-radius" borderRadiusTop
        , E.style "border-top-right-radius" borderRadiusTop
        , E.style "border-bottom-left-radius" borderRadiusBottom
        , E.style "border-bottom-right-radius" borderRadiusBottom
        ] <> clickHandler
      )
      [ E.text label ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // icons
-- ═════════════════════════════════════════════════════════════════════════════

-- | Chevron up SVG icon
renderChevronUp :: forall msg. E.Element msg
renderChevronUp =
  E.element "svg"
    [ E.attr "width" "16"
    , E.attr "height" "16"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "fill" "none"
    , E.attr "stroke" "currentColor"
    , E.attr "stroke-width" "2"
    , E.attr "stroke-linecap" "round"
    , E.attr "stroke-linejoin" "round"
    ]
    [ E.element "polyline"
        [ E.attr "points" "18 15 12 9 6 15" ]
        []
    ]

-- | Chevron down SVG icon
renderChevronDown :: forall msg. E.Element msg
renderChevronDown =
  E.element "svg"
    [ E.attr "width" "16"
    , E.attr "height" "16"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "fill" "none"
    , E.attr "stroke" "currentColor"
    , E.attr "stroke-width" "2"
    , E.attr "stroke-linecap" "round"
    , E.attr "stroke-linejoin" "round"
    ]
    [ E.element "polyline"
        [ E.attr "points" "6 9 12 15 18 9" ]
        []
    ]
