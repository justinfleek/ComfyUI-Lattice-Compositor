-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                              // hydrogen // element // slider
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Slider — Schema-native range slider component.
-- |
-- | ## Design Philosophy
-- |
-- | This component accepts **concrete Schema atoms**, not semantic tokens.
-- | All visual properties map directly to Schema pillar atoms.
-- |
-- | ## Schema Atoms Accepted
-- |
-- | | Property             | Pillar     | Type                      | CSS Output              |
-- | |----------------------|------------|---------------------------|-------------------------|
-- | | trackColor           | Color      | Color.RGB                 | background-color (track)|
-- | | rangeColor           | Color      | Color.RGB                 | background-color (range)|
-- | | thumbColor           | Color      | Color.RGB                 | background-color (thumb)|
-- | | thumbBorderColor     | Color      | Color.RGB                 | border-color (thumb)    |
-- | | focusRingColor       | Color      | Color.RGB                 | box-shadow (focus)      |
-- | | trackHeight          | Dimension  | Device.Pixel              | height/width (track)    |
-- | | thumbSize            | Dimension  | Device.Pixel              | width, height (thumb)   |
-- | | thumbBorderWidth     | Dimension  | Device.Pixel              | border-width (thumb)    |
-- | | borderRadius         | Geometry   | Geometry.Radius           | border-radius           |
-- | | transitionDuration   | Temporal   | Temporal.Milliseconds     | transition-duration     |
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.Slider as Slider
-- | import Hydrogen.Schema.Color.RGB as Color
-- | import Hydrogen.Schema.Dimension.Device as Device
-- |
-- | -- Basic slider with brand atoms
-- | Slider.slider
-- |   [ Slider.value 50.0
-- |   , Slider.onChange HandleSliderChange
-- |   , Slider.trackColor brand.surfaceColor
-- |   , Slider.rangeColor brand.primaryColor
-- |   , Slider.thumbColor brand.backgroundColor
-- |   , Slider.thumbBorderColor brand.primaryColor
-- |   ]
-- |
-- | -- Range slider with custom sizing
-- | Slider.rangeSlider
-- |   [ Slider.rangeValue { low: 20.0, high: 80.0 }
-- |   , Slider.onRangeChange HandleRangeChange
-- |   , Slider.trackHeight (Device.px 4.0)
-- |   , Slider.thumbSize (Device.px 20.0)
-- |   ]
-- | ```

module Hydrogen.Element.Compound.Slider
  ( -- * Slider Components
    slider
  , rangeSlider
  
  -- * Props
  , SliderProps
  , SliderProp
  , RangeValue
  , defaultProps
  
  -- * State Props
  , value
  , rangeValue
  , minValue
  , maxValue
  , step
  , sliderDisabled
  , orientation
  , showTicks
  , showTooltip
  
  -- * Color Atoms
  , trackColor
  , rangeColor
  , thumbColor
  , thumbBorderColor
  , focusRingColor
  , tickColor
  , tooltipBackgroundColor
  , tooltipTextColor
  
  -- * Dimension Atoms
  , trackHeight
  , thumbSize
  , thumbBorderWidth
  
  -- * Geometry Atoms
  , borderRadius
  
  -- * Motion Atoms
  , transitionDuration
  
  -- * Behavior Props
  , onChange
  , onRangeChange
  , sliderAriaLabel
  
  -- * Types
  , Orientation(Horizontal, Vertical)
  ) where

import Prelude
  ( class Eq
  , show
  , (<>)
  , (+)
  , (-)
  , (/)
  , (*)
  , (==)
  , map
  , not
  )

import Data.Array (foldl, range)
import Data.Int (round, toNumber)
import Data.Maybe (Maybe(Nothing, Just), maybe)

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Dimension.Temporal as Temporal

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Slider orientation
data Orientation
  = Horizontal
  | Vertical

derive instance eqOrientation :: Eq Orientation

-- | Range slider value
type RangeValue =
  { low :: Number
  , high :: Number
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Slider properties
-- |
-- | All visual properties accept Schema atoms directly.
-- | Use `Maybe` for optional properties that should use defaults.
type SliderProps msg =
  { -- State
    value :: Number
  , rangeVal :: RangeValue
  , minVal :: Number
  , maxVal :: Number
  , step :: Number
  , disabled :: Boolean
  , orientation :: Orientation
  , showTicks :: Boolean
  , showTooltip :: Boolean
  
  -- Color atoms
  , trackColor :: Maybe Color.RGB
  , rangeColor :: Maybe Color.RGB
  , thumbColor :: Maybe Color.RGB
  , thumbBorderColor :: Maybe Color.RGB
  , focusRingColor :: Maybe Color.RGB
  , tickColor :: Maybe Color.RGB
  , tooltipBackgroundColor :: Maybe Color.RGB
  , tooltipTextColor :: Maybe Color.RGB
  
  -- Dimension atoms
  , trackHeight :: Maybe Device.Pixel
  , thumbSize :: Maybe Device.Pixel
  , thumbBorderWidth :: Maybe Device.Pixel
  
  -- Geometry atoms
  , borderRadius :: Maybe Geometry.Radius
  
  -- Motion atoms
  , transitionDuration :: Maybe Temporal.Milliseconds
  
  -- Behavior
  , onChange :: Maybe (Number -> msg)
  , onRangeChange :: Maybe (RangeValue -> msg)
  , ariaLabel :: String
  }

-- | Property modifier function
type SliderProp msg = SliderProps msg -> SliderProps msg

-- | Default properties
-- |
-- | Visual properties default to `Nothing` (use sensible fallbacks).
-- | This ensures sliders work with any brand without hardcoded values.
defaultProps :: forall msg. SliderProps msg
defaultProps =
  { value: 0.0
  , rangeVal: { low: 0.0, high: 100.0 }
  , minVal: 0.0
  , maxVal: 100.0
  , step: 1.0
  , disabled: false
  , orientation: Horizontal
  , showTicks: false
  , showTooltip: false
  , trackColor: Nothing
  , rangeColor: Nothing
  , thumbColor: Nothing
  , thumbBorderColor: Nothing
  , focusRingColor: Nothing
  , tickColor: Nothing
  , tooltipBackgroundColor: Nothing
  , tooltipTextColor: Nothing
  , trackHeight: Nothing
  , thumbSize: Nothing
  , thumbBorderWidth: Nothing
  , borderRadius: Nothing
  , transitionDuration: Nothing
  , onChange: Nothing
  , onRangeChange: Nothing
  , ariaLabel: "Slider"
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set slider value
value :: forall msg. Number -> SliderProp msg
value v props = props { value = v }

-- | Set range slider value
rangeValue :: forall msg. RangeValue -> SliderProp msg
rangeValue v props = props { rangeVal = v }

-- | Set minimum value
minValue :: forall msg. Number -> SliderProp msg
minValue v props = props { minVal = v }

-- | Set maximum value
maxValue :: forall msg. Number -> SliderProp msg
maxValue v props = props { maxVal = v }

-- | Set step increment
step :: forall msg. Number -> SliderProp msg
step v props = props { step = v }

-- | Set disabled state
sliderDisabled :: forall msg. Boolean -> SliderProp msg
sliderDisabled d props = props { disabled = d }

-- | Set orientation
orientation :: forall msg. Orientation -> SliderProp msg
orientation o props = props { orientation = o }

-- | Show tick marks
showTicks :: forall msg. Boolean -> SliderProp msg
showTicks s props = props { showTicks = s }

-- | Show tooltip on hover/focus
showTooltip :: forall msg. Boolean -> SliderProp msg
showTooltip s props = props { showTooltip = s }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: color
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set track background color (Color.RGB atom)
trackColor :: forall msg. Color.RGB -> SliderProp msg
trackColor c props = props { trackColor = Just c }

-- | Set filled range color (Color.RGB atom)
rangeColor :: forall msg. Color.RGB -> SliderProp msg
rangeColor c props = props { rangeColor = Just c }

-- | Set thumb background color (Color.RGB atom)
thumbColor :: forall msg. Color.RGB -> SliderProp msg
thumbColor c props = props { thumbColor = Just c }

-- | Set thumb border color (Color.RGB atom)
thumbBorderColor :: forall msg. Color.RGB -> SliderProp msg
thumbBorderColor c props = props { thumbBorderColor = Just c }

-- | Set focus ring color (Color.RGB atom)
focusRingColor :: forall msg. Color.RGB -> SliderProp msg
focusRingColor c props = props { focusRingColor = Just c }

-- | Set tick mark color (Color.RGB atom)
tickColor :: forall msg. Color.RGB -> SliderProp msg
tickColor c props = props { tickColor = Just c }

-- | Set tooltip background color (Color.RGB atom)
tooltipBackgroundColor :: forall msg. Color.RGB -> SliderProp msg
tooltipBackgroundColor c props = props { tooltipBackgroundColor = Just c }

-- | Set tooltip text color (Color.RGB atom)
tooltipTextColor :: forall msg. Color.RGB -> SliderProp msg
tooltipTextColor c props = props { tooltipTextColor = Just c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // prop builders: dimension
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set track height/width (Device.Pixel atom)
trackHeight :: forall msg. Device.Pixel -> SliderProp msg
trackHeight h props = props { trackHeight = Just h }

-- | Set thumb size (Device.Pixel atom)
thumbSize :: forall msg. Device.Pixel -> SliderProp msg
thumbSize s props = props { thumbSize = Just s }

-- | Set thumb border width (Device.Pixel atom)
thumbBorderWidth :: forall msg. Device.Pixel -> SliderProp msg
thumbBorderWidth w props = props { thumbBorderWidth = Just w }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: geometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set border radius (Geometry.Radius atom)
borderRadius :: forall msg. Geometry.Radius -> SliderProp msg
borderRadius r props = props { borderRadius = Just r }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // prop builders: motion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set transition duration (Temporal.Milliseconds atom)
transitionDuration :: forall msg. Temporal.Milliseconds -> SliderProp msg
transitionDuration d props = props { transitionDuration = Just d }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: behavior
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set value change handler
onChange :: forall msg. (Number -> msg) -> SliderProp msg
onChange handler props = props { onChange = Just handler }

-- | Set range change handler
onRangeChange :: forall msg. (RangeValue -> msg) -> SliderProp msg
onRangeChange handler props = props { onRangeChange = Just handler }

-- | Set ARIA label
sliderAriaLabel :: forall msg. String -> SliderProp msg
sliderAriaLabel l props = props { ariaLabel = l }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // defaults
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default track color (neutral gray)
defaultTrackColor :: Color.RGB
defaultTrackColor = Color.rgb 229 231 235

-- | Default range color (blue)
defaultRangeColor :: Color.RGB
defaultRangeColor = Color.rgb 59 130 246

-- | Default thumb color (white)
defaultThumbColor :: Color.RGB
defaultThumbColor = Color.rgb 255 255 255

-- | Default thumb border color (same as range)
defaultThumbBorderColor :: Color.RGB
defaultThumbBorderColor = Color.rgb 59 130 246

-- | Default focus ring color (blue with transparency handled via box-shadow)
defaultFocusRingColor :: Color.RGB
defaultFocusRingColor = Color.rgb 59 130 246

-- | Default tick color (muted)
defaultTickColor :: Color.RGB
defaultTickColor = Color.rgb 156 163 175

-- | Default tooltip background (dark)
defaultTooltipBgColor :: Color.RGB
defaultTooltipBgColor = Color.rgb 31 41 55

-- | Default tooltip text (white)
defaultTooltipTextColor :: Color.RGB
defaultTooltipTextColor = Color.rgb 255 255 255

-- | Default track height
defaultTrackHeight :: Device.Pixel
defaultTrackHeight = Device.px 8.0

-- | Default thumb size
defaultThumbSize :: Device.Pixel
defaultThumbSize = Device.px 20.0

-- | Default thumb border width
defaultThumbBorderWidth :: Device.Pixel
defaultThumbBorderWidth = Device.px 2.0

-- | Default border radius (full/pill)
defaultBorderRadius :: Geometry.Radius
defaultBorderRadius = Geometry.full

-- | Default transition duration
defaultTransitionDuration :: Temporal.Milliseconds
defaultTransitionDuration = Temporal.ms 150.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate percentage position
toPercent :: Number -> Number -> Number -> Number
toPercent minV maxV val =
  ((val - minV) / (maxV - minV)) * 100.0

-- | Show a number as percentage string
showPercent :: Number -> String
showPercent n = show n <> "%"

-- | Get effective color with fallback
getColor :: Maybe Color.RGB -> Color.RGB -> Color.RGB
getColor maybeColor fallback = maybe fallback (\c -> c) maybeColor

-- | Get effective pixel with fallback
getPixel :: Maybe Device.Pixel -> Device.Pixel -> Device.Pixel
getPixel maybePixel fallback = maybe fallback (\p -> p) maybePixel

-- | Get effective radius with fallback
getRadius :: Maybe Geometry.Radius -> Geometry.Radius -> Geometry.Radius
getRadius maybeRadius fallback = maybe fallback (\r -> r) maybeRadius

-- | Get effective duration with fallback
getDuration :: Maybe Temporal.Milliseconds -> Temporal.Milliseconds -> Temporal.Milliseconds
getDuration maybeDuration fallback = maybe fallback (\d -> d) maybeDuration

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // components
-- ═════════════════════════════════════════════════════════════════════════════

-- | Single value slider
-- |
-- | A slider for selecting a single numeric value.
-- | Pure Element — renders to DOM, Halogen, Static HTML, or any target.
slider :: forall msg. Array (SliderProp msg) -> E.Element msg
slider propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    isVertical = props.orientation == Vertical
    percent = toPercent props.minVal props.maxVal props.value
    
    -- Resolve colors
    trkColor = getColor props.trackColor defaultTrackColor
    rngColor = getColor props.rangeColor defaultRangeColor
    tmbColor = getColor props.thumbColor defaultThumbColor
    tmbBorderColor = getColor props.thumbBorderColor defaultThumbBorderColor
    
    -- Resolve dimensions
    trkHeight = getPixel props.trackHeight defaultTrackHeight
    tmbSize = getPixel props.thumbSize defaultThumbSize
    tmbBorderW = getPixel props.thumbBorderWidth defaultThumbBorderWidth
    
    -- Resolve geometry
    radius = getRadius props.borderRadius defaultBorderRadius
    
    -- Resolve motion
    duration = getDuration props.transitionDuration defaultTransitionDuration
    
    -- Container styles
    containerStyles = 
      [ E.style "position" "relative"
      , E.style "display" "flex"
      , E.style "touch-action" "none"
      , E.style "user-select" "none"
      ] <> (if isVertical
              then [ E.style "flex-direction" "column"
                   , E.style "align-items" "center"
                   , E.style "height" "100%"
                   , E.style "width" (show tmbSize)
                   ]
              else [ E.style "align-items" "center"
                   , E.style "width" "100%"
                   ])
    
    -- Track styles
    trackStyles =
      [ E.style "position" "relative"
      , E.style "background-color" (Color.toLegacyCss trkColor)
      , E.style "border-radius" (Geometry.toLegacyCss radius)
      ] <> (if isVertical
              then [ E.style "width" (show trkHeight)
                   , E.style "height" "100%"
                   ]
              else [ E.style "height" (show trkHeight)
                   , E.style "width" "100%"
                   ])
    
    -- Range (filled portion) styles
    rangeStyles =
      [ E.style "position" "absolute"
      , E.style "background-color" (Color.toLegacyCss rngColor)
      , E.style "border-radius" (Geometry.toLegacyCss radius)
      ] <> (if isVertical
              then [ E.style "width" "100%"
                   , E.style "bottom" "0"
                   , E.style "height" (showPercent percent)
                   ]
              else [ E.style "height" "100%"
                   , E.style "width" (showPercent percent)
                   ])
    
    -- Thumb styles
    thumbStyles =
      [ E.style "position" "absolute"
      , E.style "display" "block"
      , E.style "width" (show tmbSize)
      , E.style "height" (show tmbSize)
      , E.style "border-radius" "50%"
      , E.style "border-style" "solid"
      , E.style "border-width" (show tmbBorderW)
      , E.style "border-color" (Color.toLegacyCss tmbBorderColor)
      , E.style "background-color" (Color.toLegacyCss tmbColor)
      , E.style "cursor" (if props.disabled then "not-allowed" else "pointer")
      , E.style "transition" ("all " <> show duration <> " ease-out")
      , E.style "outline" "none"
      ] <> (if isVertical
              then [ E.style "left" "50%"
                   , E.style "transform" "translate(-50%, 50%)"
                   , E.style "bottom" (showPercent percent)
                   ]
              else [ E.style "top" "50%"
                   , E.style "transform" "translate(-50%, -50%)"
                   , E.style "left" (showPercent percent)
                   ])
    
    -- Disabled styles
    disabledStyles = if props.disabled
      then [ E.style "opacity" "0.5", E.style "pointer-events" "none" ]
      else []
    
    tabIndexVal = if props.disabled then "-1" else "0"
  in
    E.div_
      (containerStyles <> [ E.dataAttr "orientation" (if isVertical then "vertical" else "horizontal") ])
      [ E.div_
          trackStyles
          [ E.div_ rangeStyles []
          , E.div_
              ( thumbStyles <> disabledStyles <>
                [ E.attr "tabindex" tabIndexVal
                , E.role "slider"
                , E.attr "aria-valuenow" (show props.value)
                , E.attr "aria-valuemin" (show props.minVal)
                , E.attr "aria-valuemax" (show props.maxVal)
                , E.attr "aria-disabled" (if props.disabled then "true" else "false")
                , E.ariaLabel props.ariaLabel
                ]
              )
              ( if props.showTooltip
                  then [ renderTooltip props props.value ]
                  else []
              )
          ]
      , if props.showTicks
          then renderTicks props
          else E.text ""
      ]

-- | Range slider (dual thumbs)
-- |
-- | A slider for selecting a range of values.
-- | Pure Element — renders to DOM, Halogen, Static HTML, or any target.
rangeSlider :: forall msg. Array (SliderProp msg) -> E.Element msg
rangeSlider propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    isVertical = props.orientation == Vertical
    lowPercent = toPercent props.minVal props.maxVal props.rangeVal.low
    highPercent = toPercent props.minVal props.maxVal props.rangeVal.high
    
    -- Resolve colors
    trkColor = getColor props.trackColor defaultTrackColor
    rngColor = getColor props.rangeColor defaultRangeColor
    tmbColor = getColor props.thumbColor defaultThumbColor
    tmbBorderColor = getColor props.thumbBorderColor defaultThumbBorderColor
    
    -- Resolve dimensions
    trkHeight = getPixel props.trackHeight defaultTrackHeight
    tmbSize = getPixel props.thumbSize defaultThumbSize
    tmbBorderW = getPixel props.thumbBorderWidth defaultThumbBorderWidth
    
    -- Resolve geometry
    radius = getRadius props.borderRadius defaultBorderRadius
    
    -- Resolve motion
    duration = getDuration props.transitionDuration defaultTransitionDuration
    
    -- Container styles
    containerStyles = 
      [ E.style "position" "relative"
      , E.style "display" "flex"
      , E.style "touch-action" "none"
      , E.style "user-select" "none"
      ] <> (if isVertical
              then [ E.style "flex-direction" "column"
                   , E.style "align-items" "center"
                   , E.style "height" "100%"
                   , E.style "width" (show tmbSize)
                   ]
              else [ E.style "align-items" "center"
                   , E.style "width" "100%"
                   ])
    
    -- Track styles
    trackStyles =
      [ E.style "position" "relative"
      , E.style "background-color" (Color.toLegacyCss trkColor)
      , E.style "border-radius" (Geometry.toLegacyCss radius)
      ] <> (if isVertical
              then [ E.style "width" (show trkHeight)
                   , E.style "height" "100%"
                   ]
              else [ E.style "height" (show trkHeight)
                   , E.style "width" "100%"
                   ])
    
    -- Range (filled portion) styles
    rangeStyles =
      [ E.style "position" "absolute"
      , E.style "background-color" (Color.toLegacyCss rngColor)
      , E.style "border-radius" (Geometry.toLegacyCss radius)
      ] <> (if isVertical
              then [ E.style "width" "100%"
                   , E.style "bottom" (showPercent lowPercent)
                   , E.style "height" (showPercent (highPercent - lowPercent))
                   ]
              else [ E.style "height" "100%"
                   , E.style "left" (showPercent lowPercent)
                   , E.style "width" (showPercent (highPercent - lowPercent))
                   ])
    
    -- Build thumb styles for a given position
    buildThumbStyles :: Number -> Array (E.Attribute msg)
    buildThumbStyles pct =
      [ E.style "position" "absolute"
      , E.style "display" "block"
      , E.style "width" (show tmbSize)
      , E.style "height" (show tmbSize)
      , E.style "border-radius" "50%"
      , E.style "border-style" "solid"
      , E.style "border-width" (show tmbBorderW)
      , E.style "border-color" (Color.toLegacyCss tmbBorderColor)
      , E.style "background-color" (Color.toLegacyCss tmbColor)
      , E.style "cursor" (if props.disabled then "not-allowed" else "pointer")
      , E.style "transition" ("all " <> show duration <> " ease-out")
      , E.style "outline" "none"
      ] <> (if isVertical
              then [ E.style "left" "50%"
                   , E.style "transform" "translate(-50%, 50%)"
                   , E.style "bottom" (showPercent pct)
                   ]
              else [ E.style "top" "50%"
                   , E.style "transform" "translate(-50%, -50%)"
                   , E.style "left" (showPercent pct)
                   ])
    
    -- Disabled styles
    disabledStyles = if props.disabled
      then [ E.style "opacity" "0.5", E.style "pointer-events" "none" ]
      else []
    
    tabIndexVal = if props.disabled then "-1" else "0"
  in
    E.div_
      (containerStyles <> [ E.dataAttr "orientation" (if isVertical then "vertical" else "horizontal") ])
      [ E.div_
          trackStyles
          [ E.div_ rangeStyles []
          -- Low thumb
          , E.div_
              ( buildThumbStyles lowPercent <> disabledStyles <>
                [ E.dataAttr "thumb" "low"
                , E.attr "tabindex" tabIndexVal
                , E.role "slider"
                , E.attr "aria-valuenow" (show props.rangeVal.low)
                , E.attr "aria-valuemin" (show props.minVal)
                , E.attr "aria-valuemax" (show props.rangeVal.high)
                , E.attr "aria-disabled" (if props.disabled then "true" else "false")
                , E.ariaLabel "Minimum value"
                ]
              )
              ( if props.showTooltip
                  then [ renderTooltip props props.rangeVal.low ]
                  else []
              )
          -- High thumb
          , E.div_
              ( buildThumbStyles highPercent <> disabledStyles <>
                [ E.dataAttr "thumb" "high"
                , E.attr "tabindex" tabIndexVal
                , E.role "slider"
                , E.attr "aria-valuenow" (show props.rangeVal.high)
                , E.attr "aria-valuemin" (show props.rangeVal.low)
                , E.attr "aria-valuemax" (show props.maxVal)
                , E.attr "aria-disabled" (if props.disabled then "true" else "false")
                , E.ariaLabel "Maximum value"
                ]
              )
              ( if props.showTooltip
                  then [ renderTooltip props props.rangeVal.high ]
                  else []
              )
          ]
      , if props.showTicks
          then renderTicks props
          else E.text ""
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // supporting elements
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render tooltip
renderTooltip :: forall msg. SliderProps msg -> Number -> E.Element msg
renderTooltip props val =
  let
    bgColor = getColor props.tooltipBackgroundColor defaultTooltipBgColor
    textColor = getColor props.tooltipTextColor defaultTooltipTextColor
  in
    E.div_
      [ E.style "position" "absolute"
      , E.style "top" "-32px"
      , E.style "left" "50%"
      , E.style "transform" "translateX(-50%)"
      , E.style "padding" "4px 8px"
      , E.style "background-color" (Color.toLegacyCss bgColor)
      , E.style "color" (Color.toLegacyCss textColor)
      , E.style "font-size" "12px"
      , E.style "border-radius" "4px"
      , E.style "white-space" "nowrap"
      , E.style "pointer-events" "none"
      ]
      [ E.text (show (round val)) ]

-- | Render tick marks
renderTicks :: forall msg. SliderProps msg -> E.Element msg
renderTicks props =
  let
    isVertical = props.orientation == Vertical
    numSteps = round ((props.maxVal - props.minVal) / props.step)
    ticks = range 0 numSteps
    tckColor = getColor props.tickColor defaultTickColor
    
    containerStyles =
      [ E.style "position" "absolute"
      , E.style "display" "flex"
      , E.style "justify-content" "space-between"
      ] <> (if isVertical
              then [ E.style "left" "100%"
                   , E.style "margin-left" "8px"
                   , E.style "height" "100%"
                   , E.style "flex-direction" "column"
                   ]
              else [ E.style "top" "100%"
                   , E.style "margin-top" "8px"
                   , E.style "width" "100%"
                   ])
    
    renderTick :: Int -> E.Element msg
    renderTick idx =
      let
        tickVal = props.minVal + (toNumber idx * props.step)
      in
        E.div_
          [ E.style "display" "flex"
          , E.style "flex-direction" "column"
          , E.style "align-items" "center"
          ]
          [ E.div_
              [ E.style "width" "2px"
              , E.style "height" "4px"
              , E.style "background-color" (Color.toLegacyCss tckColor)
              ]
              []
          , E.span_
              [ E.style "font-size" "10px"
              , E.style "color" (Color.toLegacyCss tckColor)
              , E.style "margin-top" "4px"
              ]
              [ E.text (show (round tickVal)) ]
          ]
  in
    E.div_ containerStyles (map renderTick ticks)
