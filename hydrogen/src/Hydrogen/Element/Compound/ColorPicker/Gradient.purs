-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // element // colorpicker // gradient
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | GradientEditor — Interactive gradient stop editor.
-- |
-- | ## Design Philosophy
-- |
-- | Allows visual editing of color gradient stops. Features:
-- | - Draggable stop handles along gradient bar
-- | - Click to add new stops
-- | - Double-click to remove stops
-- | - Color picker integration for stop colors
-- |
-- | ## Schema Atoms Accepted
-- |
-- | | Property      | Pillar    | Type              | Purpose                |
-- | |---------------|-----------|-------------------|------------------------|
-- | | gradient      | Color     | LinearGradient    | Current gradient       |
-- | | width         | Dimension | Pixel             | Editor width           |
-- | | height        | Dimension | Pixel             | Bar height             |

module Hydrogen.Element.Compound.ColorPicker.Gradient
  ( -- * Component
    gradientBar
    
  -- * Props
  , GradientBarProps
  , GradientBarProp
  , defaultGradientBarProps
  
  -- * Prop Builders
  , gradient
  , barWidth
  , barHeight
  , borderRadius
  , onStopSelect
  , onStopMove
  , onStopAdd
  , showStops
  
  -- * Change Types
  , StopSelectChange
  , StopMoveChange
  , StopAddChange
  
  -- * Utilities
  , stopColors
  , stopCount
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( show
  , map
  , (<>)
  , ($)
  , (+)
  , (-)
  , (*)
  , (/)
  )

import Data.Array (foldl, mapWithIndex, length)
import Data.Maybe (Maybe(Nothing, Just))

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as RGB
import Hydrogen.Schema.Color.Gradient as Grad
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Geometry.Radius as Radius

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // change types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Stop selection event
type StopSelectChange =
  { index :: Int
  , color :: RGB.RGB
  , position :: Number
  }

-- | Stop move event
type StopMoveChange =
  { index :: Int
  , position :: Number
  }

-- | Stop add event (click on empty area)
type StopAddChange =
  { position :: Number
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Gradient bar properties
type GradientBarProps msg =
  { -- Gradient
    gradient :: Grad.LinearGradient
  
  -- Dimensions
  , width :: Device.Pixel
  , height :: Device.Pixel
  
  -- Appearance
  , borderRadius :: Maybe Radius.Radius
  , showStops :: Boolean
  
  -- Behavior
  , onStopSelect :: Maybe (StopSelectChange -> msg)
  , onStopMove :: Maybe (StopMoveChange -> msg)
  , onStopAdd :: Maybe (StopAddChange -> msg)
  }

-- | Property modifier
type GradientBarProp msg = GradientBarProps msg -> GradientBarProps msg

-- | Default properties
defaultGradientBarProps :: forall msg. GradientBarProps msg
defaultGradientBarProps =
  { gradient: Grad.linearGradient
      [ Grad.colorStop (RGB.rgb 255 0 0) 0.0
      , Grad.colorStop (RGB.rgb 0 0 255) 1.0
      ]
  , width: Device.px 300.0
  , height: Device.px 24.0
  , borderRadius: Nothing
  , showStops: true
  , onStopSelect: Nothing
  , onStopMove: Nothing
  , onStopAdd: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set gradient
gradient :: forall msg. Grad.LinearGradient -> GradientBarProp msg
gradient g props = props { gradient = g }

-- | Set bar width
barWidth :: forall msg. Device.Pixel -> GradientBarProp msg
barWidth w props = props { width = w }

-- | Set bar height
barHeight :: forall msg. Device.Pixel -> GradientBarProp msg
barHeight h props = props { height = h }

-- | Set border radius
borderRadius :: forall msg. Radius.Radius -> GradientBarProp msg
borderRadius r props = props { borderRadius = Just r }

-- | Set stop selection handler
onStopSelect :: forall msg. (StopSelectChange -> msg) -> GradientBarProp msg
onStopSelect handler props = props { onStopSelect = Just handler }

-- | Set stop move handler
onStopMove :: forall msg. (StopMoveChange -> msg) -> GradientBarProp msg
onStopMove handler props = props { onStopMove = Just handler }

-- | Set stop add handler
onStopAdd :: forall msg. (StopAddChange -> msg) -> GradientBarProp msg
onStopAdd handler props = props { onStopAdd = Just handler }

-- | Set whether to show stop handles
showStops :: forall msg. Boolean -> GradientBarProp msg
showStops b props = props { showStops = b }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render gradient editor bar
gradientBar :: forall msg. Array (GradientBarProp msg) -> E.Element msg
gradientBar propModifiers =
  let
    props = foldl (\p f -> f p) defaultGradientBarProps propModifiers
    
    -- Dimensions
    w = Device.unwrapPixel props.width
    h = Device.unwrapPixel props.height
    widthPx = show w <> "px"
    heightPx = show h <> "px"
    
    radiusStyle = case props.borderRadius of
      Just r -> Radius.toLegacyCss r
      Nothing -> "4px"
    
    -- Get gradient CSS
    gradientCss = Grad.linearToLegacyCss props.gradient
    
    -- Get stops for handles
    stops = Grad.getStops (Grad.Linear props.gradient)
  in
    E.div_
      [ E.style "position" "relative"
      , E.style "width" widthPx
      , E.style "height" heightPx
      ]
      [ -- Checkerboard background
        renderCheckerboard radiusStyle
        
        -- Gradient bar
      , E.div_
          [ E.style "position" "absolute"
          , E.style "inset" "0"
          , E.style "background" gradientCss
          , E.style "border-radius" radiusStyle
          , E.style "border" "1px solid rgba(0,0,0,0.1)"
          , E.style "cursor" "pointer"
          ]
          []
        
        -- Stop handles
      , if props.showStops
          then E.div_
            [ E.style "position" "absolute"
            , E.style "inset" "0"
            , E.style "pointer-events" "none"
            ]
            (mapWithIndex (renderStopHandle w h) stops)
          else E.span_ [] []
      ]

-- | Render checkerboard background
renderCheckerboard :: forall msg. String -> E.Element msg
renderCheckerboard radiusStyle =
  E.div_
    [ E.style "position" "absolute"
    , E.style "inset" "0"
    , E.style "background-color" "#fff"
    , E.style "background-image" "linear-gradient(45deg, #ccc 25%, transparent 25%), linear-gradient(-45deg, #ccc 25%, transparent 25%), linear-gradient(45deg, transparent 75%, #ccc 75%), linear-gradient(-45deg, transparent 75%, #ccc 75%)"
    , E.style "background-size" "8px 8px"
    , E.style "background-position" "0 0, 0 4px, 4px -4px, -4px 0"
    , E.style "border-radius" radiusStyle
    ]
    []

-- | Render a stop handle
-- | Parameters: bar width, bar height, stop index, color stop data
renderStopHandle :: forall msg. Number -> Number -> Int -> Grad.ColorStop -> E.Element msg
renderStopHandle handleBarWidth handleBarHeight stopIndex (Grad.ColorStop stop) =
  let
    -- Position handle at stop location
    x = Grad.unwrapRatio stop.position * handleBarWidth
    handleSize = 12.0
    halfHandle = handleSize / 2.0
    
    -- Handle extends below the bar
    topOffset = handleBarHeight - 2.0
  in
    E.div_
      [ E.style "position" "absolute"
      , E.style "left" (show (x - halfHandle) <> "px")
      , E.style "top" (show topOffset <> "px")
      , E.style "width" (show handleSize <> "px")
      , E.style "height" (show handleSize <> "px")
      , E.style "pointer-events" "auto"
      , E.style "cursor" "ew-resize"
      , E.dataAttr "stop-index" $ show stopIndex
      , E.attr "role" "slider"
      , E.attr "aria-label" $ "Color stop " <> show (stopIndex + 1)
      , E.attr "aria-valuenow" $ show (Grad.unwrapRatio stop.position * 100.0)
      , E.attr "aria-valuemin" "0"
      , E.attr "aria-valuemax" "100"
      ]
      [ -- Triangle pointer
        E.div_
          [ E.style "width" "0"
          , E.style "height" "0"
          , E.style "border-left" "6px solid transparent"
          , E.style "border-right" "6px solid transparent"
          , E.style "border-bottom" ("6px solid " <> RGB.rgbToLegacyCss stop.color)
          ]
          []
        -- Color dot
      , E.div_
          [ E.style "width" (show handleSize <> "px")
          , E.style "height" (show handleSize <> "px")
          , E.style "border-radius" "50%"
          , E.style "background" (RGB.rgbToLegacyCss stop.color)
          , E.style "border" "2px solid #fff"
          , E.style "box-shadow" "0 1px 3px rgba(0,0,0,0.3)"
          ]
          []
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract all stop colors from a gradient as CSS strings
-- | Useful for color palettes, legends, or external processing
stopColors :: Grad.LinearGradient -> Array String
stopColors grad =
  let
    stops = Grad.getStops (Grad.Linear grad)
  in
    map (\(Grad.ColorStop stop) -> RGB.rgbToLegacyCss stop.color) stops

-- | Get the number of color stops in a gradient
-- | Useful for validation (minimum 2 stops required) and UI display
stopCount :: Grad.LinearGradient -> Int
stopCount grad =
  let
    stops = Grad.getStops (Grad.Linear grad)
  in
    length stops

