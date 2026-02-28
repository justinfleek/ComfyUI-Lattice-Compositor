-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // element // colorpicker // alpha
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | AlphaSlider — Opacity/transparency control with checkerboard preview.
-- |
-- | ## Design Philosophy
-- |
-- | The alpha slider controls color opacity (0-100%). It displays:
-- | - Checkerboard background to visualize transparency
-- | - Color gradient from transparent to opaque
-- | - Draggable handle for precise control
-- |
-- | ## Schema Atoms Accepted
-- |
-- | | Property      | Pillar    | Type              | Purpose                |
-- | |---------------|-----------|-------------------|------------------------|
-- | | color         | Color     | RGB               | Base color (no alpha)  |
-- | | opacity       | Color     | Opacity (0-100)   | Current alpha value    |
-- | | width         | Dimension | Pixel             | Slider width           |
-- | | height        | Dimension | Pixel             | Slider height          |

module Hydrogen.Element.Compound.ColorPicker.Alpha
  ( -- * Component
    alphaSlider
  
  -- * Props
  , AlphaProps
  , AlphaProp
  , defaultAlphaProps
  
  -- * Prop Builders
  , color
  , opacity
  , sliderWidth
  , sliderHeight
  , borderRadius
  , onChange
  
  -- * Change Type
  , AlphaChange
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( show
  , (<>)
  , ($)
  , (-)
  , (*)
  , (/)
  )

import Data.Array (foldl)
import Data.Int (toNumber) as Int
import Data.Maybe (Maybe(Nothing, Just))

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as RGB
import Hydrogen.Schema.Color.Channel as Channel
import Hydrogen.Schema.Color.Opacity as Opacity
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Geometry.Radius as Radius

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // change types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Alpha change event
type AlphaChange =
  { opacity :: Opacity.Opacity
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Alpha slider properties
type AlphaProps msg =
  { -- Color
    color :: RGB.RGB
  , opacity :: Opacity.Opacity
  
  -- Dimensions
  , width :: Device.Pixel
  , height :: Device.Pixel
  
  -- Appearance
  , borderRadius :: Maybe Radius.Radius
  
  -- Behavior
  , onChange :: Maybe (AlphaChange -> msg)
  }

-- | Property modifier
type AlphaProp msg = AlphaProps msg -> AlphaProps msg

-- | Default properties
defaultAlphaProps :: forall msg. AlphaProps msg
defaultAlphaProps =
  { color: RGB.rgb 255 0 0
  , opacity: Opacity.opacity 100
  , width: Device.px 200.0
  , height: Device.px 16.0
  , borderRadius: Nothing
  , onChange: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set base color
color :: forall msg. RGB.RGB -> AlphaProp msg
color c props = props { color = c }

-- | Set current opacity
opacity :: forall msg. Opacity.Opacity -> AlphaProp msg
opacity o props = props { opacity = o }

-- | Set slider width
sliderWidth :: forall msg. Device.Pixel -> AlphaProp msg
sliderWidth w props = props { width = w }

-- | Set slider height
sliderHeight :: forall msg. Device.Pixel -> AlphaProp msg
sliderHeight h props = props { height = h }

-- | Set border radius
borderRadius :: forall msg. Radius.Radius -> AlphaProp msg
borderRadius r props = props { borderRadius = Just r }

-- | Set change handler
onChange :: forall msg. (AlphaChange -> msg) -> AlphaProp msg
onChange handler props = props { onChange = Just handler }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render alpha slider
alphaSlider :: forall msg. Array (AlphaProp msg) -> E.Element msg
alphaSlider propModifiers =
  let
    props = foldl (\p f -> f p) defaultAlphaProps propModifiers
    
    -- Dimensions
    w = Device.unwrapPixel props.width
    h = Device.unwrapPixel props.height
    widthPx = show w <> "px"
    heightPx = show h <> "px"
    
    -- Handle position (0-100% maps to 0-width)
    opacityVal = Int.toNumber (Opacity.unwrap props.opacity)
    handleX = (opacityVal / 100.0) * w
    handleSize = h * 1.2
    
    radiusStyle = case props.borderRadius of
      Just r -> Radius.toLegacyCss r
      Nothing -> "4px"
    
    -- Color for gradient (base color at varying alpha)
    colorStr = RGB.toLegacyCss props.color
    transparentStr = "rgba(" <> channelStr props.color <> ", 0)"
    opaqueStr = "rgba(" <> channelStr props.color <> ", 1)"
    
    -- Accessibility label using colorStr
    ariaLabel = "Alpha slider for color " <> colorStr <> ", current opacity: " <> show (Opacity.unwrap props.opacity) <> "%"
  in
    E.div_
      [ E.style "position" "relative"
      , E.style "width" widthPx
      , E.style "height" heightPx
      , E.style "cursor" "pointer"
      , E.ariaLabel ariaLabel
      , E.attr "role" "slider"
      , E.attr "aria-valuemin" "0"
      , E.attr "aria-valuemax" "100"
      , E.attr "aria-valuenow" $ show (Opacity.unwrap props.opacity)
      ]
      [ -- Checkerboard background
        renderCheckerboard widthPx heightPx radiusStyle
        
        -- Alpha gradient overlay
      , E.div_
          [ E.style "position" "absolute"
          , E.style "inset" "0"
          , E.style "background" ("linear-gradient(to right, " <> transparentStr <> ", " <> opaqueStr <> ")")
          , E.style "border-radius" radiusStyle
          , E.style "border" "1px solid rgba(0,0,0,0.1)"
          ]
          []
        
        -- Handle
      , renderAlphaHandle handleX h handleSize
      ]

-- | Render checkerboard pattern for transparency visualization
-- | widthPx and heightPx are used for explicit sizing and data attributes
renderCheckerboard :: forall msg. String -> String -> String -> E.Element msg
renderCheckerboard checkerWidth checkerHeight radiusStyle =
  E.div_
    [ E.style "position" "absolute"
    , E.style "inset" "0"
    , E.style "width" checkerWidth
    , E.style "height" checkerHeight
    , E.style "background-color" "#fff"
    , E.style "background-image" "linear-gradient(45deg, #ccc 25%, transparent 25%), linear-gradient(-45deg, #ccc 25%, transparent 25%), linear-gradient(45deg, transparent 75%, #ccc 75%), linear-gradient(-45deg, transparent 75%, #ccc 75%)"
    , E.style "background-size" "8px 8px"
    , E.style "background-position" "0 0, 0 4px, 4px -4px, -4px 0"
    , E.style "border-radius" radiusStyle
    , E.dataAttr "checkerboard-width" checkerWidth
    , E.dataAttr "checkerboard-height" checkerHeight
    ]
    []

-- | Render the slider handle
-- | Parameters: x position, track height, handle size
renderAlphaHandle :: forall msg. Number -> Number -> Number -> E.Element msg
renderAlphaHandle xPos trackHeight handleSize =
  let
    halfHandle = handleSize / 2.0
    topOffset = (trackHeight - handleSize) / 2.0
  in
    E.div_
      [ E.style "position" "absolute"
      , E.style "left" (show (xPos - halfHandle) <> "px")
      , E.style "top" (show topOffset <> "px")
      , E.style "width" (show handleSize <> "px")
      , E.style "height" (show handleSize <> "px")
      , E.style "border-radius" "50%"
      , E.style "background" "#fff"
      , E.style "border" "2px solid #333"
      , E.style "box-shadow" "0 1px 3px rgba(0,0,0,0.3)"
      , E.style "pointer-events" "none"
      ]
      []

-- | Get RGB channels as comma-separated string
channelStr :: RGB.RGB -> String
channelStr c =
  let
    r = Channel.unwrap (RGB.red c)
    g = Channel.unwrap (RGB.green c)
    b = Channel.unwrap (RGB.blue c)
  in
    show r <> ", " <> show g <> ", " <> show b
