-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // element // colorpicker // panel
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | SaturationPanel — 2D color picker panel (Photoshop-style).
-- |
-- | ## Design Philosophy
-- |
-- | The saturation panel is a 2D gradient where:
-- | - X-axis: Saturation (0% left → 100% right)
-- | - Y-axis: Brightness/Value (100% top → 0% bottom)
-- |
-- | The hue is fixed (from the color wheel or sliders), and the user
-- | picks saturation and brightness by clicking/dragging on the panel.
-- |
-- | ## Schema Atoms Accepted
-- |
-- | | Property      | Pillar    | Type              | Purpose                |
-- | |---------------|-----------|-------------------|------------------------|
-- | | hue           | Color     | Hue (0-359)       | Fixed hue for panel    |
-- | | saturation    | Color     | Saturation (0-100)| Current X position     |
-- | | brightness    | Color     | Lightness (0-100) | Current Y position     |
-- | | width         | Dimension | Pixel             | Panel width            |
-- | | height        | Dimension | Pixel             | Panel height           |
-- | | handleSize    | Dimension | Pixel             | Picker handle size     |
-- | | borderColor   | Color     | RGB               | Panel border           |
-- | | borderRadius  | Geometry  | Radius            | Corner rounding        |

module Hydrogen.Element.Compound.ColorPicker.Panel
  ( -- * Component
    saturationPanel
  
  -- * Types
  , ColorChange
  
  -- * Props
  , PanelProps
  , PanelProp
  , defaultProps
  
  -- * State Props
  , hue
  , saturation
  , brightness
  
  -- * Dimension Atoms
  , width
  , height
  , handleSize
  
  -- * Color Atoms
  , borderColor
  
  -- * Geometry Atoms
  , borderRadius
  
  -- * Behavior Props
  , onChange
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( show
  , (<>)
  , (-)
  , (+)
  , (*)
  , (/)
  )

import Data.Array (foldl)
import Data.Int (toNumber) as Int
import Data.Maybe (Maybe(Nothing, Just))

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Color.Hue as Hue
import Hydrogen.Schema.Color.Saturation as Sat
import Hydrogen.Schema.Color.Lightness as Light
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Geometry.Radius as Geometry

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Color change event with saturation and brightness
type ColorChange =
  { saturation :: Sat.Saturation
  , brightness :: Light.Lightness
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Saturation panel properties
type PanelProps msg =
  { -- Color state
    hue :: Hue.Hue                   -- ^ Fixed hue (panel background)
  , saturation :: Sat.Saturation     -- ^ Current X position
  , brightness :: Light.Lightness    -- ^ Current Y position
  
  -- Dimensions
  , width :: Device.Pixel
  , height :: Device.Pixel
  , handleSize :: Device.Pixel
  
  -- Appearance
  , borderColor :: Maybe Color.RGB
  , borderRadius :: Maybe Geometry.Radius
  
  -- Behavior
  , onChange :: Maybe (ColorChange -> msg)
  }

-- | Property modifier
type PanelProp msg = PanelProps msg -> PanelProps msg

-- | Default properties
defaultProps :: forall msg. PanelProps msg
defaultProps =
  { hue: Hue.hue 0
  , saturation: Sat.saturation 100
  , brightness: Light.lightness 50
  , width: Device.px 256.0
  , height: Device.px 256.0
  , handleSize: Device.px 14.0
  , borderColor: Nothing
  , borderRadius: Nothing
  , onChange: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set fixed hue for the panel background
hue :: forall msg. Hue.Hue -> PanelProp msg
hue h props = props { hue = h }

-- | Set current saturation (X position)
saturation :: forall msg. Sat.Saturation -> PanelProp msg
saturation s props = props { saturation = s }

-- | Set current brightness (Y position)
brightness :: forall msg. Light.Lightness -> PanelProp msg
brightness b props = props { brightness = b }

-- | Set panel width
width :: forall msg. Device.Pixel -> PanelProp msg
width w props = props { width = w }

-- | Set panel height
height :: forall msg. Device.Pixel -> PanelProp msg
height h props = props { height = h }

-- | Set handle size
handleSize :: forall msg. Device.Pixel -> PanelProp msg
handleSize s props = props { handleSize = s }

-- | Set border color
borderColor :: forall msg. Color.RGB -> PanelProp msg
borderColor c props = props { borderColor = Just c }

-- | Set border radius
borderRadius :: forall msg. Geometry.Radius -> PanelProp msg
borderRadius r props = props { borderRadius = Just r }

-- | Set change handler
onChange :: forall msg. (ColorChange -> msg) -> PanelProp msg
onChange handler props = props { onChange = Just handler }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a saturation/brightness panel
-- |
-- | Creates a 2D gradient panel where X = saturation, Y = brightness.
-- | The hue is fixed and determines the color shown at full sat/brightness.
saturationPanel :: forall msg. Array (PanelProp msg) -> E.Element msg
saturationPanel propModifiers =
  let
    props = foldl (\p f -> f p) defaultProps propModifiers
    
    -- Dimensions
    w = Device.unwrapPixel props.width
    h = Device.unwrapPixel props.height
    handleR = Device.unwrapPixel props.handleSize / 2.0
    
    -- Current position from sat/brightness
    satVal = Int.toNumber (Sat.unwrap props.saturation)
    brightVal = Int.toNumber (Light.unwrap props.brightness)
    handleX = (satVal / 100.0) * w
    handleY = (1.0 - brightVal / 100.0) * h  -- Invert: 100% at top
    
    -- Hue for background color
    hueVal = Int.toNumber (Hue.unwrap props.hue)
    
    -- Border styling
    borderStyle = case props.borderColor of
      Just c -> "1px solid " <> Color.toLegacyCss c
      Nothing -> "1px solid rgba(0,0,0,0.1)"
    
    -- Border radius
    radiusStyle = case props.borderRadius of
      Just r -> Geometry.toLegacyCss r
      Nothing -> "4px"
  in
    E.div_
      [ E.style "position" "relative"
      , E.style "width" (show w <> "px")
      , E.style "height" (show h <> "px")
      , E.style "border" borderStyle
      , E.style "border-radius" radiusStyle
      , E.style "cursor" "crosshair"
      , E.style "overflow" "hidden"
      ]
      [ -- Panel gradient layers
        renderPanelGradients hueVal
        
        -- Handle
      , renderPanelHandle handleX handleY handleR
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // panel render
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render the panel gradient layers
-- |
-- | Uses two overlapping gradients:
-- | 1. Horizontal: White to hue color (saturation)
-- | 2. Vertical: Transparent to black (brightness)
-- |
-- | The gradients fill the parent container using CSS `inset: 0`.
renderPanelGradients :: forall msg. Number -> E.Element msg
renderPanelGradients hueVal =
  let
    -- Full saturation color at this hue
    hueColor = "hsl(" <> show hueVal <> ", 100%, 50%)"
  in
    E.div_
      [ E.style "position" "absolute"
      , E.style "inset" "0"
      ]
      [ -- Saturation gradient: white → hue color
        E.div_
          [ E.style "position" "absolute"
          , E.style "inset" "0"
          , E.style "background" ("linear-gradient(to right, #fff, " <> hueColor <> ")")
          ]
          []
        
        -- Brightness gradient: transparent → black
      , E.div_
          [ E.style "position" "absolute"
          , E.style "inset" "0"
          , E.style "background" "linear-gradient(to bottom, transparent, #000)"
          ]
          []
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // handle render
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render the circular picker handle
-- |
-- | The handle indicates current saturation/brightness position.
-- | Uses white fill with black border for visibility on any background.
renderPanelHandle :: forall msg. Number -> Number -> Number -> E.Element msg
renderPanelHandle x y radius =
  E.div_
    [ E.style "position" "absolute"
    , E.style "left" (show (x - radius) <> "px")
    , E.style "top" (show (y - radius) <> "px")
    , E.style "width" (show (radius * 2.0) <> "px")
    , E.style "height" (show (radius * 2.0) <> "px")
    , E.style "border-radius" "50%"
    , E.style "background" "#fff"
    , E.style "border" "2px solid #000"
    , E.style "box-shadow" "0 1px 3px rgba(0,0,0,0.3)"
    , E.style "pointer-events" "none"
    -- Accessibility: indicate position as percentage
    , E.attr "aria-label" "Color position indicator"
    , E.dataAttr "position-x" (show x)
    , E.dataAttr "position-y" (show y)
    -- Computed size for external styling (diameter = radius * 2 + border)
    , E.dataAttr "handle-diameter" (show (radius * 2.0 + 4.0))
    ]
    []

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // geometry
-- ═════════════════════════════════════════════════════════════════════════════

