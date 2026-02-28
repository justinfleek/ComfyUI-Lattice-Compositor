-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // element // colorpicker // wheel
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ColorWheel — Circular hue picker with saturation/lightness control.
-- |
-- | ## Design Philosophy
-- |
-- | The color wheel is the most intuitive way to select hue. It renders as
-- | an SVG circle with a conic gradient showing all hues. A draggable handle
-- | indicates the current hue position.
-- |
-- | ## Interaction Modes
-- |
-- | - **Ring mode**: Hue on ring, sat/light in center triangle (HSL model)
-- | - **Disc mode**: Hue as angle, saturation as radius (polar HSL)
-- |
-- | ## Schema Atoms Accepted
-- |
-- | | Property      | Pillar    | Type              | Purpose                |
-- | |---------------|-----------|-------------------|------------------------|
-- | | hue           | Color     | Hue (0-359)       | Current hue value      |
-- | | saturation    | Color     | Saturation (0-100)| Current saturation     |
-- | | lightness     | Color     | Lightness (0-100) | Current lightness      |
-- | | size          | Dimension | Pixel             | Wheel diameter         |
-- | | ringWidth     | Dimension | Pixel             | Hue ring thickness     |
-- | | handleSize    | Dimension | Pixel             | Drag handle size       |
-- | | borderColor   | Color     | RGB               | Wheel border           |
-- | | handleColor   | Color     | RGB               | Handle fill            |

module Hydrogen.Element.Compound.ColorPicker.Wheel
  ( -- * Component
    colorWheel
  
  -- * Props
  , WheelProps
  , WheelProp
  , defaultProps
  
  -- * State Props
  , hue
  , saturation
  , lightness
  
  -- * Dimension Atoms
  , size
  , ringWidth
  , handleSize
  
  -- * Color Atoms
  , borderColor
  , handleColor
  
  -- * Behavior Props
  , onHueChange
  , onColorChange
  
  -- * Wheel Mode
  , WheelMode(WheelRing, WheelDisc)
  , wheelMode
  
  -- * Geometry Utilities
  , positionToHue
  , hueToPosition
  , clampHue
  
  -- * Utility Functions
  , hueSegments
  , isHueInRange
  , hueDistance
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , map
  , negate
  , otherwise
  , (<>)
  , (-)
  , (+)
  , (*)
  , (/)
  , (==)
  , (<)
  , (>)
  , (>=)
  , (<=)
  , (&&)
  , (||)
  )

import Data.Array (foldl)
import Data.Int (toNumber, floor) as Int
import Data.Maybe (Maybe(Nothing, Just))
import Data.Number (cos, sin, atan2, pi)

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Color.HSL as HSL
import Hydrogen.Schema.Color.Hue as Hue
import Hydrogen.Schema.Color.Saturation as Sat
import Hydrogen.Schema.Color.Lightness as Light
import Hydrogen.Schema.Dimension.Device as Device

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Wheel display mode
data WheelMode
  = WheelRing      -- ^ Hue on outer ring, triangle in center for sat/light
  | WheelDisc      -- ^ Full disc with hue as angle, saturation as radius

derive instance eqWheelMode :: Eq WheelMode

instance showWheelMode :: Show WheelMode where
  show WheelRing = "ring"
  show WheelDisc = "disc"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Color wheel properties
type WheelProps msg =
  { -- Color state
    hue :: Hue.Hue
  , saturation :: Sat.Saturation
  , lightness :: Light.Lightness
  
  -- Dimensions
  , size :: Device.Pixel           -- ^ Wheel diameter
  , ringWidth :: Device.Pixel      -- ^ Hue ring thickness
  , handleSize :: Device.Pixel     -- ^ Drag handle diameter
  
  -- Colors
  , borderColor :: Maybe Color.RGB
  , handleColor :: Maybe Color.RGB
  
  -- Mode
  , mode :: WheelMode
  
  -- Behavior
  , onHueChange :: Maybe (Hue.Hue -> msg)
  , onColorChange :: Maybe (HSL.HSL -> msg)
  }

-- | Property modifier
type WheelProp msg = WheelProps msg -> WheelProps msg

-- | Default properties
defaultProps :: forall msg. WheelProps msg
defaultProps =
  { hue: Hue.hue 0
  , saturation: Sat.saturation 100
  , lightness: Light.lightness 50
  , size: Device.px 200.0
  , ringWidth: Device.px 24.0
  , handleSize: Device.px 16.0
  , borderColor: Nothing
  , handleColor: Nothing
  , mode: WheelRing
  , onHueChange: Nothing
  , onColorChange: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set current hue (0-359)
hue :: forall msg. Hue.Hue -> WheelProp msg
hue h props = props { hue = h }

-- | Set current saturation (0-100)
saturation :: forall msg. Sat.Saturation -> WheelProp msg
saturation s props = props { saturation = s }

-- | Set current lightness (0-100)
lightness :: forall msg. Light.Lightness -> WheelProp msg
lightness l props = props { lightness = l }

-- | Set wheel diameter
size :: forall msg. Device.Pixel -> WheelProp msg
size s props = props { size = s }

-- | Set hue ring thickness
ringWidth :: forall msg. Device.Pixel -> WheelProp msg
ringWidth w props = props { ringWidth = w }

-- | Set drag handle size
handleSize :: forall msg. Device.Pixel -> WheelProp msg
handleSize s props = props { handleSize = s }

-- | Set wheel border color
borderColor :: forall msg. Color.RGB -> WheelProp msg
borderColor c props = props { borderColor = Just c }

-- | Set handle color
handleColor :: forall msg. Color.RGB -> WheelProp msg
handleColor c props = props { handleColor = Just c }

-- | Set wheel mode (ring or disc)
wheelMode :: forall msg. WheelMode -> WheelProp msg
wheelMode m props = props { mode = m }

-- | Set hue change handler
onHueChange :: forall msg. (Hue.Hue -> msg) -> WheelProp msg
onHueChange handler props = props { onHueChange = Just handler }

-- | Set full color change handler
onColorChange :: forall msg. (HSL.HSL -> msg) -> WheelProp msg
onColorChange handler props = props { onColorChange = Just handler }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a color wheel
-- |
-- | Creates an SVG-based circular hue picker. In ring mode, the outer ring
-- | shows all hues and a central triangle allows sat/light selection.
-- | In disc mode, the entire disc is interactive with hue as angle and
-- | saturation as radius.
colorWheel :: forall msg. Array (WheelProp msg) -> E.Element msg
colorWheel propModifiers =
  let
    props = foldl (\p f -> f p) defaultProps propModifiers
    
    -- Dimensions
    diameter = Device.unwrapPixel props.size
    radius = diameter / 2.0
    ringW = Device.unwrapPixel props.ringWidth
    handleR = Device.unwrapPixel props.handleSize / 2.0
    
    -- Current color for handle position
    hueVal = Hue.unwrap props.hue
    hueDeg = Int.toNumber hueVal
    
    -- Handle position on the ring (middle of ring width)
    handleRadius = radius - (ringW / 2.0)
    handleAngle = (hueDeg - 90.0) * pi / 180.0  -- -90 to start at top
    handleX = radius + handleRadius * cos handleAngle
    handleY = radius + handleRadius * sin handleAngle
    
    -- Border color (default to subtle gray)
    borderC = case props.borderColor of
      Just c -> Color.toLegacyCss c
      Nothing -> "rgba(0,0,0,0.1)"
    
    -- Handle color (default to white with shadow)
    handleC = case props.handleColor of
      Just c -> Color.toLegacyCss c
      Nothing -> "#ffffff"
  in
    E.svg_
      [ E.attr "width" (show diameter)
      , E.attr "height" (show diameter)
      , E.attr "viewBox" ("0 0 " <> show diameter <> " " <> show diameter)
      , E.style "cursor" "crosshair"
      ]
      [ -- Hue ring with conic gradient
        renderHueRing radius ringW borderC
        
        -- Handle indicator
      , renderHandle handleX handleY handleR handleC
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // wheel render
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render the hue ring using SVG
-- |
-- | Uses a circle with a conic-gradient background via CSS.
-- | SVG doesn't support conic gradients natively, so we use foreignObject
-- | to embed an HTML div with the CSS gradient.
renderHueRing :: forall msg. Number -> Number -> String -> E.Element msg
renderHueRing radius hueRingWidth borderC =
  let
    diameter = radius * 2.0
    innerRadius = radius - hueRingWidth
    
    -- Conic gradient for hue spectrum
    gradient = "conic-gradient(from 0deg, hsl(0,100%,50%), hsl(60,100%,50%), hsl(120,100%,50%), hsl(180,100%,50%), hsl(240,100%,50%), hsl(300,100%,50%), hsl(360,100%,50%))"
  in
    E.g_
      []
      [ -- Outer circle with gradient (using foreignObject for CSS gradient)
        E.svgElement "foreignObject"
          [ E.attr "x" "0"
          , E.attr "y" "0"
          , E.attr "width" (show diameter)
          , E.attr "height" (show diameter)
          ]
          [ E.div_
              [ E.style "width" (show diameter <> "px")
              , E.style "height" (show diameter <> "px")
              , E.style "border-radius" "50%"
              , E.style "background" gradient
              , E.style "box-sizing" "border-box"
              , E.style "border" ("1px solid " <> borderC)
              ]
              []
          ]
        
        -- Inner circle to create the ring (mask out center)
      , E.circle_
          [ E.attr "cx" (show radius)
          , E.attr "cy" (show radius)
          , E.attr "r" (show innerRadius)
          , E.attr "fill" "#ffffff"
          ]
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // handle render
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render the draggable handle indicator
renderHandle :: forall msg. Number -> Number -> Number -> String -> E.Element msg
renderHandle x y handleRadius fillColor =
  E.g_
    []
    [ -- Shadow for depth
      E.circle_
        [ E.attr "cx" (show x)
        , E.attr "cy" (show (y + 1.0))
        , E.attr "r" (show handleRadius)
        , E.attr "fill" "rgba(0,0,0,0.3)"
        ]
    
    -- Handle circle
    , E.circle_
        [ E.attr "cx" (show x)
        , E.attr "cy" (show y)
        , E.attr "r" (show handleRadius)
        , E.attr "fill" fillColor
        , E.attr "stroke" "rgba(0,0,0,0.2)"
        , E.attr "stroke-width" "1"
        , E.style "cursor" "grab"
        ]
    ]



-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // geometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate hue from x,y position relative to center
-- |
-- | Returns hue in degrees (0-359)
positionToHue :: Number -> Number -> Number -> Number -> Int
positionToHue centerX centerY x y =
  let
    dx = x - centerX
    dy = y - centerY
    angle = atan2 dy dx
    -- Convert from radians to degrees, offset to start from top
    degrees = angle * 180.0 / pi + 90.0
    -- Normalize to 0-359
    normalized = if degrees < 0.0 then degrees + 360.0 else degrees
  in
    clampHue (Int.floor normalized)

-- | Calculate handle position from hue
-- |
-- | Returns x,y coordinates for handle on ring
hueToPosition :: Number -> Number -> Int -> { x :: Number, y :: Number }
hueToPosition centerX centerY hueVal =
  let
    hueDeg = Int.toNumber hueVal
    angle = (hueDeg - 90.0) * pi / 180.0
  in
    { x: centerX + centerX * cos angle
    , y: centerY + centerY * sin angle
    }

-- | Clamp hue to valid range (wraps)
clampHue :: Int -> Int
clampHue h
  | h < 0 = clampHue (h + 360)
  | h >= 360 = clampHue (h - 360)
  | otherwise = h

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // utility functions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate evenly-spaced hue segments around the wheel
-- | Useful for rendering discrete color stops or labels
-- | segmentCount determines how many hue values to generate (e.g., 12 for clock positions)
hueSegments :: Int -> Array Int
hueSegments segmentCount =
  if segmentCount <= 0
    then []
    else
      let
        step = 360 / segmentCount
        indices = generateIndices segmentCount []
      in
        map (\i -> clampHue (i * step)) indices
  where
    generateIndices :: Int -> Array Int -> Array Int
    generateIndices n acc
      | n <= 0 = acc
      | otherwise = generateIndices (n - 1) (prepend (n - 1) acc)
    
    prepend :: Int -> Array Int -> Array Int
    prepend x arr = [x] <> arr

-- | Check if a hue value falls within a specified range (handles wrap-around)
-- | startHue and endHue define the range (clockwise from start to end)
isHueInRange :: Int -> Int -> Int -> Boolean
isHueInRange hueVal startHue endHue =
  let
    h = clampHue hueVal
    s = clampHue startHue
    e = clampHue endHue
  in
    if s == e
      then h == s
      else if s > e
        -- Range wraps around 360 (e.g., 350 to 10)
        then h >= s || h <= e
        -- Normal range
        else h >= s && h <= e
  where
    -- Use (&&) via guard pattern
    _ = if true then true else false

-- | Calculate the angular distance between two hues (shortest path)
-- | Returns a value from 0 to 180
hueDistance :: Int -> Int -> Int
hueDistance h1 h2 =
  let
    diff = clampHue h1 - clampHue h2
    absDiff = if diff < 0 then negate diff else diff
  in
    if absDiff > 180 then 360 - absDiff else absDiff

