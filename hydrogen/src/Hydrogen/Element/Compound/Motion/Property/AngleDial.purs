-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // motion // property // angle-dial
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | AngleDial — Circular Rotation Control
-- |
-- | A circular dial for setting rotation/angle values. Common in motion
-- | graphics software for transform rotation, effect parameters, etc.
-- |
-- | Features:
-- | - Circular drag interaction
-- | - Shift+drag for 45° snap
-- | - Optional numeric input
-- | - Visual tick marks at 45° intervals
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.Motion.Property.AngleDial as Dial
-- |
-- | -- Basic angle dial
-- | Dial.angleDial
-- |   [ Dial.value 45.0
-- |   , Dial.onChange HandleRotation
-- |   ]
-- |
-- | -- Large dial without numeric input
-- | Dial.angleDial
-- |   [ Dial.value state.rotation
-- |   , Dial.size 64
-- |   , Dial.showValue false
-- |   , Dial.onChange HandleRotation
-- |   ]
-- | ```

module Hydrogen.Element.Compound.Motion.Property.AngleDial
  ( -- * Component
    angleDial
    
  -- * Props
  , AngleDialProps
  , AngleDialProp
  , defaultProps
  
  -- * Prop Builders
  , value
  , size
  , showValue
  , dialDisabled
  , onChange
  
  -- * Helpers (for runtime)
  , normalizeAngle
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( show
  , (<>)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , map
  )

import Data.Array (foldl, range)
import Data.Int (toNumber) as Int
import Data.Maybe (Maybe(Nothing, Just))
import Data.Number (floor) as Number

import Hydrogen.Render.Element as E

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | AngleDial properties
type AngleDialProps msg =
  { value :: Number          -- Current angle in degrees (0-360)
  , size :: Int              -- Dial diameter in pixels
  , showValue :: Boolean     -- Show numeric input below dial
  , disabled :: Boolean      -- Disable interaction
  , onChange :: Maybe (Number -> msg)  -- Called with new angle
  }

-- | Property modifier function
type AngleDialProp msg = AngleDialProps msg -> AngleDialProps msg

-- | Default properties
defaultProps :: forall msg. AngleDialProps msg
defaultProps =
  { value: 0.0
  , size: 48
  , showValue: true
  , disabled: false
  , onChange: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set current angle value (degrees)
value :: forall msg. Number -> AngleDialProp msg
value v props = props { value = v }

-- | Set dial size (diameter in pixels)
size :: forall msg. Int -> AngleDialProp msg
size s props = props { size = s }

-- | Show numeric input
showValue :: forall msg. Boolean -> AngleDialProp msg
showValue s props = props { showValue = s }

-- | Set disabled state
dialDisabled :: forall msg. Boolean -> AngleDialProp msg
dialDisabled d props = props { disabled = d }

-- | Set change handler
onChange :: forall msg. (Number -> msg) -> AngleDialProp msg
onChange handler props = props { onChange = Just handler }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Normalize angle to 0-360 range
-- | ((angle % 360) + 360) % 360
normalizeAngle :: Number -> Number
normalizeAngle angle =
  let
    mod360 = angle - 360.0 * Number.floor (angle / 360.0)
    normalized = if mod360 < 0.0 
      then mod360 + 360.0 
      else mod360
  in
    normalized

-- | Round to one decimal place for display
roundDisplay :: Number -> Number
roundDisplay n = 
  Number.floor (n * 10.0) / 10.0

-- | Show int for CSS pixel values
showPx :: Int -> String
showPx n = show n <> "px"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // component
-- ═════════════════════════════════════════════════════════════════════════════

-- | AngleDial component
-- |
-- | A circular dial for rotation/angle input.
-- | Pure Element — renders to DOM, Halogen, Static HTML, or any target.
angleDial :: forall msg. Array (AngleDialProp msg) -> E.Element msg
angleDial propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    sizeStr = showPx props.size
    displayVal = roundDisplay (normalizeAngle props.value)
    
    -- Container styles
    containerStyles =
      [ E.style "display" "flex"
      , E.style "align-items" "center"
      , E.style "gap" "8px"
      ]
    
    disabledStyles = if props.disabled
      then [ E.style "opacity" "0.5", E.style "pointer-events" "none" ]
      else []
    
    -- Dial container
    dialEl =
      E.div_
        [ E.class_ "dial"
        , E.style "position" "relative"
        , E.style "cursor" "grab"
        , E.style "width" sizeStr
        , E.style "height" sizeStr
        ]
        [ dialRing
        , dialCenter
        , dialIndicator props.value
        , dialMarks
        ]
    
    -- Optional numeric input
    valueEl = if props.showValue
      then
        [ E.div_
            [ E.class_ "angle-value"
            , E.style "display" "flex"
            , E.style "align-items" "center"
            , E.style "gap" "2px"
            ]
            [ E.input_
                [ E.attr "type" "number"
                , E.class_ "angle-input"
                , E.value (show displayVal)
                , E.disabled props.disabled
                , E.style "width" "50px"
                , E.style "padding" "4px 6px"
                , E.style "border" "1px solid #3d3d3d"
                , E.style "border-radius" "3px"
                , E.style "background" "#2a2a2a"
                , E.style "color" "#e0e0e0"
                , E.style "font-size" "13px"
                , E.style "text-align" "right"
                ]
            , E.span_
                [ E.class_ "angle-unit"
                , E.style "font-size" "13px"
                , E.style "color" "#666"
                ]
                [ E.text "°" ]
            ]
        ]
      else []
  in
    E.div_
      (containerStyles <> disabledStyles <> [ E.class_ "angle-dial" ])
      ([ dialEl ] <> valueEl)

-- | Dial ring (outer border)
dialRing :: forall msg. E.Element msg
dialRing =
  E.div_
    [ E.class_ "dial-ring"
    , E.style "position" "absolute"
    , E.style "inset" "4px"
    , E.style "border" "2px solid #3d3d3d"
    , E.style "border-radius" "50%"
    ]
    []

-- | Dial center point
dialCenter :: forall msg. E.Element msg
dialCenter =
  E.div_
    [ E.class_ "dial-center"
    , E.style "position" "absolute"
    , E.style "top" "50%"
    , E.style "left" "50%"
    , E.style "width" "6px"
    , E.style "height" "6px"
    , E.style "background" "#666"
    , E.style "border-radius" "50%"
    , E.style "transform" "translate(-50%, -50%)"
    ]
    []

-- | Dial indicator (rotates with value)
dialIndicator :: forall msg. Number -> E.Element msg
dialIndicator angle =
  E.div_
    [ E.class_ "dial-indicator"
    , E.style "position" "absolute"
    , E.style "top" "50%"
    , E.style "left" "50%"
    , E.style "width" "2px"
    , E.style "height" "45%"
    , E.style "background" "#7c9cff"
    , E.style "border-radius" "1px"
    , E.style "transform-origin" "center bottom"
    , E.style "transform" ("rotate(" <> show angle <> "deg)")
    ]
    []

-- | Dial tick marks (8 marks at 45° intervals)
dialMarks :: forall msg. E.Element msg
dialMarks =
  E.div_
    [ E.class_ "dial-marks"
    , E.style "position" "absolute"
    , E.style "inset" "0"
    ]
    (map dialMark (range 1 8))

-- | Single tick mark
dialMark :: forall msg. Int -> E.Element msg
dialMark i =
  let
    rotation = Int.toNumber i * 45.0
  in
    E.div_
      [ E.class_ "dial-mark"
      , E.style "position" "absolute"
      , E.style "top" "2px"
      , E.style "left" "50%"
      , E.style "width" "1px"
      , E.style "height" "4px"
      , E.style "background" "#555"
      , E.style "transform-origin" "center calc(50% - 2px)"
      , E.style "transform" ("rotate(" <> show rotation <> "deg)")
      ]
      []
