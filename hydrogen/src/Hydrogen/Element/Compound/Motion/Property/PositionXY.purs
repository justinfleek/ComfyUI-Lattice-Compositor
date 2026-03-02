-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // motion // property // position-xy
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | PositionXY — 2D/3D Position Input Control
-- |
-- | Paired (or tripled) numeric inputs for spatial coordinates.
-- | Supports XY or XYZ modes with optional proportional linking.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.Motion.Property.PositionXY as Pos
-- |
-- | -- 2D position
-- | Pos.positionXY
-- |   [ Pos.x 100.0
-- |   , Pos.y 50.0
-- |   , Pos.onChangeX HandleX
-- |   , Pos.onChangeY HandleY
-- |   ]
-- |
-- | -- 3D position with linking
-- | Pos.positionXY
-- |   [ Pos.x state.x
-- |   , Pos.y state.y
-- |   , Pos.z state.z
-- |   , Pos.linked true
-- |   , Pos.onChangeX HandleX
-- |   , Pos.onChangeY HandleY
-- |   , Pos.onChangeZ HandleZ
-- |   ]
-- | ```

module Hydrogen.Element.Compound.Motion.Property.PositionXY
  ( -- * Component
    positionXY
    
  -- * Props
  , PositionXYProps
  , PositionXYProp
  , defaultProps
  
  -- * Prop Builders
  , x
  , y
  , z
  , linked
  , showLink
  , step
  , minValue
  , maxValue
  , posDisabled
  , precision
  , onChangeX
  , onChangeY
  , onChangeZ
  , onToggleLink
  
  -- * Helpers (for runtime implementations)
  , roundTo
  , power
  , formatValue
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( show
  , negate
  , (<>)
  , (-)
  , (*)
  , (/)
  , (==)
  , (>)
  , (&&)
  )

import Data.Array (foldl)
import Data.Int (toNumber, round) as Int
import Data.Maybe (Maybe(Nothing, Just))
import Data.Number (floor) as Number

import Hydrogen.Render.Element as E

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | PositionXY properties
type PositionXYProps msg =
  { x :: Number
  , y :: Number
  , z :: Maybe Number          -- When present, shows Z axis
  , linked :: Boolean          -- Link X/Y proportionally
  , showLink :: Boolean        -- Show link toggle button
  , step :: Number
  , min :: Maybe Number
  , max :: Maybe Number
  , disabled :: Boolean
  , precision :: Int
  , onChangeX :: Maybe (Number -> msg)
  , onChangeY :: Maybe (Number -> msg)
  , onChangeZ :: Maybe (Number -> msg)
  , onToggleLink :: Maybe (Boolean -> msg)
  }

-- | Property modifier function
type PositionXYProp msg = PositionXYProps msg -> PositionXYProps msg

-- | Default properties
defaultProps :: forall msg. PositionXYProps msg
defaultProps =
  { x: 0.0
  , y: 0.0
  , z: Nothing
  , linked: false
  , showLink: true
  , step: 1.0
  , min: Nothing
  , max: Nothing
  , disabled: false
  , precision: 2
  , onChangeX: Nothing
  , onChangeY: Nothing
  , onChangeZ: Nothing
  , onToggleLink: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set X value
x :: forall msg. Number -> PositionXYProp msg
x v props = props { x = v }

-- | Set Y value
y :: forall msg. Number -> PositionXYProp msg
y v props = props { y = v }

-- | Set Z value (enables 3D mode)
z :: forall msg. Number -> PositionXYProp msg
z v props = props { z = Just v }

-- | Set linked state
linked :: forall msg. Boolean -> PositionXYProp msg
linked l props = props { linked = l }

-- | Show/hide link button
showLink :: forall msg. Boolean -> PositionXYProp msg
showLink s props = props { showLink = s }

-- | Set step increment
step :: forall msg. Number -> PositionXYProp msg
step s props = props { step = s }

-- | Set minimum value
minValue :: forall msg. Number -> PositionXYProp msg
minValue m props = props { min = Just m }

-- | Set maximum value
maxValue :: forall msg. Number -> PositionXYProp msg
maxValue m props = props { max = Just m }

-- | Set disabled state
posDisabled :: forall msg. Boolean -> PositionXYProp msg
posDisabled d props = props { disabled = d }

-- | Set display precision
precision :: forall msg. Int -> PositionXYProp msg
precision p props = props { precision = p }

-- | X change handler
onChangeX :: forall msg. (Number -> msg) -> PositionXYProp msg
onChangeX handler props = props { onChangeX = Just handler }

-- | Y change handler
onChangeY :: forall msg. (Number -> msg) -> PositionXYProp msg
onChangeY handler props = props { onChangeY = Just handler }

-- | Z change handler
onChangeZ :: forall msg. (Number -> msg) -> PositionXYProp msg
onChangeZ handler props = props { onChangeZ = Just handler }

-- | Link toggle handler
onToggleLink :: forall msg. (Boolean -> msg) -> PositionXYProp msg
onToggleLink handler props = props { onToggleLink = Just handler }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Round to specified precision (decimal places)
-- |
-- | Essential for display formatting of position values.
-- | ```purescript
-- | roundTo 2 3.14159  -- 3.14
-- | roundTo 0 3.7      -- 4.0
-- | ```
roundTo :: Int -> Number -> Number
roundTo prec val =
  let
    factor = power 10.0 prec
    rounded = Int.toNumber (Int.round (val * factor))
  in
    rounded / factor

-- | Power function for precision rounding
-- |
-- | Computes base^exp for both positive and negative exponents.
-- | Used by roundTo to calculate decimal place factors.
power :: Number -> Int -> Number
power base exp =
  if exp == 0 then 1.0
  else if exp > 0 then base * power base (exp - 1)
  else 1.0 / power base (negate exp)

-- | Format display value with precision
-- |
-- | Intelligently formats numbers for display:
-- | - Removes unnecessary decimal points for whole numbers at precision 0
-- | - Rounds to specified precision for decimal values
formatValue :: Int -> Number -> String
formatValue prec val =
  let
    rounded = roundTo prec val
    floored = Number.floor rounded
  in
    if prec == 0 && rounded == floored
      then show (Int.round rounded)
      else show rounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // component
-- ═════════════════════════════════════════════════════════════════════════════

-- | PositionXY component
-- |
-- | Paired/tripled numeric inputs for spatial coordinates.
-- | Pure Element — renders to DOM, Halogen, Static HTML, or any target.
positionXY :: forall msg. Array (PositionXYProp msg) -> E.Element msg
positionXY propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    -- Container styles
    containerStyles =
      [ E.style "display" "flex"
      , E.style "align-items" "center"
      , E.style "gap" "8px"
      ]
    
    disabledStyles = if props.disabled
      then [ E.style "opacity" "0.5", E.style "pointer-events" "none" ]
      else []
    
    -- Min/max attributes
    minAttr = case props.min of
      Just m -> [ E.attr "min" (show m) ]
      Nothing -> []
    
    maxAttr = case props.max of
      Just m -> [ E.attr "max" (show m) ]
      Nothing -> []
    
    stepAttr = [ E.attr "step" (show props.step) ]
    
    -- X row
    xRow = axisRow "X" props.x props.precision minAttr maxAttr stepAttr props.disabled
    
    -- Link button
    linkBtn = if props.showLink
      then
        [ E.button_
            [ E.class_ "link-btn"
            , E.style "width" "20px"
            , E.style "height" "20px"
            , E.style "padding" "0"
            , E.style "border" "none"
            , E.style "border-radius" "3px"
            , E.style "background" "transparent"
            , E.style "color" (if props.linked then "#7c9cff" else "#666")
            , E.style "cursor" "pointer"
            , E.style "display" "flex"
            , E.style "align-items" "center"
            , E.style "justify-content" "center"
            , E.style "transition" "all 0.1s"
            , E.title "Link X and Y"
            ]
            [ linkIcon props.linked ]
        ]
      else []
    
    -- Y row
    yRow = axisRow "Y" props.y props.precision minAttr maxAttr stepAttr props.disabled
    
    -- Z row (optional)
    zRow = case props.z of
      Just zVal -> [ axisRow "Z" zVal props.precision minAttr maxAttr stepAttr props.disabled ]
      Nothing -> []
  in
    E.div_
      (containerStyles <> disabledStyles <> [ E.class_ "position-xy" ])
      ([ xRow ] <> linkBtn <> [ yRow ] <> zRow)

-- | Single axis row (label + input)
axisRow :: forall msg. String -> Number -> Int -> Array (E.Attribute msg) -> Array (E.Attribute msg) -> Array (E.Attribute msg) -> Boolean -> E.Element msg
axisRow labelText val prec minAttr maxAttr stepAttr isDisabled =
  E.div_
    [ E.class_ "position-row"
    , E.style "display" "flex"
    , E.style "align-items" "center"
    , E.style "gap" "4px"
    ]
    [ E.label_
        [ E.class_ "axis-label"
        , E.style "font-size" "12px"
        , E.style "color" "#666"
        , E.style "font-weight" "500"
        , E.style "min-width" "12px"
        ]
        [ E.text labelText ]
    , E.input_
        ( [ E.attr "type" "number"
          , E.class_ "position-input"
          , E.value (formatValue prec val)
          , E.disabled isDisabled
          , E.style "width" "55px"
          , E.style "padding" "4px 6px"
          , E.style "border" "1px solid #3d3d3d"
          , E.style "border-radius" "3px"
          , E.style "background" "#2a2a2a"
          , E.style "color" "#e0e0e0"
          , E.style "font-size" "13px"
          , E.style "text-align" "right"
          ] <> minAttr <> maxAttr <> stepAttr
        )
    ]

-- | Link icon (chain or minus based on state)
linkIcon :: forall msg. Boolean -> E.Element msg
linkIcon isLinked =
  if isLinked
    then
      -- Chain link icon
      E.svg_
        [ E.attr "xmlns" "http://www.w3.org/2000/svg"
        , E.attr "viewBox" "0 0 24 24"
        , E.attr "fill" "none"
        , E.attr "stroke" "currentColor"
        , E.attr "stroke-width" "2"
        , E.attr "stroke-linecap" "round"
        , E.attr "stroke-linejoin" "round"
        , E.style "width" "12px"
        , E.style "height" "12px"
        ]
        [ E.path_ [ E.attr "d" "M10 13a5 5 0 0 0 7.54.54l3-3a5 5 0 0 0-7.07-7.07l-1.72 1.71" ]
        , E.path_ [ E.attr "d" "M14 11a5 5 0 0 0-7.54-.54l-3 3a5 5 0 0 0 7.07 7.07l1.71-1.71" ]
        ]
    else
      -- Minus/unlink icon
      E.svg_
        [ E.attr "xmlns" "http://www.w3.org/2000/svg"
        , E.attr "viewBox" "0 0 24 24"
        , E.attr "fill" "none"
        , E.attr "stroke" "currentColor"
        , E.attr "stroke-width" "2"
        , E.attr "stroke-linecap" "round"
        , E.attr "stroke-linejoin" "round"
        , E.style "width" "12px"
        , E.style "height" "12px"
        ]
        [ E.line_ [ E.attr "x1" "5", E.attr "y1" "12", E.attr "x2" "19", E.attr "y2" "12" ]
        ]
