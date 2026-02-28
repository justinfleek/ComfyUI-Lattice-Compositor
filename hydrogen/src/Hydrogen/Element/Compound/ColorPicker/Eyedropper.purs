-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // element // color-picker // eye-dropper
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Eyedropper — Screen color picker button and indicator.
-- |
-- | ## Design Philosophy
-- |
-- | The eyedropper allows picking colors from anywhere on screen.
-- | This component renders:
-- | - An eyedropper icon button to activate picking mode
-- | - Visual feedback when picking is active
-- | - The picked color preview
-- |
-- | Note: Actual screen color picking requires browser EyeDropper API
-- | which is handled at the runtime/FFI boundary, not in this pure component.
-- |
-- | ## Schema Atoms Accepted
-- |
-- | | Property      | Pillar    | Type              | Purpose                |
-- | |---------------|-----------|-------------------|------------------------|
-- | | isActive      | Reactive  | Boolean           | Picking mode active    |
-- | | pickedColor   | Color     | Maybe RGB         | Last picked color      |
-- | | buttonSize    | Dimension | Pixel             | Button dimensions      |

module Hydrogen.Element.Compound.ColorPicker.Eyedropper
  ( -- * Component
    eyedropperButton
    
  -- * Props
  , EyedropperProps
  , EyedropperProp
  , defaultEyedropperProps
  
  -- * Prop Builders
  , isActive
  , pickedColor
  , buttonSize
  , borderRadius
  , onActivate
  , onDeactivate
  
  -- * Icon
  , eyedropperIcon
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( show
  , not
  , (<>)
  , ($)
  )

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just))

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as RGB
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Geometry.Radius as Radius

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Eyedropper button properties
type EyedropperProps msg =
  { -- State
    isActive :: Boolean
  , pickedColor :: Maybe RGB.RGB
  
  -- Dimensions
  , buttonSize :: Device.Pixel
  
  -- Appearance
  , borderRadius :: Maybe Radius.Radius
  
  -- Behavior
  , onActivate :: Maybe msg
  , onDeactivate :: Maybe msg
  }

-- | Property modifier
type EyedropperProp msg = EyedropperProps msg -> EyedropperProps msg

-- | Default properties
defaultEyedropperProps :: forall msg. EyedropperProps msg
defaultEyedropperProps =
  { isActive: false
  , pickedColor: Nothing
  , buttonSize: Device.px 36.0
  , borderRadius: Nothing
  , onActivate: Nothing
  , onDeactivate: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set active state
isActive :: forall msg. Boolean -> EyedropperProp msg
isActive b props = props { isActive = b }

-- | Set picked color
pickedColor :: forall msg. RGB.RGB -> EyedropperProp msg
pickedColor c props = props { pickedColor = Just c }

-- | Set button size
buttonSize :: forall msg. Device.Pixel -> EyedropperProp msg
buttonSize s props = props { buttonSize = s }

-- | Set border radius
borderRadius :: forall msg. Radius.Radius -> EyedropperProp msg
borderRadius r props = props { borderRadius = Just r }

-- | Set activation handler
onActivate :: forall msg. msg -> EyedropperProp msg
onActivate m props = props { onActivate = Just m }

-- | Set deactivation handler
onDeactivate :: forall msg. msg -> EyedropperProp msg
onDeactivate m props = props { onDeactivate = Just m }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render eyedropper button
eyedropperButton :: forall msg. Array (EyedropperProp msg) -> E.Element msg
eyedropperButton propModifiers =
  let
    props = foldl (\p f -> f p) defaultEyedropperProps propModifiers
    
    -- Dimensions
    sizePx = show (Device.unwrapPixel props.buttonSize) <> "px"
    
    radiusStyle = case props.borderRadius of
      Just r -> Radius.toLegacyCss r
      Nothing -> "8px"
    
    -- Active styling
    bgColor = if props.isActive then "#3b82f6" else "#f3f4f6"
    iconColor = if props.isActive then "#fff" else "#374151"
    borderColor = if props.isActive then "#2563eb" else "#d1d5db"
    
    -- Cursor style depends on active state
    cursorStyle = if not props.isActive then "pointer" else "crosshair"
    
    -- Aria label for accessibility
    ariaLabel = if props.isActive 
      then "Eyedropper active - click anywhere to pick color"
      else "Activate eyedropper"
  in
    E.div_
      [ E.style "display" "inline-flex"
      , E.style "align-items" "center"
      , E.style "gap" "8px"
      ]
      [ -- Button
        E.button_
          [ E.style "width" sizePx
          , E.style "height" sizePx
          , E.style "display" "flex"
          , E.style "align-items" "center"
          , E.style "justify-content" "center"
          , E.style "background" bgColor
          , E.style "border" ("1px solid " <> borderColor)
          , E.style "border-radius" radiusStyle
          , E.style "cursor" cursorStyle
          , E.style "transition" "all 0.15s"
          , E.ariaLabel $ ariaLabel
          , E.attr "aria-pressed" $ show props.isActive
          ]
          [ eyedropperIcon iconColor ]
        
        -- Picked color preview (if any)
      , case props.pickedColor of
          Just color ->
            E.div_
              [ E.style "width" "24px"
              , E.style "height" "24px"
              , E.style "border-radius" "4px"
              , E.style "background" (RGB.toLegacyCss color)
              , E.style "border" "1px solid rgba(0,0,0,0.1)"
              ]
              []
          Nothing -> E.span_ [] []
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // icon
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render eyedropper SVG icon
eyedropperIcon :: forall msg. String -> E.Element msg
eyedropperIcon color =
  E.svg_
    [ E.attr "width" "20"
    , E.attr "height" "20"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "fill" "none"
    , E.attr "stroke" color
    , E.attr "stroke-width" "2"
    , E.attr "stroke-linecap" "round"
    , E.attr "stroke-linejoin" "round"
    ]
    [ -- Eyedropper path (simplified)
      E.path_
        [ E.attr "d" "M2 22l1-1h3l9-9" ]
    , E.path_
        [ E.attr "d" "M3 21v-3l9-9" ]
    , E.circle_
        [ E.attr "cx" "17"
        , E.attr "cy" "7"
        , E.attr "r" "5"
        ]
    ]
