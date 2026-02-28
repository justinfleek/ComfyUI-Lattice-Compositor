-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                              // hydrogen // element // swatch
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Swatch — Schema-native color swatch component.
-- |
-- | ## Design Philosophy
-- |
-- | A swatch displays a color sample with optional transparency indication.
-- | This component accepts **concrete Schema atoms**, not semantic tokens.
-- |
-- | ## Schema Atoms Accepted
-- |
-- | | Property         | Pillar     | Type                        | CSS Output              |
-- | |------------------|------------|-----------------------------|-------------------------|
-- | | color            | Color      | Color.RGBA                  | background-color        |
-- | | size             | Dimension  | Swatch.SwatchSize           | width, height           |
-- | | checkerboardSize | Dimension  | Swatch.CheckerboardSize     | background-size         |
-- | | borderRadius     | Geometry   | Geometry.Corners            | border-radius           |
-- | | borderColor      | Color      | Color.RGB                   | border-color            |
-- | | borderWidth      | Dimension  | Stroke.StrokeWidth          | border-width            |
-- |
-- | ## Transparency Display
-- |
-- | When displaying colors with alpha < 1.0, a checkerboard pattern
-- | appears behind the color to indicate transparency. The checkerboard
-- | uses CSS gradients — no images required.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.Swatch as Swatch
-- | import Hydrogen.Schema.Color.RGB as Color
-- | import Hydrogen.Schema.Dimension.Swatch as SwatchDim
-- |
-- | -- Basic opaque swatch
-- | Swatch.swatch
-- |   [ Swatch.color (Color.rgba 255 0 0 255)
-- |   , Swatch.size SwatchDim.swatchSizeMd
-- |   ]
-- |
-- | -- Transparent swatch (shows checkerboard)
-- | Swatch.swatch
-- |   [ Swatch.color (Color.rgba 255 0 0 128)
-- |   , Swatch.size SwatchDim.swatchSizeLg
-- |   , Swatch.checkerboardSize SwatchDim.checkerboardSizeMd
-- |   ]
-- |
-- | -- Clickable swatch in a picker
-- | Swatch.swatch
-- |   [ Swatch.color brandColor
-- |   , Swatch.size SwatchDim.swatchSizeSm
-- |   , Swatch.onClick (SelectColor brandColor)
-- |   , Swatch.selected true
-- |   ]
-- | ```

module Hydrogen.Element.Compound.Swatch
  ( -- * Main Component
    swatch
  
  -- * Props
  , SwatchProps
  , SwatchProp
  , defaultProps
  
  -- * Color Atoms
  , color
  , borderColor
  
  -- * Dimension Atoms
  , size
  , checkerboardSize
  , borderWidth
  
  -- * Geometry Atoms
  , borderRadius
  
  -- * Behavior Props
  , onClick
  , selected
  , disabled
  
  -- * Accessibility
  , ariaLabel
  
  -- * Escape Hatch
  , extraAttributes
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( show
  , negate
  , (<>)
  , (<)
  , (==)
  , (&&)
  , not
  , (*)
  )

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just), maybe, isJust)

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Color.Opacity as Opacity
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Dimension.Swatch as SwatchDim
import Hydrogen.Schema.Dimension.Stroke as Stroke

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Swatch properties
type SwatchProps msg =
  { -- Color atoms
    color :: Maybe Color.RGBA
  , borderColor :: Maybe Color.RGB
  
  -- Dimension atoms
  , size :: Maybe SwatchDim.SwatchSize
  , checkerboardSize :: Maybe SwatchDim.CheckerboardSize
  , borderWidth :: Maybe Stroke.StrokeWidth
  
  -- Geometry atoms
  , borderRadius :: Maybe Geometry.Corners
  
  -- Behavior
  , onClick :: Maybe msg
  , selected :: Boolean
  , disabled :: Boolean
  
  -- Accessibility
  , ariaLabel :: Maybe String
  
  -- Escape hatch
  , extraAttributes :: Array (E.Attribute msg)
  }

-- | Property modifier
type SwatchProp msg = SwatchProps msg -> SwatchProps msg

-- | Default properties
defaultProps :: forall msg. SwatchProps msg
defaultProps =
  { color: Nothing
  , borderColor: Nothing
  , size: Nothing
  , checkerboardSize: Nothing
  , borderWidth: Nothing
  , borderRadius: Nothing
  , onClick: Nothing
  , selected: false
  , disabled: false
  , ariaLabel: Nothing
  , extraAttributes: []
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: color
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set the swatch color (Color.RGBA atom)
-- |
-- | When alpha < 255, a checkerboard pattern will appear behind the color.
color :: forall msg. Color.RGBA -> SwatchProp msg
color c props = props { color = Just c }

-- | Set the border color (Color.RGB atom)
borderColor :: forall msg. Color.RGB -> SwatchProp msg
borderColor c props = props { borderColor = Just c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // prop builders: dimension
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set the swatch size (SwatchSize atom)
-- |
-- | Swatches are square — this sets both width and height.
size :: forall msg. SwatchDim.SwatchSize -> SwatchProp msg
size s props = props { size = Just s }

-- | Set the checkerboard cell size (CheckerboardSize atom)
-- |
-- | Only visible when the color has transparency (alpha < 255).
checkerboardSize :: forall msg. SwatchDim.CheckerboardSize -> SwatchProp msg
checkerboardSize s props = props { checkerboardSize = Just s }

-- | Set the border width (StrokeWidth atom)
borderWidth :: forall msg. Stroke.StrokeWidth -> SwatchProp msg
borderWidth w props = props { borderWidth = Just w }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: geometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set the border radius (Corners atom)
borderRadius :: forall msg. Geometry.Corners -> SwatchProp msg
borderRadius r props = props { borderRadius = Just r }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: behavior
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set click handler
-- |
-- | When provided, the swatch becomes interactive (cursor: pointer).
onClick :: forall msg. msg -> SwatchProp msg
onClick msg props = props { onClick = Just msg }

-- | Mark swatch as selected
-- |
-- | Adds a visual indicator (typically a ring or checkmark).
selected :: forall msg. Boolean -> SwatchProp msg
selected s props = props { selected = s }

-- | Disable the swatch
-- |
-- | Prevents interaction and reduces opacity.
disabled :: forall msg. Boolean -> SwatchProp msg
disabled d props = props { disabled = d }

-- ═════════════════════════════════════════════════════════════════════════════
--                                               // prop builders: accessibility
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set accessible label
-- |
-- | Example: "Red, #FF0000" or "Brand Primary Color"
ariaLabel :: forall msg. String -> SwatchProp msg
ariaLabel label props = props { ariaLabel = Just label }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                // prop builders: escape hatch
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add extra attributes
extraAttributes :: forall msg. Array (E.Attribute msg) -> SwatchProp msg
extraAttributes attrs props = props { extraAttributes = attrs }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a color swatch element
-- |
-- | The swatch displays a color sample. For transparent colors (alpha < 255),
-- | a checkerboard pattern appears behind the color to indicate transparency.
swatch :: forall msg. Array (SwatchProp msg) -> E.Element msg
swatch propModifiers =
  let
    props = foldl (\p f -> f p) defaultProps propModifiers
    
    -- Size (default to medium)
    swatchSizeVal = maybe 32.0 SwatchDim.swatchSizeValue props.size
    sizeStr = show swatchSizeVal <> "px"
    
    -- Checkerboard (default to medium)
    checkerSizeVal = maybe 8.0 SwatchDim.checkerboardSizeValue props.checkerboardSize
    
    -- Check if we need transparency display
    hasTransparency = case props.color of
      Nothing -> false
      Just rgba -> not (Opacity.isOpaque (Color.alpha rgba))
    
    -- Build styles
    baseStyles =
      [ E.style "display" "inline-block"
      , E.style "position" "relative"
      , E.style "width" sizeStr
      , E.style "height" sizeStr
      , E.style "overflow" "hidden"
      , E.style "box-sizing" "border-box"
      ]
    
    -- Border styles
    borderStyles = buildBorderStyles props
    
    -- Cursor and interaction styles
    interactionStyles = buildInteractionStyles props
    
    -- Radius styles
    radiusStyles = case props.borderRadius of
      Nothing -> []
      Just r -> [ E.style "border-radius" (Geometry.cornersToLegacyCss r) ]
    
    -- Selection indicator
    selectionStyles = 
      if props.selected
        then [ E.style "box-shadow" "0 0 0 2px currentColor" ]
        else []
    
    -- Accessibility
    accessibilityAttrs = buildAccessibilityAttrs props
    
    -- Event handlers
    eventHandlers = buildEventHandlers props
    
    -- All outer container attributes
    outerAttrs = 
      baseStyles 
      <> borderStyles 
      <> interactionStyles 
      <> radiusStyles 
      <> selectionStyles
      <> accessibilityAttrs
      <> eventHandlers
      <> props.extraAttributes
    
  in
    E.div_ outerAttrs
      [ -- Checkerboard layer (only if transparent)
        if hasTransparency
          then checkerboardLayer checkerSizeVal
          else E.empty
      
      -- Color layer
      , colorLayer props
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // internal: layers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Checkerboard background layer for transparency indication
-- |
-- | Uses CSS gradients to create the pattern — no images needed.
checkerboardLayer :: forall msg. Number -> E.Element msg
checkerboardLayer cellSize =
  let
    size2x = show (cellSize * 2.0) <> "px"
    sizeStr = show cellSize <> "px"
    
    -- Checkerboard pattern using CSS gradients
    -- Two overlapping 45-degree gradients create the checkerboard effect
    gradient1 = "linear-gradient(45deg, #ccc 25%, transparent 25%, transparent 75%, #ccc 75%, #ccc)"
    gradient2 = "linear-gradient(45deg, #ccc 25%, transparent 25%, transparent 75%, #ccc 75%, #ccc)"
    
    backgroundImage = gradient1 <> ", " <> gradient2
    backgroundSize = size2x <> " " <> size2x
    backgroundPosition = "0 0, " <> sizeStr <> " " <> sizeStr
  in
    E.div_
      [ E.style "position" "absolute"
      , E.style "inset" "0"
      , E.style "background-color" "#fff"
      , E.style "background-image" backgroundImage
      , E.style "background-size" backgroundSize
      , E.style "background-position" backgroundPosition
      , E.ariaHidden true
      ]
      []

-- | Color overlay layer
colorLayer :: forall msg. SwatchProps msg -> E.Element msg
colorLayer props =
  let
    colorStyle = case props.color of
      Nothing -> [ E.style "background-color" "transparent" ]
      Just rgba -> [ E.style "background-color" (Color.toLegacyCssA rgba) ]
  in
    E.div_
      ( [ E.style "position" "absolute"
        , E.style "inset" "0"
        , E.ariaHidden true
        ] <> colorStyle
      )
      []

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // internal: style builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Build border styles from props
buildBorderStyles :: forall msg. SwatchProps msg -> Array (E.Attribute msg)
buildBorderStyles props =
  let
    widthStyle = case props.borderWidth of
      Nothing -> []
      Just w -> 
        if Stroke.isStrokeWidthZero w
          then []
          else [ E.style "border-width" (Stroke.strokeWidthToCss w)
               , E.style "border-style" "solid"
               ]
    
    colorStyle = case props.borderColor of
      Nothing -> 
        -- Default to semi-transparent black border if width is set
        case props.borderWidth of
          Nothing -> []
          Just _ -> [ E.style "border-color" "rgba(0, 0, 0, 0.1)" ]
      Just c -> [ E.style "border-color" (Color.toLegacyCss c) ]
  in
    widthStyle <> colorStyle

-- | Build interaction styles
buildInteractionStyles :: forall msg. SwatchProps msg -> Array (E.Attribute msg)
buildInteractionStyles props =
  let
    cursorStyle = case props.onClick of
      Nothing -> []
      Just _ -> 
        if props.disabled
          then [ E.style "cursor" "not-allowed" ]
          else [ E.style "cursor" "pointer" ]
    
    opacityStyle = 
      if props.disabled
        then [ E.style "opacity" "0.5" ]
        else []
  in
    cursorStyle <> opacityStyle

-- | Build accessibility attributes
buildAccessibilityAttrs :: forall msg. SwatchProps msg -> Array (E.Attribute msg)
buildAccessibilityAttrs props =
  let
    roleAttr = case props.onClick of
      Nothing -> []
      Just _ -> [ E.role "button" ]
    
    labelAttr = case props.ariaLabel of
      Nothing -> []
      Just label -> [ E.ariaLabel label ]
    
    selectedAttr = 
      if props.selected
        then [ E.attr "aria-selected" "true" ]
        else []
    
    disabledAttr =
      if props.disabled && isJust props.onClick
        then [ E.attr "aria-disabled" "true" ]
        else []
    
    tabIndexAttr = case props.onClick of
      Nothing -> []
      Just _ -> 
        if props.disabled
          then [ E.tabIndex (-1) ]
          else [ E.tabIndex 0 ]
  in
    roleAttr <> labelAttr <> selectedAttr <> disabledAttr <> tabIndexAttr

-- | Build event handlers
buildEventHandlers :: forall msg. SwatchProps msg -> Array (E.Attribute msg)
buildEventHandlers props =
  case props.onClick of
    Nothing -> []
    Just msg ->
      if props.disabled
        then []
        else [ E.onClick msg ]


