-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                           // hydrogen // element // separator
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Separator — Schema-native visual divider component.
-- |
-- | ## Design Philosophy
-- |
-- | This component accepts **concrete Schema atoms**, not semantic tokens.
-- |
-- | ## Schema Atoms Accepted
-- |
-- | | Property         | Pillar     | Type                      | CSS Output              |
-- | |------------------|------------|---------------------------|-------------------------|
-- | | color            | Color      | Color.RGB                 | background-color        |
-- | | thickness        | Dimension  | Device.Pixel              | height/width            |
-- | | labelColor       | Color      | Color.RGB                 | color (for label)       |
-- | | labelFontSize    | Typography | Typography.FontSize       | font-size               |
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.Separator as Separator
-- | import Hydrogen.Schema.Color.RGB as Color
-- |
-- | -- Horizontal separator (default)
-- | Separator.separator []
-- |
-- | -- Vertical separator
-- | Separator.separator [ Separator.orientation Separator.Vertical ]
-- |
-- | -- With brand atoms
-- | Separator.separator
-- |   [ Separator.color brand.dividerColor
-- |   , Separator.thickness (Device.px 2.0)
-- |   ]
-- |
-- | -- With label
-- | Separator.separatorWithLabel
-- |   [ Separator.labelColor brand.mutedText ]
-- |   [ E.text "OR" ]
-- | ```

module Hydrogen.Element.Compound.Separator
  ( -- * Main Components
    separator
  , separatorWithLabel
  
  -- * Types
  , Orientation(Horizontal, Vertical)
  
  -- * Props
  , SeparatorProps
  , SeparatorProp
  , defaultProps
  
  -- * Orientation
  , orientation
  
  -- * Color Atoms
  , color
  , labelColor
  
  -- * Dimension Atoms
  , thickness
  , gap
  
  -- * Typography Atoms
  , labelFontSize
  
  -- * Escape Hatch
  , extraAttributes
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  )

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just), maybe)

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Typography.FontSize as FontSize

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Separator orientation
data Orientation
  = Horizontal
  | Vertical

derive instance eqOrientation :: Eq Orientation

instance showOrientation :: Show Orientation where
  show Horizontal = "horizontal"
  show Vertical = "vertical"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Separator properties
type SeparatorProps msg =
  { -- Orientation
    orientation :: Orientation
  
  -- Color atoms
  , color :: Maybe Color.RGB
  , labelColor :: Maybe Color.RGB
  
  -- Dimension atoms
  , thickness :: Maybe Device.Pixel
  , gap :: Maybe Device.Pixel
  
  -- Typography atoms
  , labelFontSize :: Maybe FontSize.FontSize
  
  -- Escape hatch
  , extraAttributes :: Array (E.Attribute msg)
  }

-- | Property modifier
type SeparatorProp msg = SeparatorProps msg -> SeparatorProps msg

-- | Default properties
defaultProps :: forall msg. SeparatorProps msg
defaultProps =
  { orientation: Horizontal
  , color: Nothing
  , labelColor: Nothing
  , thickness: Nothing
  , gap: Nothing
  , labelFontSize: Nothing
  , extraAttributes: []
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                 // prop builders: orientation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set separator orientation
orientation :: forall msg. Orientation -> SeparatorProp msg
orientation o props = props { orientation = o }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: color
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set separator color (Color.RGB atom)
color :: forall msg. Color.RGB -> SeparatorProp msg
color c props = props { color = Just c }

-- | Set label text color (Color.RGB atom)
labelColor :: forall msg. Color.RGB -> SeparatorProp msg
labelColor c props = props { labelColor = Just c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // prop builders: dimension
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set separator thickness (Device.Pixel atom)
thickness :: forall msg. Device.Pixel -> SeparatorProp msg
thickness t props = props { thickness = Just t }

-- | Set gap around label (Device.Pixel atom)
gap :: forall msg. Device.Pixel -> SeparatorProp msg
gap g props = props { gap = Just g }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // prop builders: typography
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set label font size (FontSize atom)
labelFontSize :: forall msg. FontSize.FontSize -> SeparatorProp msg
labelFontSize s props = props { labelFontSize = Just s }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                // prop builders: escape hatch
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add extra attributes (escape hatch)
extraAttributes :: forall msg. Array (E.Attribute msg) -> SeparatorProp msg
extraAttributes attrs props = props { extraAttributes = props.extraAttributes <> attrs }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // main component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a separator line
-- |
-- | Pure Element — renders to DOM, Halogen, Static HTML, or any target.
separator :: forall msg. Array (SeparatorProp msg) -> E.Element msg
separator propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
  in
    E.div_
      (buildSeparatorAttrs props)
      []

-- | Build separator attributes
buildSeparatorAttrs :: forall msg. SeparatorProps msg -> Array (E.Attribute msg)
buildSeparatorAttrs props =
  let
    -- Default color
    defaultColor = Color.rgb 226 232 240  -- Light gray
    sepColor = maybe defaultColor (\c -> c) props.color
    
    -- Thickness
    thicknessValue = maybe "1px" show props.thickness
    
    -- Orientation-specific styles
    orientationStyles = case props.orientation of
      Horizontal ->
        [ E.style "width" "100%"
        , E.style "height" thicknessValue
        ]
      Vertical ->
        [ E.style "width" thicknessValue
        , E.style "height" "100%"
        ]
    
    -- Core styles
    coreStyles =
      [ E.role "separator"
      , E.style "flex-shrink" "0"
      , E.style "background-color" (Color.toLegacyCss sepColor)
      ]
  in
    coreStyles <> orientationStyles <> props.extraAttributes

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // labeled separator
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a separator with centered label
-- |
-- | Always horizontal. Label is centered with lines on either side.
separatorWithLabel :: forall msg. Array (SeparatorProp msg) -> Array (E.Element msg) -> E.Element msg
separatorWithLabel propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    -- Default colors
    defaultSepColor = Color.rgb 226 232 240
    defaultLabelColor = Color.rgb 148 163 184  -- Muted gray
    
    sepColor = maybe defaultSepColor (\c -> c) props.color
    lblColor = maybe defaultLabelColor (\c -> c) props.labelColor
    
    -- Gap
    gapValue = maybe "12px" show props.gap
    
    -- Font size
    fontSizeStyle = case props.labelFontSize of
      Nothing -> [ E.style "font-size" "12px" ]
      Just s -> [ E.style "font-size" (FontSize.toLegacyCss s) ]
    
    -- Line element
    lineElement =
      E.div_
        [ E.style "flex" "1"
        , E.style "height" "1px"
        , E.style "background-color" (Color.toLegacyCss sepColor)
        ]
        []
    
    -- Label element
    labelElement =
      E.span_
        ( [ E.style "padding-left" gapValue
          , E.style "padding-right" gapValue
          , E.style "color" (Color.toLegacyCss lblColor)
          , E.style "white-space" "nowrap"
          ]
          <> fontSizeStyle
        )
        children
  in
    E.div_
      ( [ E.style "display" "flex"
        , E.style "align-items" "center"
        , E.style "width" "100%"
        ]
        <> props.extraAttributes
      )
      [ lineElement
      , labelElement
      , lineElement
      ]
