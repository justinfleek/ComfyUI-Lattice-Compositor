-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // element // compound // badge
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Badge — Schema-native status indicator component.
-- |
-- | ## Design Philosophy
-- |
-- | This component accepts **concrete Schema atoms**, not semantic tokens.
-- | Colors and sizes come from the BrandSchema, not "variant" enums.
-- |
-- | ## Schema Atoms Accepted
-- |
-- | | Property         | Pillar     | Type                      | CSS Output              |
-- | |------------------|------------|---------------------------|-------------------------|
-- | | backgroundColor  | Color      | Color.RGB                 | background-color        |
-- | | textColor        | Color      | Color.RGB                 | color                   |
-- | | borderColor      | Color      | Color.RGB                 | border-color            |
-- | | borderRadius     | Geometry   | Geometry.Corners          | border-radius           |
-- | | borderWidth      | Dimension  | Device.Pixel              | border-width            |
-- | | paddingX         | Dimension  | Device.Pixel              | padding-left/right      |
-- | | paddingY         | Dimension  | Device.Pixel              | padding-top/bottom      |
-- | | fontSize         | Typography | Typography.FontSize       | font-size               |
-- | | fontWeight       | Typography | Typography.FontWeight     | font-weight             |
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.Badge as Badge
-- | import Hydrogen.Schema.Color.RGB as Color
-- |
-- | -- Basic badge with brand colors
-- | Badge.badge
-- |   [ Badge.backgroundColor brand.primaryColor
-- |   , Badge.textColor brand.onPrimaryColor
-- |   ]
-- |   [ E.text "New" ]
-- |
-- | -- Success badge
-- | Badge.badge
-- |   [ Badge.backgroundColor (Color.rgb 34 197 94)  -- Green
-- |   , Badge.textColor (Color.rgb 255 255 255)
-- |   ]
-- |   [ E.text "Active" ]
-- |
-- | -- Outline badge
-- | Badge.badge
-- |   [ Badge.borderColor brand.primaryColor
-- |   , Badge.textColor brand.primaryColor
-- |   ]
-- |   [ E.text "Draft" ]
-- | ```

module Hydrogen.Element.Compound.Badge
  ( -- * Main Component
    badge
  
  -- * Props
  , BadgeProps
  , BadgeProp
  , defaultProps
  
  -- * Color Atoms
  , backgroundColor
  , textColor
  , borderColor
  
  -- * Geometry Atoms
  , borderRadius
  , borderWidth
  
  -- * Dimension Atoms
  , paddingX
  , paddingY
  
  -- * Typography Atoms
  , fontSize
  , fontWeight
  
  -- * Escape Hatch
  , extraAttributes
  ) where

import Prelude
  ( show
  , (<>)
  )

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just), maybe)

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Typography.FontSize as FontSize
import Hydrogen.Schema.Typography.FontWeight as FontWeight

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Badge properties
type BadgeProps msg =
  { -- Color atoms
    backgroundColor :: Maybe Color.RGB
  , textColor :: Maybe Color.RGB
  , borderColor :: Maybe Color.RGB
  
  -- Geometry atoms
  , borderRadius :: Maybe Geometry.Corners
  , borderWidth :: Maybe Device.Pixel
  
  -- Dimension atoms
  , paddingX :: Maybe Device.Pixel
  , paddingY :: Maybe Device.Pixel
  
  -- Typography atoms
  , fontSize :: Maybe FontSize.FontSize
  , fontWeight :: Maybe FontWeight.FontWeight
  
  -- Escape hatch
  , extraAttributes :: Array (E.Attribute msg)
  }

-- | Property modifier
type BadgeProp msg = BadgeProps msg -> BadgeProps msg

-- | Default properties
defaultProps :: forall msg. BadgeProps msg
defaultProps =
  { backgroundColor: Nothing
  , textColor: Nothing
  , borderColor: Nothing
  , borderRadius: Nothing
  , borderWidth: Nothing
  , paddingX: Nothing
  , paddingY: Nothing
  , fontSize: Nothing
  , fontWeight: Nothing
  , extraAttributes: []
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: color
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set badge background color (Color.RGB atom)
backgroundColor :: forall msg. Color.RGB -> BadgeProp msg
backgroundColor c props = props { backgroundColor = Just c }

-- | Set badge text color (Color.RGB atom)
textColor :: forall msg. Color.RGB -> BadgeProp msg
textColor c props = props { textColor = Just c }

-- | Set badge border color (Color.RGB atom)
-- |
-- | For outline-style badges, set this without backgroundColor.
borderColor :: forall msg. Color.RGB -> BadgeProp msg
borderColor c props = props { borderColor = Just c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: geometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set border radius (Geometry.Corners atom)
-- |
-- | Default is fully rounded (pill shape).
borderRadius :: forall msg. Geometry.Corners -> BadgeProp msg
borderRadius r props = props { borderRadius = Just r }

-- | Set border width (Device.Pixel atom)
borderWidth :: forall msg. Device.Pixel -> BadgeProp msg
borderWidth w props = props { borderWidth = Just w }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // prop builders: dimension
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set horizontal padding (Device.Pixel atom)
paddingX :: forall msg. Device.Pixel -> BadgeProp msg
paddingX p props = props { paddingX = Just p }

-- | Set vertical padding (Device.Pixel atom)
paddingY :: forall msg. Device.Pixel -> BadgeProp msg
paddingY p props = props { paddingY = Just p }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // prop builders: typography
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set font size (FontSize atom)
fontSize :: forall msg. FontSize.FontSize -> BadgeProp msg
fontSize s props = props { fontSize = Just s }

-- | Set font weight (FontWeight atom)
fontWeight :: forall msg. FontWeight.FontWeight -> BadgeProp msg
fontWeight w props = props { fontWeight = Just w }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                // prop builders: escape hatch
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add extra attributes (escape hatch)
extraAttributes :: forall msg. Array (E.Attribute msg) -> BadgeProp msg
extraAttributes attrs props = props { extraAttributes = props.extraAttributes <> attrs }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // main component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a badge
-- |
-- | Pure Element — renders to DOM, Halogen, Static HTML, or any target.
badge :: forall msg. Array (BadgeProp msg) -> Array (E.Element msg) -> E.Element msg
badge propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
  in
    E.span_
      (buildBadgeAttrs props)
      children

-- | Build badge attributes from props
buildBadgeAttrs :: forall msg. BadgeProps msg -> Array (E.Attribute msg)
buildBadgeAttrs props =
  let
    -- Default values
    defaultBgColor = Color.rgb 59 130 246  -- Blue
    defaultTextColor = Color.rgb 255 255 255  -- White
    
    -- Core styles
    coreStyles =
      [ E.style "display" "inline-flex"
      , E.style "align-items" "center"
      , E.style "justify-content" "center"
      , E.style "white-space" "nowrap"
      , E.style "vertical-align" "middle"
      ]
    
    -- Background color (transparent if not set and border is set = outline style)
    bgStyle = case props.backgroundColor of
      Just c -> [ E.style "background-color" (Color.toLegacyCss c) ]
      Nothing -> case props.borderColor of
        Just _ -> [ E.style "background-color" "transparent" ]
        Nothing -> [ E.style "background-color" (Color.toLegacyCss defaultBgColor) ]
    
    -- Text color
    textStyle = case props.textColor of
      Just c -> [ E.style "color" (Color.toLegacyCss c) ]
      Nothing -> [ E.style "color" (Color.toLegacyCss defaultTextColor) ]
    
    -- Border styles
    borderStyle = case props.borderColor of
      Nothing -> [ E.style "border" "1px solid transparent" ]
      Just bc ->
        let bw = maybe "1px" show props.borderWidth
        in [ E.style "border-style" "solid"
           , E.style "border-width" bw
           , E.style "border-color" (Color.toLegacyCss bc)
           ]
    
    -- Border radius (default: fully rounded)
    radiusStyle = case props.borderRadius of
      Nothing -> [ E.style "border-radius" "9999px" ]  -- Pill shape
      Just r -> [ E.style "border-radius" (Geometry.cornersToLegacyCss r) ]
    
    -- Padding
    paddingStyle =
      let
        px = maybe "10px" show props.paddingX
        py = maybe "2px" show props.paddingY
      in
        [ E.style "padding" (py <> " " <> px) ]
    
    -- Typography
    fontSizeStyle = case props.fontSize of
      Nothing -> [ E.style "font-size" "12px" ]
      Just s -> [ E.style "font-size" (FontSize.toLegacyCss s) ]
    
    fontWeightStyle = case props.fontWeight of
      Nothing -> [ E.style "font-weight" "600" ]
      Just w -> [ E.style "font-weight" (FontWeight.toLegacyCss w) ]
    
    -- Line height
    lineHeightStyle = [ E.style "line-height" "1" ]
  in
    coreStyles 
    <> bgStyle 
    <> textStyle 
    <> borderStyle 
    <> radiusStyle 
    <> paddingStyle 
    <> fontSizeStyle 
    <> fontWeightStyle 
    <> lineHeightStyle
    <> props.extraAttributes
