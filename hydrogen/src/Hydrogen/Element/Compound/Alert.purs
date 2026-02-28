-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // element // compound // alert
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Alert — Schema-native notification/message component.
-- |
-- | ## Design Philosophy
-- |
-- | This component accepts **concrete Schema atoms**, not semantic tokens.
-- | Every visual property maps directly to atoms from the 12 pillars.
-- |
-- | ## Schema Atoms Accepted
-- |
-- | | Property         | Pillar     | Type                      | CSS Output              |
-- | |------------------|------------|---------------------------|-------------------------|
-- | | backgroundColor  | Color      | Color.RGB                 | background-color        |
-- | | textColor        | Color      | Color.RGB                 | color                   |
-- | | borderColor      | Color      | Color.RGB                 | border-color            |
-- | | iconColor        | Color      | Color.RGB                 | icon fill/stroke        |
-- | | borderRadius     | Geometry   | Geometry.Corners          | border-radius           |
-- | | borderWidth      | Dimension  | Device.Pixel              | border-width            |
-- | | padding          | Dimension  | Device.Pixel              | padding                 |
-- | | gap              | Dimension  | Device.Pixel              | gap                     |
-- | | titleFontSize    | Typography | Typography.FontSize       | font-size               |
-- | | titleFontWeight  | Typography | Typography.FontWeight     | font-weight             |
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.Alert as Alert
-- | import Hydrogen.Schema.Color.RGB as Color
-- |
-- | -- Basic alert
-- | Alert.alert []
-- |   [ Alert.alertTitle [] [ E.text "Heads up!" ]
-- |   , Alert.alertDescription [] [ E.text "Important information here." ]
-- |   ]
-- |
-- | -- With brand atoms (error style)
-- | Alert.alert
-- |   [ Alert.backgroundColor brand.errorBackground
-- |   , Alert.borderColor brand.errorBorder
-- |   , Alert.textColor brand.errorText
-- |   ]
-- |   [ Alert.alertTitle [] [ E.text "Error" ]
-- |   , Alert.alertDescription [] [ E.text "Something went wrong." ]
-- |   ]
-- | ```

module Hydrogen.Element.Compound.Alert
  ( -- * Main Component
    alert
  
  -- * Section Components
  , alertTitle
  , alertDescription
  , alertIcon
  
  -- * Props
  , AlertProps
  , AlertProp
  , defaultProps
  
  -- * Color Atoms
  , backgroundColor
  , textColor
  , borderColor
  , iconColor
  , titleColor
  , descriptionColor
  
  -- * Geometry Atoms
  , borderRadius
  , borderWidth
  
  -- * Dimension Atoms
  , padding
  , gap
  , iconSize
  
  -- * Typography Atoms
  , titleFontSize
  , titleFontWeight
  , descriptionFontSize
  
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

-- | Alert properties
type AlertProps msg =
  { -- Color atoms
    backgroundColor :: Maybe Color.RGB
  , textColor :: Maybe Color.RGB
  , borderColor :: Maybe Color.RGB
  , iconColor :: Maybe Color.RGB
  , titleColor :: Maybe Color.RGB
  , descriptionColor :: Maybe Color.RGB
  
  -- Geometry atoms
  , borderRadius :: Maybe Geometry.Corners
  , borderWidth :: Maybe Device.Pixel
  
  -- Dimension atoms
  , padding :: Maybe Device.Pixel
  , gap :: Maybe Device.Pixel
  , iconSize :: Maybe Device.Pixel
  
  -- Typography atoms
  , titleFontSize :: Maybe FontSize.FontSize
  , titleFontWeight :: Maybe FontWeight.FontWeight
  , descriptionFontSize :: Maybe FontSize.FontSize
  
  -- Escape hatch
  , extraAttributes :: Array (E.Attribute msg)
  }

-- | Property modifier
type AlertProp msg = AlertProps msg -> AlertProps msg

-- | Default properties
defaultProps :: forall msg. AlertProps msg
defaultProps =
  { backgroundColor: Nothing
  , textColor: Nothing
  , borderColor: Nothing
  , iconColor: Nothing
  , titleColor: Nothing
  , descriptionColor: Nothing
  , borderRadius: Nothing
  , borderWidth: Nothing
  , padding: Nothing
  , gap: Nothing
  , iconSize: Nothing
  , titleFontSize: Nothing
  , titleFontWeight: Nothing
  , descriptionFontSize: Nothing
  , extraAttributes: []
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: color
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set alert background color (Color.RGB atom)
backgroundColor :: forall msg. Color.RGB -> AlertProp msg
backgroundColor c props = props { backgroundColor = Just c }

-- | Set alert text color (Color.RGB atom)
textColor :: forall msg. Color.RGB -> AlertProp msg
textColor c props = props { textColor = Just c }

-- | Set alert border color (Color.RGB atom)
borderColor :: forall msg. Color.RGB -> AlertProp msg
borderColor c props = props { borderColor = Just c }

-- | Set icon color (Color.RGB atom)
iconColor :: forall msg. Color.RGB -> AlertProp msg
iconColor c props = props { iconColor = Just c }

-- | Set title text color (Color.RGB atom)
titleColor :: forall msg. Color.RGB -> AlertProp msg
titleColor c props = props { titleColor = Just c }

-- | Set description text color (Color.RGB atom)
descriptionColor :: forall msg. Color.RGB -> AlertProp msg
descriptionColor c props = props { descriptionColor = Just c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: geometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set border radius (Geometry.Corners atom)
borderRadius :: forall msg. Geometry.Corners -> AlertProp msg
borderRadius r props = props { borderRadius = Just r }

-- | Set border width (Device.Pixel atom)
borderWidth :: forall msg. Device.Pixel -> AlertProp msg
borderWidth w props = props { borderWidth = Just w }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // prop builders: dimension
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set padding (Device.Pixel atom)
padding :: forall msg. Device.Pixel -> AlertProp msg
padding p props = props { padding = Just p }

-- | Set gap between elements (Device.Pixel atom)
gap :: forall msg. Device.Pixel -> AlertProp msg
gap g props = props { gap = Just g }

-- | Set icon size (Device.Pixel atom)
iconSize :: forall msg. Device.Pixel -> AlertProp msg
iconSize s props = props { iconSize = Just s }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // prop builders: typography
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set title font size (FontSize atom)
titleFontSize :: forall msg. FontSize.FontSize -> AlertProp msg
titleFontSize s props = props { titleFontSize = Just s }

-- | Set title font weight (FontWeight atom)
titleFontWeight :: forall msg. FontWeight.FontWeight -> AlertProp msg
titleFontWeight w props = props { titleFontWeight = Just w }

-- | Set description font size (FontSize atom)
descriptionFontSize :: forall msg. FontSize.FontSize -> AlertProp msg
descriptionFontSize s props = props { descriptionFontSize = Just s }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                // prop builders: escape hatch
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add extra attributes (escape hatch)
extraAttributes :: forall msg. Array (E.Attribute msg) -> AlertProp msg
extraAttributes attrs props = props { extraAttributes = props.extraAttributes <> attrs }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // main component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render an alert
-- |
-- | Pure Element — renders to DOM, Halogen, Static HTML, or any target.
alert :: forall msg. Array (AlertProp msg) -> Array (E.Element msg) -> E.Element msg
alert propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
  in
    E.div_
      (buildAlertAttrs props)
      children

-- | Build alert attributes from props
buildAlertAttrs :: forall msg. AlertProps msg -> Array (E.Attribute msg)
buildAlertAttrs props =
  let
    -- Default values
    defaultBgColor = Color.rgb 255 255 255
    defaultBorderColor = Color.rgb 226 232 240
    
    bgColor = maybe defaultBgColor (\c -> c) props.backgroundColor
    brdColor = maybe defaultBorderColor (\c -> c) props.borderColor
    
    -- Core styles
    coreStyles =
      [ E.role "alert"
      , E.style "position" "relative"
      , E.style "width" "100%"
      , E.style "background-color" (Color.toLegacyCss bgColor)
      ]
    
    -- Text color
    textColorStyle = case props.textColor of
      Nothing -> []
      Just c -> [ E.style "color" (Color.toLegacyCss c) ]
    
    -- Border styles
    borderStyle =
      let bw = maybe "1px" show props.borderWidth
      in [ E.style "border-style" "solid"
         , E.style "border-width" bw
         , E.style "border-color" (Color.toLegacyCss brdColor)
         ]
    
    -- Border radius
    radiusStyle = case props.borderRadius of
      Nothing -> [ E.style "border-radius" "8px" ]
      Just r -> [ E.style "border-radius" (Geometry.cornersToLegacyCss r) ]
    
    -- Padding
    paddingStyle = case props.padding of
      Nothing -> [ E.style "padding" "16px" ]
      Just p -> [ E.style "padding" (show p) ]
  in
    coreStyles <> textColorStyle <> borderStyle <> radiusStyle <> paddingStyle <> props.extraAttributes

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // section components
-- ═════════════════════════════════════════════════════════════════════════════

-- | Alert title
alertTitle :: forall msg. Array (AlertProp msg) -> Array (E.Element msg) -> E.Element msg
alertTitle propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    fontSizeStyle = case props.titleFontSize of
      Nothing -> [ E.style "font-size" "16px" ]
      Just s -> [ E.style "font-size" (FontSize.toLegacyCss s) ]
    
    fontWeightStyle = case props.titleFontWeight of
      Nothing -> [ E.style "font-weight" "500" ]
      Just w -> [ E.style "font-weight" (FontWeight.toLegacyCss w) ]
    
    colorStyle = case props.titleColor of
      Nothing -> []
      Just c -> [ E.style "color" (Color.toLegacyCss c) ]
  in
    E.h5_
      ( [ E.style "margin" "0"
        , E.style "margin-bottom" "4px"
        , E.style "line-height" "1.4"
        , E.style "letter-spacing" "-0.01em"
        ]
        <> fontSizeStyle
        <> fontWeightStyle
        <> colorStyle
      )
      children

-- | Alert description
alertDescription :: forall msg. Array (AlertProp msg) -> Array (E.Element msg) -> E.Element msg
alertDescription propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    fontSizeStyle = case props.descriptionFontSize of
      Nothing -> [ E.style "font-size" "14px" ]
      Just s -> [ E.style "font-size" (FontSize.toLegacyCss s) ]
    
    colorStyle = case props.descriptionColor of
      Nothing -> [ E.style "opacity" "0.9" ]
      Just c -> [ E.style "color" (Color.toLegacyCss c) ]
  in
    E.div_
      ( [ E.style "margin" "0"
        , E.style "line-height" "1.5"
        ]
        <> fontSizeStyle
        <> colorStyle
      )
      children

-- | Alert icon container
-- |
-- | Wrapper for icon placement within alert.
alertIcon :: forall msg. Array (AlertProp msg) -> Array (E.Element msg) -> E.Element msg
alertIcon propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    sizeStyle = case props.iconSize of
      Nothing -> [ E.style "width" "20px", E.style "height" "20px" ]
      Just s -> [ E.style "width" (show s), E.style "height" (show s) ]
    
    colorStyle = case props.iconColor of
      Nothing -> []
      Just c -> [ E.style "color" (Color.toLegacyCss c) ]
  in
    E.span_
      ( [ E.style "flex-shrink" "0"
        , E.style "display" "inline-flex"
        , E.style "align-items" "center"
        , E.style "justify-content" "center"
        ]
        <> sizeStyle
        <> colorStyle
      )
      children
