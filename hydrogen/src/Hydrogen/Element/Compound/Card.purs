-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // element // compound // card
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Card — Schema-native container component.
-- |
-- | ## Design Philosophy
-- |
-- | This component accepts **concrete Schema atoms**, not semantic tokens.
-- | Every visual property maps directly to atoms from the 12 pillars:
-- |
-- | - **Color**: Background, text, border
-- | - **Geometry**: Border radius, border width
-- | - **Elevation**: Shadow
-- | - **Dimension**: Padding
-- |
-- | The **BrandSchema** defines what these atoms are for a given brand.
-- | This component just renders them faithfully.
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
-- | | shadow           | Elevation  | Shadow.LayeredShadow      | box-shadow              |
-- | | padding          | Dimension  | Device.Pixel              | padding                 |
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.Card as Card
-- | import Hydrogen.Schema.Color.RGB as Color
-- | import Hydrogen.Schema.Geometry.Radius as Geometry
-- | import Hydrogen.Schema.Elevation.Shadow as Shadow
-- | import Hydrogen.Render.Element as E
-- |
-- | -- Basic card
-- | Card.card []
-- |   [ Card.cardHeader []
-- |       [ Card.cardTitle [] [ E.text "Title" ]
-- |       , Card.cardDescription [] [ E.text "Description" ]
-- |       ]
-- |   , Card.cardContent []
-- |       [ E.p_ [] [ E.text "Content goes here" ] ]
-- |   , Card.cardFooter []
-- |       [ Button.button [] [ E.text "Action" ] ]
-- |   ]
-- |
-- | -- With brand atoms
-- | Card.card
-- |   [ Card.backgroundColor brand.cardBackground
-- |   , Card.borderRadius brand.cardRadius
-- |   , Card.shadow brand.cardShadow
-- |   , Card.padding brand.cardPadding
-- |   ]
-- |   [ ... ]
-- | ```
-- |
-- | ## Card Sections
-- |
-- | - `card` — Main container
-- | - `cardHeader` — Header section (title + description)
-- | - `cardTitle` — Title text
-- | - `cardDescription` — Description/subtitle text
-- | - `cardContent` — Main content area
-- | - `cardFooter` — Footer with actions

module Hydrogen.Element.Compound.Card
  ( -- * Main Component
    card
  
  -- * Section Components
  , cardHeader
  , cardTitle
  , cardDescription
  , cardContent
  , cardFooter
  
  -- * Props
  , CardProps
  , CardProp
  , defaultProps
  
  -- * Color Atoms
  , backgroundColor
  , textColor
  , borderColor
  , titleColor
  , descriptionColor
  
  -- * Geometry Atoms
  , borderRadius
  , borderWidth
  
  -- * Elevation Atoms
  , shadow
  
  -- * Dimension Atoms
  , padding
  , headerPadding
  , contentPadding
  , footerPadding
  , gap
  
  -- * Typography Atoms
  , titleFontSize
  , titleFontWeight
  , descriptionFontSize
  
  -- * Behavior Props
  , onClick
  , hoverable
  
  -- * Escape Hatch
  , extraAttributes
  ) where

import Prelude
  ( show
  , (<>)
  , (||)
  )

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just), maybe)

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Elevation.Shadow as Shadow
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Typography.FontSize as FontSize
import Hydrogen.Schema.Typography.FontWeight as FontWeight

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Card properties
-- |
-- | All visual properties accept concrete Schema atoms.
-- | `Maybe` indicates optional — `Nothing` uses inherited/default styles.
type CardProps msg =
  { -- Color atoms
    backgroundColor :: Maybe Color.RGB
  , textColor :: Maybe Color.RGB
  , borderColor :: Maybe Color.RGB
  , titleColor :: Maybe Color.RGB
  , descriptionColor :: Maybe Color.RGB
  
  -- Geometry atoms
  , borderRadius :: Maybe Geometry.Corners
  , borderWidth :: Maybe Device.Pixel
  
  -- Elevation atoms
  , shadow :: Maybe Shadow.LayeredShadow
  
  -- Dimension atoms
  , padding :: Maybe Device.Pixel
  , headerPadding :: Maybe Device.Pixel
  , contentPadding :: Maybe Device.Pixel
  , footerPadding :: Maybe Device.Pixel
  , gap :: Maybe Device.Pixel
  
  -- Typography atoms
  , titleFontSize :: Maybe FontSize.FontSize
  , titleFontWeight :: Maybe FontWeight.FontWeight
  , descriptionFontSize :: Maybe FontSize.FontSize
  
  -- Behavior
  , onClick :: Maybe msg
  , hoverable :: Boolean
  
  -- Escape hatch
  , extraAttributes :: Array (E.Attribute msg)
  }

-- | Property modifier
type CardProp msg = CardProps msg -> CardProps msg

-- | Default properties
-- |
-- | Visual atoms default to `Nothing` (inherit from context/brand).
-- | This ensures the component works with any BrandSchema.
defaultProps :: forall msg. CardProps msg
defaultProps =
  { backgroundColor: Nothing
  , textColor: Nothing
  , borderColor: Nothing
  , titleColor: Nothing
  , descriptionColor: Nothing
  , borderRadius: Nothing
  , borderWidth: Nothing
  , shadow: Nothing
  , padding: Nothing
  , headerPadding: Nothing
  , contentPadding: Nothing
  , footerPadding: Nothing
  , gap: Nothing
  , titleFontSize: Nothing
  , titleFontWeight: Nothing
  , descriptionFontSize: Nothing
  , onClick: Nothing
  , hoverable: false
  , extraAttributes: []
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: color
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set card background color (Color.RGB atom)
backgroundColor :: forall msg. Color.RGB -> CardProp msg
backgroundColor c props = props { backgroundColor = Just c }

-- | Set card text color (Color.RGB atom)
textColor :: forall msg. Color.RGB -> CardProp msg
textColor c props = props { textColor = Just c }

-- | Set card border color (Color.RGB atom)
borderColor :: forall msg. Color.RGB -> CardProp msg
borderColor c props = props { borderColor = Just c }

-- | Set title text color (Color.RGB atom)
titleColor :: forall msg. Color.RGB -> CardProp msg
titleColor c props = props { titleColor = Just c }

-- | Set description text color (Color.RGB atom)
descriptionColor :: forall msg. Color.RGB -> CardProp msg
descriptionColor c props = props { descriptionColor = Just c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: geometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set border radius (Geometry.Corners atom)
-- |
-- | Supports per-corner radius for asymmetric cards.
borderRadius :: forall msg. Geometry.Corners -> CardProp msg
borderRadius r props = props { borderRadius = Just r }

-- | Set border width (Device.Pixel atom)
borderWidth :: forall msg. Device.Pixel -> CardProp msg
borderWidth w props = props { borderWidth = Just w }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // prop builders: elevation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set box shadow (Shadow.LayeredShadow atom)
-- |
-- | Supports multiple shadow layers for depth effects.
shadow :: forall msg. Shadow.LayeredShadow -> CardProp msg
shadow s props = props { shadow = Just s }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // prop builders: dimension
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set overall card padding (Device.Pixel atom)
-- |
-- | Applied to all sections unless overridden.
padding :: forall msg. Device.Pixel -> CardProp msg
padding p props = props { padding = Just p }

-- | Set header section padding (Device.Pixel atom)
headerPadding :: forall msg. Device.Pixel -> CardProp msg
headerPadding p props = props { headerPadding = Just p }

-- | Set content section padding (Device.Pixel atom)
contentPadding :: forall msg. Device.Pixel -> CardProp msg
contentPadding p props = props { contentPadding = Just p }

-- | Set footer section padding (Device.Pixel atom)
footerPadding :: forall msg. Device.Pixel -> CardProp msg
footerPadding p props = props { footerPadding = Just p }

-- | Set gap between elements (Device.Pixel atom)
gap :: forall msg. Device.Pixel -> CardProp msg
gap g props = props { gap = Just g }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // prop builders: typography
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set title font size (FontSize atom)
titleFontSize :: forall msg. FontSize.FontSize -> CardProp msg
titleFontSize s props = props { titleFontSize = Just s }

-- | Set title font weight (FontWeight atom)
titleFontWeight :: forall msg. FontWeight.FontWeight -> CardProp msg
titleFontWeight w props = props { titleFontWeight = Just w }

-- | Set description font size (FontSize atom)
descriptionFontSize :: forall msg. FontSize.FontSize -> CardProp msg
descriptionFontSize s props = props { descriptionFontSize = Just s }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: behavior
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set click handler
-- |
-- | Makes the entire card interactive.
onClick :: forall msg. msg -> CardProp msg
onClick handler props = props { onClick = Just handler }

-- | Enable hover effects
-- |
-- | Adds subtle lift/shadow on hover.
hoverable :: forall msg. Boolean -> CardProp msg
hoverable h props = props { hoverable = h }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                // prop builders: escape hatch
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add extra attributes (escape hatch)
extraAttributes :: forall msg. Array (E.Attribute msg) -> CardProp msg
extraAttributes attrs props = props { extraAttributes = props.extraAttributes <> attrs }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // main component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a card container
-- |
-- | Pure Element — renders to DOM, Halogen, Static HTML, or any target.
-- | All visual properties come from Schema atoms passed via props.
card :: forall msg. Array (CardProp msg) -> Array (E.Element msg) -> E.Element msg
card propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    isInteractive = hasOnClick props || props.hoverable
  in
    E.div_
      (buildCardAttrs isInteractive props)
      children

-- | Check if onClick is set
hasOnClick :: forall msg. CardProps msg -> Boolean
hasOnClick props = case props.onClick of
  Just _ -> true
  Nothing -> false

-- | Build card attributes from props
buildCardAttrs :: forall msg. Boolean -> CardProps msg -> Array (E.Attribute msg)
buildCardAttrs isInteractive props =
  let
    -- Style attributes
    styleAttrs = buildCardStyles isInteractive props
    
    -- Click handler
    clickAttr = case props.onClick of
      Just handler -> [ E.onClick handler ]
      Nothing -> []
  in
    styleAttrs <> clickAttr <> props.extraAttributes

-- | Build card styles from Schema atoms
buildCardStyles :: forall msg. Boolean -> CardProps msg -> Array (E.Attribute msg)
buildCardStyles isInteractive props =
  let
    -- Default values (fallback if no atom provided)
    defaultBgColor = Color.rgb 255 255 255   -- White
    
    -- Apply atoms or defaults
    bgColor = maybe defaultBgColor (\c -> c) props.backgroundColor
    
    -- Core styles
    coreStyles =
      [ E.style "background-color" (Color.toLegacyCss bgColor)
      , E.style "position" "relative"
      , E.style "overflow" "hidden"
      ]
    
    -- Text color
    textColorStyle = case props.textColor of
      Nothing -> []
      Just c -> [ E.style "color" (Color.toLegacyCss c) ]
    
    -- Border styles
    borderStyle = case props.borderColor of
      Nothing -> [ E.style "border" "1px solid rgba(0, 0, 0, 0.1)" ]  -- Subtle default
      Just bc -> 
        let bw = maybe "1px" show props.borderWidth
        in [ E.style "border-style" "solid"
           , E.style "border-width" bw
           , E.style "border-color" (Color.toLegacyCss bc)
           ]
    
    -- Border radius
    radiusStyle = case props.borderRadius of
      Nothing -> [ E.style "border-radius" "8px" ]  -- Default rounded
      Just r -> [ E.style "border-radius" (Geometry.cornersToLegacyCss r) ]
    
    -- Shadow styles
    shadowStyle = case props.shadow of
      Nothing -> [ E.style "box-shadow" "0 1px 3px rgba(0, 0, 0, 0.1), 0 1px 2px rgba(0, 0, 0, 0.06)" ]
      Just s -> 
        if Shadow.isNoShadow s
          then []
          else [ E.style "box-shadow" (Shadow.layeredToLegacyCss s) ]
    
    -- Interactive styles
    interactiveStyles =
      if isInteractive
        then 
          [ E.style "cursor" "pointer"
          , E.style "transition" "transform 150ms ease-out, box-shadow 150ms ease-out"
          ]
        else []
  in
    coreStyles <> textColorStyle <> borderStyle <> radiusStyle <> shadowStyle <> interactiveStyles

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // section components
-- ═════════════════════════════════════════════════════════════════════════════

-- | Card header section
-- |
-- | Contains title and description. Uses inherited props from parent card
-- | or accepts its own overrides.
cardHeader :: forall msg. Array (CardProp msg) -> Array (E.Element msg) -> E.Element msg
cardHeader propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    paddingValue = maybe "24px" show props.headerPadding
    gapValue = maybe "6px" show props.gap
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "padding" paddingValue
      , E.style "gap" gapValue
      ]
      children

-- | Card title
-- |
-- | Primary heading for the card.
cardTitle :: forall msg. Array (CardProp msg) -> Array (E.Element msg) -> E.Element msg
cardTitle propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    fontSizeStyle = case props.titleFontSize of
      Nothing -> [ E.style "font-size" "24px" ]
      Just s -> [ E.style "font-size" (FontSize.toLegacyCss s) ]
    
    fontWeightStyle = case props.titleFontWeight of
      Nothing -> [ E.style "font-weight" "600" ]
      Just w -> [ E.style "font-weight" (FontWeight.toLegacyCss w) ]
    
    colorStyle = case props.titleColor of
      Nothing -> []
      Just c -> [ E.style "color" (Color.toLegacyCss c) ]
  in
    E.h3_
      ( [ E.style "margin" "0"
        , E.style "line-height" "1.3"
        , E.style "letter-spacing" "-0.02em"
        ]
        <> fontSizeStyle
        <> fontWeightStyle
        <> colorStyle
      )
      children

-- | Card description
-- |
-- | Secondary text below the title.
cardDescription :: forall msg. Array (CardProp msg) -> Array (E.Element msg) -> E.Element msg
cardDescription propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    fontSizeStyle = case props.descriptionFontSize of
      Nothing -> [ E.style "font-size" "14px" ]
      Just s -> [ E.style "font-size" (FontSize.toLegacyCss s) ]
    
    colorStyle = case props.descriptionColor of
      Nothing -> [ E.style "color" "rgba(0, 0, 0, 0.6)" ]  -- Muted default
      Just c -> [ E.style "color" (Color.toLegacyCss c) ]
  in
    E.p_
      ( [ E.style "margin" "0"
        , E.style "line-height" "1.5"
        ]
        <> fontSizeStyle
        <> colorStyle
      )
      children

-- | Card content section
-- |
-- | Main content area of the card.
cardContent :: forall msg. Array (CardProp msg) -> Array (E.Element msg) -> E.Element msg
cardContent propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    paddingValue = maybe "24px" show props.contentPadding
  in
    E.div_
      [ E.style "padding" paddingValue
      , E.style "padding-top" "0"
      ]
      children

-- | Card footer section
-- |
-- | Footer area for actions and secondary information.
cardFooter :: forall msg. Array (CardProp msg) -> Array (E.Element msg) -> E.Element msg
cardFooter propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    paddingValue = maybe "24px" show props.footerPadding
    gapValue = maybe "8px" show props.gap
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "align-items" "center"
      , E.style "padding" paddingValue
      , E.style "padding-top" "0"
      , E.style "gap" gapValue
      ]
      children
