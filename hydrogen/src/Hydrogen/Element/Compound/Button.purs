-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // element // compound // button
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Button — Schema-native interactive button component.
-- |
-- | ## Design Philosophy
-- |
-- | This component accepts **concrete Schema atoms**, not semantic tokens.
-- | Every visual property maps directly to atoms from the 12 pillars:
-- |
-- | - **Color**: Background, text, border, hover states, focus ring
-- | - **Geometry**: Border radius, border width
-- | - **Elevation**: Shadow
-- | - **Dimension**: Height, padding, min width
-- | - **Typography**: Font size, font weight
-- | - **Motion**: Transition duration, easing
-- |
-- | The **BrandSchema** defines what these atoms are for a given brand.
-- | This component just renders them faithfully.
-- |
-- | ## Schema Atoms Accepted
-- |
-- | | Property              | Pillar     | Type                      | CSS Output              |
-- | |-----------------------|------------|---------------------------|-------------------------|
-- | | backgroundColor       | Color      | Color.RGB                 | background-color        |
-- | | textColor             | Color      | Color.RGB                 | color                   |
-- | | borderColor           | Color      | Color.RGB                 | border-color            |
-- | | hoverBackgroundColor  | Color      | Color.RGB                 | :hover background       |
-- | | hoverTextColor        | Color      | Color.RGB                 | :hover color            |
-- | | hoverBorderColor      | Color      | Color.RGB                 | :hover border-color     |
-- | | focusRingColor        | Color      | Color.RGB                 | focus outline           |
-- | | borderRadius          | Geometry   | Geometry.Corners          | border-radius           |
-- | | borderWidth           | Dimension  | Device.Pixel              | border-width            |
-- | | shadow                | Elevation  | Shadow.LayeredShadow      | box-shadow              |
-- | | height                | Dimension  | Device.Pixel              | height                  |
-- | | paddingX              | Dimension  | Device.Pixel              | padding-left/right      |
-- | | paddingY              | Dimension  | Device.Pixel              | padding-top/bottom      |
-- | | minWidth              | Dimension  | Device.Pixel              | min-width               |
-- | | fontSize              | Typography | Typography.FontSize       | font-size               |
-- | | fontWeight            | Typography | Typography.FontWeight     | font-weight             |
-- | | transitionDuration    | Motion     | Temporal.Milliseconds     | transition-duration     |
-- | | transitionEasing      | Motion     | Easing.Easing             | transition-timing       |
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.Button as Button
-- | import Hydrogen.Schema.Color.RGB as Color
-- | import Hydrogen.Schema.Geometry.Radius as Geometry
-- | import Hydrogen.Schema.Dimension.Device as Device
-- | import Hydrogen.Render.Element as E
-- |
-- | -- Minimal usage with children
-- | Button.button
-- |   [ Button.onClick SubmitForm ]
-- |   [ E.text "Submit" ]
-- |
-- | -- With brand atoms
-- | Button.button
-- |   [ Button.onClick SubmitForm
-- |   , Button.backgroundColor brand.primaryColor
-- |   , Button.textColor brand.onPrimaryColor
-- |   , Button.borderRadius brand.buttonRadius
-- |   , Button.height brand.buttonHeight
-- |   , Button.paddingX brand.buttonPaddingX
-- |   , Button.shadow brand.buttonShadow
-- |   ]
-- |   [ E.text "Submit" ]
-- |
-- | -- Disabled state
-- | Button.button
-- |   [ Button.disabled true
-- |   , Button.backgroundColor (Color.rgb 200 200 200)
-- |   ]
-- |   [ E.text "Disabled" ]
-- |
-- | -- Loading state
-- | Button.button
-- |   [ Button.loading true ]
-- |   [ E.text "Saving..." ]
-- | ```
-- |
-- | ## Companion Components
-- |
-- | - `buttonLink` — Button-styled anchor element
-- | - `iconButton` — Button optimized for icon-only content
-- | - `loadingSpinner` — Spinner element for loading states

module Hydrogen.Element.Compound.Button
  ( -- * Main Component
    button
  
  -- * Companion Components
  , buttonLink
  , iconButton
  , loadingSpinner
  
  -- * Types
  , ButtonType(TypeButton, TypeSubmit, TypeReset)
  
  -- * Props
  , ButtonProps
  , ButtonProp
  , defaultProps
  
  -- * Content Props
  , buttonType
  , disabled
  , loading
  
  -- * Color Atoms
  , backgroundColor
  , textColor
  , borderColor
  , hoverBackgroundColor
  , hoverTextColor
  , hoverBorderColor
  , activeBackgroundColor
  , focusRingColor
  
  -- * Geometry Atoms
  , borderRadius
  , borderWidth
  
  -- * Elevation Atoms
  , shadow
  , hoverShadow
  
  -- * Dimension Atoms
  , height
  , paddingX
  , paddingY
  , minWidth
  , iconSize
  , gap
  
  -- * Typography Atoms
  , fontSize
  , fontWeight
  
  -- * Motion Atoms
  , transitionDuration
  , transitionEasing
  
  -- * Behavior Props
  , onClick
  
  -- * Escape Hatch
  , extraAttributes
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  , (||)
  , not
  )

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just), maybe)

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Elevation.Shadow as Shadow
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Dimension.Temporal as Temporal
import Hydrogen.Schema.Typography.FontSize as FontSize
import Hydrogen.Schema.Typography.FontWeight as FontWeight
import Hydrogen.Schema.Motion.Easing as Easing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | HTML button type attribute
-- |
-- | - `TypeButton`: Standard button (default)
-- | - `TypeSubmit`: Form submission button
-- | - `TypeReset`: Form reset button
data ButtonType
  = TypeButton
  | TypeSubmit
  | TypeReset

derive instance eqButtonType :: Eq ButtonType

instance showButtonType :: Show ButtonType where
  show TypeButton = "button"
  show TypeSubmit = "submit"
  show TypeReset = "reset"

-- | Convert ButtonType to HTML attribute value
buttonTypeToString :: ButtonType -> String
buttonTypeToString TypeButton = "button"
buttonTypeToString TypeSubmit = "submit"
buttonTypeToString TypeReset = "reset"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Button properties
-- |
-- | All visual properties accept concrete Schema atoms.
-- | `Maybe` indicates optional — `Nothing` uses inherited/default styles.
type ButtonProps msg =
  { -- Behavior
    buttonType :: ButtonType
  , disabled :: Boolean
  , loading :: Boolean
  , onClick :: Maybe msg
  
  -- Color atoms
  , backgroundColor :: Maybe Color.RGB
  , textColor :: Maybe Color.RGB
  , borderColor :: Maybe Color.RGB
  , hoverBackgroundColor :: Maybe Color.RGB
  , hoverTextColor :: Maybe Color.RGB
  , hoverBorderColor :: Maybe Color.RGB
  , activeBackgroundColor :: Maybe Color.RGB
  , focusRingColor :: Maybe Color.RGB
  
  -- Geometry atoms
  , borderRadius :: Maybe Geometry.Corners
  , borderWidth :: Maybe Device.Pixel
  
  -- Elevation atoms
  , shadow :: Maybe Shadow.LayeredShadow
  , hoverShadow :: Maybe Shadow.LayeredShadow
  
  -- Dimension atoms
  , height :: Maybe Device.Pixel
  , paddingX :: Maybe Device.Pixel
  , paddingY :: Maybe Device.Pixel
  , minWidth :: Maybe Device.Pixel
  , iconSize :: Maybe Device.Pixel
  , gap :: Maybe Device.Pixel
  
  -- Typography atoms
  , fontSize :: Maybe FontSize.FontSize
  , fontWeight :: Maybe FontWeight.FontWeight
  
  -- Motion atoms
  , transitionDuration :: Maybe Temporal.Milliseconds
  , transitionEasing :: Maybe Easing.Easing
  
  -- Escape hatch
  , extraAttributes :: Array (E.Attribute msg)
  }

-- | Property modifier
type ButtonProp msg = ButtonProps msg -> ButtonProps msg

-- | Default properties
-- |
-- | Visual atoms default to `Nothing` (inherit from context/brand).
-- | This ensures the component works with any BrandSchema.
defaultProps :: forall msg. ButtonProps msg
defaultProps =
  { buttonType: TypeButton
  , disabled: false
  , loading: false
  , onClick: Nothing
  , backgroundColor: Nothing
  , textColor: Nothing
  , borderColor: Nothing
  , hoverBackgroundColor: Nothing
  , hoverTextColor: Nothing
  , hoverBorderColor: Nothing
  , activeBackgroundColor: Nothing
  , focusRingColor: Nothing
  , borderRadius: Nothing
  , borderWidth: Nothing
  , shadow: Nothing
  , hoverShadow: Nothing
  , height: Nothing
  , paddingX: Nothing
  , paddingY: Nothing
  , minWidth: Nothing
  , iconSize: Nothing
  , gap: Nothing
  , fontSize: Nothing
  , fontWeight: Nothing
  , transitionDuration: Nothing
  , transitionEasing: Nothing
  , extraAttributes: []
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: behavior
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set button type (button, submit, reset)
buttonType :: forall msg. ButtonType -> ButtonProp msg
buttonType t props = props { buttonType = t }

-- | Set disabled state
disabled :: forall msg. Boolean -> ButtonProp msg
disabled d props = props { disabled = d }

-- | Set loading state
-- |
-- | When loading, the button is also disabled and shows a spinner.
loading :: forall msg. Boolean -> ButtonProp msg
loading l props = props { loading = l }

-- | Set click handler
onClick :: forall msg. msg -> ButtonProp msg
onClick handler props = props { onClick = Just handler }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: color
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set button background color (Color.RGB atom)
backgroundColor :: forall msg. Color.RGB -> ButtonProp msg
backgroundColor c props = props { backgroundColor = Just c }

-- | Set button text color (Color.RGB atom)
textColor :: forall msg. Color.RGB -> ButtonProp msg
textColor c props = props { textColor = Just c }

-- | Set button border color (Color.RGB atom)
borderColor :: forall msg. Color.RGB -> ButtonProp msg
borderColor c props = props { borderColor = Just c }

-- | Set hover background color (Color.RGB atom)
hoverBackgroundColor :: forall msg. Color.RGB -> ButtonProp msg
hoverBackgroundColor c props = props { hoverBackgroundColor = Just c }

-- | Set hover text color (Color.RGB atom)
hoverTextColor :: forall msg. Color.RGB -> ButtonProp msg
hoverTextColor c props = props { hoverTextColor = Just c }

-- | Set hover border color (Color.RGB atom)
hoverBorderColor :: forall msg. Color.RGB -> ButtonProp msg
hoverBorderColor c props = props { hoverBorderColor = Just c }

-- | Set active/pressed background color (Color.RGB atom)
activeBackgroundColor :: forall msg. Color.RGB -> ButtonProp msg
activeBackgroundColor c props = props { activeBackgroundColor = Just c }

-- | Set focus ring color (Color.RGB atom)
focusRingColor :: forall msg. Color.RGB -> ButtonProp msg
focusRingColor c props = props { focusRingColor = Just c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: geometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set border radius (Geometry.Corners atom)
-- |
-- | Supports per-corner radius for asymmetric buttons.
borderRadius :: forall msg. Geometry.Corners -> ButtonProp msg
borderRadius r props = props { borderRadius = Just r }

-- | Set border width (Device.Pixel atom)
borderWidth :: forall msg. Device.Pixel -> ButtonProp msg
borderWidth w props = props { borderWidth = Just w }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // prop builders: elevation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set box shadow (Shadow.LayeredShadow atom)
-- |
-- | Supports multiple shadow layers for depth effects.
shadow :: forall msg. Shadow.LayeredShadow -> ButtonProp msg
shadow s props = props { shadow = Just s }

-- | Set hover box shadow (Shadow.LayeredShadow atom)
hoverShadow :: forall msg. Shadow.LayeredShadow -> ButtonProp msg
hoverShadow s props = props { hoverShadow = Just s }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // prop builders: dimension
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set button height (Device.Pixel atom)
height :: forall msg. Device.Pixel -> ButtonProp msg
height h props = props { height = Just h }

-- | Set horizontal padding (Device.Pixel atom)
paddingX :: forall msg. Device.Pixel -> ButtonProp msg
paddingX p props = props { paddingX = Just p }

-- | Set vertical padding (Device.Pixel atom)
paddingY :: forall msg. Device.Pixel -> ButtonProp msg
paddingY p props = props { paddingY = Just p }

-- | Set minimum width (Device.Pixel atom)
minWidth :: forall msg. Device.Pixel -> ButtonProp msg
minWidth w props = props { minWidth = Just w }

-- | Set icon size for icon buttons (Device.Pixel atom)
iconSize :: forall msg. Device.Pixel -> ButtonProp msg
iconSize s props = props { iconSize = Just s }

-- | Set gap between icon and text (Device.Pixel atom)
gap :: forall msg. Device.Pixel -> ButtonProp msg
gap g props = props { gap = Just g }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // prop builders: typography
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set font size (FontSize atom)
fontSize :: forall msg. FontSize.FontSize -> ButtonProp msg
fontSize s props = props { fontSize = Just s }

-- | Set font weight (FontWeight atom)
fontWeight :: forall msg. FontWeight.FontWeight -> ButtonProp msg
fontWeight w props = props { fontWeight = Just w }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // prop builders: motion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set transition duration (Temporal.Milliseconds atom)
transitionDuration :: forall msg. Temporal.Milliseconds -> ButtonProp msg
transitionDuration d props = props { transitionDuration = Just d }

-- | Set transition easing (Easing.Easing atom)
transitionEasing :: forall msg. Easing.Easing -> ButtonProp msg
transitionEasing e props = props { transitionEasing = Just e }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                // prop builders: escape hatch
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add extra attributes (escape hatch)
extraAttributes :: forall msg. Array (E.Attribute msg) -> ButtonProp msg
extraAttributes attrs props = props { extraAttributes = props.extraAttributes <> attrs }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // main component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a button
-- |
-- | Pure Element — renders to DOM, Halogen, Static HTML, or any target.
-- | All visual properties come from Schema atoms passed via props.
button :: forall msg. Array (ButtonProp msg) -> Array (E.Element msg) -> E.Element msg
button propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    isDisabled = props.disabled || props.loading
  in
    E.button_
      (buildButtonAttrs isDisabled props)
      (buildButtonContent props children)

-- | Build button attributes from props
buildButtonAttrs :: forall msg. Boolean -> ButtonProps msg -> Array (E.Attribute msg)
buildButtonAttrs isDisabled props =
  let
    -- Core attributes
    coreAttrs =
      [ E.type_ (buttonTypeToString props.buttonType)
      , E.disabled isDisabled
      ]
    
    -- Click handler
    clickAttr = case props.onClick of
      Just handler -> 
        if isDisabled
          then []
          else [ E.onClick handler ]
      Nothing -> []
    
    -- Style attributes
    styleAttrs = buildButtonStyles isDisabled props
  in
    coreAttrs <> clickAttr <> styleAttrs <> props.extraAttributes

-- | Build button styles from Schema atoms
buildButtonStyles :: forall msg. Boolean -> ButtonProps msg -> Array (E.Attribute msg)
buildButtonStyles isDisabled props =
  let
    -- Default values (fallback if no atom provided)
    defaultBgColor = Color.rgb 59 130 246      -- Blue
    defaultTextColor = Color.rgb 255 255 255   -- White
    
    -- Apply atoms or defaults
    bgColor = maybe defaultBgColor (\c -> c) props.backgroundColor
    txtColor = maybe defaultTextColor (\c -> c) props.textColor
    
    -- Core layout styles
    layoutStyles =
      [ E.style "display" "inline-flex"
      , E.style "align-items" "center"
      , E.style "justify-content" "center"
      , E.style "white-space" "nowrap"
      , E.style "cursor" (if isDisabled then "not-allowed" else "pointer")
      , E.style "user-select" "none"
      , E.style "box-sizing" "border-box"
      ]
    
    -- Color styles
    colorStyles =
      [ E.style "background-color" (Color.toLegacyCss bgColor)
      , E.style "color" (Color.toLegacyCss txtColor)
      ]
    
    -- Border styles
    borderColorStyle = case props.borderColor of
      Nothing -> [ E.style "border" "none" ]
      Just bc -> 
        let bw = maybe "1px" show props.borderWidth
        in [ E.style "border-style" "solid"
           , E.style "border-width" bw
           , E.style "border-color" (Color.toLegacyCss bc)
           ]
    
    -- Border radius
    radiusStyle = case props.borderRadius of
      Nothing -> [ E.style "border-radius" "6px" ]  -- Default rounded
      Just r -> [ E.style "border-radius" (Geometry.cornersToLegacyCss r) ]
    
    -- Dimension styles
    heightStyle = case props.height of
      Nothing -> [ E.style "height" "40px" ]  -- Default height
      Just h -> [ E.style "height" (show h) ]
    
    paddingStyle =
      let
        px = maybe "16px" show props.paddingX
        py = maybe "8px" show props.paddingY
      in
        [ E.style "padding" (py <> " " <> px) ]
    
    minWidthStyle = case props.minWidth of
      Nothing -> []
      Just w -> [ E.style "min-width" (show w) ]
    
    gapStyle = case props.gap of
      Nothing -> [ E.style "gap" "8px" ]  -- Default gap
      Just g -> [ E.style "gap" (show g) ]
    
    -- Typography styles
    fontSizeStyle = case props.fontSize of
      Nothing -> [ E.style "font-size" "14px" ]  -- Default
      Just s -> [ E.style "font-size" (FontSize.toLegacyCss s) ]
    
    fontWeightStyle = case props.fontWeight of
      Nothing -> [ E.style "font-weight" "500" ]  -- Medium
      Just w -> [ E.style "font-weight" (FontWeight.toLegacyCss w) ]
    
    -- Shadow styles
    shadowStyle = case props.shadow of
      Nothing -> []
      Just s -> 
        if Shadow.isNoShadow s
          then []
          else [ E.style "box-shadow" (Shadow.layeredToLegacyCss s) ]
    
    -- Transition styles
    transitionStyle =
      let
        dur = maybe "150ms" show props.transitionDuration
        ease = maybe "ease-out" Easing.toLegacyCssString props.transitionEasing
        transitionValue = "background-color " <> dur <> " " <> ease 
                       <> ", color " <> dur <> " " <> ease
                       <> ", border-color " <> dur <> " " <> ease
                       <> ", box-shadow " <> dur <> " " <> ease
                       <> ", transform " <> dur <> " " <> ease
      in
        [ E.style "transition" transitionValue ]
    
    -- Disabled/loading opacity
    opacityStyle = 
      if isDisabled
        then [ E.style "opacity" "0.5" ]
        else []
    
    -- Focus visible styles (accessibility)
    focusStyles =
      [ E.style "outline" "none"
      ]
  in
    layoutStyles 
    <> colorStyles 
    <> borderColorStyle 
    <> radiusStyle 
    <> heightStyle 
    <> paddingStyle 
    <> minWidthStyle 
    <> gapStyle
    <> fontSizeStyle 
    <> fontWeightStyle 
    <> shadowStyle 
    <> transitionStyle 
    <> opacityStyle
    <> focusStyles

-- | Build button content with optional loading spinner
buildButtonContent :: forall msg. ButtonProps msg -> Array (E.Element msg) -> Array (E.Element msg)
buildButtonContent props children =
  if props.loading
    then [ loadingSpinner, E.span_ [ E.style "margin-left" "8px" ] children ]
    else children

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // companion components
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a button-styled link
-- |
-- | For navigation that should look like a button.
buttonLink :: forall msg. Array (ButtonProp msg) -> String -> Array (E.Element msg) -> E.Element msg
buttonLink propMods href children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    styleAttrs = buildButtonStyles false props
  in
    E.a_
      ([ E.href href, E.style "text-decoration" "none" ] <> styleAttrs <> props.extraAttributes)
      children

-- | Render an icon button
-- |
-- | Square button optimized for icon-only content.
iconButton :: forall msg. Array (ButtonProp msg) -> Array (E.Element msg) -> E.Element msg
iconButton propMods children =
  let
    -- Override padding to be square
    squareProps = 
      [ paddingX (Device.px 0.0)
      , paddingY (Device.px 0.0)
      ]
    allProps = propMods <> squareProps
    props = foldl (\p f -> f p) defaultProps allProps
    isDisabled = props.disabled || props.loading
    
    -- Get size (height determines width for square)
    size = maybe "40px" show props.height
    
    -- Build custom styles
    baseStyles = buildButtonStyles isDisabled props
    
    -- Override for square dimensions
    squareStyles =
      [ E.style "width" size
      , E.style "height" size
      , E.style "padding" "0"
      ]
    
    coreAttrs =
      [ E.type_ (buttonTypeToString props.buttonType)
      , E.disabled isDisabled
      ]
    
    clickAttr = case props.onClick of
      Just handler -> 
        if not isDisabled
          then [ E.onClick handler ]
          else []
      Nothing -> []
  in
    E.button_
      (coreAttrs <> clickAttr <> baseStyles <> squareStyles <> props.extraAttributes)
      children

-- | Loading spinner for button loading state
-- |
-- | Renders a circular spinning indicator.
loadingSpinner :: forall msg. E.Element msg
loadingSpinner =
  E.div_
    [ E.style "width" "16px"
    , E.style "height" "16px"
    , E.style "border" "2px solid currentColor"
    , E.style "border-top-color" "transparent"
    , E.style "border-radius" "50%"
    , E.style "animation" "button-spin 0.6s linear infinite"
    ]
    []
