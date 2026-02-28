-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                               // hydrogen // element // toast
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Toast — Schema-native notification component.
-- |
-- | ## Design Philosophy
-- |
-- | This component accepts **concrete Schema atoms**, not semantic tokens.
-- | Toast notifications display brief messages to users.
-- |
-- | ## Schema Atoms Accepted
-- |
-- | | Property            | Pillar     | Type                      | CSS Output              |
-- | |---------------------|------------|---------------------------|-------------------------|
-- | | backgroundColor     | Color      | Color.RGB                 | background-color        |
-- | | textColor           | Color      | Color.RGB                 | color                   |
-- | | borderColor         | Color      | Color.RGB                 | border-color            |
-- | | iconColor           | Color      | Color.RGB                 | icon color              |
-- | | borderRadius        | Geometry   | Geometry.Corners          | border-radius           |
-- | | padding             | Dimension  | Device.Pixel              | padding                 |
-- | | shadow              | Elevation  | Shadow.LayeredShadow      | box-shadow              |
-- | | gap                 | Dimension  | Device.Pixel              | gap between toasts      |
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.Toast as Toast
-- | import Hydrogen.Schema.Color.RGB as Color
-- |
-- | -- Toast container (place once at app root)
-- | Toast.toastContainer
-- |   [ Toast.position Toast.TopRight
-- |   , Toast.gap (Device.px 12.0)
-- |   ]
-- |   toastElements
-- |
-- | -- Individual toast with brand atoms
-- | Toast.toast
-- |   [ Toast.title "Success!"
-- |   , Toast.description "Your changes have been saved."
-- |   , Toast.backgroundColor brand.successBackground
-- |   , Toast.textColor brand.successText
-- |   , Toast.dismissible true
-- |   , Toast.onDismiss DismissToast
-- |   ]
-- | ```

module Hydrogen.Element.Compound.Toast
  ( -- * Main Components
    toast
  , toastContainer
  , toastTitle
  , toastDescription
  , toastAction
  , toastClose
  
  -- * Types
  , ToastPosition(TopRight, TopLeft, TopCenter, BottomRight, BottomLeft, BottomCenter)
  , ToastActionConfig
  
  -- * Toast Props
  , ToastProps
  , ToastProp
  , defaultProps
  
  -- * Container Props
  , ContainerProps
  , ContainerProp
  , defaultContainerProps
  
  -- * Content Props
  , title
  , description
  , dismissible
  , action
  , toastId
  
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
  
  -- * Elevation Atoms
  , shadow
  
  -- * Dimension Atoms
  , padding
  , maxWidth
  , gap
  
  -- * Typography Atoms
  , titleFontSize
  , titleFontWeight
  , descriptionFontSize
  
  -- * Container Props
  , position
  , containerGap
  
  -- * Behavior Props
  , onDismiss
  
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
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Elevation.Shadow as Shadow
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Typography.FontSize as FontSize
import Hydrogen.Schema.Typography.FontWeight as FontWeight

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Toast position on screen
data ToastPosition
  = TopRight
  | TopLeft
  | TopCenter
  | BottomRight
  | BottomLeft
  | BottomCenter

derive instance eqToastPosition :: Eq ToastPosition

instance showToastPosition :: Show ToastPosition where
  show TopRight = "top-right"
  show TopLeft = "top-left"
  show TopCenter = "top-center"
  show BottomRight = "bottom-right"
  show BottomLeft = "bottom-left"
  show BottomCenter = "bottom-center"

-- | Action button configuration
type ToastActionConfig msg =
  { label :: String
  , onAction :: msg
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // toast props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Toast properties
type ToastProps msg =
  { -- Content
    title :: Maybe String
  , description :: Maybe String
  , dismissible :: Boolean
  , action :: Maybe (ToastActionConfig msg)
  , id :: Maybe String
  
  -- Color atoms
  , backgroundColor :: Maybe Color.RGB
  , textColor :: Maybe Color.RGB
  , borderColor :: Maybe Color.RGB
  , iconColor :: Maybe Color.RGB
  , titleColor :: Maybe Color.RGB
  , descriptionColor :: Maybe Color.RGB
  
  -- Geometry atoms
  , borderRadius :: Maybe Geometry.Corners
  , borderWidth :: Maybe Device.Pixel
  
  -- Elevation atoms
  , shadow :: Maybe Shadow.LayeredShadow
  
  -- Dimension atoms
  , padding :: Maybe Device.Pixel
  , maxWidth :: Maybe Device.Pixel
  , gap :: Maybe Device.Pixel
  
  -- Typography atoms
  , titleFontSize :: Maybe FontSize.FontSize
  , titleFontWeight :: Maybe FontWeight.FontWeight
  , descriptionFontSize :: Maybe FontSize.FontSize
  
  -- Behavior
  , onDismiss :: Maybe msg
  
  -- Escape hatch
  , extraAttributes :: Array (E.Attribute msg)
  }

-- | Property modifier
type ToastProp msg = ToastProps msg -> ToastProps msg

-- | Default properties
defaultProps :: forall msg. ToastProps msg
defaultProps =
  { title: Nothing
  , description: Nothing
  , dismissible: true
  , action: Nothing
  , id: Nothing
  , backgroundColor: Nothing
  , textColor: Nothing
  , borderColor: Nothing
  , iconColor: Nothing
  , titleColor: Nothing
  , descriptionColor: Nothing
  , borderRadius: Nothing
  , borderWidth: Nothing
  , shadow: Nothing
  , padding: Nothing
  , maxWidth: Nothing
  , gap: Nothing
  , titleFontSize: Nothing
  , titleFontWeight: Nothing
  , descriptionFontSize: Nothing
  , onDismiss: Nothing
  , extraAttributes: []
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // container props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Container properties
type ContainerProps msg =
  { -- Position
    position :: ToastPosition
  
  -- Dimension atoms
  , gap :: Maybe Device.Pixel
  , padding :: Maybe Device.Pixel
  
  -- Escape hatch
  , extraAttributes :: Array (E.Attribute msg)
  }

-- | Container property modifier
type ContainerProp msg = ContainerProps msg -> ContainerProps msg

-- | Default container properties
defaultContainerProps :: forall msg. ContainerProps msg
defaultContainerProps =
  { position: TopRight
  , gap: Nothing
  , padding: Nothing
  , extraAttributes: []
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // prop builders: content
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set toast title
title :: forall msg. String -> ToastProp msg
title t props = props { title = Just t }

-- | Set toast description
description :: forall msg. String -> ToastProp msg
description d props = props { description = Just d }

-- | Set whether toast is dismissible
dismissible :: forall msg. Boolean -> ToastProp msg
dismissible d props = props { dismissible = d }

-- | Set action button
action :: forall msg. ToastActionConfig msg -> ToastProp msg
action a props = props { action = Just a }

-- | Set toast ID
toastId :: forall msg. String -> ToastProp msg
toastId i props = props { id = Just i }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: color
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set background color (Color.RGB atom)
backgroundColor :: forall msg. Color.RGB -> ToastProp msg
backgroundColor c props = props { backgroundColor = Just c }

-- | Set text color (Color.RGB atom)
textColor :: forall msg. Color.RGB -> ToastProp msg
textColor c props = props { textColor = Just c }

-- | Set border color (Color.RGB atom)
borderColor :: forall msg. Color.RGB -> ToastProp msg
borderColor c props = props { borderColor = Just c }

-- | Set icon color (Color.RGB atom)
iconColor :: forall msg. Color.RGB -> ToastProp msg
iconColor c props = props { iconColor = Just c }

-- | Set title text color (Color.RGB atom)
titleColor :: forall msg. Color.RGB -> ToastProp msg
titleColor c props = props { titleColor = Just c }

-- | Set description text color (Color.RGB atom)
descriptionColor :: forall msg. Color.RGB -> ToastProp msg
descriptionColor c props = props { descriptionColor = Just c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: geometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set border radius (Geometry.Corners atom)
borderRadius :: forall msg. Geometry.Corners -> ToastProp msg
borderRadius r props = props { borderRadius = Just r }

-- | Set border width (Device.Pixel atom)
borderWidth :: forall msg. Device.Pixel -> ToastProp msg
borderWidth w props = props { borderWidth = Just w }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // prop builders: elevation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set shadow (Shadow.LayeredShadow atom)
shadow :: forall msg. Shadow.LayeredShadow -> ToastProp msg
shadow s props = props { shadow = Just s }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // prop builders: dimension
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set padding (Device.Pixel atom)
padding :: forall msg. Device.Pixel -> ToastProp msg
padding p props = props { padding = Just p }

-- | Set max width (Device.Pixel atom)
maxWidth :: forall msg. Device.Pixel -> ToastProp msg
maxWidth w props = props { maxWidth = Just w }

-- | Set gap between title and description (Device.Pixel atom)
gap :: forall msg. Device.Pixel -> ToastProp msg
gap g props = props { gap = Just g }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // prop builders: typography
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set title font size (FontSize atom)
titleFontSize :: forall msg. FontSize.FontSize -> ToastProp msg
titleFontSize s props = props { titleFontSize = Just s }

-- | Set title font weight (FontWeight atom)
titleFontWeight :: forall msg. FontWeight.FontWeight -> ToastProp msg
titleFontWeight w props = props { titleFontWeight = Just w }

-- | Set description font size (FontSize atom)
descriptionFontSize :: forall msg. FontSize.FontSize -> ToastProp msg
descriptionFontSize s props = props { descriptionFontSize = Just s }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // prop builders: container
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set container position
position :: forall msg. ToastPosition -> ContainerProp msg
position p props = props { position = p }

-- | Set gap between toasts in container (Device.Pixel atom)
containerGap :: forall msg. Device.Pixel -> ContainerProp msg
containerGap g props = props { gap = Just g }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: behavior
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set dismiss handler
onDismiss :: forall msg. msg -> ToastProp msg
onDismiss handler props = props { onDismiss = Just handler }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                // prop builders: escape hatch
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add extra attributes (escape hatch)
extraAttributes :: forall msg. Array (E.Attribute msg) -> ToastProp msg
extraAttributes attrs props = props { extraAttributes = props.extraAttributes <> attrs }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // main component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a toast notification
-- |
-- | Pure Element — renders to DOM, Halogen, Static HTML, or any target.
toast :: forall msg. Array (ToastProp msg) -> E.Element msg
toast propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
  in
    E.div_
      (buildToastAttrs props)
      (buildToastContent props)

-- | Build toast attributes
buildToastAttrs :: forall msg. ToastProps msg -> Array (E.Attribute msg)
buildToastAttrs props =
  let
    -- Default colors
    defaultBgColor = Color.rgb 255 255 255  -- White
    defaultBorderColor = Color.rgb 226 232 240  -- Light gray
    
    bgColor = maybe defaultBgColor (\c -> c) props.backgroundColor
    brdColor = maybe defaultBorderColor (\c -> c) props.borderColor
    
    -- Core styles
    coreStyles =
      [ E.role "alert"
      , E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "background-color" (Color.toLegacyCss bgColor)
      , E.style "pointer-events" "auto"
      ]
    
    -- Text color
    textColorStyle = case props.textColor of
      Nothing -> []
      Just c -> [ E.style "color" (Color.toLegacyCss c) ]
    
    -- Border
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
    
    -- Shadow
    shadowStyle = case props.shadow of
      Nothing -> [ E.style "box-shadow" "0 4px 12px rgba(0, 0, 0, 0.15)" ]
      Just s ->
        if Shadow.isNoShadow s
          then []
          else [ E.style "box-shadow" (Shadow.layeredToLegacyCss s) ]
    
    -- Padding
    paddingStyle = case props.padding of
      Nothing -> [ E.style "padding" "16px" ]
      Just p -> [ E.style "padding" (show p) ]
    
    -- Max width
    maxWidthStyle = case props.maxWidth of
      Nothing -> [ E.style "max-width" "360px" ]
      Just w -> [ E.style "max-width" (show w) ]
    
    -- Gap
    gapStyle = case props.gap of
      Nothing -> [ E.style "gap" "4px" ]
      Just g -> [ E.style "gap" (show g) ]
  in
    coreStyles 
    <> textColorStyle 
    <> borderStyle 
    <> radiusStyle 
    <> shadowStyle 
    <> paddingStyle 
    <> maxWidthStyle 
    <> gapStyle
    <> props.extraAttributes

-- | Build toast content
buildToastContent :: forall msg. ToastProps msg -> Array (E.Element msg)
buildToastContent props =
  let
    -- Title
    titleEl = case props.title of
      Nothing -> E.empty
      Just t -> toastTitle props t
    
    -- Description
    descEl = case props.description of
      Nothing -> E.empty
      Just d -> toastDescription props d
    
    -- Action
    actionEl = case props.action of
      Nothing -> E.empty
      Just cfg -> toastAction props cfg
    
    -- Close button
    closeEl = if props.dismissible
      then case props.onDismiss of
        Nothing -> E.empty
        Just _ -> toastClose props
      else E.empty
  in
    [ E.div_
        [ E.style "display" "flex"
        , E.style "justify-content" "space-between"
        , E.style "align-items" "flex-start"
        ]
        [ E.div_
            [ E.style "flex" "1" ]
            [ titleEl, descEl ]
        , closeEl
        ]
    , actionEl
    ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // sub-components
-- ═════════════════════════════════════════════════════════════════════════════

-- | Toast title element
toastTitle :: forall msg. ToastProps msg -> String -> E.Element msg
toastTitle props titleText =
  let
    fontSizeStyle = case props.titleFontSize of
      Nothing -> [ E.style "font-size" "14px" ]
      Just s -> [ E.style "font-size" (FontSize.toLegacyCss s) ]
    
    fontWeightStyle = case props.titleFontWeight of
      Nothing -> [ E.style "font-weight" "600" ]
      Just w -> [ E.style "font-weight" (FontWeight.toLegacyCss w) ]
    
    colorStyle = case props.titleColor of
      Nothing -> []
      Just c -> [ E.style "color" (Color.toLegacyCss c) ]
  in
    E.div_
      ( [ E.style "line-height" "1.4" ]
        <> fontSizeStyle
        <> fontWeightStyle
        <> colorStyle
      )
      [ E.text titleText ]

-- | Toast description element
toastDescription :: forall msg. ToastProps msg -> String -> E.Element msg
toastDescription props descText =
  let
    fontSizeStyle = case props.descriptionFontSize of
      Nothing -> [ E.style "font-size" "13px" ]
      Just s -> [ E.style "font-size" (FontSize.toLegacyCss s) ]
    
    colorStyle = case props.descriptionColor of
      Nothing -> [ E.style "opacity" "0.8" ]
      Just c -> [ E.style "color" (Color.toLegacyCss c) ]
  in
    E.div_
      ( [ E.style "line-height" "1.5"
        , E.style "margin-top" "4px"
        ]
        <> fontSizeStyle
        <> colorStyle
      )
      [ E.text descText ]

-- | Toast action button
toastAction :: forall msg. ToastProps msg -> ToastActionConfig msg -> E.Element msg
toastAction _ cfg =
  E.button_
    [ E.onClick cfg.onAction
    , E.style "margin-top" "8px"
    , E.style "padding" "6px 12px"
    , E.style "font-size" "13px"
    , E.style "font-weight" "500"
    , E.style "background-color" "transparent"
    , E.style "border" "1px solid currentColor"
    , E.style "border-radius" "4px"
    , E.style "cursor" "pointer"
    , E.style "opacity" "0.8"
    ]
    [ E.text cfg.label ]

-- | Toast close button
toastClose :: forall msg. ToastProps msg -> E.Element msg
toastClose props =
  case props.onDismiss of
    Nothing -> E.empty
    Just handler ->
      E.button_
        [ E.onClick handler
        , E.style "background" "transparent"
        , E.style "border" "none"
        , E.style "cursor" "pointer"
        , E.style "padding" "4px"
        , E.style "margin-left" "8px"
        , E.style "opacity" "0.5"
        , E.style "font-size" "18px"
        , E.style "line-height" "1"
        ]
        [ E.text "×" ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // toast container
-- ═════════════════════════════════════════════════════════════════════════════

-- | Container for multiple toasts
-- |
-- | Place once at app root. Position determines where toasts appear.
toastContainer :: forall msg. Array (ContainerProp msg) -> Array (E.Element msg) -> E.Element msg
toastContainer propMods children =
  let
    props = foldl (\p f -> f p) defaultContainerProps propMods
  in
    E.div_
      (buildContainerAttrs props)
      children

-- | Build container attributes
buildContainerAttrs :: forall msg. ContainerProps msg -> Array (E.Attribute msg)
buildContainerAttrs props =
  let
    -- Gap
    gapValue = maybe "12px" show props.gap
    
    -- Padding
    paddingValue = maybe "16px" show props.padding
    
    -- Position-specific styles
    positionStyles = case props.position of
      TopRight ->
        [ E.style "top" "0"
        , E.style "right" "0"
        , E.style "flex-direction" "column"
        ]
      TopLeft ->
        [ E.style "top" "0"
        , E.style "left" "0"
        , E.style "flex-direction" "column"
        ]
      TopCenter ->
        [ E.style "top" "0"
        , E.style "left" "50%"
        , E.style "transform" "translateX(-50%)"
        , E.style "flex-direction" "column"
        , E.style "align-items" "center"
        ]
      BottomRight ->
        [ E.style "bottom" "0"
        , E.style "right" "0"
        , E.style "flex-direction" "column-reverse"
        ]
      BottomLeft ->
        [ E.style "bottom" "0"
        , E.style "left" "0"
        , E.style "flex-direction" "column-reverse"
        ]
      BottomCenter ->
        [ E.style "bottom" "0"
        , E.style "left" "50%"
        , E.style "transform" "translateX(-50%)"
        , E.style "flex-direction" "column-reverse"
        , E.style "align-items" "center"
        ]
    
    -- Core styles
    coreStyles =
      [ E.style "position" "fixed"
      , E.style "z-index" "9999"
      , E.style "display" "flex"
      , E.style "gap" gapValue
      , E.style "padding" paddingValue
      , E.style "pointer-events" "none"
      , E.style "max-height" "100vh"
      , E.style "overflow" "hidden"
      ]
  in
    coreStyles <> positionStyles <> props.extraAttributes
