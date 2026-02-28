-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // element // compound // avatar
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Avatar — Schema-native user avatar component.
-- |
-- | ## Design Philosophy
-- |
-- | This component accepts **concrete Schema atoms**, not semantic tokens.
-- | Size is specified as Device.Pixel, not "sm/md/lg".
-- |
-- | ## Schema Atoms Accepted
-- |
-- | | Property            | Pillar     | Type                      | CSS Output              |
-- | |---------------------|------------|---------------------------|-------------------------|
-- | | size                | Dimension  | Device.Pixel              | width, height           |
-- | | backgroundColor     | Color      | Color.RGB                 | background-color        |
-- | | textColor           | Color      | Color.RGB                 | color (fallback text)   |
-- | | borderColor         | Color      | Color.RGB                 | border-color            |
-- | | borderWidth         | Dimension  | Device.Pixel              | border-width            |
-- | | fontSize            | Typography | Typography.FontSize       | font-size (fallback)    |
-- | | fontWeight          | Typography | Typography.FontWeight     | font-weight (fallback)  |
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.Avatar as Avatar
-- | import Hydrogen.Schema.Dimension.Device as Device
-- | import Hydrogen.Schema.Color.RGB as Color
-- |
-- | -- With image
-- | Avatar.avatar [ Avatar.size (Device.px 40.0) ]
-- |   [ Avatar.avatarImage [ Avatar.imgSrc "/user.jpg", Avatar.imgAlt "User" ]
-- |   , Avatar.avatarFallback [] [ E.text "JD" ]
-- |   ]
-- |
-- | -- Fallback only with brand atoms
-- | Avatar.avatar
-- |   [ Avatar.size brand.avatarSize
-- |   , Avatar.backgroundColor brand.avatarBackground
-- |   , Avatar.textColor brand.avatarText
-- |   ]
-- |   [ Avatar.avatarFallback [] [ E.text "AB" ] ]
-- | ```

module Hydrogen.Element.Compound.Avatar
  ( -- * Main Component
    avatar
  
  -- * Sub-components
  , avatarImage
  , avatarFallback
  
  -- * Props
  , AvatarProps
  , AvatarProp
  , ImageProps
  , ImageProp
  , defaultProps
  , defaultImageProps
  
  -- * Dimension Atoms
  , size
  
  -- * Color Atoms
  , backgroundColor
  , textColor
  , borderColor
  
  -- * Geometry Atoms
  , borderWidth
  
  -- * Typography Atoms
  , fontSize
  , fontWeight
  
  -- * Image Props
  , imgSrc
  , imgAlt
  
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
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Typography.FontSize as FontSize
import Hydrogen.Schema.Typography.FontWeight as FontWeight

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Avatar properties
type AvatarProps msg =
  { -- Dimension atoms
    size :: Maybe Device.Pixel
  
  -- Color atoms
  , backgroundColor :: Maybe Color.RGB
  , textColor :: Maybe Color.RGB
  , borderColor :: Maybe Color.RGB
  
  -- Geometry atoms
  , borderWidth :: Maybe Device.Pixel
  
  -- Typography atoms
  , fontSize :: Maybe FontSize.FontSize
  , fontWeight :: Maybe FontWeight.FontWeight
  
  -- Escape hatch
  , extraAttributes :: Array (E.Attribute msg)
  }

-- | Property modifier
type AvatarProp msg = AvatarProps msg -> AvatarProps msg

-- | Default properties
defaultProps :: forall msg. AvatarProps msg
defaultProps =
  { size: Nothing
  , backgroundColor: Nothing
  , textColor: Nothing
  , borderColor: Nothing
  , borderWidth: Nothing
  , fontSize: Nothing
  , fontWeight: Nothing
  , extraAttributes: []
  }

-- | Image properties
type ImageProps =
  { imgSrc :: String
  , imgAlt :: String
  }

-- | Image property modifier
type ImageProp = ImageProps -> ImageProps

-- | Default image properties
defaultImageProps :: ImageProps
defaultImageProps =
  { imgSrc: ""
  , imgAlt: ""
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // prop builders: dimension
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set avatar size (Device.Pixel atom)
-- |
-- | Controls both width and height for a square avatar.
size :: forall msg. Device.Pixel -> AvatarProp msg
size s props = props { size = Just s }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: color
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set fallback background color (Color.RGB atom)
backgroundColor :: forall msg. Color.RGB -> AvatarProp msg
backgroundColor c props = props { backgroundColor = Just c }

-- | Set fallback text color (Color.RGB atom)
textColor :: forall msg. Color.RGB -> AvatarProp msg
textColor c props = props { textColor = Just c }

-- | Set border color (Color.RGB atom)
borderColor :: forall msg. Color.RGB -> AvatarProp msg
borderColor c props = props { borderColor = Just c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: geometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set border width (Device.Pixel atom)
borderWidth :: forall msg. Device.Pixel -> AvatarProp msg
borderWidth w props = props { borderWidth = Just w }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // prop builders: typography
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set fallback font size (FontSize atom)
fontSize :: forall msg. FontSize.FontSize -> AvatarProp msg
fontSize s props = props { fontSize = Just s }

-- | Set fallback font weight (FontWeight atom)
fontWeight :: forall msg. FontWeight.FontWeight -> AvatarProp msg
fontWeight w props = props { fontWeight = Just w }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: image
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set image source URL
imgSrc :: String -> ImageProp
imgSrc s props = props { imgSrc = s }

-- | Set image alt text
imgAlt :: String -> ImageProp
imgAlt a props = props { imgAlt = a }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                // prop builders: escape hatch
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add extra attributes (escape hatch)
extraAttributes :: forall msg. Array (E.Attribute msg) -> AvatarProp msg
extraAttributes attrs props = props { extraAttributes = props.extraAttributes <> attrs }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // main component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render an avatar container
-- |
-- | Pure Element — renders to DOM, Halogen, Static HTML, or any target.
avatar :: forall msg. Array (AvatarProp msg) -> Array (E.Element msg) -> E.Element msg
avatar propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
  in
    E.span_
      (buildAvatarAttrs props)
      children

-- | Build avatar attributes from props
buildAvatarAttrs :: forall msg. AvatarProps msg -> Array (E.Attribute msg)
buildAvatarAttrs props =
  let
    -- Size (default 40px)
    sizeValue = maybe "40px" show props.size
    
    -- Core styles
    coreStyles =
      [ E.style "position" "relative"
      , E.style "display" "inline-flex"
      , E.style "flex-shrink" "0"
      , E.style "overflow" "hidden"
      , E.style "border-radius" "50%"
      , E.style "width" sizeValue
      , E.style "height" sizeValue
      ]
    
    -- Border styles
    borderStyle = case props.borderColor of
      Nothing -> []
      Just bc ->
        let bw = maybe "2px" show props.borderWidth
        in [ E.style "border-style" "solid"
           , E.style "border-width" bw
           , E.style "border-color" (Color.toLegacyCss bc)
           ]
  in
    coreStyles <> borderStyle <> props.extraAttributes

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // sub-components
-- ═════════════════════════════════════════════════════════════════════════════

-- | Avatar image
-- |
-- | Renders the user's image. Falls back to avatarFallback when image fails.
avatarImage :: forall msg. Array ImageProp -> E.Element msg
avatarImage propMods =
  let
    props = foldl (\p f -> f p) defaultImageProps propMods
  in
    E.img_
      [ E.src props.imgSrc
      , E.alt props.imgAlt
      , E.style "aspect-ratio" "1"
      , E.style "width" "100%"
      , E.style "height" "100%"
      , E.style "object-fit" "cover"
      ]

-- | Avatar fallback
-- |
-- | Shown when image fails to load or isn't provided.
-- | Typically contains user initials.
avatarFallback :: forall msg. Array (AvatarProp msg) -> Array (E.Element msg) -> E.Element msg
avatarFallback propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    -- Default colors
    defaultBgColor = Color.rgb 226 232 240  -- Light gray
    defaultTextColor = Color.rgb 71 85 105  -- Dark gray
    
    bgColor = maybe defaultBgColor (\c -> c) props.backgroundColor
    txtColor = maybe defaultTextColor (\c -> c) props.textColor
    
    -- Font styles
    fontSizeStyle = case props.fontSize of
      Nothing -> [ E.style "font-size" "14px" ]
      Just s -> [ E.style "font-size" (FontSize.toLegacyCss s) ]
    
    fontWeightStyle = case props.fontWeight of
      Nothing -> [ E.style "font-weight" "500" ]
      Just w -> [ E.style "font-weight" (FontWeight.toLegacyCss w) ]
  in
    E.span_
      ( [ E.style "display" "flex"
        , E.style "width" "100%"
        , E.style "height" "100%"
        , E.style "align-items" "center"
        , E.style "justify-content" "center"
        , E.style "border-radius" "50%"
        , E.style "background-color" (Color.toLegacyCss bgColor)
        , E.style "color" (Color.toLegacyCss txtColor)
        , E.style "text-transform" "uppercase"
        ]
        <> fontSizeStyle
        <> fontWeightStyle
      )
      children
