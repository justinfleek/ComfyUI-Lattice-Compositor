-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                            // hydrogen // element // skeleton
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Skeleton — Schema-native loading placeholder component.
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
-- | | shimmerColor     | Color      | Color.RGB                 | shimmer highlight       |
-- | | width            | Dimension  | Device.Pixel              | width                   |
-- | | height           | Dimension  | Device.Pixel              | height                  |
-- | | borderRadius     | Geometry   | Geometry.Corners          | border-radius           |
-- | | animationDuration| Motion     | Temporal.Milliseconds     | animation-duration      |
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.Skeleton as Skeleton
-- | import Hydrogen.Schema.Dimension.Device as Device
-- | import Hydrogen.Schema.Color.RGB as Color
-- |
-- | -- Basic skeleton
-- | Skeleton.skeleton
-- |   [ Skeleton.width (Device.px 200.0)
-- |   , Skeleton.height (Device.px 16.0)
-- |   ]
-- |
-- | -- Circle skeleton (avatar)
-- | Skeleton.circle [ Skeleton.size (Device.px 48.0) ]
-- |
-- | -- With brand atoms
-- | Skeleton.skeleton
-- |   [ Skeleton.color brand.skeletonBase
-- |   , Skeleton.shimmerColor brand.skeletonHighlight
-- |   , Skeleton.borderRadius brand.cardRadius
-- |   ]
-- |
-- | -- Skeleton group
-- | Skeleton.group [ Skeleton.direction Skeleton.Horizontal, Skeleton.gap (Device.px 12.0) ]
-- |   [ Skeleton.circle [ Skeleton.size (Device.px 40.0) ]
-- |   , Skeleton.group [ Skeleton.direction Skeleton.Vertical ]
-- |       [ Skeleton.skeleton [ Skeleton.width (Device.px 120.0) ]
-- |       , Skeleton.skeleton [ Skeleton.width (Device.px 80.0) ]
-- |       ]
-- |   ]
-- | ```

module Hydrogen.Element.Compound.Skeleton
  ( -- * Main Components
    skeleton
  , circle
  , rectangle
  , textLine
  , group
  
  -- * Presets
  , cardSkeleton
  , avatarWithText
  
  -- * Types
  , Animation(Pulse, Shimmer, None)
  , Direction(Horizontal, Vertical)
  
  -- * Props
  , SkeletonProps
  , SkeletonProp
  , GroupProps
  , GroupProp
  , defaultProps
  , defaultGroupProps
  
  -- * Color Atoms
  , color
  , shimmerColor
  
  -- * Geometry Atoms
  , borderRadius
  
  -- * Dimension Atoms
  , width
  , height
  , size
  , gap
  
  -- * Motion Atoms
  , animationDuration
  
  -- * Other Props
  , animation
  , direction
  
  -- * Escape Hatch
  , extraAttributes
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  , (==)
  )

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just), maybe)

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Dimension.Temporal as Temporal

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Skeleton animation type
data Animation
  = Pulse     -- Fading in/out
  | Shimmer   -- Moving highlight
  | None      -- No animation

derive instance eqAnimation :: Eq Animation

instance showAnimation :: Show Animation where
  show Pulse = "pulse"
  show Shimmer = "shimmer"
  show None = "none"

-- | Group direction
data Direction
  = Horizontal
  | Vertical

derive instance eqDirection :: Eq Direction

instance showDirection :: Show Direction where
  show Horizontal = "horizontal"
  show Vertical = "vertical"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // skeleton props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Skeleton properties
type SkeletonProps msg =
  { -- Color atoms
    color :: Maybe Color.RGB
  , shimmerColor :: Maybe Color.RGB
  
  -- Geometry atoms
  , borderRadius :: Maybe Geometry.Corners
  
  -- Dimension atoms
  , width :: Maybe Device.Pixel
  , height :: Maybe Device.Pixel
  
  -- Motion atoms
  , animationDuration :: Maybe Temporal.Milliseconds
  
  -- Animation type
  , animation :: Animation
  
  -- Escape hatch
  , extraAttributes :: Array (E.Attribute msg)
  }

-- | Property modifier
type SkeletonProp msg = SkeletonProps msg -> SkeletonProps msg

-- | Default properties
defaultProps :: forall msg. SkeletonProps msg
defaultProps =
  { color: Nothing
  , shimmerColor: Nothing
  , borderRadius: Nothing
  , width: Nothing
  , height: Nothing
  , animationDuration: Nothing
  , animation: Pulse
  , extraAttributes: []
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // group props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Group properties
type GroupProps msg =
  { -- Direction
    direction :: Direction
  
  -- Dimension atoms
  , gap :: Maybe Device.Pixel
  
  -- Escape hatch
  , extraAttributes :: Array (E.Attribute msg)
  }

-- | Group property modifier
type GroupProp msg = GroupProps msg -> GroupProps msg

-- | Default group properties
defaultGroupProps :: forall msg. GroupProps msg
defaultGroupProps =
  { direction: Vertical
  , gap: Nothing
  , extraAttributes: []
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: color
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set skeleton base color (Color.RGB atom)
color :: forall msg. Color.RGB -> SkeletonProp msg
color c props = props { color = Just c }

-- | Set shimmer highlight color (Color.RGB atom)
shimmerColor :: forall msg. Color.RGB -> SkeletonProp msg
shimmerColor c props = props { shimmerColor = Just c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: geometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set border radius (Geometry.Corners atom)
borderRadius :: forall msg. Geometry.Corners -> SkeletonProp msg
borderRadius r props = props { borderRadius = Just r }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // prop builders: dimension
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set width (Device.Pixel atom)
width :: forall msg. Device.Pixel -> SkeletonProp msg
width w props = props { width = Just w }

-- | Set height (Device.Pixel atom)
height :: forall msg. Device.Pixel -> SkeletonProp msg
height h props = props { height = Just h }

-- | Set size for square/circle skeletons (Device.Pixel atom)
-- |
-- | Sets both width and height to the same value.
size :: forall msg. Device.Pixel -> SkeletonProp msg
size s props = props { width = Just s, height = Just s }

-- | Set gap between group items (Device.Pixel atom)
gap :: forall msg. Device.Pixel -> GroupProp msg
gap g props = props { gap = Just g }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // prop builders: motion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set animation duration (Temporal.Milliseconds atom)
animationDuration :: forall msg. Temporal.Milliseconds -> SkeletonProp msg
animationDuration d props = props { animationDuration = Just d }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: other
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set animation type
animation :: forall msg. Animation -> SkeletonProp msg
animation a props = props { animation = a }

-- | Set group direction
direction :: forall msg. Direction -> GroupProp msg
direction d props = props { direction = d }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                // prop builders: escape hatch
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add extra attributes (escape hatch)
extraAttributes :: forall msg. Array (E.Attribute msg) -> SkeletonProp msg
extraAttributes attrs props = props { extraAttributes = props.extraAttributes <> attrs }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // main component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a skeleton placeholder
-- |
-- | Pure Element — renders to DOM, Halogen, Static HTML, or any target.
skeleton :: forall msg. Array (SkeletonProp msg) -> E.Element msg
skeleton propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
  in
    E.div_
      (buildSkeletonAttrs props)
      []

-- | Build skeleton attributes
buildSkeletonAttrs :: forall msg. SkeletonProps msg -> Array (E.Attribute msg)
buildSkeletonAttrs props =
  let
    -- Default color (light gray)
    defaultColor = Color.rgb 226 232 240
    baseColor = maybe defaultColor (\c -> c) props.color
    
    -- Dimensions
    widthValue = maybe "100%" show props.width
    heightValue = maybe "16px" show props.height
    
    -- Border radius (default: small rounded)
    radiusStyle = case props.borderRadius of
      Nothing -> [ E.style "border-radius" "4px" ]
      Just r -> [ E.style "border-radius" (Geometry.cornersToLegacyCss r) ]
    
    -- Animation
    animationValue = case props.animation of
      None -> "none"
      Pulse -> 
        let dur = maybe "1.5s" show props.animationDuration
        in "skeleton-pulse " <> dur <> " ease-in-out infinite"
      Shimmer ->
        let dur = maybe "1.5s" show props.animationDuration
        in "skeleton-shimmer " <> dur <> " linear infinite"
    
    animationStyle = if props.animation == None
      then []
      else [ E.style "animation" animationValue ]
    
    -- Core styles
    coreStyles =
      [ E.style "display" "block"
      , E.style "width" widthValue
      , E.style "height" heightValue
      , E.style "background-color" (Color.toLegacyCss baseColor)
      ]
  in
    coreStyles <> radiusStyle <> animationStyle <> props.extraAttributes

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // shape variants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Circle skeleton (for avatars)
circle :: forall msg. Array (SkeletonProp msg) -> E.Element msg
circle propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    -- Get size (use width, default 40px)
    sizeValue = maybe "40px" show props.width
    
    -- Override border radius for circle
    circleStyles =
      [ E.style "border-radius" "50%"
      , E.style "width" sizeValue
      , E.style "height" sizeValue
      ]
    
    baseAttrs = buildSkeletonAttrs props
  in
    E.div_
      (baseAttrs <> circleStyles)
      []

-- | Rectangle skeleton (for images/cards)
rectangle :: forall msg. Array (SkeletonProp msg) -> E.Element msg
rectangle propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    -- Default larger height for rectangles
    heightValue = maybe "120px" show props.height
    
    -- Override height
    rectStyles = [ E.style "height" heightValue ]
    
    baseAttrs = buildSkeletonAttrs props
  in
    E.div_
      (baseAttrs <> rectStyles)
      []

-- | Text line skeleton
textLine :: forall msg. Array (SkeletonProp msg) -> E.Element msg
textLine propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    -- Default text-like height
    heightValue = maybe "14px" show props.height
    
    -- Override height
    textStyles = [ E.style "height" heightValue ]
    
    baseAttrs = buildSkeletonAttrs props
  in
    E.div_
      (baseAttrs <> textStyles)
      []

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // group
-- ═════════════════════════════════════════════════════════════════════════════

-- | Group of skeletons
group :: forall msg. Array (GroupProp msg) -> Array (E.Element msg) -> E.Element msg
group propMods children =
  let
    props = foldl (\p f -> f p) defaultGroupProps propMods
    
    -- Direction
    flexDirection = case props.direction of
      Horizontal -> "row"
      Vertical -> "column"
    
    -- Gap
    gapValue = maybe "8px" show props.gap
  in
    E.div_
      ( [ E.style "display" "flex"
        , E.style "flex-direction" flexDirection
        , E.style "gap" gapValue
        ]
        <> props.extraAttributes
      )
      children

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Card skeleton preset
cardSkeleton :: forall msg. E.Element msg
cardSkeleton =
  group [ direction Vertical, gap (Device.px 12.0) ]
    [ rectangle [ width (Device.px 280.0), height (Device.px 160.0) ]
    , textLine [ width (Device.px 200.0) ]
    , textLine [ width (Device.px 160.0) ]
    , textLine [ width (Device.px 100.0) ]
    ]

-- | Avatar with text skeleton preset
avatarWithText :: forall msg. E.Element msg
avatarWithText =
  group [ direction Horizontal, gap (Device.px 12.0) ]
    [ circle [ size (Device.px 48.0) ]
    , group [ direction Vertical, gap (Device.px 8.0) ]
        [ textLine [ width (Device.px 120.0), height (Device.px 14.0) ]
        , textLine [ width (Device.px 80.0), height (Device.px 12.0) ]
        ]
    ]
