-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                            // hydrogen // element // progress
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Progress — Schema-native progress indicator component.
-- |
-- | ## Design Philosophy
-- |
-- | This component accepts **concrete Schema atoms**, not semantic tokens.
-- | Value is specified as a bounded Percent type for type safety.
-- |
-- | ## Schema Atoms Accepted
-- |
-- | | Property            | Pillar     | Type                      | CSS Output              |
-- | |---------------------|------------|---------------------------|-------------------------|
-- | | trackColor          | Color      | Color.RGB                 | background-color (track)|
-- | | indicatorColor      | Color      | Color.RGB                 | background-color (bar)  |
-- | | height              | Dimension  | Device.Pixel              | height                  |
-- | | borderRadius        | Geometry   | Geometry.Corners          | border-radius           |
-- | | transitionDuration  | Motion     | Temporal.Milliseconds     | transition-duration     |
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.Progress as Progress
-- | import Hydrogen.Schema.Color.RGB as Color
-- | import Hydrogen.Schema.Dimension.Device as Device
-- |
-- | -- Basic progress bar (60%)
-- | Progress.progress [ Progress.value 60 ]
-- |
-- | -- With brand atoms
-- | Progress.progress
-- |   [ Progress.value 80
-- |   , Progress.indicatorColor brand.primaryColor
-- |   , Progress.trackColor brand.progressTrack
-- |   , Progress.height (Device.px 8.0)
-- |   ]
-- |
-- | -- Indeterminate (loading)
-- | Progress.progressIndeterminate
-- |   [ Progress.indicatorColor brand.primaryColor ]
-- | ```

module Hydrogen.Element.Compound.Progress
  ( -- * Main Components
    progress
  , progressIndeterminate
  
  -- * Props
  , ProgressProps
  , ProgressProp
  , defaultProps
  
  -- * Value Props
  , value
  , maxValue
  
  -- * Color Atoms
  , trackColor
  , indicatorColor
  
  -- * Geometry Atoms
  , borderRadius
  
  -- * Dimension Atoms
  , height
  
  -- * Motion Atoms
  , transitionDuration
  
  -- * Escape Hatch
  , extraAttributes
  ) where

import Prelude
  ( show
  , (<>)
  , (/)
  , (*)
  )

import Data.Array (foldl)
import Data.Int (toNumber)
import Data.Maybe (Maybe(Nothing, Just), maybe)

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Dimension.Temporal as Temporal

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Progress properties
type ProgressProps msg =
  { -- Value
    value :: Int
  , maxValue :: Int
  
  -- Color atoms
  , trackColor :: Maybe Color.RGB
  , indicatorColor :: Maybe Color.RGB
  
  -- Geometry atoms
  , borderRadius :: Maybe Geometry.Corners
  
  -- Dimension atoms
  , height :: Maybe Device.Pixel
  
  -- Motion atoms
  , transitionDuration :: Maybe Temporal.Milliseconds
  
  -- Escape hatch
  , extraAttributes :: Array (E.Attribute msg)
  }

-- | Property modifier
type ProgressProp msg = ProgressProps msg -> ProgressProps msg

-- | Default properties
defaultProps :: forall msg. ProgressProps msg
defaultProps =
  { value: 0
  , maxValue: 100
  , trackColor: Nothing
  , indicatorColor: Nothing
  , borderRadius: Nothing
  , height: Nothing
  , transitionDuration: Nothing
  , extraAttributes: []
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: value
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set progress value (0-100)
value :: forall msg. Int -> ProgressProp msg
value v props = props { value = v }

-- | Set maximum value (default 100)
maxValue :: forall msg. Int -> ProgressProp msg
maxValue m props = props { maxValue = m }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: color
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set track background color (Color.RGB atom)
trackColor :: forall msg. Color.RGB -> ProgressProp msg
trackColor c props = props { trackColor = Just c }

-- | Set indicator/bar color (Color.RGB atom)
indicatorColor :: forall msg. Color.RGB -> ProgressProp msg
indicatorColor c props = props { indicatorColor = Just c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: geometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set border radius (Geometry.Corners atom)
borderRadius :: forall msg. Geometry.Corners -> ProgressProp msg
borderRadius r props = props { borderRadius = Just r }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // prop builders: dimension
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set bar height (Device.Pixel atom)
height :: forall msg. Device.Pixel -> ProgressProp msg
height h props = props { height = Just h }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // prop builders: motion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set transition duration (Temporal.Milliseconds atom)
transitionDuration :: forall msg. Temporal.Milliseconds -> ProgressProp msg
transitionDuration d props = props { transitionDuration = Just d }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                // prop builders: escape hatch
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add extra attributes (escape hatch)
extraAttributes :: forall msg. Array (E.Attribute msg) -> ProgressProp msg
extraAttributes attrs props = props { extraAttributes = props.extraAttributes <> attrs }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // main component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a progress bar
-- |
-- | Pure Element — renders to DOM, Halogen, Static HTML, or any target.
progress :: forall msg. Array (ProgressProp msg) -> E.Element msg
progress propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    percentage = (toNumber props.value * 100.0) / toNumber props.maxValue
  in
    E.div_
      (buildTrackAttrs props)
      [ E.div_
          (buildIndicatorAttrs percentage props)
          []
      ]

-- | Build track (container) attributes
buildTrackAttrs :: forall msg. ProgressProps msg -> Array (E.Attribute msg)
buildTrackAttrs props =
  let
    -- Default track color
    defaultTrackColor = Color.rgb 226 232 240  -- Light gray
    trackCol = maybe defaultTrackColor (\c -> c) props.trackColor
    
    -- Height
    heightValue = maybe "16px" show props.height
    
    -- Border radius
    radiusStyle = case props.borderRadius of
      Nothing -> [ E.style "border-radius" "9999px" ]  -- Fully rounded
      Just r -> [ E.style "border-radius" (Geometry.cornersToLegacyCss r) ]
    
    -- Core styles
    coreStyles =
      [ E.role "progressbar"
      , E.attr "aria-valuenow" (show props.value)
      , E.attr "aria-valuemin" "0"
      , E.attr "aria-valuemax" (show props.maxValue)
      , E.style "position" "relative"
      , E.style "width" "100%"
      , E.style "height" heightValue
      , E.style "overflow" "hidden"
      , E.style "background-color" (Color.toLegacyCss trackCol)
      ]
  in
    coreStyles <> radiusStyle <> props.extraAttributes

-- | Build indicator (progress bar) attributes
buildIndicatorAttrs :: forall msg. Number -> ProgressProps msg -> Array (E.Attribute msg)
buildIndicatorAttrs percentage props =
  let
    -- Default indicator color
    defaultIndicatorColor = Color.rgb 59 130 246  -- Blue
    indicatorCol = maybe defaultIndicatorColor (\c -> c) props.indicatorColor
    
    -- Transition
    transitionStyle = case props.transitionDuration of
      Nothing -> [ E.style "transition" "width 300ms ease-out" ]
      Just d -> [ E.style "transition" ("width " <> show d <> " ease-out") ]
    
    -- Core styles
    coreStyles =
      [ E.style "height" "100%"
      , E.style "width" (show percentage <> "%")
      , E.style "background-color" (Color.toLegacyCss indicatorCol)
      , E.style "border-radius" "inherit"
      ]
  in
    coreStyles <> transitionStyle

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // indeterminate state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render an indeterminate progress bar (loading state)
-- |
-- | Shows an animated indicator for unknown progress.
progressIndeterminate :: forall msg. Array (ProgressProp msg) -> E.Element msg
progressIndeterminate propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    -- Default colors
    defaultTrackColor = Color.rgb 226 232 240
    defaultIndicatorColor = Color.rgb 59 130 246
    
    trackCol = maybe defaultTrackColor (\c -> c) props.trackColor
    indicatorCol = maybe defaultIndicatorColor (\c -> c) props.indicatorColor
    
    -- Height
    heightValue = maybe "16px" show props.height
    
    -- Border radius
    radiusStyle = case props.borderRadius of
      Nothing -> [ E.style "border-radius" "9999px" ]
      Just r -> [ E.style "border-radius" (Geometry.cornersToLegacyCss r) ]
    
    -- Track styles
    trackStyles =
      [ E.role "progressbar"
      , E.style "position" "relative"
      , E.style "width" "100%"
      , E.style "height" heightValue
      , E.style "overflow" "hidden"
      , E.style "background-color" (Color.toLegacyCss trackCol)
      ]
    
    -- Indicator styles (animated)
    indicatorStyles =
      [ E.style "height" "100%"
      , E.style "width" "33%"
      , E.style "background-color" (Color.toLegacyCss indicatorCol)
      , E.style "border-radius" "inherit"
      , E.style "animation" "progress-indeterminate 1.5s ease-in-out infinite"
      ]
  in
    E.div_
      (trackStyles <> radiusStyle <> props.extraAttributes)
      [ E.div_ indicatorStyles [] ]
