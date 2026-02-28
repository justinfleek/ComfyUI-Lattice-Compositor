-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // element // loading-bar
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | LoadingBar — Schema-native page/progress loading indicator.
-- |
-- | ## Design Philosophy
-- |
-- | This component accepts **concrete Schema atoms**, not semantic tokens.
-- | Used for page transitions, async operations, and file uploads.
-- |
-- | ## Schema Atoms Accepted
-- |
-- | | Property            | Pillar     | Type                      | CSS Output              |
-- | |---------------------|------------|---------------------------|-------------------------|
-- | | barColor            | Color      | Color.RGB                 | background-color (bar)  |
-- | | trackColor          | Color      | Color.RGB                 | background-color (track)|
-- | | height              | Dimension  | Device.Pixel              | height                  |
-- | | animationDuration   | Motion     | Temporal.Milliseconds     | animation-duration      |
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.LoadingBar as LoadingBar
-- | import Hydrogen.Schema.Color.RGB as Color
-- | import Hydrogen.Schema.Dimension.Device as Device
-- |
-- | -- Indeterminate loading (continuous animation)
-- | LoadingBar.loadingBar
-- |   [ LoadingBar.indeterminate true
-- |   , LoadingBar.visible state.isLoading
-- |   , LoadingBar.barColor brand.primaryColor
-- |   ]
-- |
-- | -- Determinate progress (0-100)
-- | LoadingBar.loadingBar
-- |   [ LoadingBar.progress 65
-- |   , LoadingBar.visible true
-- |   , LoadingBar.barColor brand.successColor
-- |   ]
-- |
-- | -- Fixed to top of page
-- | LoadingBar.loadingBar
-- |   [ LoadingBar.position LoadingBar.Top
-- |   , LoadingBar.indeterminate true
-- |   , LoadingBar.visible state.isLoading
-- |   ]
-- | ```

module Hydrogen.Element.Compound.LoadingBar
  ( -- * Main Components
    loadingBar
  , loadingBarInline
  
  -- * Types
  , Position(Top, Bottom, Inline)
  
  -- * Props
  , LoadingBarProps
  , LoadingBarProp
  , defaultProps
  
  -- * State Props
  , progress
  , indeterminate
  , visible
  , position
  
  -- * Color Atoms
  , barColor
  , trackColor
  
  -- * Dimension Atoms
  , height
  
  -- * Motion Atoms
  , animationDuration
  
  -- * Escape Hatch
  , extraAttributes
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  , not
  )

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just), maybe)

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Dimension.Temporal as Temporal

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Loading bar position
data Position
  = Top       -- Fixed to top of viewport
  | Bottom    -- Fixed to bottom of viewport
  | Inline    -- Inline within content flow

derive instance eqPosition :: Eq Position

instance showPosition :: Show Position where
  show Top = "top"
  show Bottom = "bottom"
  show Inline = "inline"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | LoadingBar properties
type LoadingBarProps msg =
  { -- State
    progress :: Int          -- 0-100
  , indeterminate :: Boolean
  , visible :: Boolean
  , position :: Position
  
  -- Color atoms
  , barColor :: Maybe Color.RGB
  , trackColor :: Maybe Color.RGB
  
  -- Dimension atoms
  , height :: Maybe Device.Pixel
  
  -- Motion atoms
  , animationDuration :: Maybe Temporal.Milliseconds
  
  -- Escape hatch
  , extraAttributes :: Array (E.Attribute msg)
  }

-- | Property modifier
type LoadingBarProp msg = LoadingBarProps msg -> LoadingBarProps msg

-- | Default properties
defaultProps :: forall msg. LoadingBarProps msg
defaultProps =
  { progress: 0
  , indeterminate: true
  , visible: true
  , position: Inline
  , barColor: Nothing
  , trackColor: Nothing
  , height: Nothing
  , animationDuration: Nothing
  , extraAttributes: []
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set progress value (0-100)
-- |
-- | Only used when indeterminate is false.
progress :: forall msg. Int -> LoadingBarProp msg
progress p props = props { progress = p }

-- | Set indeterminate mode
-- |
-- | When true, shows continuous animation instead of progress percentage.
indeterminate :: forall msg. Boolean -> LoadingBarProp msg
indeterminate i props = props { indeterminate = i }

-- | Set visibility
-- |
-- | Controls whether the loading bar is rendered.
visible :: forall msg. Boolean -> LoadingBarProp msg
visible v props = props { visible = v }

-- | Set position
position :: forall msg. Position -> LoadingBarProp msg
position p props = props { position = p }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: color
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set bar/indicator color (Color.RGB atom)
barColor :: forall msg. Color.RGB -> LoadingBarProp msg
barColor c props = props { barColor = Just c }

-- | Set track background color (Color.RGB atom)
trackColor :: forall msg. Color.RGB -> LoadingBarProp msg
trackColor c props = props { trackColor = Just c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // prop builders: dimension
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set bar height (Device.Pixel atom)
height :: forall msg. Device.Pixel -> LoadingBarProp msg
height h props = props { height = Just h }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // prop builders: motion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set animation duration (Temporal.Milliseconds atom)
-- |
-- | Controls how long the indeterminate animation cycle takes.
animationDuration :: forall msg. Temporal.Milliseconds -> LoadingBarProp msg
animationDuration d props = props { animationDuration = Just d }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                // prop builders: escape hatch
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add extra attributes (escape hatch)
extraAttributes :: forall msg. Array (E.Attribute msg) -> LoadingBarProp msg
extraAttributes attrs props = props { extraAttributes = props.extraAttributes <> attrs }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // main component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a loading bar
-- |
-- | Pure Element — renders to DOM, Halogen, Static HTML, or any target.
loadingBar :: forall msg. Array (LoadingBarProp msg) -> E.Element msg
loadingBar propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
  in
    if not props.visible
      then E.empty
      else E.div_
        (buildContainerAttrs props)
        [ E.div_ (buildBarAttrs props) [] ]

-- | Render an inline loading bar (convenience function)
-- |
-- | Same as loadingBar but forces Inline position.
loadingBarInline :: forall msg. Array (LoadingBarProp msg) -> E.Element msg
loadingBarInline propMods =
  loadingBar (propMods <> [ position Inline ])

-- | Build container attributes
buildContainerAttrs :: forall msg. LoadingBarProps msg -> Array (E.Attribute msg)
buildContainerAttrs props =
  let
    -- Default track color (very light)
    defaultTrackColor = Color.rgb 226 232 240
    trackCol = maybe defaultTrackColor (\c -> c) props.trackColor
    
    -- Height
    heightValue = maybe "3px" show props.height
    
    -- Position-specific styles
    positionStyles = case props.position of
      Top ->
        [ E.style "position" "fixed"
        , E.style "top" "0"
        , E.style "left" "0"
        , E.style "right" "0"
        , E.style "z-index" "9999"
        ]
      Bottom ->
        [ E.style "position" "fixed"
        , E.style "bottom" "0"
        , E.style "left" "0"
        , E.style "right" "0"
        , E.style "z-index" "9999"
        ]
      Inline ->
        [ E.style "position" "relative"
        , E.style "width" "100%"
        ]
    
    -- Core styles
    coreStyles =
      [ E.style "height" heightValue
      , E.style "background-color" (Color.toLegacyCss trackCol)
      , E.style "overflow" "hidden"
      ]
  in
    coreStyles <> positionStyles <> props.extraAttributes

-- | Build bar (indicator) attributes
buildBarAttrs :: forall msg. LoadingBarProps msg -> Array (E.Attribute msg)
buildBarAttrs props =
  let
    -- Default bar color (blue)
    defaultBarColor = Color.rgb 59 130 246
    barCol = maybe defaultBarColor (\c -> c) props.barColor
    
    -- Animation duration
    animDur = maybe "1.5s" show props.animationDuration
    
    -- Width and animation based on mode
    widthAndAnimation = if props.indeterminate
      then
        [ E.style "width" "30%"
        , E.style "animation" ("loading-bar-indeterminate " <> animDur <> " ease-in-out infinite")
        ]
      else
        [ E.style "width" (show props.progress <> "%")
        , E.style "transition" "width 300ms ease-out"
        ]
    
    -- Core styles
    coreStyles =
      [ E.style "height" "100%"
      , E.style "background-color" (Color.toLegacyCss barCol)
      ]
  in
    coreStyles <> widthAndAnimation
