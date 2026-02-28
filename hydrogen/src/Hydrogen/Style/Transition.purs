-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                            // hydrogen // style // transition
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Advanced transition and animation builders
-- |
-- | This module provides composable builders for complex CSS transitions
-- | and animations, bridging Schema motion primitives to inline styles.
-- |
-- | ## Inline Style Building
-- |
-- | For dynamic values from the Schema (like custom bezier curves), 
-- | we need inline styles rather than Tailwind classes.
-- |
-- | ```purescript
-- | import Hydrogen.Style.Transition as Trans
-- | import Hydrogen.Schema.Motion.Easing as SchemaEasing
-- |
-- | -- Build a custom transition style
-- | Trans.transitionStyle
-- |   { property: Trans.PropTransform
-- |   , duration: 300
-- |   , easing: SchemaEasing.easeOutCubic
-- |   , delay: 0
-- |   }
-- | -- "transition: transform 300ms cubic-bezier(0.33, 1, 0.68, 1) 0ms"
-- | ```
-- |
-- | ## Keyframe Animation Styles
-- |
-- | ```purescript
-- | Trans.animationStyle
-- |   { name: "slideIn"
-- |   , duration: 500
-- |   , easing: SchemaEasing.easeOutBack
-- |   , delay: 100
-- |   , iteration: Trans.Infinite
-- |   , direction: Trans.Alternate
-- |   , fillMode: Trans.FillBoth
-- |   }
-- | ```
module Hydrogen.Style.Transition
  ( -- * Transition Config
    TransitionConfig
  , transitionConfig
  , transitionStyle
  , transitionsStyle
  
  -- * Transition Properties
  , Property(..)
  , propertyToCss
  
  -- * Animation Config
  , AnimationConfig
  , animationConfig
  , animationStyle
  
  -- * Animation Values
  , Iteration(..)
  , iterationToCss
  , Direction(..)
  , directionToCss
  , FillMode(..)
  , fillModeToCss
  , PlayState(..)
  , playStateToCss
  
  -- * Transform Utilities
  , TransformConfig
  , defaultTransform
  , transformStyle
  , translate
  , translateX
  , translateY
  , rotate
  , scale
  , scaleX
  , scaleY
  , skewX
  , skewY
  
  -- * Will-Change Optimization
  , willChange
  , willChangeTransform
  , willChangeOpacity
  , willChangeScroll
  ) where

import Prelude

import Data.Array (filter, intercalate)
import Hydrogen.Schema.Motion.Easing (Easing)
import Hydrogen.Schema.Motion.Easing (toLegacyCssString) as SchemaEasing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // transition config
-- ═════════════════════════════════════════════════════════════════════════════

-- | CSS properties that can be transitioned
data Property
  = PropAll
  | PropNone
  | PropTransform
  | PropOpacity
  | PropColor
  | PropBackgroundColor
  | PropBorderColor
  | PropBoxShadow
  | PropWidth
  | PropHeight
  | PropTop
  | PropLeft
  | PropRight
  | PropBottom
  | PropMargin
  | PropPadding
  | PropCustom String

derive instance eqProperty :: Eq Property

-- | Convert property to CSS string
propertyToCss :: Property -> String
propertyToCss = case _ of
  PropAll -> "all"
  PropNone -> "none"
  PropTransform -> "transform"
  PropOpacity -> "opacity"
  PropColor -> "color"
  PropBackgroundColor -> "background-color"
  PropBorderColor -> "border-color"
  PropBoxShadow -> "box-shadow"
  PropWidth -> "width"
  PropHeight -> "height"
  PropTop -> "top"
  PropLeft -> "left"
  PropRight -> "right"
  PropBottom -> "bottom"
  PropMargin -> "margin"
  PropPadding -> "padding"
  PropCustom p -> p

-- | Configuration for a single transition
type TransitionConfig =
  { property :: Property
  , duration :: Int        -- milliseconds
  , easing :: Easing       -- Schema easing
  , delay :: Int           -- milliseconds
  }

-- | Create a default transition config
transitionConfig :: Property -> Int -> Easing -> TransitionConfig
transitionConfig prop dur eas =
  { property: prop
  , duration: dur
  , easing: eas
  , delay: 0
  }

-- | Build a CSS transition property string from config
-- |
-- | Returns: "transition: transform 300ms cubic-bezier(...) 0ms"
transitionStyle :: TransitionConfig -> String
transitionStyle cfg =
  "transition: " <> 
  propertyToCss cfg.property <> " " <>
  show cfg.duration <> "ms " <>
  SchemaEasing.toLegacyCssString cfg.easing <>
  (if cfg.delay > 0 then " " <> show cfg.delay <> "ms" else "")

-- | Build CSS for multiple transitions
-- |
-- | Returns: "transition: transform 300ms ease-out, opacity 200ms ease-in"
transitionsStyle :: Array TransitionConfig -> String
transitionsStyle configs =
  "transition: " <> intercalate ", " (map singleTransition configs)
  where
    singleTransition cfg =
      propertyToCss cfg.property <> " " <>
      show cfg.duration <> "ms " <>
      SchemaEasing.toLegacyCssString cfg.easing <>
      (if cfg.delay > 0 then " " <> show cfg.delay <> "ms" else "")

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // animation config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Animation iteration count
data Iteration
  = Once
  | Twice
  | Times Int
  | Infinite

derive instance eqIteration :: Eq Iteration

-- | Convert iteration to CSS
iterationToCss :: Iteration -> String
iterationToCss = case _ of
  Once -> "1"
  Twice -> "2"
  Times n -> show n
  Infinite -> "infinite"

-- | Animation direction
data Direction
  = Normal
  | Reverse
  | Alternate
  | AlternateReverse

derive instance eqDirection :: Eq Direction

-- | Convert direction to CSS
directionToCss :: Direction -> String
directionToCss = case _ of
  Normal -> "normal"
  Reverse -> "reverse"
  Alternate -> "alternate"
  AlternateReverse -> "alternate-reverse"

-- | Animation fill mode
data FillMode
  = FillNone
  | Forwards
  | Backwards
  | Both

derive instance eqFillMode :: Eq FillMode

-- | Convert fill mode to CSS
fillModeToCss :: FillMode -> String
fillModeToCss = case _ of
  FillNone -> "none"
  Forwards -> "forwards"
  Backwards -> "backwards"
  Both -> "both"

-- | Animation play state
data PlayState
  = Running
  | Paused

derive instance eqPlayState :: Eq PlayState

-- | Convert play state to CSS
playStateToCss :: PlayState -> String
playStateToCss = case _ of
  Running -> "running"
  Paused -> "paused"

-- | Full animation configuration
type AnimationConfig =
  { name :: String
  , duration :: Int
  , easing :: Easing
  , delay :: Int
  , iteration :: Iteration
  , direction :: Direction
  , fillMode :: FillMode
  , playState :: PlayState
  }

-- | Create a default animation config
animationConfig :: String -> Int -> Easing -> AnimationConfig
animationConfig animName dur eas =
  { name: animName
  , duration: dur
  , easing: eas
  , delay: 0
  , iteration: Once
  , direction: Normal
  , fillMode: FillNone
  , playState: Running
  }

-- | Build a CSS animation property string
-- |
-- | Returns: "animation: slideIn 500ms cubic-bezier(...) 0ms infinite alternate both running"
animationStyle :: AnimationConfig -> String
animationStyle cfg =
  "animation: " <>
  cfg.name <> " " <>
  show cfg.duration <> "ms " <>
  SchemaEasing.toLegacyCssString cfg.easing <> " " <>
  show cfg.delay <> "ms " <>
  iterationToCss cfg.iteration <> " " <>
  directionToCss cfg.direction <> " " <>
  fillModeToCss cfg.fillMode <> " " <>
  playStateToCss cfg.playState

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // transform utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Transform configuration
type TransformConfig =
  { translateX :: Number
  , translateY :: Number
  , rotate :: Number
  , scaleX :: Number
  , scaleY :: Number
  , skewX :: Number
  , skewY :: Number
  }

-- | Default transform (identity)
defaultTransform :: TransformConfig
defaultTransform =
  { translateX: 0.0
  , translateY: 0.0
  , rotate: 0.0
  , scaleX: 1.0
  , scaleY: 1.0
  , skewX: 0.0
  , skewY: 0.0
  }

-- | Build a CSS transform string
transformStyle :: TransformConfig -> String
transformStyle cfg =
  let
    parts = 
      [ if cfg.translateX /= 0.0 || cfg.translateY /= 0.0
          then "translate(" <> show cfg.translateX <> "px, " <> show cfg.translateY <> "px)"
          else ""
      , if cfg.rotate /= 0.0
          then "rotate(" <> show cfg.rotate <> "deg)"
          else ""
      , if cfg.scaleX /= 1.0 || cfg.scaleY /= 1.0
          then "scale(" <> show cfg.scaleX <> ", " <> show cfg.scaleY <> ")"
          else ""
      , if cfg.skewX /= 0.0
          then "skewX(" <> show cfg.skewX <> "deg)"
          else ""
      , if cfg.skewY /= 0.0
          then "skewY(" <> show cfg.skewY <> "deg)"
          else ""
      ]
    nonEmpty = intercalate " " $ filter (\s -> s /= "") parts
  in
    if nonEmpty == "" 
      then "transform: none" 
      else "transform: " <> nonEmpty

-- | Create translate transform
translate :: Number -> Number -> String
translate x y = "transform: translate(" <> show x <> "px, " <> show y <> "px)"

-- | Create translateX transform
translateX :: Number -> String
translateX x = "transform: translateX(" <> show x <> "px)"

-- | Create translateY transform
translateY :: Number -> String
translateY y = "transform: translateY(" <> show y <> "px)"

-- | Create rotate transform
rotate :: Number -> String
rotate deg = "transform: rotate(" <> show deg <> "deg)"

-- | Create scale transform
scale :: Number -> String
scale s = "transform: scale(" <> show s <> ")"

-- | Create scaleX transform
scaleX :: Number -> String
scaleX s = "transform: scaleX(" <> show s <> ")"

-- | Create scaleY transform
scaleY :: Number -> String
scaleY s = "transform: scaleY(" <> show s <> ")"

-- | Create skewX transform
skewX :: Number -> String
skewX deg = "transform: skewX(" <> show deg <> "deg)"

-- | Create skewY transform
skewY :: Number -> String
skewY deg = "transform: skewY(" <> show deg <> "deg)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // will-change utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Hint to browser about upcoming changes for optimization
-- |
-- | Use sparingly - only for elements that will actually animate.
willChange :: Array String -> String
willChange props = "will-change: " <> intercalate ", " props

-- | Will-change for transform animations
willChangeTransform :: String
willChangeTransform = "will-change: transform"

-- | Will-change for opacity animations
willChangeOpacity :: String
willChangeOpacity = "will-change: opacity"

-- | Will-change for scroll position
willChangeScroll :: String
willChangeScroll = "will-change: scroll-position"
