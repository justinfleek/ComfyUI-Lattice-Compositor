-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // element // carousel // transitions
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Carousel Transitions — Transition timing and easing configurations.
-- |
-- | ## Design Philosophy
-- |
-- | Transitions are pure data describing animation parameters.
-- | The runtime interprets these to produce CSS transitions or JS animations.
-- | No imperative animation code here — just declarative configuration.
-- |
-- | ## Dependencies
-- |
-- | - Carousel.Types (TransitionKind)
-- | - Schema.Dimension.Temporal (Milliseconds for duration)

module Hydrogen.Element.Compound.Carousel.Transitions
  ( -- * Easing Functions
    EasingFunction
      ( EaseLinear
      , EaseIn
      , EaseOut
      , EaseInOut
      , EaseInQuad
      , EaseOutQuad
      , EaseInOutQuad
      , EaseInCubic
      , EaseOutCubic
      , EaseInOutCubic
      , EaseInQuart
      , EaseOutQuart
      , EaseInOutQuart
      , EaseInExpo
      , EaseOutExpo
      , EaseInOutExpo
      , EaseInBack
      , EaseOutBack
      , EaseInOutBack
      , EaseSpring
      , EaseBounce
      , EaseCustom
      )
  , easingToCss
  
  -- * Transition Config
  , TransitionConfig
  , transitionConfig
  , defaultTransition
  , instantTransition
  , slowTransition
  
  -- * Preset Transitions
  , fadeTransition
  , slideTransition
  , slideVerticalTransition
  , zoomTransition
  , flipTransition
  , flipVerticalTransition
  , cubeTransition
  , coverflowTransition
  , cardsTransition
  , wheelTransition
  , spiralTransition
  , parallaxTransition
  , morphTransition
  , dissolveTransition
  , blurTransition
  , wipeTransition
  , revealTransition
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  )

import Hydrogen.Element.Compound.Carousel.Types 
  ( TransitionKind
      ( TransitionNone
      , TransitionSlide
      , TransitionSlideVertical
      , TransitionFade
      , TransitionZoom
      , TransitionFlip
      , TransitionFlipVertical
      , TransitionCube
      , TransitionCoverflow
      , TransitionCards
      , TransitionWheel
      , TransitionSpiral
      , TransitionParallax
      , TransitionMorph
      , TransitionDissolve
      , TransitionBlur
      , TransitionWipe
      , TransitionReveal
      )
  )
import Hydrogen.Schema.Dimension.Temporal as Temporal

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // easing functions
-- ═════════════════════════════════════════════════════════════════════════════

-- | CSS easing functions for transitions
-- |
-- | Standard CSS timing functions plus common cubic-bezier presets.
data EasingFunction
  = EaseLinear           -- ^ Constant speed
  | EaseIn               -- ^ Slow start
  | EaseOut              -- ^ Slow end
  | EaseInOut            -- ^ Slow start and end
  | EaseInQuad           -- ^ Quadratic ease in
  | EaseOutQuad          -- ^ Quadratic ease out
  | EaseInOutQuad        -- ^ Quadratic ease in/out
  | EaseInCubic          -- ^ Cubic ease in
  | EaseOutCubic         -- ^ Cubic ease out
  | EaseInOutCubic       -- ^ Cubic ease in/out
  | EaseInQuart          -- ^ Quartic ease in
  | EaseOutQuart         -- ^ Quartic ease out
  | EaseInOutQuart       -- ^ Quartic ease in/out
  | EaseInExpo           -- ^ Exponential ease in
  | EaseOutExpo          -- ^ Exponential ease out
  | EaseInOutExpo        -- ^ Exponential ease in/out
  | EaseInBack           -- ^ Overshoot ease in
  | EaseOutBack          -- ^ Overshoot ease out
  | EaseInOutBack        -- ^ Overshoot ease in/out
  | EaseSpring           -- ^ Spring physics
  | EaseBounce           -- ^ Bounce effect
  | EaseCustom Number Number Number Number  -- ^ Custom cubic-bezier(x1,y1,x2,y2)

derive instance eqEasingFunction :: Eq EasingFunction

instance showEasingFunction :: Show EasingFunction where
  show EaseLinear = "linear"
  show EaseIn = "ease-in"
  show EaseOut = "ease-out"
  show EaseInOut = "ease-in-out"
  show EaseInQuad = "ease-in-quad"
  show EaseOutQuad = "ease-out-quad"
  show EaseInOutQuad = "ease-in-out-quad"
  show EaseInCubic = "ease-in-cubic"
  show EaseOutCubic = "ease-out-cubic"
  show EaseInOutCubic = "ease-in-out-cubic"
  show EaseInQuart = "ease-in-quart"
  show EaseOutQuart = "ease-out-quart"
  show EaseInOutQuart = "ease-in-out-quart"
  show EaseInExpo = "ease-in-expo"
  show EaseOutExpo = "ease-out-expo"
  show EaseInOutExpo = "ease-in-out-expo"
  show EaseInBack = "ease-in-back"
  show EaseOutBack = "ease-out-back"
  show EaseInOutBack = "ease-in-out-back"
  show EaseSpring = "spring"
  show EaseBounce = "bounce"
  show (EaseCustom x1 y1 x2 y2) = 
    "cubic-bezier(" <> show x1 <> "," <> show y1 <> "," <> show x2 <> "," <> show y2 <> ")"

-- | Convert easing function to CSS timing-function value
easingToCss :: EasingFunction -> String
easingToCss EaseLinear = "linear"
easingToCss EaseIn = "ease-in"
easingToCss EaseOut = "ease-out"
easingToCss EaseInOut = "ease-in-out"
easingToCss EaseInQuad = "cubic-bezier(0.55, 0.085, 0.68, 0.53)"
easingToCss EaseOutQuad = "cubic-bezier(0.25, 0.46, 0.45, 0.94)"
easingToCss EaseInOutQuad = "cubic-bezier(0.455, 0.03, 0.515, 0.955)"
easingToCss EaseInCubic = "cubic-bezier(0.55, 0.055, 0.675, 0.19)"
easingToCss EaseOutCubic = "cubic-bezier(0.215, 0.61, 0.355, 1)"
easingToCss EaseInOutCubic = "cubic-bezier(0.645, 0.045, 0.355, 1)"
easingToCss EaseInQuart = "cubic-bezier(0.895, 0.03, 0.685, 0.22)"
easingToCss EaseOutQuart = "cubic-bezier(0.165, 0.84, 0.44, 1)"
easingToCss EaseInOutQuart = "cubic-bezier(0.77, 0, 0.175, 1)"
easingToCss EaseInExpo = "cubic-bezier(0.95, 0.05, 0.795, 0.035)"
easingToCss EaseOutExpo = "cubic-bezier(0.19, 1, 0.22, 1)"
easingToCss EaseInOutExpo = "cubic-bezier(1, 0, 0, 1)"
easingToCss EaseInBack = "cubic-bezier(0.6, -0.28, 0.735, 0.045)"
easingToCss EaseOutBack = "cubic-bezier(0.175, 0.885, 0.32, 1.275)"
easingToCss EaseInOutBack = "cubic-bezier(0.68, -0.55, 0.265, 1.55)"
easingToCss EaseSpring = "cubic-bezier(0.5, 1.5, 0.5, 1)"
easingToCss EaseBounce = "cubic-bezier(0.68, -0.55, 0.265, 1.55)"
easingToCss (EaseCustom x1 y1 x2 y2) = 
  "cubic-bezier(" <> show x1 <> ", " <> show y1 <> ", " <> show x2 <> ", " <> show y2 <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // transition config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for a slide transition
-- |
-- | Combines transition type, duration, and easing into a single config.
type TransitionConfig =
  { kind :: TransitionKind
  , duration :: Temporal.Milliseconds
  , easing :: EasingFunction
  , delay :: Temporal.Milliseconds
  }

-- | Create a transition config
transitionConfig :: TransitionKind -> Temporal.Milliseconds -> EasingFunction -> TransitionConfig
transitionConfig kind duration easing =
  { kind
  , duration
  , easing
  , delay: Temporal.milliseconds 0.0
  }

-- | Default transition (slide, 300ms, ease-out)
defaultTransition :: TransitionConfig
defaultTransition = transitionConfig 
  TransitionSlide 
  (Temporal.milliseconds 300.0) 
  EaseOut

-- | Instant transition (no animation)
instantTransition :: TransitionConfig
instantTransition = transitionConfig 
  TransitionNone 
  (Temporal.milliseconds 0.0) 
  EaseLinear

-- | Slow transition (500ms)
slowTransition :: TransitionConfig
slowTransition = transitionConfig 
  TransitionSlide 
  (Temporal.milliseconds 500.0) 
  EaseInOutCubic

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // preset transitions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Fade/crossfade transition
fadeTransition :: TransitionConfig
fadeTransition = transitionConfig 
  TransitionFade 
  (Temporal.milliseconds 400.0) 
  EaseInOut

-- | Horizontal slide transition
slideTransition :: TransitionConfig
slideTransition = transitionConfig 
  TransitionSlide 
  (Temporal.milliseconds 300.0) 
  EaseOutCubic

-- | Zoom in/out transition
zoomTransition :: TransitionConfig
zoomTransition = transitionConfig 
  TransitionZoom 
  (Temporal.milliseconds 350.0) 
  EaseOutBack

-- | 3D flip transition
flipTransition :: TransitionConfig
flipTransition = transitionConfig 
  TransitionFlip 
  (Temporal.milliseconds 600.0) 
  EaseInOutQuart

-- | 3D cube rotation transition
cubeTransition :: TransitionConfig
cubeTransition = transitionConfig 
  TransitionCube 
  (Temporal.milliseconds 700.0) 
  EaseInOutCubic

-- | iTunes-style coverflow transition
coverflowTransition :: TransitionConfig
coverflowTransition = transitionConfig 
  TransitionCoverflow 
  (Temporal.milliseconds 400.0) 
  EaseOutQuart

-- | Vertical slide transition
slideVerticalTransition :: TransitionConfig
slideVerticalTransition = transitionConfig 
  TransitionSlideVertical 
  (Temporal.milliseconds 300.0) 
  EaseOutCubic

-- | Vertical 3D flip transition
flipVerticalTransition :: TransitionConfig
flipVerticalTransition = transitionConfig 
  TransitionFlipVertical 
  (Temporal.milliseconds 600.0) 
  EaseInOutQuart

-- | Card stack transition
cardsTransition :: TransitionConfig
cardsTransition = transitionConfig 
  TransitionCards 
  (Temporal.milliseconds 450.0) 
  EaseOutBack

-- | Spinning wheel transition
wheelTransition :: TransitionConfig
wheelTransition = transitionConfig 
  TransitionWheel 
  (Temporal.milliseconds 800.0) 
  EaseInOutCubic

-- | Spiral inward/outward transition
spiralTransition :: TransitionConfig
spiralTransition = transitionConfig 
  TransitionSpiral 
  (Temporal.milliseconds 700.0) 
  EaseInOutQuart

-- | Parallax scrolling transition
parallaxTransition :: TransitionConfig
parallaxTransition = transitionConfig 
  TransitionParallax 
  (Temporal.milliseconds 350.0) 
  EaseOutCubic

-- | Shape-morphing transition
morphTransition :: TransitionConfig
morphTransition = transitionConfig 
  TransitionMorph 
  (Temporal.milliseconds 500.0) 
  EaseInOutCubic

-- | Pixel dissolve transition
dissolveTransition :: TransitionConfig
dissolveTransition = transitionConfig 
  TransitionDissolve 
  (Temporal.milliseconds 450.0) 
  EaseLinear

-- | Blur in/out transition
blurTransition :: TransitionConfig
blurTransition = transitionConfig 
  TransitionBlur 
  (Temporal.milliseconds 400.0) 
  EaseInOut

-- | Wipe across transition
wipeTransition :: TransitionConfig
wipeTransition = transitionConfig 
  TransitionWipe 
  (Temporal.milliseconds 350.0) 
  EaseOutQuad

-- | Reveal from edge transition
revealTransition :: TransitionConfig
revealTransition = transitionConfig 
  TransitionReveal 
  (Temporal.milliseconds 400.0) 
  EaseOutCubic
