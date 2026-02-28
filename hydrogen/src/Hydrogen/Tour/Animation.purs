-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                              // hydrogen // tour // animation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Animation System for Product Tours
-- |
-- | This module provides the motion vocabulary for tour transitions:
-- | - Easing curves (bounded, named presets + custom cubic-bezier)
-- | - Spring physics configuration
-- | - Morph transitions (spotlight shape morphing)
-- | - Animation composition
-- |
-- | ## Design Philosophy
-- |
-- | All animations are described as pure data. The runtime interprets these
-- | descriptions to produce actual motion. This enables:
-- | - Deterministic animations (same config = same motion)
-- | - Composable animation primitives
-- | - Spring physics for natural feel
-- | - Respect for reduced motion preferences
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Tour.Animation as Anim
-- |
-- | -- Use presets
-- | tooltipAnim = Anim.fadeSlideIn Anim.Bottom Anim.springSnappy
-- |
-- | -- Custom easing
-- | customEase = Anim.cubicBezier 0.34 1.56 0.64 1.0
-- |
-- | -- Compose animations
-- | combined = Anim.sequence [fadeIn, slideIn, scaleUp]
-- | ```
module Hydrogen.Tour.Animation
  ( -- * Easing Curves
    EasingCurve(..)
  , EasingPreset(..)
  , cubicBezier
  , easingPreset
  , easingToCss
    -- * Spring Configuration
  , SpringConfig
  , springConfig
  , SpringPreset(..)
  , springPreset
  , springDefault
  , springSnappy
  , springGentle
  , springBouncy
  , springStiff
    -- * Morph Configuration
  , MorphConfig
  , defaultMorphConfig
  , morphWithSpring
  , morphWithDuration
  , MorphTarget(..)
    -- * Animation Types
  , TourAnimation(..)
  , AnimationDirection(..)
  , AnimationFill(..)
  , AnimationPlayState(..)
    -- * Animation Builders
  , fadeIn
  , fadeOut
  , slideIn
  , slideOut
  , scaleIn
  , scaleOut
  , fadeSlideIn
  , fadeSlideOut
    -- * Animation Composition
  , AnimationComposition(..)
  , sequence
  , parallel
  , stagger
  , withDelay
  , withDuration
    -- * Reduced Motion
  , ReducedMotionStrategy(..)
  , applyReducedMotion
    -- * CSS Generation
  , animationToCss
  , keyframesToCss
  ) where

import Prelude

import Data.Array (intercalate, mapWithIndex)
import Data.String (joinWith)
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(Just, Nothing))
import Data.Number (abs)
import Data.Show.Generic (genericShow)
import Hydrogen.Tour.Types (Milliseconds(Milliseconds), Pixel(Pixel), Side(Bottom, Left, Right, Top))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // easing curves
-- ═════════════════════════════════════════════════════════════════════════════

-- | Easing curve for animations
-- |
-- | Either a named preset or a custom cubic-bezier curve.
-- | All values are bounded to valid CSS ranges.
data EasingCurve
  = Preset EasingPreset
    -- ^ Named easing preset
  | CubicBezier Number Number Number Number
    -- ^ Custom cubic-bezier(x1, y1, x2, y2)
    -- | x1, x2 must be in [0, 1]
    -- | y1, y2 can exceed [0, 1] for overshoot

derive instance eqEasingCurve :: Eq EasingCurve
derive instance genericEasingCurve :: Generic EasingCurve _

instance showEasingCurve :: Show EasingCurve where
  show = genericShow

-- | Named easing presets
-- |
-- | These map to standard CSS timing functions or well-known curves.
data EasingPreset
  = EaseLinear
    -- ^ No easing (constant velocity)
  | EaseIn
    -- ^ Slow start, fast end
  | EaseOut
    -- ^ Fast start, slow end
  | EaseInOut
    -- ^ Slow start and end
  | EaseInQuad
    -- ^ Quadratic ease in
  | EaseOutQuad
    -- ^ Quadratic ease out
  | EaseInOutQuad
    -- ^ Quadratic ease in-out
  | EaseInCubic
    -- ^ Cubic ease in
  | EaseOutCubic
    -- ^ Cubic ease out
  | EaseInOutCubic
    -- ^ Cubic ease in-out
  | EaseInQuart
    -- ^ Quartic ease in
  | EaseOutQuart
    -- ^ Quartic ease out
  | EaseInOutQuart
    -- ^ Quartic ease in-out
  | EaseInExpo
    -- ^ Exponential ease in
  | EaseOutExpo
    -- ^ Exponential ease out
  | EaseInOutExpo
    -- ^ Exponential ease in-out
  | EaseInBack
    -- ^ Overshoot ease in
  | EaseOutBack
    -- ^ Overshoot ease out
  | EaseInOutBack
    -- ^ Overshoot ease in-out

derive instance eqEasingPreset :: Eq EasingPreset
derive instance ordEasingPreset :: Ord EasingPreset
derive instance genericEasingPreset :: Generic EasingPreset _

instance showEasingPreset :: Show EasingPreset where
  show = genericShow

-- | Create a custom cubic-bezier easing
-- |
-- | Clamps x values to [0, 1] range. y values can exceed for overshoot.
cubicBezier :: Number -> Number -> Number -> Number -> EasingCurve
cubicBezier x1 y1 x2 y2 = CubicBezier (clamp01 x1) y1 (clamp01 x2) y2
  where
  clamp01 :: Number -> Number
  clamp01 n
    | n < 0.0 = 0.0
    | n > 1.0 = 1.0
    | otherwise = n

-- | Create easing from preset
easingPreset :: EasingPreset -> EasingCurve
easingPreset = Preset

-- | Convert easing to CSS timing function
easingToCss :: EasingCurve -> String
easingToCss = case _ of
  Preset EaseLinear -> "linear"
  Preset EaseIn -> "ease-in"
  Preset EaseOut -> "ease-out"
  Preset EaseInOut -> "ease-in-out"
  Preset EaseInQuad -> "cubic-bezier(0.55, 0.085, 0.68, 0.53)"
  Preset EaseOutQuad -> "cubic-bezier(0.25, 0.46, 0.45, 0.94)"
  Preset EaseInOutQuad -> "cubic-bezier(0.455, 0.03, 0.515, 0.955)"
  Preset EaseInCubic -> "cubic-bezier(0.55, 0.055, 0.675, 0.19)"
  Preset EaseOutCubic -> "cubic-bezier(0.215, 0.61, 0.355, 1)"
  Preset EaseInOutCubic -> "cubic-bezier(0.645, 0.045, 0.355, 1)"
  Preset EaseInQuart -> "cubic-bezier(0.895, 0.03, 0.685, 0.22)"
  Preset EaseOutQuart -> "cubic-bezier(0.165, 0.84, 0.44, 1)"
  Preset EaseInOutQuart -> "cubic-bezier(0.77, 0, 0.175, 1)"
  Preset EaseInExpo -> "cubic-bezier(0.95, 0.05, 0.795, 0.035)"
  Preset EaseOutExpo -> "cubic-bezier(0.19, 1, 0.22, 1)"
  Preset EaseInOutExpo -> "cubic-bezier(1, 0, 0, 1)"
  Preset EaseInBack -> "cubic-bezier(0.6, -0.28, 0.735, 0.045)"
  Preset EaseOutBack -> "cubic-bezier(0.175, 0.885, 0.32, 1.275)"
  Preset EaseInOutBack -> "cubic-bezier(0.68, -0.55, 0.265, 1.55)"
  CubicBezier x1 y1 x2 y2 ->
    "cubic-bezier(" <> show x1 <> ", " <> show y1 <> ", " <> show x2 <> ", " <> show y2 <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // spring configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Spring physics configuration
-- |
-- | Based on damped harmonic oscillator:
-- | - stiffness: Spring constant (higher = faster, more force)
-- | - damping: Resistance (higher = less bouncy)
-- | - mass: Inertia (higher = slower response)
-- | - velocity: Initial velocity for momentum
type SpringConfig =
  { stiffness :: Number
    -- ^ Spring constant [1, 1000]
  , damping :: Number
    -- ^ Damping coefficient [1, 100]
  , mass :: Number
    -- ^ Mass [0.1, 10]
  , velocity :: Number
    -- ^ Initial velocity [-100, 100]
  , precision :: Number
    -- ^ Rest threshold [0.001, 0.1]
  }

-- | Create spring configuration with validation
springConfig
  :: { stiffness :: Number, damping :: Number, mass :: Number }
  -> SpringConfig
springConfig { stiffness, damping, mass } =
  { stiffness: clampRange 1.0 1000.0 stiffness
  , damping: clampRange 1.0 100.0 damping
  , mass: clampRange 0.1 10.0 mass
  , velocity: 0.0
  , precision: 0.01
  }
  where
  clampRange :: Number -> Number -> Number -> Number
  clampRange minVal maxVal val
    | val < minVal = minVal
    | val > maxVal = maxVal
    | otherwise = val

-- | Named spring presets
data SpringPreset
  = SpringDefault
    -- ^ Balanced spring (React Spring default)
  | SpringSnappy
    -- ^ Quick response, minimal bounce
  | SpringGentle
    -- ^ Smooth, slower transition
  | SpringBouncy
    -- ^ Playful bounce
  | SpringStiff
    -- ^ Immediate response

derive instance eqSpringPreset :: Eq SpringPreset
derive instance ordSpringPreset :: Ord SpringPreset
derive instance genericSpringPreset :: Generic SpringPreset _

instance showSpringPreset :: Show SpringPreset where
  show = genericShow

-- | Convert preset to spring config
springPreset :: SpringPreset -> SpringConfig
springPreset = case _ of
  SpringDefault -> springDefault
  SpringSnappy -> springSnappy
  SpringGentle -> springGentle
  SpringBouncy -> springBouncy
  SpringStiff -> springStiff

-- | Default spring (balanced)
springDefault :: SpringConfig
springDefault = springConfig { stiffness: 170.0, damping: 26.0, mass: 1.0 }

-- | Snappy spring (quick, minimal bounce)
springSnappy :: SpringConfig
springSnappy = springConfig { stiffness: 300.0, damping: 30.0, mass: 1.0 }

-- | Gentle spring (smooth, slower)
springGentle :: SpringConfig
springGentle = springConfig { stiffness: 120.0, damping: 14.0, mass: 1.0 }

-- | Bouncy spring (playful)
springBouncy :: SpringConfig
springBouncy = springConfig { stiffness: 180.0, damping: 12.0, mass: 1.0 }

-- | Stiff spring (immediate)
springStiff :: SpringConfig
springStiff = springConfig { stiffness: 400.0, damping: 40.0, mass: 1.0 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // morph configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for spotlight morph transitions
-- |
-- | Controls how the spotlight shape animates between targets.
type MorphConfig =
  { duration :: Milliseconds
    -- ^ Duration if using CSS transitions
  , spring :: Maybe SpringConfig
    -- ^ Optional spring physics (overrides duration)
  , easing :: EasingCurve
    -- ^ Easing curve (when not using spring)
  , morphPath :: Boolean
    -- ^ Whether to morph the path shape (vs. instant)
  }

-- | Default morph configuration
defaultMorphConfig :: MorphConfig
defaultMorphConfig =
  { duration: Milliseconds 300
  , spring: Just springDefault
  , easing: Preset EaseOutCubic
  , morphPath: true
  }

-- | Morph with spring physics
morphWithSpring :: SpringConfig -> MorphConfig
morphWithSpring spring = defaultMorphConfig { spring = Just spring }

-- | Morph with duration (no spring)
morphWithDuration :: Milliseconds -> EasingCurve -> MorphConfig
morphWithDuration duration easing = 
  defaultMorphConfig { spring = Nothing, duration = duration, easing = easing }

-- | Target states for morph animation
data MorphTarget
  = MorphToRect
      { x :: Pixel
      , y :: Pixel
      , width :: Pixel
      , height :: Pixel
      , borderRadius :: Pixel
      }
  | MorphToCircle
      { cx :: Pixel
      , cy :: Pixel
      , r :: Pixel
      }
  | MorphToViewport
    -- ^ Full viewport (no spotlight)
  | MorphHidden
    -- ^ Invisible state

derive instance eqMorphTarget :: Eq MorphTarget
derive instance genericMorphTarget :: Generic MorphTarget _

instance showMorphTarget :: Show MorphTarget where
  show = genericShow

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // animation types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Tour animation description
-- |
-- | Pure data describing an animation. The runtime interprets this.
data TourAnimation
  = AnimFade
      { opacity :: { from :: Number, to :: Number }
      , duration :: Milliseconds
      , easing :: EasingCurve
      }
  | AnimSlide
      { translate :: { fromX :: Pixel, fromY :: Pixel, toX :: Pixel, toY :: Pixel }
      , duration :: Milliseconds
      , easing :: EasingCurve
      }
  | AnimScale
      { scale :: { from :: Number, to :: Number }
      , transformOrigin :: String
      , duration :: Milliseconds
      , easing :: EasingCurve
      }
  | AnimSpring
      { property :: String
      , from :: Number
      , to :: Number
      , spring :: SpringConfig
      }
  | AnimComposite
      { animations :: Array TourAnimation
      , composition :: AnimationComposition
      }

derive instance eqTourAnimation :: Eq TourAnimation
derive instance genericTourAnimation :: Generic TourAnimation _

-- | Manual Show instance to handle recursive AnimComposite
instance showTourAnimation :: Show TourAnimation where
  show = case _ of
    AnimFade cfg -> 
      "(AnimFade { opacity: " <> show cfg.opacity <> 
      ", duration: " <> show cfg.duration <> 
      ", easing: " <> show cfg.easing <> " })"
    AnimSlide cfg ->
      "(AnimSlide { translate: " <> show cfg.translate <>
      ", duration: " <> show cfg.duration <>
      ", easing: " <> show cfg.easing <> " })"
    AnimScale cfg ->
      "(AnimScale { scale: " <> show cfg.scale <>
      ", transformOrigin: " <> show cfg.transformOrigin <>
      ", duration: " <> show cfg.duration <>
      ", easing: " <> show cfg.easing <> " })"
    AnimSpring cfg ->
      "(AnimSpring { property: " <> show cfg.property <>
      ", from: " <> show cfg.from <>
      ", to: " <> show cfg.to <>
      ", spring: " <> show cfg.spring <> " })"
    AnimComposite cfg ->
      "(AnimComposite { animations: [" <> 
      joinWith ", " (map show cfg.animations) <>
      "], composition: " <> show cfg.composition <> " })"

-- | Animation direction
data AnimationDirection
  = Normal
  | Reverse
  | Alternate
  | AlternateReverse

derive instance eqAnimationDirection :: Eq AnimationDirection
derive instance genericAnimationDirection :: Generic AnimationDirection _

instance showAnimationDirection :: Show AnimationDirection where
  show = genericShow

-- | Animation fill mode
data AnimationFill
  = FillNone
  | FillForwards
  | FillBackwards
  | FillBoth

derive instance eqAnimationFill :: Eq AnimationFill
derive instance genericAnimationFill :: Generic AnimationFill _

instance showAnimationFill :: Show AnimationFill where
  show = genericShow

-- | Animation play state
data AnimationPlayState
  = Playing
  | Paused

derive instance eqAnimationPlayState :: Eq AnimationPlayState
derive instance genericAnimationPlayState :: Generic AnimationPlayState _

instance showAnimationPlayState :: Show AnimationPlayState where
  show = genericShow

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // animation builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Fade in animation
fadeIn :: Milliseconds -> EasingCurve -> TourAnimation
fadeIn duration easing = AnimFade
  { opacity: { from: 0.0, to: 1.0 }
  , duration
  , easing
  }

-- | Fade out animation
fadeOut :: Milliseconds -> EasingCurve -> TourAnimation
fadeOut duration easing = AnimFade
  { opacity: { from: 1.0, to: 0.0 }
  , duration
  , easing
  }

-- | Slide in from a direction
slideIn :: Side -> Pixel -> Milliseconds -> EasingCurve -> TourAnimation
slideIn side (Pixel distance) duration easing = AnimSlide
  { translate: case side of
      Top -> { fromX: Pixel 0, fromY: Pixel (-distance), toX: Pixel 0, toY: Pixel 0 }
      Bottom -> { fromX: Pixel 0, fromY: Pixel distance, toX: Pixel 0, toY: Pixel 0 }
      Left -> { fromX: Pixel (-distance), fromY: Pixel 0, toX: Pixel 0, toY: Pixel 0 }
      Right -> { fromX: Pixel distance, fromY: Pixel 0, toX: Pixel 0, toY: Pixel 0 }
  , duration
  , easing
  }

-- | Slide out to a direction
slideOut :: Side -> Pixel -> Milliseconds -> EasingCurve -> TourAnimation
slideOut side (Pixel distance) duration easing = AnimSlide
  { translate: case side of
      Top -> { fromX: Pixel 0, fromY: Pixel 0, toX: Pixel 0, toY: Pixel (-distance) }
      Bottom -> { fromX: Pixel 0, fromY: Pixel 0, toX: Pixel 0, toY: Pixel distance }
      Left -> { fromX: Pixel 0, fromY: Pixel 0, toX: Pixel (-distance), toY: Pixel 0 }
      Right -> { fromX: Pixel 0, fromY: Pixel 0, toX: Pixel distance, toY: Pixel 0 }
  , duration
  , easing
  }

-- | Scale in animation
scaleIn :: Number -> Milliseconds -> EasingCurve -> TourAnimation
scaleIn fromScale duration easing = AnimScale
  { scale: { from: fromScale, to: 1.0 }
  , transformOrigin: "center"
  , duration
  , easing
  }

-- | Scale out animation
scaleOut :: Number -> Milliseconds -> EasingCurve -> TourAnimation
scaleOut toScale duration easing = AnimScale
  { scale: { from: 1.0, to: toScale }
  , transformOrigin: "center"
  , duration
  , easing
  }

-- | Combined fade + slide in (common tooltip entrance)
fadeSlideIn :: Side -> SpringConfig -> TourAnimation
fadeSlideIn side spring = AnimComposite
  { animations:
      [ AnimFade { opacity: { from: 0.0, to: 1.0 }, duration: Milliseconds 200, easing: Preset EaseOut }
      , AnimSpring { property: "translateY", from: slideOffset side, to: 0.0, spring }
      ]
  , composition: Parallel
  }
  where
  slideOffset :: Side -> Number
  slideOffset = case _ of
    Top -> -8.0
    Bottom -> 8.0
    Left -> 0.0
    Right -> 0.0

-- | Combined fade + slide out
fadeSlideOut :: Side -> Milliseconds -> EasingCurve -> TourAnimation
fadeSlideOut side duration easing = AnimComposite
  { animations:
      [ fadeOut duration easing
      , slideOut side (Pixel 8) duration easing
      ]
  , composition: Parallel
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // animation composition
-- ═════════════════════════════════════════════════════════════════════════════

-- | How multiple animations compose
data AnimationComposition
  = Sequence
    -- ^ Play one after another
  | Parallel
    -- ^ Play simultaneously
  | Stagger Milliseconds
    -- ^ Parallel with delay between each

derive instance eqAnimationComposition :: Eq AnimationComposition
derive instance genericAnimationComposition :: Generic AnimationComposition _

instance showAnimationComposition :: Show AnimationComposition where
  show = genericShow

-- | Sequence animations (play one after another)
sequence :: Array TourAnimation -> TourAnimation
sequence animations = AnimComposite { animations, composition: Sequence }

-- | Parallel animations (play simultaneously)
parallel :: Array TourAnimation -> TourAnimation
parallel animations = AnimComposite { animations, composition: Parallel }

-- | Stagger animations (parallel with delay between each)
stagger :: Milliseconds -> Array TourAnimation -> TourAnimation
stagger delayMs animations = AnimComposite { animations, composition: Stagger delayMs }

-- | Add delay to an animation
withDelay :: Milliseconds -> TourAnimation -> TourAnimation
withDelay (Milliseconds delayMs) anim = case anim of
  AnimFade cfg -> AnimFade cfg { duration = addDelay cfg.duration }
  AnimSlide cfg -> AnimSlide cfg { duration = addDelay cfg.duration }
  AnimScale cfg -> AnimScale cfg { duration = addDelay cfg.duration }
  AnimSpring cfg -> anim  -- Springs don't have delay built-in
  AnimComposite cfg -> AnimComposite cfg
  where
  addDelay :: Milliseconds -> Milliseconds
  addDelay (Milliseconds d) = Milliseconds (d + delayMs)

-- | Override animation duration
withDuration :: Milliseconds -> TourAnimation -> TourAnimation
withDuration duration anim = case anim of
  AnimFade cfg -> AnimFade cfg { duration = duration }
  AnimSlide cfg -> AnimSlide cfg { duration = duration }
  AnimScale cfg -> AnimScale cfg { duration = duration }
  AnimSpring _ -> anim  -- Springs don't use duration
  AnimComposite cfg -> AnimComposite cfg

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // reduced motion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Strategy for reduced motion preference
-- |
-- | Users can enable "prefers-reduced-motion" in their OS settings.
-- | We should respect this preference.
data ReducedMotionStrategy
  = InstantTransition
    -- ^ Instant state change, no animation
  | FadeOnly
    -- ^ Allow fade, but no movement
  | SlowerAnimation
    -- ^ Keep animation but make it slower
  | PreserveAnimation
    -- ^ Ignore preference (not recommended)

derive instance eqReducedMotionStrategy :: Eq ReducedMotionStrategy
derive instance genericReducedMotionStrategy :: Generic ReducedMotionStrategy _

instance showReducedMotionStrategy :: Show ReducedMotionStrategy where
  show = genericShow

-- | Apply reduced motion strategy to an animation
applyReducedMotion :: ReducedMotionStrategy -> TourAnimation -> TourAnimation
applyReducedMotion strategy anim = case strategy of
  InstantTransition -> makeInstant anim
  FadeOnly -> stripMotion anim
  SlowerAnimation -> makeSlower anim
  PreserveAnimation -> anim
  where
  makeInstant :: TourAnimation -> TourAnimation
  makeInstant = case _ of
    AnimFade cfg -> AnimFade cfg { duration = Milliseconds 0 }
    AnimSlide cfg -> AnimSlide cfg { duration = Milliseconds 0 }
    AnimScale cfg -> AnimScale cfg { duration = Milliseconds 0 }
    AnimSpring cfg -> AnimFade
      { opacity: { from: if cfg.from < cfg.to then 0.0 else 1.0
                 , to: if cfg.from < cfg.to then 1.0 else 0.0 }
      , duration: Milliseconds 0
      , easing: Preset EaseLinear
      }
    AnimComposite cfg -> AnimComposite cfg { animations = map makeInstant cfg.animations }
  
  stripMotion :: TourAnimation -> TourAnimation
  stripMotion = case _ of
    AnimFade cfg -> AnimFade cfg  -- Keep fades
    AnimSlide cfg -> AnimFade  -- Convert slides to fades
      { opacity: { from: 0.0, to: 1.0 }
      , duration: cfg.duration
      , easing: cfg.easing
      }
    AnimScale cfg -> AnimFade  -- Convert scales to fades
      { opacity: { from: 0.0, to: 1.0 }
      , duration: cfg.duration
      , easing: cfg.easing
      }
    AnimSpring cfg -> AnimFade
      { opacity: { from: 0.0, to: 1.0 }
      , duration: Milliseconds 200
      , easing: Preset EaseOut
      }
    AnimComposite cfg -> AnimComposite cfg { animations = map stripMotion cfg.animations }
  
  makeSlower :: TourAnimation -> TourAnimation
  makeSlower = case _ of
    AnimFade cfg -> AnimFade cfg { duration = multiplyDuration 2.0 cfg.duration }
    AnimSlide cfg -> AnimSlide cfg { duration = multiplyDuration 2.0 cfg.duration }
    AnimScale cfg -> AnimScale cfg { duration = multiplyDuration 2.0 cfg.duration }
    AnimSpring cfg -> AnimSpring cfg { spring = makeSpringSlower cfg.spring }
    AnimComposite cfg -> AnimComposite cfg { animations = map makeSlower cfg.animations }
  
  multiplyDuration :: Number -> Milliseconds -> Milliseconds
  multiplyDuration factor (Milliseconds ms) = Milliseconds (floor (toNumber ms * factor))
  
  makeSpringSlower :: SpringConfig -> SpringConfig
  makeSpringSlower cfg = cfg 
    { stiffness = cfg.stiffness * 0.5
    , damping = cfg.damping * 1.5
    }
  
  floor :: Number -> Int
  floor n = unsafeFloor n

foreign import unsafeFloor :: Number -> Int
foreign import toNumber :: Int -> Number

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // css generation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert animation to CSS animation property value
animationToCss :: TourAnimation -> String
animationToCss = case _ of
  AnimFade cfg ->
    "fade " <> durationToCss cfg.duration <> " " <> easingToCss cfg.easing <> " forwards"
  AnimSlide cfg ->
    "slide " <> durationToCss cfg.duration <> " " <> easingToCss cfg.easing <> " forwards"
  AnimScale cfg ->
    "scale " <> durationToCss cfg.duration <> " " <> easingToCss cfg.easing <> " forwards"
  AnimSpring _ ->
    -- Springs require JS, fallback to CSS transition
    "spring 300ms ease-out forwards"
  AnimComposite _ ->
    -- Composites need JS orchestration
    "composite 300ms ease-out forwards"
  where
  durationToCss :: Milliseconds -> String
  durationToCss (Milliseconds ms) = show ms <> "ms"

-- | Generate keyframe CSS for animations
keyframesToCss :: String -> TourAnimation -> String
keyframesToCss name anim = case anim of
  AnimFade cfg ->
    "@keyframes " <> name <> " {\n" <>
    "  from { opacity: " <> show cfg.opacity.from <> "; }\n" <>
    "  to { opacity: " <> show cfg.opacity.to <> "; }\n" <>
    "}"
  AnimSlide cfg ->
    "@keyframes " <> name <> " {\n" <>
    "  from { transform: translate(" <> pxToCss cfg.translate.fromX <> ", " <> pxToCss cfg.translate.fromY <> "); }\n" <>
    "  to { transform: translate(" <> pxToCss cfg.translate.toX <> ", " <> pxToCss cfg.translate.toY <> "); }\n" <>
    "}"
  AnimScale cfg ->
    "@keyframes " <> name <> " {\n" <>
    "  from { transform: scale(" <> show cfg.scale.from <> "); transform-origin: " <> cfg.transformOrigin <> "; }\n" <>
    "  to { transform: scale(" <> show cfg.scale.to <> "); transform-origin: " <> cfg.transformOrigin <> "; }\n" <>
    "}"
  AnimSpring _ ->
    "/* Spring animations require JavaScript runtime */"
  AnimComposite cfg ->
    intercalate "\n" (mapWithIndex (\i a -> keyframesToCss (name <> "-" <> show i) a) cfg.animations)
  where
  pxToCss :: Pixel -> String
  pxToCss (Pixel p) = show p <> "px"
