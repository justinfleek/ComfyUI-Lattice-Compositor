-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // element // tour // animation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Tour Animation — Transitions and timing for tour steps.
-- |
-- | ## Architecture
-- |
-- | Animations control how tour elements move and transition:
-- | - Tooltip entrance/exit animations
-- | - Step-to-step transitions
-- | - Highlight morphing
-- | - Scroll animations
-- |
-- | ## Schema Mapping
-- |
-- | | Type            | Pillar    | Purpose                              |
-- | |-----------------|-----------|--------------------------------------|
-- | | TransitionKind  | Temporal  | How elements animate between states  |
-- | | EasingCurve     | Temporal  | Acceleration curve for animations    |
-- | | Duration        | Temporal  | Animation duration                   |
-- | | Delay           | Temporal  | Delay before animation starts        |
-- | | EntranceKind    | Temporal  | How tooltip appears                  |
-- | | ExitKind        | Temporal  | How tooltip disappears               |

module Hydrogen.Element.Compound.Tour.Animation
  ( -- * Transition Kind
    TransitionKind
      ( TransitionNone
      , TransitionFade
      , TransitionSlide
      , TransitionZoom
      , TransitionFlip
      , TransitionMorph
      , TransitionCrossfade
      )
  
  -- * Easing Curve
  , EasingCurve
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
      , EaseInBounce
      , EaseOutBounce
      , EaseInOutBounce
      , EaseSpring
      , EaseCustom
      )
  , easingToCss
  
  -- * Entrance Kind
  , EntranceKind
      ( EnterFade
      , EnterSlideUp
      , EnterSlideDown
      , EnterSlideLeft
      , EnterSlideRight
      , EnterZoomIn
      , EnterFlipX
      , EnterFlipY
      , EnterPop
      , EnterNone
      )
  
  -- * Exit Kind
  , ExitKind
      ( ExitFade
      , ExitSlideUp
      , ExitSlideDown
      , ExitSlideLeft
      , ExitSlideRight
      , ExitZoomOut
      , ExitFlipX
      , ExitFlipY
      , ExitPop
      , ExitNone
      )
  
  -- * Duration
  , Duration
  , duration
  , unwrapDuration
  , instant
  , fast
  , normal
  , slow
  , verySlow
  
  -- * Delay
  , Delay
  , delay
  , unwrapDelay
  , noDelay
  , shortDelay
  , mediumDelay
  , longDelay
  
  -- * Spring Config
  , SpringConfig
  , springConfig
  , defaultSpring
  , bouncySpring
  , stiffSpring
  , gentleSpring
  
  -- * Animation Config
  , AnimationConfig
  , defaultAnimationConfig
  , fastAnimationConfig
  , slowAnimationConfig
  , noAnimationConfig
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Bounded
  , class Eq
  , class Ord
  , class Show
  , max
  , show
  , (<>)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // transition kind
-- ═════════════════════════════════════════════════════════════════════════════

-- | How elements transition between steps.
-- |
-- | Applied to the entire tour container when changing steps.
data TransitionKind
  = TransitionNone       -- ^ Instant change
  | TransitionFade       -- ^ Crossfade between steps
  | TransitionSlide      -- ^ Slide in direction of navigation
  | TransitionZoom       -- ^ Zoom in/out between steps
  | TransitionFlip       -- ^ 3D flip animation
  | TransitionMorph      -- ^ Morph highlight shape to new target
  | TransitionCrossfade  -- ^ Overlap old/new with crossfade

derive instance eqTransitionKind :: Eq TransitionKind
derive instance ordTransitionKind :: Ord TransitionKind

instance showTransitionKind :: Show TransitionKind where
  show TransitionNone = "none"
  show TransitionFade = "fade"
  show TransitionSlide = "slide"
  show TransitionZoom = "zoom"
  show TransitionFlip = "flip"
  show TransitionMorph = "morph"
  show TransitionCrossfade = "crossfade"

instance boundedTransitionKind :: Bounded TransitionKind where
  bottom = TransitionNone
  top = TransitionCrossfade

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // easing curve
-- ═════════════════════════════════════════════════════════════════════════════

-- | Easing curve for animations.
-- |
-- | Comprehensive set covering CSS standard easings and physics-based options.
data EasingCurve
  = EaseLinear          -- ^ No acceleration
  | EaseIn              -- ^ Accelerate from zero
  | EaseOut             -- ^ Decelerate to zero
  | EaseInOut           -- ^ Accelerate then decelerate
  | EaseInQuad          -- ^ Quadratic ease in
  | EaseOutQuad         -- ^ Quadratic ease out
  | EaseInOutQuad       -- ^ Quadratic ease in-out
  | EaseInCubic         -- ^ Cubic ease in
  | EaseOutCubic        -- ^ Cubic ease out
  | EaseInOutCubic      -- ^ Cubic ease in-out
  | EaseInQuart         -- ^ Quartic ease in
  | EaseOutQuart        -- ^ Quartic ease out
  | EaseInOutQuart      -- ^ Quartic ease in-out
  | EaseInExpo          -- ^ Exponential ease in
  | EaseOutExpo         -- ^ Exponential ease out
  | EaseInOutExpo       -- ^ Exponential ease in-out
  | EaseInBack          -- ^ Back ease in (overshoot)
  | EaseOutBack         -- ^ Back ease out (overshoot)
  | EaseInOutBack       -- ^ Back ease in-out
  | EaseInBounce        -- ^ Bounce ease in
  | EaseOutBounce       -- ^ Bounce ease out
  | EaseInOutBounce     -- ^ Bounce ease in-out
  | EaseSpring          -- ^ Physics-based spring (see SpringConfig)
  | EaseCustom String   -- ^ Custom cubic-bezier string

derive instance eqEasingCurve :: Eq EasingCurve
derive instance ordEasingCurve :: Ord EasingCurve

instance showEasingCurve :: Show EasingCurve where
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
  show EaseInBounce = "ease-in-bounce"
  show EaseOutBounce = "ease-out-bounce"
  show EaseInOutBounce = "ease-in-out-bounce"
  show EaseSpring = "spring"
  show (EaseCustom s) = "cubic-bezier(" <> s <> ")"

instance boundedEasingCurve :: Bounded EasingCurve where
  bottom = EaseLinear
  top = EaseCustom ""

-- | Convert easing to CSS timing function
easingToCss :: EasingCurve -> String
easingToCss = case _ of
  EaseLinear -> "linear"
  EaseIn -> "ease-in"
  EaseOut -> "ease-out"
  EaseInOut -> "ease-in-out"
  EaseInQuad -> "cubic-bezier(0.55, 0.085, 0.68, 0.53)"
  EaseOutQuad -> "cubic-bezier(0.25, 0.46, 0.45, 0.94)"
  EaseInOutQuad -> "cubic-bezier(0.455, 0.03, 0.515, 0.955)"
  EaseInCubic -> "cubic-bezier(0.55, 0.055, 0.675, 0.19)"
  EaseOutCubic -> "cubic-bezier(0.215, 0.61, 0.355, 1)"
  EaseInOutCubic -> "cubic-bezier(0.645, 0.045, 0.355, 1)"
  EaseInQuart -> "cubic-bezier(0.895, 0.03, 0.685, 0.22)"
  EaseOutQuart -> "cubic-bezier(0.165, 0.84, 0.44, 1)"
  EaseInOutQuart -> "cubic-bezier(0.77, 0, 0.175, 1)"
  EaseInExpo -> "cubic-bezier(0.95, 0.05, 0.795, 0.035)"
  EaseOutExpo -> "cubic-bezier(0.19, 1, 0.22, 1)"
  EaseInOutExpo -> "cubic-bezier(1, 0, 0, 1)"
  EaseInBack -> "cubic-bezier(0.6, -0.28, 0.735, 0.045)"
  EaseOutBack -> "cubic-bezier(0.175, 0.885, 0.32, 1.275)"
  EaseInOutBack -> "cubic-bezier(0.68, -0.55, 0.265, 1.55)"
  EaseInBounce -> "cubic-bezier(0.6, -0.28, 0.735, 0.045)"
  EaseOutBounce -> "cubic-bezier(0.175, 0.885, 0.32, 1.275)"
  EaseInOutBounce -> "cubic-bezier(0.68, -0.55, 0.265, 1.55)"
  EaseSpring -> "cubic-bezier(0.5, 1.5, 0.5, 1)"
  EaseCustom s -> "cubic-bezier(" <> s <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // entrance kind
-- ═════════════════════════════════════════════════════════════════════════════

-- | How tooltip enters the view.
data EntranceKind
  = EnterFade        -- ^ Fade in
  | EnterSlideUp     -- ^ Slide from below
  | EnterSlideDown   -- ^ Slide from above
  | EnterSlideLeft   -- ^ Slide from right
  | EnterSlideRight  -- ^ Slide from left
  | EnterZoomIn      -- ^ Scale up from small
  | EnterFlipX       -- ^ Flip on horizontal axis
  | EnterFlipY       -- ^ Flip on vertical axis
  | EnterPop         -- ^ Pop in with overshoot
  | EnterNone        -- ^ Instant appearance

derive instance eqEntranceKind :: Eq EntranceKind
derive instance ordEntranceKind :: Ord EntranceKind

instance showEntranceKind :: Show EntranceKind where
  show EnterFade = "fade"
  show EnterSlideUp = "slide-up"
  show EnterSlideDown = "slide-down"
  show EnterSlideLeft = "slide-left"
  show EnterSlideRight = "slide-right"
  show EnterZoomIn = "zoom-in"
  show EnterFlipX = "flip-x"
  show EnterFlipY = "flip-y"
  show EnterPop = "pop"
  show EnterNone = "none"

instance boundedEntranceKind :: Bounded EntranceKind where
  bottom = EnterFade
  top = EnterNone

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // exit kind
-- ═════════════════════════════════════════════════════════════════════════════

-- | How tooltip exits the view.
data ExitKind
  = ExitFade        -- ^ Fade out
  | ExitSlideUp     -- ^ Slide upward
  | ExitSlideDown   -- ^ Slide downward
  | ExitSlideLeft   -- ^ Slide to left
  | ExitSlideRight  -- ^ Slide to right
  | ExitZoomOut     -- ^ Scale down to nothing
  | ExitFlipX       -- ^ Flip on horizontal axis
  | ExitFlipY       -- ^ Flip on vertical axis
  | ExitPop         -- ^ Pop out with undershoot
  | ExitNone        -- ^ Instant disappearance

derive instance eqExitKind :: Eq ExitKind
derive instance ordExitKind :: Ord ExitKind

instance showExitKind :: Show ExitKind where
  show ExitFade = "fade"
  show ExitSlideUp = "slide-up"
  show ExitSlideDown = "slide-down"
  show ExitSlideLeft = "slide-left"
  show ExitSlideRight = "slide-right"
  show ExitZoomOut = "zoom-out"
  show ExitFlipX = "flip-x"
  show ExitFlipY = "flip-y"
  show ExitPop = "pop"
  show ExitNone = "none"

instance boundedExitKind :: Bounded ExitKind where
  bottom = ExitFade
  top = ExitNone

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // duration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Animation duration in milliseconds.
newtype Duration = Duration Int

derive instance eqDuration :: Eq Duration
derive instance ordDuration :: Ord Duration

instance showDuration :: Show Duration where
  show (Duration ms) = "Duration(" <> show ms <> "ms)"

-- | Create a duration (clamped to non-negative)
duration :: Int -> Duration
duration ms = Duration (max 0 ms)

-- | Extract duration in milliseconds
unwrapDuration :: Duration -> Int
unwrapDuration (Duration ms) = ms

-- | Instant (0ms)
instant :: Duration
instant = Duration 0

-- | Fast (150ms)
fast :: Duration
fast = Duration 150

-- | Normal (300ms)
normal :: Duration
normal = Duration 300

-- | Slow (500ms)
slow :: Duration
slow = Duration 500

-- | Very slow (800ms)
verySlow :: Duration
verySlow = Duration 800

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // delay
-- ═════════════════════════════════════════════════════════════════════════════

-- | Animation delay in milliseconds.
newtype Delay = Delay Int

derive instance eqDelay :: Eq Delay
derive instance ordDelay :: Ord Delay

instance showDelay :: Show Delay where
  show (Delay ms) = "Delay(" <> show ms <> "ms)"

-- | Create a delay (clamped to non-negative)
delay :: Int -> Delay
delay ms = Delay (max 0 ms)

-- | Extract delay in milliseconds
unwrapDelay :: Delay -> Int
unwrapDelay (Delay ms) = ms

-- | No delay (0ms)
noDelay :: Delay
noDelay = Delay 0

-- | Short delay (100ms)
shortDelay :: Delay
shortDelay = Delay 100

-- | Medium delay (300ms)
mediumDelay :: Delay
mediumDelay = Delay 300

-- | Long delay (500ms)
longDelay :: Delay
longDelay = Delay 500

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // spring config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Physics-based spring animation configuration.
-- |
-- | Based on Framer Motion's spring parameters.
type SpringConfig =
  { stiffness :: Number   -- ^ Spring stiffness (default: 100)
  , damping :: Number     -- ^ Damping ratio (default: 10)
  , mass :: Number        -- ^ Mass (default: 1)
  , velocity :: Number    -- ^ Initial velocity (default: 0)
  }

-- | Create a spring configuration
springConfig :: Number -> Number -> Number -> SpringConfig
springConfig stiff damp m =
  { stiffness: max 0.0 stiff
  , damping: max 0.0 damp
  , mass: max 0.1 m
  , velocity: 0.0
  }

-- | Default spring (balanced)
defaultSpring :: SpringConfig
defaultSpring = springConfig 100.0 10.0 1.0

-- | Bouncy spring (more oscillation)
bouncySpring :: SpringConfig
bouncySpring = springConfig 200.0 5.0 1.0

-- | Stiff spring (quick, less oscillation)
stiffSpring :: SpringConfig
stiffSpring = springConfig 400.0 30.0 1.0

-- | Gentle spring (slow, smooth)
gentleSpring :: SpringConfig
gentleSpring = springConfig 50.0 15.0 1.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // animation config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete animation configuration for tour.
type AnimationConfig =
  { stepTransition :: TransitionKind    -- ^ Transition between steps
  , easing :: EasingCurve               -- ^ Default easing curve
  , duration :: Duration                -- ^ Default animation duration
  , entrance :: EntranceKind            -- ^ Tooltip entrance animation
  , exit :: ExitKind                    -- ^ Tooltip exit animation
  , entranceDelay :: Delay              -- ^ Delay before entrance
  , exitDelay :: Delay                  -- ^ Delay before exit
  , spring :: SpringConfig              -- ^ Spring config for spring easing
  , reduceMotion :: Boolean             -- ^ Respect prefers-reduced-motion
  , highlightMorph :: Boolean           -- ^ Morph highlight between targets
  }

-- | Default animation configuration
defaultAnimationConfig :: AnimationConfig
defaultAnimationConfig =
  { stepTransition: TransitionFade
  , easing: EaseOutCubic
  , duration: normal
  , entrance: EnterFade
  , exit: ExitFade
  , entranceDelay: noDelay
  , exitDelay: noDelay
  , spring: defaultSpring
  , reduceMotion: true
  , highlightMorph: true
  }

-- | Fast animation configuration
fastAnimationConfig :: AnimationConfig
fastAnimationConfig = defaultAnimationConfig
  { duration = fast
  , entrance = EnterPop
  , exit = ExitFade
  , easing = EaseOutBack
  }

-- | Slow animation configuration
slowAnimationConfig :: AnimationConfig
slowAnimationConfig = defaultAnimationConfig
  { duration = slow
  , entrance = EnterSlideUp
  , exit = ExitSlideDown
  , easing = EaseInOutCubic
  }

-- | No animation configuration
noAnimationConfig :: AnimationConfig
noAnimationConfig = defaultAnimationConfig
  { stepTransition = TransitionNone
  , duration = instant
  , entrance = EnterNone
  , exit = ExitNone
  , highlightMorph = false
  }
