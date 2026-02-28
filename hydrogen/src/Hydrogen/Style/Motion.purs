-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                // hydrogen // style // motion
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Motion and animation style tokens
-- |
-- | This module provides type-safe tokens for CSS transitions and animations,
-- | bridging the Schema motion primitives to Tailwind CSS classes.
-- |
-- | ## Duration Tokens
-- |
-- | Duration represents how long animations/transitions take:
-- | - `Instant` (0ms) - Immediate, no transition
-- | - `Fast` (75ms) - Micro-interactions, hover states
-- | - `Quick` (150ms) - Snappy UI feedback
-- | - `Normal` (300ms) - Standard transitions
-- | - `Slow` (500ms) - Deliberate animations
-- | - `Slower` (700ms) - Complex state changes
-- | - `Slowest` (1000ms) - Page transitions, loading states
-- |
-- | ## Easing Tokens
-- |
-- | Easing defines the acceleration curve:
-- | - `Linear` - Constant speed
-- | - `EaseIn` - Start slow, end fast
-- | - `EaseOut` - Start fast, end slow
-- | - `EaseInOut` - Slow at both ends
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Style.Motion as Motion
-- | import Hydrogen.Style.LegacyCss (cx)
-- |
-- | -- Basic transition
-- | cx [ Motion.transition Motion.All
-- |    , Motion.duration Motion.Normal
-- |    , Motion.easing Motion.EaseOut
-- |    ]
-- | -- "transition-all duration-300 ease-out"
-- |
-- | -- Quick hover feedback
-- | cx [ Motion.transition Motion.Colors
-- |    , Motion.duration Motion.Quick
-- |    ]
-- | -- "transition-colors duration-150"
-- |
-- | -- Animated element
-- | cx [ Motion.animate Motion.Spin ]
-- | -- "animate-spin"
-- |
-- | -- Respect user preferences
-- | cx [ Motion.motionSafe (Motion.duration Motion.Normal)
-- |    , Motion.motionReduce (Motion.duration Motion.Instant)
-- |    ]
-- | ```
module Hydrogen.Style.Motion
  ( -- * Duration
    Duration(..)
  , duration
  , durationMs
  , durationValue
  
  -- * Easing
  , Easing(..)
  , easing
  , easingCss
  
  -- * Transition Property
  , TransitionProperty(..)
  , transition
  , transitionNone
  
  -- * Animation
  , Animation(..)
  , animate
  , animateNone
  
  -- * Delay
  , Delay(..)
  , delay
  , delayMs
  
  -- * Animation Iteration
  , Iteration(..)
  , iteration
  
  -- * Animation Direction
  , Direction(..)
  , direction
  
  -- * Animation Fill Mode
  , FillMode(..)
  , fillMode
  
  -- * Animation Play State
  , PlayState(..)
  , playState
  
  -- * Combined Utilities
  , transitionAll
  , transitionFast
  , transitionNormal
  , transitionSlow
  
  -- * Motion Accessibility
  , motionSafe
  , motionReduce
  
  -- * Schema Bridge
  , fromSchemaEasing
  ) where

import Prelude

import Hydrogen.Schema.Motion.Easing (Easing) as Schema
import Hydrogen.Schema.Motion.Easing as SchemaEasing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // duration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Duration scale for transitions and animations
-- |
-- | Semantic durations aligned with UX best practices:
-- | - Micro-interactions: Fast (75ms) to Quick (150ms)
-- | - Standard UI: Normal (300ms)
-- | - Complex animations: Slow (500ms) to Slowest (1000ms)
data Duration
  = Instant     -- 0ms - No transition
  | Fast        -- 75ms - Micro-interactions
  | Quick       -- 150ms - Snappy feedback
  | Normal      -- 300ms - Standard transitions
  | Slow        -- 500ms - Deliberate animations
  | Slower      -- 700ms - Complex transitions
  | Slowest     -- 1000ms - Page transitions
  | DurationMs Int  -- Custom duration in milliseconds

derive instance eqDuration :: Eq Duration

instance showDuration :: Show Duration where
  show = case _ of
    Instant -> "duration-0"
    Fast -> "duration-75"
    Quick -> "duration-150"
    Normal -> "duration-300"
    Slow -> "duration-500"
    Slower -> "duration-700"
    Slowest -> "duration-1000"
    DurationMs ms -> "duration-[" <> show ms <> "ms]"

-- | Convert duration to Tailwind class
duration :: Duration -> String
duration = show

-- | Create a custom duration in milliseconds
durationMs :: Int -> Duration
durationMs = DurationMs

-- | Get the numeric value in milliseconds
durationValue :: Duration -> Int
durationValue = case _ of
  Instant -> 0
  Fast -> 75
  Quick -> 150
  Normal -> 300
  Slow -> 500
  Slower -> 700
  Slowest -> 1000
  DurationMs ms -> ms

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // easing
-- ═════════════════════════════════════════════════════════════════════════════

-- | Easing functions for transitions and animations
-- |
-- | Standard easing curves that map to Tailwind's built-in classes.
-- | For custom bezier curves, use the Schema easing system.
data Easing
  = Linear      -- constant speed
  | EaseIn      -- slow start, fast end
  | EaseOut     -- fast start, slow end
  | EaseInOut   -- slow at both ends

derive instance eqEasing :: Eq Easing

instance showEasing :: Show Easing where
  show = case _ of
    Linear -> "ease-linear"
    EaseIn -> "ease-in"
    EaseOut -> "ease-out"
    EaseInOut -> "ease-in-out"

-- | Convert easing to Tailwind class
easing :: Easing -> String
easing = show

-- | Convert easing to CSS timing function value
easingCss :: Easing -> String
easingCss = case _ of
  Linear -> "linear"
  EaseIn -> "ease-in"
  EaseOut -> "ease-out"
  EaseInOut -> "ease-in-out"

-- | Bridge from Schema easing to Style easing
-- |
-- | Maps complex Schema easing curves to the closest Tailwind preset.
-- | For exact curves, use inline styles with `Schema.Easing.toLegacyCssString`.
fromSchemaEasing :: Schema.Easing -> Easing
fromSchemaEasing schemaEasing =
  -- Map to closest standard easing based on the Schema easing name
  case SchemaEasing.name schemaEasing of
    "linear" -> Linear
    "easeIn" -> EaseIn
    "easeOut" -> EaseOut
    "easeInOut" -> EaseInOut
    "easeInSine" -> EaseIn
    "easeOutSine" -> EaseOut
    "easeInOutSine" -> EaseInOut
    "easeInQuad" -> EaseIn
    "easeOutQuad" -> EaseOut
    "easeInOutQuad" -> EaseInOut
    "easeInCubic" -> EaseIn
    "easeOutCubic" -> EaseOut
    "easeInOutCubic" -> EaseInOut
    "easeInQuart" -> EaseIn
    "easeOutQuart" -> EaseOut
    "easeInOutQuart" -> EaseInOut
    "easeInQuint" -> EaseIn
    "easeOutQuint" -> EaseOut
    "easeInOutQuint" -> EaseInOut
    "easeInExpo" -> EaseIn
    "easeOutExpo" -> EaseOut
    "easeInOutExpo" -> EaseInOut
    "easeInCirc" -> EaseIn
    "easeOutCirc" -> EaseOut
    "easeInOutCirc" -> EaseInOut
    "easeInBack" -> EaseIn
    "easeOutBack" -> EaseOut
    "easeInOutBack" -> EaseInOut
    _ -> EaseInOut  -- Default for elastic, bounce, custom beziers

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // transition property
-- ═════════════════════════════════════════════════════════════════════════════

-- | Properties that can be transitioned
data TransitionProperty
  = None        -- No transition
  | All         -- All properties
  | Colors      -- Color-related properties
  | Opacity     -- Opacity only
  | Shadow      -- Box shadow
  | Transform   -- Transform properties

derive instance eqTransitionProperty :: Eq TransitionProperty

instance showTransitionProperty :: Show TransitionProperty where
  show = case _ of
    None -> "transition-none"
    All -> "transition-all"
    Colors -> "transition-colors"
    Opacity -> "transition-opacity"
    Shadow -> "transition-shadow"
    Transform -> "transition-transform"

-- | Convert transition property to Tailwind class
transition :: TransitionProperty -> String
transition = show

-- | No transition
transitionNone :: String
transitionNone = transition None

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // animation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Built-in animation presets
data Animation
  = NoAnimation   -- No animation
  | Spin          -- Continuous rotation
  | Ping          -- Radar ping effect
  | Pulse         -- Gentle opacity pulse
  | Bounce        -- Vertical bounce

derive instance eqAnimation :: Eq Animation

instance showAnimation :: Show Animation where
  show = case _ of
    NoAnimation -> "animate-none"
    Spin -> "animate-spin"
    Ping -> "animate-ping"
    Pulse -> "animate-pulse"
    Bounce -> "animate-bounce"

-- | Convert animation to Tailwind class
animate :: Animation -> String
animate = show

-- | No animation
animateNone :: String
animateNone = animate NoAnimation

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // delay
-- ═════════════════════════════════════════════════════════════════════════════

-- | Animation/transition delay
data Delay
  = NoDelay     -- 0ms
  | Delay75     -- 75ms
  | Delay100    -- 100ms
  | Delay150    -- 150ms
  | Delay200    -- 200ms
  | Delay300    -- 300ms
  | Delay500    -- 500ms
  | Delay700    -- 700ms
  | Delay1000   -- 1000ms
  | DelayMs Int -- Custom delay

derive instance eqDelay :: Eq Delay

instance showDelay :: Show Delay where
  show = case _ of
    NoDelay -> "delay-0"
    Delay75 -> "delay-75"
    Delay100 -> "delay-100"
    Delay150 -> "delay-150"
    Delay200 -> "delay-200"
    Delay300 -> "delay-300"
    Delay500 -> "delay-500"
    Delay700 -> "delay-700"
    Delay1000 -> "delay-1000"
    DelayMs ms -> "delay-[" <> show ms <> "ms]"

-- | Convert delay to Tailwind class
delay :: Delay -> String
delay = show

-- | Create a custom delay in milliseconds
delayMs :: Int -> Delay
delayMs = DelayMs

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // animation iteration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Animation iteration count
data Iteration
  = Once        -- Play once
  | Twice       -- Play twice
  | Infinite    -- Loop forever

derive instance eqIteration :: Eq Iteration

-- | Convert iteration to CSS value (for use in inline styles)
iteration :: Iteration -> String
iteration = case _ of
  Once -> "1"
  Twice -> "2"
  Infinite -> "infinite"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // animation direction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Animation direction
data Direction
  = DirectionNormal     -- Play forward
  | DirectionReverse    -- Play backward
  | DirectionAlternate  -- Alternate forward/backward
  | DirectionAlternateReverse  -- Alternate, starting backward

derive instance eqDirection :: Eq Direction

-- | Convert direction to CSS value
direction :: Direction -> String
direction = case _ of
  DirectionNormal -> "normal"
  DirectionReverse -> "reverse"
  DirectionAlternate -> "alternate"
  DirectionAlternateReverse -> "alternate-reverse"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // animation fill mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | Animation fill mode (how styles apply before/after animation)
data FillMode
  = FillNone      -- No styles applied outside animation
  | FillForwards  -- Keep final keyframe styles
  | FillBackwards -- Apply first keyframe styles during delay
  | FillBoth      -- Apply both forwards and backwards

derive instance eqFillMode :: Eq FillMode

-- | Convert fill mode to CSS value
fillMode :: FillMode -> String
fillMode = case _ of
  FillNone -> "none"
  FillForwards -> "forwards"
  FillBackwards -> "backwards"
  FillBoth -> "both"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // animation play state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Animation play state
data PlayState
  = Playing  -- Animation is running
  | Paused   -- Animation is paused

derive instance eqPlayState :: Eq PlayState

-- | Convert play state to CSS value
playState :: PlayState -> String
playState = case _ of
  Playing -> "running"
  Paused -> "paused"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // combined utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Quick transition all properties
-- |
-- | Combines: transition-all duration-300 ease-out
transitionAll :: String
transitionAll = "transition-all duration-300 ease-out"

-- | Fast transition for micro-interactions
-- |
-- | Combines: transition-all duration-75 ease-out
transitionFast :: String
transitionFast = "transition-all duration-75 ease-out"

-- | Normal transition speed
-- |
-- | Combines: transition-all duration-300 ease-in-out
transitionNormal :: String
transitionNormal = "transition-all duration-300 ease-in-out"

-- | Slow, deliberate transition
-- |
-- | Combines: transition-all duration-500 ease-in-out
transitionSlow :: String
transitionSlow = "transition-all duration-500 ease-in-out"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // motion accessibility
-- ═════════════════════════════════════════════════════════════════════════════

-- | Apply styles only when motion is safe (user hasn't requested reduced motion)
-- |
-- | ```purescript
-- | cx [ motionSafe "animate-bounce" ]
-- | -- "motion-safe:animate-bounce"
-- | ```
motionSafe :: String -> String
motionSafe cls = "motion-safe:" <> cls

-- | Apply styles when user prefers reduced motion
-- |
-- | ```purescript
-- | cx [ motionReduce "animate-none" ]
-- | -- "motion-reduce:animate-none"
-- | ```
motionReduce :: String -> String
motionReduce cls = "motion-reduce:" <> cls
