-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                           // hydrogen // motion // transition
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | CSS Transitions
-- |
-- | Type-safe transition utilities for animations.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Motion.Transition as T
-- |
-- | -- Predefined transitions
-- | T.transitionAll      -- "transition-all"
-- | T.transitionColors   -- "transition-colors"
-- |
-- | -- With duration
-- | T.duration T.D300    -- "duration-300"
-- |
-- | -- Combined
-- | T.transition T.All T.D300 T.EaseInOut
-- | -- "transition-all duration-300 ease-in-out"
-- | ```
module Hydrogen.Motion.Transition
  ( -- * Transition Classes
    transitionNone
  , transitionAll
  , transitionDefault
  , transitionColors
  , transitionOpacity
  , transitionShadow
  , transitionTransform
    -- * Duration
  , Duration(..)
  , duration
    -- * Timing Functions
  , TimingFunction(..)
  , timingFunction
    -- * Delay
  , Delay(..)
  , delay
    -- * Combined
  , transition
  , TransitionProperty(..)
    -- * Animation Classes
  , animate
  , Animation(..)
  ) where

import Prelude

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // durations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Transition duration
data Duration
  = D0
  | D75
  | D100
  | D150
  | D200
  | D300
  | D500
  | D700
  | D1000

derive instance eqDuration :: Eq Duration

-- | Convert duration to Tailwind class
duration :: Duration -> String
duration = case _ of
  D0 -> "duration-0"
  D75 -> "duration-75"
  D100 -> "duration-100"
  D150 -> "duration-150"
  D200 -> "duration-200"
  D300 -> "duration-300"
  D500 -> "duration-500"
  D700 -> "duration-700"
  D1000 -> "duration-1000"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // timing functions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Timing function (easing)
data TimingFunction
  = EaseLinear
  | EaseIn
  | EaseOut
  | EaseInOut

derive instance eqTimingFunction :: Eq TimingFunction

-- | Convert timing function to Tailwind class
timingFunction :: TimingFunction -> String
timingFunction = case _ of
  EaseLinear -> "ease-linear"
  EaseIn -> "ease-in"
  EaseOut -> "ease-out"
  EaseInOut -> "ease-in-out"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // delay
-- ═════════════════════════════════════════════════════════════════════════════

-- | Transition delay
data Delay
  = Delay0
  | Delay75
  | Delay100
  | Delay150
  | Delay200
  | Delay300
  | Delay500
  | Delay700
  | Delay1000

derive instance eqDelay :: Eq Delay

-- | Convert delay to Tailwind class
delay :: Delay -> String
delay = case _ of
  Delay0 -> "delay-0"
  Delay75 -> "delay-75"
  Delay100 -> "delay-100"
  Delay150 -> "delay-150"
  Delay200 -> "delay-200"
  Delay300 -> "delay-300"
  Delay500 -> "delay-500"
  Delay700 -> "delay-700"
  Delay1000 -> "delay-1000"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // transition properties
-- ═════════════════════════════════════════════════════════════════════════════

-- | Transition property
data TransitionProperty
  = None
  | All
  | Default
  | Colors
  | Opacity
  | Shadow
  | Transform

derive instance eqTransitionProperty :: Eq TransitionProperty

transitionProperty :: TransitionProperty -> String
transitionProperty = case _ of
  None -> "transition-none"
  All -> "transition-all"
  Default -> "transition"
  Colors -> "transition-colors"
  Opacity -> "transition-opacity"
  Shadow -> "transition-shadow"
  Transform -> "transition-transform"

-- | No transition
transitionNone :: String
transitionNone = "transition-none"

-- | Transition all properties
transitionAll :: String
transitionAll = "transition-all"

-- | Default transition (common properties)
transitionDefault :: String
transitionDefault = "transition"

-- | Transition colors only
transitionColors :: String
transitionColors = "transition-colors"

-- | Transition opacity only
transitionOpacity :: String
transitionOpacity = "transition-opacity"

-- | Transition shadow only
transitionShadow :: String
transitionShadow = "transition-shadow"

-- | Transition transform only
transitionTransform :: String
transitionTransform = "transition-transform"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // combined
-- ═════════════════════════════════════════════════════════════════════════════

-- | Combined transition class string
transition :: TransitionProperty -> Duration -> TimingFunction -> String
transition prop dur timing =
  transitionProperty prop <> " " <> duration dur <> " " <> timingFunction timing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // animation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Predefined animations
data Animation
  = AnimateNone
  | AnimateSpin
  | AnimatePing
  | AnimatePulse
  | AnimateBounce
  -- Custom animations (require @keyframes in CSS)
  | AnimateFadeIn
  | AnimateFadeOut
  | AnimateSlideIn
  | AnimateSlideOut
  | AnimateZoomIn
  | AnimateZoomOut

derive instance eqAnimation :: Eq Animation

-- | Convert animation to Tailwind class
animate :: Animation -> String
animate = case _ of
  AnimateNone -> "animate-none"
  AnimateSpin -> "animate-spin"
  AnimatePing -> "animate-ping"
  AnimatePulse -> "animate-pulse"
  AnimateBounce -> "animate-bounce"
  AnimateFadeIn -> "animate-in fade-in"
  AnimateFadeOut -> "animate-out fade-out"
  AnimateSlideIn -> "animate-in slide-in-from-bottom"
  AnimateSlideOut -> "animate-out slide-out-to-bottom"
  AnimateZoomIn -> "animate-in zoom-in"
  AnimateZoomOut -> "animate-out zoom-out"
