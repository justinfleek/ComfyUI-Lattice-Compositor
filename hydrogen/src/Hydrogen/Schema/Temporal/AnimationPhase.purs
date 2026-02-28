-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // schema // temporal // animation-phase
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | AnimationPhase — Bounded normalized animation time (0.0-1.0).
-- |
-- | Represents the progress through an animation curve:
-- | - **0.0**: Animation start
-- | - **0.5**: Animation midpoint
-- | - **1.0**: Animation complete
-- |
-- | This is the fundamental atom for animation state. Combined with easing
-- | functions, it drives all temporal interpolation in the rendering pipeline.
-- |
-- | ## Design Philosophy
-- |
-- | The phase is always normalized [0.0, 1.0] regardless of actual duration.
-- | This decouples animation logic from wall-clock time, enabling:
-- | - Deterministic replay at any speed
-- | - Reversible animations (phase can decrease)
-- | - Loop detection (phase wraps at 1.0)
-- | - Scrubbing (set phase directly for preview)

module Hydrogen.Schema.Temporal.AnimationPhase
  ( AnimationPhase
  , animationPhase
  , unsafeAnimationPhase
  , unwrap
  , toNumber
  , fromNumber
  , advance
  , reverse
  , wrap
  , clamp
  , isComplete
  , isStarted
  , blend
  , bounds
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (+)
  , (-)
  , (*)
  , (<)
  , (>)
  , (>=)
  , (<>)
  )

import Data.Int (floor) as Int
import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // animation phase
-- ═════════════════════════════════════════════════════════════════════════════

-- | Normalized animation phase (0.0-1.0)
-- |
-- | Represents progress through an animation. 0.0 is the start, 1.0 is complete.
-- | Bounded by construction — invalid phases cannot exist.
newtype AnimationPhase = AnimationPhase Number

derive instance eqAnimationPhase :: Eq AnimationPhase
derive instance ordAnimationPhase :: Ord AnimationPhase

instance showAnimationPhase :: Show AnimationPhase where
  show (AnimationPhase p) = "phase(" <> show p <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create an AnimationPhase, clamping to valid range [0.0, 1.0]
-- |
-- | Values outside the range are clamped:
-- | ```purescript
-- | animationPhase 0.5   -- AnimationPhase 0.5
-- | animationPhase 1.5   -- AnimationPhase 1.0 (clamped)
-- | animationPhase (-0.2) -- AnimationPhase 0.0 (clamped)
-- | ```
animationPhase :: Number -> AnimationPhase
animationPhase n = AnimationPhase (Bounded.clampNumber 0.0 1.0 n)

-- | Create an AnimationPhase without clamping
-- |
-- | Use only when you know the value is valid [0.0, 1.0].
-- | Invalid values will break invariants.
unsafeAnimationPhase :: Number -> AnimationPhase
unsafeAnimationPhase = AnimationPhase

-- | Create phase from Number (alias for animationPhase)
fromNumber :: Number -> AnimationPhase
fromNumber = animationPhase

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Advance the phase by a delta, clamping to [0.0, 1.0]
-- |
-- | For forward-playing animations:
-- | ```purescript
-- | advance 0.1 (animationPhase 0.5)  -- AnimationPhase 0.6
-- | advance 0.3 (animationPhase 0.9)  -- AnimationPhase 1.0 (clamped)
-- | ```
advance :: Number -> AnimationPhase -> AnimationPhase
advance delta (AnimationPhase p) = animationPhase (p + delta)

-- | Reverse the phase by a delta (move backward), clamping to [0.0, 1.0]
-- |
-- | For reverse-playing animations:
-- | ```purescript
-- | reverse 0.1 (animationPhase 0.5)  -- AnimationPhase 0.4
-- | reverse 0.3 (animationPhase 0.1)  -- AnimationPhase 0.0 (clamped)
-- | ```
reverse :: Number -> AnimationPhase -> AnimationPhase
reverse delta (AnimationPhase p) = animationPhase (p - delta)

-- | Wrap the phase at boundaries (for looping animations)
-- |
-- | When phase exceeds 1.0, wrap to 0.0 and continue:
-- | ```purescript
-- | wrap (animationPhase 0.5)  -- AnimationPhase 0.5
-- | wrap (animationPhase 1.2)  -- AnimationPhase 0.2 (wrapped)
-- | wrap (animationPhase 2.5)  -- AnimationPhase 0.5 (wrapped)
-- | wrap (animationPhase (-0.3))  -- AnimationPhase 0.7 (wrapped)
-- | ```
wrap :: AnimationPhase -> AnimationPhase
wrap (AnimationPhase p) =
  let 
    fractional = p - intPartAsNumber (Int.floor p)
    wrapped = if fractional < 0.0 then fractional + 1.0 else fractional
  in AnimationPhase (Bounded.clampNumber 0.0 1.0 wrapped)
  where
    intPartAsNumber :: Int -> Number
    intPartAsNumber n = case n of
      _ | n < 0 -> 0.0 - intPartPositive (0 - n)
      _ -> intPartPositive n
      where
        intPartPositive :: Int -> Number
        intPartPositive 0 = 0.0
        intPartPositive i = 1.0 + intPartPositive (i - 1)

-- | Clamp the phase to [0.0, 1.0] (explicit clamp operation)
-- |
-- | Useful when composing with operations that might exceed bounds:
-- | ```purescript
-- | clamp (unsafeAnimationPhase 1.5)  -- AnimationPhase 1.0
-- | ```
clamp :: AnimationPhase -> AnimationPhase
clamp (AnimationPhase p) = animationPhase p

-- | Blend two animation phases with weight
-- |
-- | Linear interpolation between phases:
-- | ```purescript
-- | blend 0.0 (animationPhase 0.2) (animationPhase 0.8)  -- AnimationPhase 0.2
-- | blend 0.5 (animationPhase 0.2) (animationPhase 0.8)  -- AnimationPhase 0.5
-- | blend 1.0 (animationPhase 0.2) (animationPhase 0.8)  -- AnimationPhase 0.8
-- | ```
blend :: Number -> AnimationPhase -> AnimationPhase -> AnimationPhase
blend weight (AnimationPhase a) (AnimationPhase b) =
  let w = Bounded.clampNumber 0.0 1.0 weight
      result = a * (1.0 - w) + b * w
  in animationPhase result

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if animation is complete (phase >= 1.0)
-- |
-- | Useful for cleanup and state transitions:
-- | ```purescript
-- | isComplete (animationPhase 1.0)   -- true
-- | isComplete (animationPhase 0.99)  -- false
-- | ```
isComplete :: AnimationPhase -> Boolean
isComplete (AnimationPhase p) = p >= 1.0

-- | Check if animation has started (phase > 0.0)
-- |
-- | Useful for detecting animation activation:
-- | ```purescript
-- | isStarted (animationPhase 0.0)    -- false
-- | isStarted (animationPhase 0.01)   -- true
-- | ```
isStarted :: AnimationPhase -> Boolean
isStarted (AnimationPhase p) = p > 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Number value [0.0, 1.0]
unwrap :: AnimationPhase -> Number
unwrap (AnimationPhase p) = p

-- | Convert to Number (alias for unwrap)
toNumber :: AnimationPhase -> Number
toNumber = unwrap

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // metadata
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds documentation for this type
bounds :: Bounded.NumberBounds
bounds = Bounded.numberBounds 0.0 1.0 "animationPhase" 
  "Normalized animation progress from 0.0 (start) to 1.0 (complete)"
