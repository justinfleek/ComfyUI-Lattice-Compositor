-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                    // hydrogen // schema // temporal // animation-composition
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Animation composition primitives.
-- |
-- | ## Sequence
-- | Animations play one after another.
-- |
-- | ## Parallel
-- | Animations play simultaneously.
-- |
-- | ## Stagger
-- | Animations play with incremental delays.

module Hydrogen.Schema.Temporal.AnimationComposition
  ( -- * Animation Reference
    AnimationRef
  , animationRef
  , animationRefId
  , animationRefDuration
  , showAnimationRef
  
  -- * Sequence
  , Sequence
  , sequence
  , sequenceAnimations
  , sequenceTotalDuration
  , sequenceDelayBetween
  , showSequence
  
  -- * Parallel
  , Parallel
  , parallel
  , parallelAnimations
  , parallelDuration
  , showParallel
  
  -- * Stagger
  , Stagger
  , stagger
  , staggerAnimations
  , staggerDelay
  , staggerTotalDuration
  , staggerFromEnd
  , showStagger
  
  -- * Fill Mode
  , FillMode(..)
  , fillModeLabel
  
  -- * Transition
  , Transition
  , transition
  , transitionProperty
  , transitionDuration
  , transitionEasing
  , transitionDelay
  , showTransition
  
  -- * Animation Group
  , AnimationGroup(..)
  , groupDuration
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  , (+)
  , (*)
  , (-)
  , (>)
  , max
  )

import Data.Int (toNumber)
import Data.Array (length)
import Data.Foldable (foldl)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // animation ref
-- ═════════════════════════════════════════════════════════════════════════════

-- | AnimationRef - reference to an animation with its duration.
type AnimationRef =
  { id :: String
  , durationMs :: Number
  }

-- | Construct an animation reference.
animationRef :: String -> Number -> AnimationRef
animationRef id dur =
  { id: id
  , durationMs: max 0.0 dur
  }

-- | Get animation ID.
animationRefId :: AnimationRef -> String
animationRefId a = a.id

-- | Get animation duration.
animationRefDuration :: AnimationRef -> Number
animationRefDuration a = a.durationMs

-- | Show animation reference for debug output.
showAnimationRef :: AnimationRef -> String
showAnimationRef a = "(AnimationRef " <> a.id <> " " <> show a.durationMs <> "ms)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // sequence
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sequence - animations that play one after another.
type Sequence =
  { animations :: Array AnimationRef
  , delayBetween :: Number    -- Delay between each animation
  }

-- | Construct a sequence.
sequence :: Array AnimationRef -> Number -> Sequence
sequence anims delay =
  { animations: anims
  , delayBetween: max 0.0 delay
  }

-- | Get animations in sequence.
sequenceAnimations :: Sequence -> Array AnimationRef
sequenceAnimations s = s.animations

-- | Get delay between animations.
sequenceDelayBetween :: Sequence -> Number
sequenceDelayBetween s = s.delayBetween

-- | Calculate total duration of sequence.
sequenceTotalDuration :: Sequence -> Number
sequenceTotalDuration s =
  let animDurations = foldl (\acc a -> acc + a.durationMs) 0.0 s.animations
      n = length s.animations
      delays = if n > 1 then s.delayBetween * intToNumber (n - 1) else 0.0
  in animDurations + delays

-- | Show sequence for debug output.
showSequence :: Sequence -> String
showSequence s =
  "(Sequence " <> show (length s.animations) <> " anims, " <>
  show s.delayBetween <> "ms delay, total=" <> show (sequenceTotalDuration s) <> "ms)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // parallel
-- ═════════════════════════════════════════════════════════════════════════════

-- | Parallel - animations that play simultaneously.
type Parallel =
  { animations :: Array AnimationRef
  }

-- | Construct a parallel group.
parallel :: Array AnimationRef -> Parallel
parallel anims = { animations: anims }

-- | Get animations.
parallelAnimations :: Parallel -> Array AnimationRef
parallelAnimations p = p.animations

-- | Duration is the longest animation.
parallelDuration :: Parallel -> Number
parallelDuration p = foldl (\acc a -> max acc a.durationMs) 0.0 p.animations

-- | Show parallel for debug output.
showParallel :: Parallel -> String
showParallel p =
  "(Parallel " <> show (length p.animations) <> " anims, " <>
  "duration=" <> show (parallelDuration p) <> "ms)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // stagger
-- ═════════════════════════════════════════════════════════════════════════════

-- | Stagger - animations with incremental start delays.
type Stagger =
  { animations :: Array AnimationRef
  , delayIncrement :: Number  -- Delay added for each subsequent animation
  , fromEnd :: Boolean        -- Start stagger from end instead of beginning
  }

-- | Construct a stagger group.
stagger :: Array AnimationRef -> Number -> Boolean -> Stagger
stagger anims delay fromEnd =
  { animations: anims
  , delayIncrement: max 0.0 delay
  , fromEnd: fromEnd
  }

-- | Get animations.
staggerAnimations :: Stagger -> Array AnimationRef
staggerAnimations s = s.animations

-- | Get delay increment.
staggerDelay :: Stagger -> Number
staggerDelay s = s.delayIncrement

-- | Is stagger from end?
staggerFromEnd :: Stagger -> Boolean
staggerFromEnd s = s.fromEnd

-- | Calculate total duration including stagger.
staggerTotalDuration :: Stagger -> Number
staggerTotalDuration s =
  let n = length s.animations
      maxDuration = foldl (\acc a -> max acc a.durationMs) 0.0 s.animations
      totalStagger = s.delayIncrement * intToNumber (max 0 (n - 1))
  in maxDuration + totalStagger

-- | Show stagger for debug output.
showStagger :: Stagger -> String
showStagger s =
  "(Stagger " <> show (length s.animations) <> " anims, " <>
  show s.delayIncrement <> "ms increment, total=" <> show (staggerTotalDuration s) <> "ms)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // fill mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | FillMode - what happens before/after animation.
data FillMode
  = FillNone      -- ^ Element reverts to initial state
  | FillForwards  -- ^ Element retains final keyframe values
  | FillBackwards -- ^ Element takes initial keyframe values during delay
  | FillBoth      -- ^ Combines forwards and backwards

derive instance eqFillMode :: Eq FillMode
derive instance ordFillMode :: Ord FillMode

instance showFillMode :: Show FillMode where
  show = fillModeLabel

-- | Get CSS label for fill mode.
fillModeLabel :: FillMode -> String
fillModeLabel FillNone = "none"
fillModeLabel FillForwards = "forwards"
fillModeLabel FillBackwards = "backwards"
fillModeLabel FillBoth = "both"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // transition
-- ═════════════════════════════════════════════════════════════════════════════

-- | Transition - CSS transition definition.
type Transition =
  { property :: String        -- CSS property name or "all"
  , durationMs :: Number
  , easing :: String          -- Easing function name
  , delayMs :: Number
  }

-- | Construct a transition.
transition :: String -> Number -> String -> Number -> Transition
transition prop dur ease delay =
  { property: prop
  , durationMs: max 0.0 dur
  , easing: ease
  , delayMs: max 0.0 delay
  }

-- | Get property.
transitionProperty :: Transition -> String
transitionProperty t = t.property

-- | Get duration.
transitionDuration :: Transition -> Number
transitionDuration t = t.durationMs

-- | Get easing.
transitionEasing :: Transition -> String
transitionEasing t = t.easing

-- | Get delay.
transitionDelay :: Transition -> Number
transitionDelay t = t.delayMs

-- | Show transition for debug output.
showTransition :: Transition -> String
showTransition t =
  "(Transition " <> t.property <> " " <> show t.durationMs <> "ms " <>
  t.easing <> " delay=" <> show t.delayMs <> "ms)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // animation group
-- ═════════════════════════════════════════════════════════════════════════════

-- | AnimationGroup - union of composition types.
data AnimationGroup
  = GroupSequence Sequence
  | GroupParallel Parallel
  | GroupStagger Stagger

derive instance eqAnimationGroup :: Eq AnimationGroup

instance showAnimationGroup :: Show AnimationGroup where
  show (GroupSequence _) = "(GroupSequence ...)"
  show (GroupParallel _) = "(GroupParallel ...)"
  show (GroupStagger _) = "(GroupStagger ...)"

-- | Get total duration of any animation group.
groupDuration :: AnimationGroup -> Number
groupDuration (GroupSequence s) = sequenceTotalDuration s
groupDuration (GroupParallel p) = parallelDuration p
groupDuration (GroupStagger s) = staggerTotalDuration s

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

intToNumber :: Int -> Number
intToNumber = toNumber
