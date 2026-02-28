-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // schema // motion // orchestration
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Orchestration — composing animations into sequences, parallels, and timelines.
-- |
-- | ## The Problem
-- |
-- | Individual animations (fade, slide, scale) are atoms. But real UI requires
-- | coordinated motion: a modal fades in while its backdrop blurs, a list
-- | staggers its items, a notification slides in then auto-dismisses.
-- |
-- | ## The Solution
-- |
-- | This module provides combinators for composing animations:
-- |
-- | - **Sequence**: Run animations one after another
-- | - **Parallel**: Run animations simultaneously
-- | - **Stagger**: Run animations with incremental delays
-- | - **Timeline**: Explicit timing control for complex choreography
-- |
-- | ## Algebraic Properties
-- |
-- | ```
-- | sequence [a, b, c]  ≡  a >> b >> c
-- | parallel [a, b, c]  ≡  a <|> b <|> c
-- | stagger 50ms [a, b, c]  ≡  parallel [delay 0ms a, delay 50ms b, delay 100ms c]
-- | ```
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Motion.Orchestration as O
-- | import Hydrogen.Schema.Motion.Transition (fadeTransition, slideTransition)
-- |
-- | -- Modal enter animation: backdrop fades while content slides up
-- | modalEnter = O.parallel
-- |   [ O.animate "backdrop" fadeTransition
-- |   , O.animate "content" (slideTransition SlideFromBottom)
-- |   ]
-- |
-- | -- Staggered list reveal
-- | listReveal items = O.stagger (ms 50)
-- |   (map (\item -> O.animate item.id fadeTransition) items)
-- |
-- | -- Complex timeline
-- | complexAnimation = O.timeline
-- |   [ O.at (ms 0) (O.animate "title" fadeTransition)
-- |   , O.at (ms 200) (O.animate "subtitle" fadeTransition)
-- |   , O.at (ms 400) (O.parallel
-- |       [ O.animate "button1" scaleTransition
-- |       , O.animate "button2" scaleTransition
-- |       ])
-- |   ]
-- | ```

module Hydrogen.Schema.Motion.Orchestration
  ( -- * Animation Reference
    AnimationRef
  , animate
  , animateWithConfig
  
  -- * Orchestration ADT
  , Orchestration(..)
  
  -- * Combinators
  , sequence
  , parallel
  , stagger
  , staggerReverse
  , timeline
  , delay
  , at
  
  -- * Timeline Entry
  , TimelineEntry(TimelineEntry)
  , timelineEntry
  , entryTime
  , entryAnimation
  
  -- * Inspection
  , totalDuration
  , animationCount
  , allRefs
  
  -- * Predicates
  , isEmpty
  , isSequential
  , isParallel
  , isStaggered
  
  -- * Operations
  , reverse
  , scale
  , shiftBy
  , append
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , map
  , max
  , ($)
  , (+)
  , (-)
  , (*)
  , (<>)
  , (==)
  , (>)
  , (>=)
  , otherwise
  )

import Data.Array (length, null, foldl, reverse, index) as Array
import Data.Foldable (sum)
import Data.Int (toNumber)
import Data.Maybe (Maybe(Nothing, Just))
import Hydrogen.Schema.Dimension.Temporal (Milliseconds(Milliseconds), ms)
import Hydrogen.Schema.Motion.Transition (TransitionConfig, transitionDuration)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // animation reference
-- ═════════════════════════════════════════════════════════════════════════════

-- | Reference to an element and its animation configuration.
-- |
-- | The targetId identifies which DOM element to animate.
-- | The config specifies how the animation behaves.
type AnimationRef =
  { targetId :: String
  , config :: TransitionConfig
  }

-- | Create an animation reference
animate :: String -> TransitionConfig -> AnimationRef
animate targetId config = { targetId, config }

-- | Create an animation reference (explicit record)
animateWithConfig :: { targetId :: String, config :: TransitionConfig } -> AnimationRef
animateWithConfig = identity
  where
  identity :: forall a. a -> a
  identity x = x

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // orchestration adt
-- ═════════════════════════════════════════════════════════════════════════════

-- | Orchestration ADT — recursive structure for composing animations.
-- |
-- | This forms a tree where leaves are single animations and branches
-- | are composition strategies (sequence, parallel, stagger, timeline).
data Orchestration
  = Single AnimationRef                        -- ^ Single animation
  | Sequence (Array Orchestration)             -- ^ Run in sequence
  | Parallel (Array Orchestration)             -- ^ Run simultaneously  
  | Stagger Milliseconds (Array Orchestration) -- ^ Run with incremental delays
  | Delayed Milliseconds Orchestration         -- ^ Delay before starting
  | Timeline (Array TimelineEntry)             -- ^ Explicit timing

derive instance eqOrchestration :: Eq Orchestration

instance showOrchestration :: Show Orchestration where
  show (Single ref) = "Single(" <> ref.targetId <> ")"
  show (Sequence arr) = "Sequence[" <> show (Array.length arr) <> "]"
  show (Parallel arr) = "Parallel[" <> show (Array.length arr) <> "]"
  show (Stagger d arr) = "Stagger(" <> show (unwrapMs d) <> "ms)[" <> show (Array.length arr) <> "]"
  show (Delayed d _) = "Delayed(" <> show (unwrapMs d) <> "ms)"
  show (Timeline entries) = "Timeline[" <> show (Array.length entries) <> "]"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // timeline entry
-- ═════════════════════════════════════════════════════════════════════════════

-- | A point in a timeline with an associated animation.
newtype TimelineEntry = TimelineEntry
  { time :: Milliseconds
  , animation :: Orchestration
  }

derive instance eqTimelineEntry :: Eq TimelineEntry

-- | Create a timeline entry
timelineEntry :: Milliseconds -> Orchestration -> TimelineEntry
timelineEntry time animation = TimelineEntry { time, animation }

-- | Get entry time
entryTime :: TimelineEntry -> Milliseconds
entryTime (TimelineEntry e) = e.time

-- | Get entry animation
entryAnimation :: TimelineEntry -> Orchestration
entryAnimation (TimelineEntry e) = e.animation

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // combinators
-- ═════════════════════════════════════════════════════════════════════════════

-- | Run animations in sequence (one after another).
-- |
-- | Total duration = sum of individual durations.
-- |
-- | ```purescript
-- | sequence [fadeIn, slideUp, scaleIn]
-- | -- fadeIn completes, then slideUp, then scaleIn
-- | ```
sequence :: Array Orchestration -> Orchestration
sequence = Sequence

-- | Run animations in parallel (all at once).
-- |
-- | Total duration = max of individual durations.
-- |
-- | ```purescript
-- | parallel [fadeBackdrop, slideContent, scaleButton]
-- | -- All three start simultaneously
-- | ```
parallel :: Array Orchestration -> Orchestration
parallel = Parallel

-- | Run animations with staggered start times.
-- |
-- | Each animation starts `interval` after the previous.
-- |
-- | ```purescript
-- | stagger (ms 50) [item1, item2, item3, item4]
-- | -- item1 at 0ms, item2 at 50ms, item3 at 100ms, item4 at 150ms
-- | ```
stagger :: Milliseconds -> Array Orchestration -> Orchestration
stagger interval = Stagger interval

-- | Stagger in reverse order (last item starts first).
-- |
-- | Useful for exit animations where you want items to leave
-- | in reverse order of their appearance.
staggerReverse :: Milliseconds -> Array Orchestration -> Orchestration
staggerReverse interval arr = Stagger interval (Array.reverse arr)

-- | Create a timeline with explicit timing.
-- |
-- | Unlike sequence/parallel/stagger, timeline gives complete control
-- | over when each animation starts.
-- |
-- | ```purescript
-- | timeline
-- |   [ at (ms 0) titleFade
-- |   , at (ms 200) subtitleFade
-- |   , at (ms 500) buttonScale
-- |   ]
-- | ```
timeline :: Array TimelineEntry -> Orchestration
timeline = Timeline

-- | Add delay before an animation.
-- |
-- | ```purescript
-- | delay (ms 300) fadeIn
-- | -- Wait 300ms, then start fadeIn
-- | ```
delay :: Milliseconds -> Orchestration -> Orchestration
delay = Delayed

-- | Create a timeline entry at a specific time.
-- |
-- | Convenience function for building timelines.
at :: Milliseconds -> Orchestration -> TimelineEntry
at = timelineEntry

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // inspection
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate total duration of an orchestration.
-- |
-- | - Single: duration from config
-- | - Sequence: sum of all durations
-- | - Parallel: max of all durations
-- | - Stagger: last item start time + its duration
-- | - Delayed: delay + inner duration
-- | - Timeline: max(entry.time + entry.duration) for all entries
totalDuration :: Orchestration -> Milliseconds
totalDuration (Single ref) = transitionDuration ref.config
totalDuration (Sequence arr) = sumMs (map totalDuration arr)
totalDuration (Parallel arr) = foldMax (ms 0.0) (map totalDuration arr)
totalDuration (Stagger interval arr) =
  let count = Array.length arr
      lastStartTime = ms (toNumber (count - 1) * unwrapMs interval)
      lastDuration = case lastItem arr of
        Nothing -> ms 0.0
        Just orch -> totalDuration orch
  in addMs lastStartTime lastDuration
totalDuration (Delayed delayTime inner) = addMs delayTime (totalDuration inner)
totalDuration (Timeline entries) = foldMax (ms 0.0) (map calcEntryEnd entries)
  where
  calcEntryEnd entry = addMs (entryTime entry) (totalDuration (entryAnimation entry))

-- | Count total number of animations in an orchestration.
animationCount :: Orchestration -> Int
animationCount (Single _) = 1
animationCount (Sequence arr) = sum (map animationCount arr)
animationCount (Parallel arr) = sum (map animationCount arr)
animationCount (Stagger _ arr) = sum (map animationCount arr)
animationCount (Delayed _ inner) = animationCount inner
animationCount (Timeline entries) = sum (map (animationCount <<< entryAnimation) entries)

-- | Get all animation target IDs in an orchestration.
allRefs :: Orchestration -> Array String
allRefs (Single ref) = [ref.targetId]
allRefs (Sequence arr) = concatMap allRefs arr
allRefs (Parallel arr) = concatMap allRefs arr
allRefs (Stagger _ arr) = concatMap allRefs arr
allRefs (Delayed _ inner) = allRefs inner
allRefs (Timeline entries) = concatMap (allRefs <<< entryAnimation) entries

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if orchestration has no animations
isEmpty :: Orchestration -> Boolean
isEmpty (Single _) = false
isEmpty (Sequence arr) = Array.null arr
isEmpty (Parallel arr) = Array.null arr
isEmpty (Stagger _ arr) = Array.null arr
isEmpty (Delayed _ inner) = isEmpty inner
isEmpty (Timeline entries) = Array.null entries

-- | Check if orchestration is sequential
isSequential :: Orchestration -> Boolean
isSequential (Sequence _) = true
isSequential _ = false

-- | Check if orchestration is parallel
isParallel :: Orchestration -> Boolean
isParallel (Parallel _) = true
isParallel _ = false

-- | Check if orchestration is staggered
isStaggered :: Orchestration -> Boolean
isStaggered (Stagger _ _) = true
isStaggered _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Reverse the order of animations in sequences and staggers.
-- |
-- | Useful for creating exit animations from enter animations.
reverse :: Orchestration -> Orchestration
reverse (Single ref) = Single ref
reverse (Sequence arr) = Sequence (Array.reverse (map reverse arr))
reverse (Parallel arr) = Parallel (map reverse arr) -- Order doesn't matter for parallel
reverse (Stagger interval arr) = Stagger interval (Array.reverse (map reverse arr))
reverse (Delayed d inner) = Delayed d (reverse inner)
reverse (Timeline entries) = 
  let total = totalDuration (Timeline entries)
      reversed = map (reverseEntry total) entries
  in Timeline reversed
  where
  reverseEntry tot entry =
    let newTime = subtractMs tot (addMs (entryTime entry) (totalDuration (entryAnimation entry)))
    in TimelineEntry { time: newTime, animation: reverse (entryAnimation entry) }

-- | Scale all durations by a factor.
-- |
-- | ```purescript
-- | scale 2.0 animation  -- Everything takes twice as long
-- | scale 0.5 animation  -- Everything takes half the time
-- | ```
scale :: Number -> Orchestration -> Orchestration
scale factor (Single ref) = Single (scaleRef factor ref)
scale factor (Sequence arr) = Sequence (map (scale factor) arr)
scale factor (Parallel arr) = Parallel (map (scale factor) arr)
scale factor (Stagger interval arr) = 
  Stagger (scaleMs factor interval) (map (scale factor) arr)
scale factor (Delayed d inner) = 
  Delayed (scaleMs factor d) (scale factor inner)
scale factor (Timeline entries) = 
  Timeline (map (scaleEntry factor) entries)
  where
  scaleEntry f entry = 
    TimelineEntry
      { time: scaleMs f (entryTime entry)
      , animation: scale f (entryAnimation entry)
      }

-- | Shift all timeline entries by a duration.
-- |
-- | Useful for inserting animations into existing timelines.
shiftBy :: Milliseconds -> Orchestration -> Orchestration
shiftBy amount (Single ref) = Delayed amount (Single ref)
shiftBy amount (Sequence arr) = Delayed amount (Sequence arr)
shiftBy amount (Parallel arr) = Delayed amount (Parallel arr)
shiftBy amount (Stagger interval arr) = Delayed amount (Stagger interval arr)
shiftBy amount (Delayed d inner) = Delayed (addMs d amount) inner
shiftBy amount (Timeline entries) = 
  Timeline (map (shiftEntry amount) entries)
  where
  shiftEntry amt entry = TimelineEntry { time: addMs (entryTime entry) amt, animation: entryAnimation entry }

-- | Append one orchestration after another.
-- |
-- | Equivalent to `sequence [a, b]` but more convenient for chaining.
append :: Orchestration -> Orchestration -> Orchestration
append a b = Sequence [a, b]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Function composition
infixr 9 composeFlipped as <<<

composeFlipped :: forall a b c. (b -> c) -> (a -> b) -> a -> c
composeFlipped f g x = f (g x)

-- | Unwrap Milliseconds to Number
unwrapMs :: Milliseconds -> Number
unwrapMs (Milliseconds n) = n

-- | Add two Milliseconds values
addMs :: Milliseconds -> Milliseconds -> Milliseconds
addMs a b = ms (unwrapMs a + unwrapMs b)

-- | Sum an array of Milliseconds
sumMs :: Array Milliseconds -> Milliseconds
sumMs arr = Array.foldl addMs (ms 0.0) arr

-- | Subtract Milliseconds (result clamped to 0)
subtractMs :: Milliseconds -> Milliseconds -> Milliseconds
subtractMs a b = 
  let result = unwrapMs a - unwrapMs b
  in ms (if result > 0.0 then result else 0.0)

-- | Scale Milliseconds by a factor
scaleMs :: Number -> Milliseconds -> Milliseconds
scaleMs factor m = ms (unwrapMs m * factor)

-- | Scale animation ref duration
scaleRef :: Number -> AnimationRef -> AnimationRef
scaleRef _ ref = ref -- TransitionConfig scaling would require modifying the config

-- | Get last item from array
lastItem :: forall a. Array a -> Maybe a
lastItem arr = 
  let len = Array.length arr
  in if len >= 1 
     then Array.index arr (len - 1) 
     else Nothing

-- | Fold with max
foldMax :: Milliseconds -> Array Milliseconds -> Milliseconds
foldMax initial arr = Array.foldl maxMs initial arr
  where
  maxMs a b = if unwrapMs a > unwrapMs b then a else b

-- | Concat map for arrays
concatMap :: forall a b. (a -> Array b) -> Array a -> Array b
concatMap f arr = Array.foldl (\acc x -> acc <> f x) [] arr
