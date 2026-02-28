-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                             // hydrogen // runtime // animate
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Animation State Helpers
-- |
-- | Ergonomic utilities for managing animated values in Hydrogen apps.
-- | Works with the Cmd-based tick pattern where animation state lives
-- | in app state and ticks are scheduled via `animationFrame`.
-- |
-- | ## Spring Animation Pattern
-- |
-- | ```purescript
-- | import Hydrogen.Runtime.Animate as Animate
-- | import Hydrogen.Runtime.Cmd (animationFrame, noCmd, transition)
-- |
-- | type State = { position :: Animate.SpringState }
-- |
-- | init = { position: Animate.springState springDefault 0.0 }
-- |
-- | update = case _ of
-- |   MoveTo target -> 
-- |     transition state 
-- |       { position = Animate.springTo state.position target }
-- |       (animationFrame Tick)
-- |   
-- |   Tick timestamp ->
-- |     let pos = Animate.tickSpring timestamp state.position
-- |     in case Animate.isComplete pos of
-- |       true -> noCmd state { position = pos }
-- |       false -> transition state { position = pos } (animationFrame Tick)
-- |
-- | view state =
-- |   E.div_ 
-- |     [ E.style "transform" (translateX (Animate.value state.position)) ]
-- |     []
-- | ```
-- |
-- | ## Tween Animation Pattern
-- |
-- | ```purescript
-- | type State = { opacity :: Animate.TweenState }
-- |
-- | update = case _ of
-- |   FadeIn -> 
-- |     transition state
-- |       { opacity = Animate.tweenTo state.opacity 1.0 300.0 easeOutCubic }
-- |       (animationFrame Tick)
-- | ```
module Hydrogen.Runtime.Animate
  ( -- * Spring Animation
    SpringState
  , springState
  , springTo
  , tickSpring
  
  -- * Tween Animation
  , TweenState
  , tweenState
  , tweenTo
  , tickTween
  
  -- * Spring Value Access
  , springValue
  , springComplete
  , resetSpring
  
  -- * Tween Value Access
  , tweenValue
  , tweenComplete
  , resetTween
  
  -- * Style Helpers
  , translateX
  , translateY
  , translate
  , scale
  , rotate
  , opacity
  
  -- * Vec2 Animation (for position, size, etc.)
  , Vec2
  , Vec2State
  , vec2State
  , vec2To
  , tickVec2
  , vec2Value
  , vec2Complete
  
  -- * Color Animation
  , RGB
  , ColorState
  , colorState
  , colorTo
  , tickColor
  , colorValue
  , colorComplete
  , rgbToLegacyCss
  
  -- * Multi-Property Animation
  , AnimatorState
  , animator
  , withSpring
  , withTween
  , withVec2
  , withColor
  , startAnimator
  , tickAnimator
  , animatorComplete
  , getSpring
  , getTween
  , getVec2
  , getColor
  
  -- * Sequencing
  , SequenceStep  -- abstract, use andThen/withDelay to construct
  , Sequence
  , sequence
  , andThen
  , withDelay
  , tickSequence
  , sequenceComplete
  , sequenceValue
  ) where

import Prelude
  ( map
  , negate
  , show
  , ($)
  , (&&)
  , (<)
  , (<>)
  , (+)
  , (-)
  , (*)
  , (/)
  , (==)
  , (>=)
  )

import Data.Array (filter, index, length, snoc) as Array
import Data.Foldable (foldl) as Foldable
import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Motion.Spring (SpringConfig)
import Hydrogen.Motion.Spring as Spring
import Hydrogen.Schema.Motion.Easing (Easing)
import Hydrogen.Schema.Motion.Easing as Easing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // spring // animation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Spring animation state.
-- |
-- | Contains everything needed to evaluate a spring at any timestamp.
-- | Uses "pending start" pattern - startTime of -1.0 means "start on first tick".
type SpringState =
  { config :: SpringConfig
  , from :: Number
  , to :: Number
  , startTime :: Number  -- -1.0 means "pending start"
  , currentValue :: Number
  , complete :: Boolean
  }

-- | Create initial spring state.
springState :: SpringConfig -> Number -> SpringState
springState config initialValue =
  { config
  , from: initialValue
  , to: initialValue
  , startTime: 0.0
  , currentValue: initialValue
  , complete: true  -- No animation in progress
  }

-- | Start spring animation toward a target value.
-- |
-- | Call this when you want to animate to a new value. The spring will
-- | start from its current position. Uses -1.0 as sentinel to indicate
-- | "capture timestamp on first tick".
springTo :: SpringState -> Number -> SpringState
springTo state target =
  { config: state.config
  , from: state.currentValue
  , to: target
  , startTime: -1.0  -- Sentinel: start on first tick
  , currentValue: state.currentValue
  , complete: false
  }

-- | Advance spring animation to a new timestamp.
-- |
-- | Call this on each animation frame to update the current value.
-- | If startTime is -1.0, this tick captures the start time.
tickSpring :: Number -> SpringState -> SpringState
tickSpring timestamp state =
  case state.complete of
    true -> state
    false ->
      -- Handle pending start
      let
        actualStartTime = case state.startTime < 0.0 of
          true -> timestamp  -- First tick captures start time
          false -> state.startTime
        
        -- Time since animation started (in seconds)
        elapsed = (timestamp - actualStartTime) / 1000.0
        
        -- Evaluate spring physics
        newValue = Spring.springValue state.config state.from state.to elapsed
        
        -- Check if spring is at rest
        atRest = Spring.isAtRest state.config state.from state.to elapsed
      in
        state 
          { startTime = actualStartTime
          , currentValue = newValue
          , complete = atRest
          }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // tween // animation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Tween (duration-based) animation state.
-- | Uses "pending start" pattern - startTime of -1.0 means "start on first tick".
type TweenState =
  { easing :: Easing
  , from :: Number
  , to :: Number
  , duration :: Number     -- milliseconds
  , startTime :: Number    -- -1.0 means "pending start"
  , currentValue :: Number
  , complete :: Boolean
  }

-- | Create initial tween state.
tweenState :: Number -> TweenState
tweenState initialValue =
  { easing: Easing.linear
  , from: initialValue
  , to: initialValue
  , duration: 0.0
  , startTime: 0.0
  , currentValue: initialValue
  , complete: true
  }

-- | Start tween animation toward a target value.
-- | Uses -1.0 as sentinel to indicate "capture timestamp on first tick".
tweenTo :: TweenState -> Number -> Number -> Easing -> TweenState
tweenTo state target duration easing =
  { easing
  , from: state.currentValue
  , to: target
  , duration
  , startTime: -1.0  -- Sentinel: start on first tick
  , currentValue: state.currentValue
  , complete: false
  }

-- | Advance tween animation to a new timestamp.
-- | If startTime is -1.0, this tick captures the start time.
tickTween :: Number -> TweenState -> TweenState
tickTween timestamp state =
  case state.complete of
    true -> state
    false ->
      let
        -- Handle pending start
        actualStartTime = case state.startTime < 0.0 of
          true -> timestamp
          false -> state.startTime
        
        elapsed = timestamp - actualStartTime
        progress = elapsed / state.duration
      in
        case progress >= 1.0 of
          true -> state
            { startTime = actualStartTime
            , currentValue = state.to
            , complete = true
            }
          false ->
            let
              easedProgress = Easing.evaluate state.easing progress
              newValue = state.from + (state.to - state.from) * easedProgress
            in
              state 
                { startTime = actualStartTime
                , currentValue = newValue 
                }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // spring // value // access
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the current value from a spring animation.
springValue :: SpringState -> Number
springValue s = s.currentValue

-- | Check if spring animation is complete.
springComplete :: SpringState -> Boolean
springComplete s = s.complete

-- | Reset a spring to a specific value (stops animation).
resetSpring :: Number -> SpringState -> SpringState
resetSpring v s = s { currentValue = v, from = v, to = v, complete = true }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // tween // value // access
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the current value from a tween animation.
tweenValue :: TweenState -> Number
tweenValue s = s.currentValue

-- | Check if tween animation is complete.
tweenComplete :: TweenState -> Boolean
tweenComplete s = s.complete

-- | Reset a tween to a specific value (stops animation).
resetTween :: Number -> TweenState -> TweenState
resetTween v s = s { currentValue = v, from = v, to = v, complete = true }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // style // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate translateX transform style value.
translateX :: Number -> String
translateX x = "translateX(" <> show x <> "px)"

-- | Generate translateY transform style value.
translateY :: Number -> String
translateY y = "translateY(" <> show y <> "px)"

-- | Generate translate transform style value.
translate :: Number -> Number -> String
translate x y = "translate(" <> show x <> "px, " <> show y <> "px)"

-- | Generate scale transform style value.
scale :: Number -> String
scale s = "scale(" <> show s <> ")"

-- | Generate rotate transform style value (degrees).
rotate :: Number -> String
rotate deg = "rotate(" <> show deg <> "deg)"

-- | Generate opacity style value.
opacity :: Number -> String
opacity o = show o

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // vec2 // animation
-- ═════════════════════════════════════════════════════════════════════════════

-- | 2D vector type for position, size, etc.
type Vec2 = { x :: Number, y :: Number }

-- | Vec2 tween animation state.
-- |
-- | Animates two values together with the same timing.
-- | Uses "pending start" pattern - startTime of -1.0 means "start on first tick".
type Vec2State =
  { easing :: Easing
  , from :: Vec2
  , to :: Vec2
  , duration :: Number
  , startTime :: Number  -- -1.0 means "pending start"
  , currentValue :: Vec2
  , complete :: Boolean
  }

-- | Create initial Vec2 state.
vec2State :: Vec2 -> Vec2State
vec2State initial =
  { easing: Easing.linear
  , from: initial
  , to: initial
  , duration: 0.0
  , startTime: 0.0
  , currentValue: initial
  , complete: true
  }

-- | Start Vec2 animation toward a target.
-- | Uses -1.0 as sentinel to indicate "capture timestamp on first tick".
vec2To :: Vec2State -> Vec2 -> Number -> Easing -> Vec2State
vec2To state target duration easing =
  { easing
  , from: state.currentValue
  , to: target
  , duration
  , startTime: -1.0  -- Sentinel: start on first tick
  , currentValue: state.currentValue
  , complete: false
  }

-- | Advance Vec2 animation to a new timestamp.
-- | If startTime is -1.0, this tick captures the start time.
tickVec2 :: Number -> Vec2State -> Vec2State
tickVec2 timestamp state =
  case state.complete of
    true -> state
    false ->
      let
        -- Handle pending start
        actualStartTime = case state.startTime < 0.0 of
          true -> timestamp
          false -> state.startTime
        
        elapsed = timestamp - actualStartTime
        progress = elapsed / state.duration
      in
        case progress >= 1.0 of
          true -> state
            { startTime = actualStartTime
            , currentValue = state.to
            , complete = true
            }
          false ->
            let
              t = Easing.evaluate state.easing progress
              newX = state.from.x + (state.to.x - state.from.x) * t
              newY = state.from.y + (state.to.y - state.from.y) * t
            in
              state 
                { startTime = actualStartTime
                , currentValue = { x: newX, y: newY } 
                }

-- | Get current Vec2 value.
vec2Value :: Vec2State -> Vec2
vec2Value s = s.currentValue

-- | Check if Vec2 animation is complete.
vec2Complete :: Vec2State -> Boolean
vec2Complete s = s.complete

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // color // animation
-- ═════════════════════════════════════════════════════════════════════════════

-- | RGB color type for color animation.
type RGB = { r :: Number, g :: Number, b :: Number }

-- | Color tween animation state.
-- |
-- | Interpolates RGB values with easing.
-- | Uses "pending start" pattern - startTime of -1.0 means "start on first tick".
type ColorState =
  { easing :: Easing
  , from :: RGB
  , to :: RGB
  , duration :: Number
  , startTime :: Number  -- -1.0 means "pending start"
  , currentValue :: RGB
  , complete :: Boolean
  }

-- | Create initial color state.
colorState :: RGB -> ColorState
colorState initial =
  { easing: Easing.linear
  , from: initial
  , to: initial
  , duration: 0.0
  , startTime: 0.0
  , currentValue: initial
  , complete: true
  }

-- | Start color animation toward a target.
-- | Uses -1.0 as sentinel to indicate "capture timestamp on first tick".
colorTo :: ColorState -> RGB -> Number -> Easing -> ColorState
colorTo state target duration easing =
  { easing
  , from: state.currentValue
  , to: target
  , duration
  , startTime: -1.0  -- Sentinel: start on first tick
  , currentValue: state.currentValue
  , complete: false
  }

-- | Advance color animation to a new timestamp.
-- | If startTime is -1.0, this tick captures the start time.
tickColor :: Number -> ColorState -> ColorState
tickColor timestamp state =
  case state.complete of
    true -> state
    false ->
      let
        -- Handle pending start
        actualStartTime = case state.startTime < 0.0 of
          true -> timestamp
          false -> state.startTime
        
        elapsed = timestamp - actualStartTime
        progress = elapsed / state.duration
      in
        case progress >= 1.0 of
          true -> state
            { startTime = actualStartTime
            , currentValue = state.to
            , complete = true
            }
          false ->
            let
              t = Easing.evaluate state.easing progress
              newR = state.from.r + (state.to.r - state.from.r) * t
              newG = state.from.g + (state.to.g - state.from.g) * t
              newB = state.from.b + (state.to.b - state.from.b) * t
            in
              state 
                { startTime = actualStartTime
                , currentValue = { r: newR, g: newG, b: newB } 
                }

-- | Get current color value.
colorValue :: ColorState -> RGB
colorValue s = s.currentValue

-- | Check if color animation is complete.
colorComplete :: ColorState -> Boolean
colorComplete s = s.complete

-- | Convert RGB to CSS string.
rgbToLegacyCss :: RGB -> String
rgbToLegacyCss c = "rgb(" <> show c.r <> ", " <> show c.g <> ", " <> show c.b <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                              // multi // property // animator
-- ═════════════════════════════════════════════════════════════════════════════

-- | Named animation entry.
-- |
-- | Tracks multiple animations by string key.
data AnimationEntry
  = SpringEntry String SpringState
  | TweenEntry String TweenState
  | Vec2Entry String Vec2State
  | ColorEntry String ColorState

-- | Multi-property animator state.
-- |
-- | Manages multiple named animations that can be started and ticked together.
-- |
-- | ```purescript
-- | state = animator
-- |   # withTween "opacity" 0.0
-- |   # withVec2 "position" { x: 0.0, y: 0.0 }
-- |   # withColor "background" { r: 255.0, g: 255.0, b: 255.0 }
-- | ```
newtype AnimatorState = AnimatorState (Array AnimationEntry)

-- | Create an empty animator.
animator :: AnimatorState
animator = AnimatorState []

-- | Add a spring animation.
withSpring :: String -> SpringConfig -> Number -> AnimatorState -> AnimatorState
withSpring name config initial (AnimatorState entries) =
  AnimatorState $ Array.snoc entries (SpringEntry name (springState config initial))

-- | Add a tween animation.
withTween :: String -> Number -> AnimatorState -> AnimatorState
withTween name initial (AnimatorState entries) =
  AnimatorState $ Array.snoc entries (TweenEntry name (tweenState initial))

-- | Add a Vec2 animation.
withVec2 :: String -> Vec2 -> AnimatorState -> AnimatorState
withVec2 name initial (AnimatorState entries) =
  AnimatorState $ Array.snoc entries (Vec2Entry name (vec2State initial))

-- | Add a color animation.
withColor :: String -> RGB -> AnimatorState -> AnimatorState
withColor name initial (AnimatorState entries) =
  AnimatorState $ Array.snoc entries (ColorEntry name (colorState initial))

-- | Start an animation by name (for tweens).
-- | Timestamp is no longer needed - uses pending start pattern.
startAnimator :: String -> Number -> Number -> Easing -> AnimatorState -> AnimatorState
startAnimator name target duration easing (AnimatorState entries) =
  AnimatorState $ map (startEntry name target duration easing) entries
  where
  startEntry :: String -> Number -> Number -> Easing -> AnimationEntry -> AnimationEntry
  startEntry n t d e entry = case entry of
    TweenEntry entryName s ->
      case entryName == n of
        true -> TweenEntry entryName (tweenTo s t d e)
        false -> entry
    _ -> entry

-- | Tick all animations.
tickAnimator :: Number -> AnimatorState -> AnimatorState
tickAnimator timestamp (AnimatorState entries) =
  AnimatorState $ map (tickEntry timestamp) entries
  where
  tickEntry :: Number -> AnimationEntry -> AnimationEntry
  tickEntry ts entry = case entry of
    SpringEntry n s -> SpringEntry n (tickSpring ts s)
    TweenEntry n s -> TweenEntry n (tickTween ts s)
    Vec2Entry n s -> Vec2Entry n (tickVec2 ts s)
    ColorEntry n s -> ColorEntry n (tickColor ts s)

-- | Check if all animations are complete.
animatorComplete :: AnimatorState -> Boolean
animatorComplete (AnimatorState entries) =
  allComplete entries
  where
  allComplete :: Array AnimationEntry -> Boolean
  allComplete arr = case arr of
    [] -> true
    _ -> foldlArray (\acc e -> acc && entryComplete e) true arr
  
  entryComplete :: AnimationEntry -> Boolean
  entryComplete entry = case entry of
    SpringEntry _ s -> s.complete
    TweenEntry _ s -> s.complete
    Vec2Entry _ s -> s.complete
    ColorEntry _ s -> s.complete

-- | Get a spring value by name.
getSpring :: String -> AnimatorState -> Maybe Number
getSpring name (AnimatorState entries) =
  findSpring name entries
  where
  findSpring :: String -> Array AnimationEntry -> Maybe Number
  findSpring _ [] = Nothing
  findSpring n arr = case findFirst n arr of
    Just (SpringEntry _ s) -> Just s.currentValue
    _ -> Nothing

-- | Get a tween value by name.
getTween :: String -> AnimatorState -> Maybe Number
getTween name (AnimatorState entries) =
  findTween name entries
  where
  findTween :: String -> Array AnimationEntry -> Maybe Number
  findTween _ [] = Nothing
  findTween n arr = case findFirst n arr of
    Just (TweenEntry _ s) -> Just s.currentValue
    _ -> Nothing

-- | Get a Vec2 value by name.
getVec2 :: String -> AnimatorState -> Maybe Vec2
getVec2 name (AnimatorState entries) =
  findVec2 name entries
  where
  findVec2 :: String -> Array AnimationEntry -> Maybe Vec2
  findVec2 _ [] = Nothing
  findVec2 n arr = case findFirst n arr of
    Just (Vec2Entry _ s) -> Just s.currentValue
    _ -> Nothing

-- | Get a color value by name.
getColor :: String -> AnimatorState -> Maybe RGB
getColor name (AnimatorState entries) =
  findColor name entries
  where
  findColor :: String -> Array AnimationEntry -> Maybe RGB
  findColor _ [] = Nothing
  findColor n arr = case findFirst n arr of
    Just (ColorEntry _ s) -> Just s.currentValue
    _ -> Nothing

-- | Find first entry matching name.
findFirst :: String -> Array AnimationEntry -> Maybe AnimationEntry
findFirst name entries =
  case Array.filter (matchesName name) entries of
    [] -> Nothing
    arr -> headMay arr
  where
  matchesName :: String -> AnimationEntry -> Boolean
  matchesName n entry = case entry of
    SpringEntry en _ -> en == n
    TweenEntry en _ -> en == n
    Vec2Entry en _ -> en == n
    ColorEntry en _ -> en == n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // sequencing
-- ═════════════════════════════════════════════════════════════════════════════

-- | A step in an animation sequence.
data SequenceStep
  = TweenStep Number Number Easing  -- target, duration, easing
  | DelayStep Number                 -- duration

-- | Animation sequence state.
-- |
-- | Runs animations one after another.
-- | Uses "pending start" pattern - stepStartTime of -1.0 means "start on first tick".
type Sequence =
  { steps :: Array SequenceStep
  , currentStep :: Int
  , tween :: TweenState
  , stepStartTime :: Number  -- -1.0 means "pending start"
  , delayRemaining :: Number
  , complete :: Boolean
  , started :: Boolean       -- Has sequence been started?
  }

-- | Create a sequence starting from a value.
sequence :: Number -> Sequence
sequence initial =
  { steps: []
  , currentStep: 0
  , tween: tweenState initial
  , stepStartTime: -1.0
  , delayRemaining: 0.0
  , complete: true
  , started: false
  }

-- | Add a tween step to the sequence.
andThen :: Number -> Number -> Easing -> Sequence -> Sequence
andThen target duration easing seq =
  seq { steps = Array.snoc seq.steps (TweenStep target duration easing) }

-- | Add a delay step to the sequence.
withDelay :: Number -> Sequence -> Sequence
withDelay duration seq =
  seq { steps = Array.snoc seq.steps (DelayStep duration) }

-- | Start and tick the sequence.
-- | On first call, marks the sequence as started. Subsequent calls advance it.
tickSequence :: Number -> Sequence -> Sequence
tickSequence timestamp seq =
  case seq.started of
    false -> 
      -- Start sequence if we have steps
      case arrayLength seq.steps of
        0 -> seq
        _ -> advanceSequence timestamp seq 
              { started = true
              , complete = false
              , stepStartTime = timestamp 
              }
    true -> 
      case seq.complete of
        true -> seq
        false -> advanceSequence timestamp seq

-- | Advance sequence to next timestamp.
advanceSequence :: Number -> Sequence -> Sequence
advanceSequence timestamp seq =
  case arrayIndex seq.currentStep seq.steps of
    Nothing -> seq { complete = true }
    Just step -> case step of
      DelayStep duration ->
        let elapsed = timestamp - seq.stepStartTime
        in case elapsed >= duration of
          true -> advanceSequence timestamp seq 
            { currentStep = seq.currentStep + 1
            , stepStartTime = timestamp
            }
          false -> seq { delayRemaining = duration - elapsed }
      
      TweenStep target duration easing ->
        -- Check if tween needs to be started (complete and at step start)
        case seq.tween.complete of
          true ->
            -- Start new tween for this step
            let newTween = tweenTo seq.tween target duration easing
            in advanceSequence timestamp seq { tween = newTween }
          false ->
            -- Tween in progress, tick it
            let tickedTween = tickTween timestamp seq.tween
            in case tickedTween.complete of
              true -> advanceSequence timestamp seq
                { tween = tickedTween
                , currentStep = seq.currentStep + 1
                , stepStartTime = timestamp
                }
              false -> seq { tween = tickedTween }

-- | Check if sequence is complete.
sequenceComplete :: Sequence -> Boolean
sequenceComplete seq = seq.complete

-- | Get current sequence value.
sequenceValue :: Sequence -> Number
sequenceValue seq = seq.tween.currentValue

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Safe head
headMay :: forall a. Array a -> Maybe a
headMay arr = arrayIndex 0 arr

-- | Array length (pure implementation)
arrayLength :: forall a. Array a -> Int
arrayLength = Array.length

-- | Array index - safe indexing with Maybe (pure implementation)
arrayIndex :: forall a. Int -> Array a -> Maybe a
arrayIndex idx arr = Array.index arr idx

-- | foldl for arrays (pure implementation)
foldlArray :: forall a b. (b -> a -> b) -> b -> Array a -> b
foldlArray = Foldable.foldl
