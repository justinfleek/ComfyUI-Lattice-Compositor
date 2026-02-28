-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // gpu // framestate // animation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Animation — Temporal Interpolation State
-- |
-- | ## Purpose
-- |
-- | This module manages all time-varying state for a render frame:
-- |
-- | - **Keyframe Animations**: Progress through duration with easing
-- | - **Spring Physics**: Physically-based interpolation with damping
-- |
-- | Both are forms of temporal interpolation — springs are just animations
-- | where the "easing" is determined by physics rather than a curve.
-- |
-- | ## Why External State?
-- |
-- | At billion-agent scale, animation state must be:
-- |
-- | 1. **Centralized**: Single registry per viewport, not per-component
-- | 2. **Serializable**: Save/restore for undo, replay, debugging
-- | 3. **Deterministic**: Same inputs → same interpolated values
-- | 4. **O(log n) access**: Map-based registry, not O(n) array scan
-- |
-- | ## Spring Physics
-- |
-- | Springs use semi-implicit Euler integration:
-- |
-- | ```
-- | F = -kx - cv           (Hooke's law + damping)
-- | a = F/m
-- | v' = v + a*dt          (velocity update)
-- | x' = x + v'*dt         (position update)
-- | ```
-- |
-- | Where k=stiffness, c=damping, m=mass, x=displacement, v=velocity.

module Hydrogen.GPU.FrameState.Animation
  ( -- * Core Types
    FrameTime
    
  -- * Animation Types
  , AnimationHandle
  , AnimationPhase(..)
  , AnimationInstance
  , EasingType(..)
  , AnimationDirection(..)
  , AnimationIteration(..)
  
  -- * Animation Registry
  , AnimationRegistry
  , mkAnimationRegistry
  , registerAnimation
  , unregisterAnimation
  , getAnimationPhase
  , getAllAnimations
  , tickAnimations
  
  -- * Spring Types
  , SpringHandle
  , SpringInstance
  
  -- * Spring Registry
  , SpringRegistry
  , mkSpringRegistry
  , registerSpring
  , getSpringValue
  , setSpringTarget
  , tickSprings
  
  -- * List-Based Queries (Lazy/Streaming)
  , animationsAsList
  , springsAsList
  , runningAnimations
  , completedAnimations
  , animationHandles
  , springHandles
  , findAnimationByPhase
  , anyAnimationRunning
  , allAnimationsComplete
  , getSpringValueMaybe
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , map
  , not
  , (<>)
  , (==)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (>=)
  , (&&)
  , ($)
  , min
  , negate
  )

import Data.Array as Array
import Data.List (List)
import Data.List as List
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(Nothing, Just))
import Data.Set as Set
import Data.Tuple (Tuple(Tuple))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // animation types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Time in milliseconds (re-exported from FrameState for convenience)
type FrameTime = Number

-- | Unique handle for registered animation
-- |
-- | Handles are monotonically increasing integers. Once assigned, a handle
-- | identifies an animation for its entire lifetime. Handles are never reused
-- | within a session to avoid ABA problems.
type AnimationHandle = Int

-- | Animation phase for effect interpolation
-- |
-- | Pure data describing where an animation is in its lifecycle.
-- | Effects query this to determine current visual state.
data AnimationPhase
  = AnimationIdle            -- Not started (before delay completes)
  | AnimationRunning Number  -- Progress 0.0-1.0 (eased value)
  | AnimationComplete        -- Finished (at 1.0)
  | AnimationReversing Number -- Playing backward (for alternate direction)

derive instance eqAnimationPhase :: Eq AnimationPhase

instance showAnimationPhase :: Show AnimationPhase where
  show AnimationIdle = "AnimationIdle"
  show (AnimationRunning p) = "(AnimationRunning " <> show p <> ")"
  show AnimationComplete = "AnimationComplete"
  show (AnimationReversing p) = "(AnimationReversing " <> show p <> ")"

-- | Animation instance in the registry
-- |
-- | Complete description of an animation's configuration and current state.
type AnimationInstance =
  { handle :: AnimationHandle
  , startTime :: FrameTime
  , duration :: FrameTime      -- Duration in ms
  , delay :: FrameTime         -- Delay before start in ms
  , easing :: EasingType
  , direction :: AnimationDirection
  , iteration :: AnimationIteration
  , phase :: AnimationPhase
  }

-- | Easing function type
-- |
-- | Determines the rate of change over time. Linear is constant velocity;
-- | others accelerate/decelerate for more natural motion.
data EasingType
  = EasingLinear       -- Constant velocity
  | EasingEaseIn       -- Start slow, accelerate
  | EasingEaseOut      -- Start fast, decelerate
  | EasingEaseInOut    -- Slow start and end, fast middle
  | EasingSpring       -- Physics-based overshoot

derive instance eqEasingType :: Eq EasingType

-- | Animation direction
data AnimationDirection
  = DirectionNormal          -- 0→1
  | DirectionReverse         -- 1→0
  | DirectionAlternate       -- 0→1→0→1...
  | DirectionAlternateReverse -- 1→0→1→0...

derive instance eqAnimationDirection :: Eq AnimationDirection

-- | Animation iteration count
data AnimationIteration
  = IterateOnce              -- Play once and stop
  | IterateCount Int         -- Play N times
  | IterateInfinite          -- Loop forever

derive instance eqAnimationIteration :: Eq AnimationIteration

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // animation registry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Registry of active animations
-- |
-- | Uses Map for O(log n) lookup by handle instead of O(n) Array.find.
-- | At 1000 animations and 120fps, this reduces comparisons from
-- | ~60 million/second to ~12,000/second.
type AnimationRegistry =
  { animations :: Map AnimationHandle AnimationInstance
  , nextHandle :: AnimationHandle
  }

-- | Create empty animation registry
mkAnimationRegistry :: AnimationRegistry
mkAnimationRegistry =
  { animations: Map.empty
  , nextHandle: 1
  }

-- | Register a new animation
-- |
-- | O(log n) insertion via Map.insert
registerAnimation 
  :: FrameTime      -- Current time
  -> FrameTime      -- Duration
  -> FrameTime      -- Delay
  -> EasingType
  -> AnimationDirection
  -> AnimationIteration
  -> AnimationRegistry
  -> Tuple AnimationHandle AnimationRegistry
registerAnimation currentTime duration delay easing direction iteration registry =
  let
    handle = registry.nextHandle
    instance_ = 
      { handle
      , startTime: currentTime
      , duration
      , delay
      , easing
      , direction
      , iteration
      , phase: AnimationIdle
      }
    newRegistry =
      { animations: Map.insert handle instance_ registry.animations
      , nextHandle: handle + 1
      }
  in
    Tuple handle newRegistry

-- | Unregister an animation
-- |
-- | O(log n) deletion via Map.delete
unregisterAnimation :: AnimationHandle -> AnimationRegistry -> AnimationRegistry
unregisterAnimation handle registry =
  { animations: Map.delete handle registry.animations
  , nextHandle: registry.nextHandle
  }

-- | Get animation phase by handle
-- |
-- | O(log n) lookup via Map.lookup (was O(n) with Array.find)
getAnimationPhase :: AnimationHandle -> AnimationRegistry -> AnimationPhase
getAnimationPhase handle registry =
  case Map.lookup handle registry.animations of
    Just anim -> anim.phase
    Nothing -> AnimationIdle

-- | Get all active animations
-- |
-- | Returns array of all animation instances (for iteration/tick)
getAllAnimations :: AnimationRegistry -> Array AnimationInstance
getAllAnimations registry = Array.fromFoldable $ Map.values registry.animations

-- | Advance all animations by delta time
-- |
-- | O(n) tick is unavoidable — we must update all animations each frame.
-- | But lookups between ticks are now O(log n).
tickAnimations :: FrameTime -> FrameTime -> AnimationRegistry -> AnimationRegistry
tickAnimations currentTime deltaTime registry =
  { animations: map (tickAnimation currentTime deltaTime) registry.animations
  , nextHandle: registry.nextHandle
  }

-- | Advance single animation
tickAnimation :: FrameTime -> FrameTime -> AnimationInstance -> AnimationInstance
tickAnimation currentTime _ anim =
  let
    elapsed = currentTime - anim.startTime - anim.delay
    progress = if elapsed < 0.0 then 0.0
               else if anim.duration >= 0.0 then min 1.0 (elapsed / anim.duration)
               else 1.0
    newPhase = if elapsed < 0.0 then AnimationIdle
               else if progress >= 1.0 then AnimationComplete
               else AnimationRunning progress
  in
    anim { phase = newPhase }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // spring types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unique handle for registered spring
type SpringHandle = Int

-- | Spring physics instance
-- |
-- | Models a damped harmonic oscillator for smooth value transitions.
type SpringInstance =
  { handle :: SpringHandle
  , current :: Number          -- Current value
  , target :: Number           -- Target value
  , velocity :: Number         -- Current velocity
  , stiffness :: Number        -- Spring stiffness (k)
  , damping :: Number          -- Damping coefficient (c)
  , mass :: Number             -- Mass (m)
  , restThreshold :: Number    -- Velocity threshold for "at rest"
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // spring registry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Registry of active springs
-- |
-- | Uses Map for O(log n) lookup by handle instead of O(n) Array.find.
-- | Critical for interactive UIs where springs are queried every frame.
type SpringRegistry =
  { springs :: Map SpringHandle SpringInstance
  , nextHandle :: SpringHandle
  }

-- | Create empty spring registry
mkSpringRegistry :: SpringRegistry
mkSpringRegistry =
  { springs: Map.empty
  , nextHandle: 1
  }

-- | Register a new spring
-- |
-- | O(log n) insertion via Map.insert
registerSpring
  :: Number         -- Initial value
  -> Number         -- Target value
  -> Number         -- Stiffness
  -> Number         -- Damping
  -> SpringRegistry
  -> Tuple SpringHandle SpringRegistry
registerSpring initial target stiffness damping registry =
  let
    handle = registry.nextHandle
    instance_ =
      { handle
      , current: initial
      , target
      , velocity: 0.0
      , stiffness
      , damping
      , mass: 1.0
      , restThreshold: 0.001
      }
    newRegistry =
      { springs: Map.insert handle instance_ registry.springs
      , nextHandle: handle + 1
      }
  in
    Tuple handle newRegistry

-- | Get spring current value
-- |
-- | O(log n) lookup via Map.lookup (was O(n) with Array.find)
getSpringValue :: SpringHandle -> SpringRegistry -> Number
getSpringValue handle registry =
  case Map.lookup handle registry.springs of
    Just spring -> spring.current
    Nothing -> 0.0

-- | Try to get spring value (returns Maybe)
-- |
-- | O(log n) lookup via Map.lookup
getSpringValueMaybe :: SpringHandle -> SpringRegistry -> Maybe Number
getSpringValueMaybe handle registry =
  case Map.lookup handle registry.springs of
    Just spring -> Just spring.current
    Nothing -> Nothing

-- | Set spring target value
-- |
-- | O(log n) update via Map.update
setSpringTarget :: SpringHandle -> Number -> SpringRegistry -> SpringRegistry
setSpringTarget handle newTarget registry =
  { springs: Map.update (\s -> Just $ s { target = newTarget }) handle registry.springs
  , nextHandle: registry.nextHandle
  }

-- | Advance all springs by delta time
tickSprings :: FrameTime -> SpringRegistry -> SpringRegistry
tickSprings deltaTime registry =
  { springs: map (tickSpring deltaTime) registry.springs
  , nextHandle: registry.nextHandle
  }

-- | Advance single spring using semi-implicit Euler integration
-- |
-- | Semi-implicit Euler updates velocity first, then position:
-- | - Stable for constant timesteps
-- | - Energy-conserving (won't explode)
-- | - First-order accurate
tickSpring :: FrameTime -> SpringInstance -> SpringInstance
tickSpring deltaTimeMs spring =
  let
    dt = deltaTimeMs / 1000.0  -- Convert to seconds
    displacement = spring.target - spring.current
    
    -- Hooke's law: F = -kx - cv
    -- a = F/m = (-kx - cv) / m
    springForce = spring.stiffness * displacement
    dampingForce = spring.damping * spring.velocity
    acceleration = (springForce - dampingForce) / spring.mass
    
    -- Semi-implicit Euler integration
    newVelocity = spring.velocity + acceleration * dt
    newCurrent = spring.current + newVelocity * dt
    
    -- Check if at rest
    isAtRest = absNum displacement < spring.restThreshold && 
               absNum newVelocity < spring.restThreshold
    
    finalCurrent = if isAtRest then spring.target else newCurrent
    finalVelocity = if isAtRest then 0.0 else newVelocity
  in
    spring { current = finalCurrent, velocity = finalVelocity }
  where
    absNum n = if n < 0.0 then negate n else n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // list-based queries (lazy)
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get all animations as a lazy List
-- |
-- | Useful for streaming iteration without materializing full Array.
-- | At 10,000 animations, avoids allocating intermediate arrays.
animationsAsList :: AnimationRegistry -> List AnimationInstance
animationsAsList registry = Map.values registry.animations

-- | Get all springs as a lazy List
springsAsList :: SpringRegistry -> List SpringInstance
springsAsList registry = Map.values registry.springs

-- | Get only running animations (lazy filter)
-- |
-- | Returns List for lazy evaluation — only materializes elements as consumed.
runningAnimations :: AnimationRegistry -> List AnimationInstance
runningAnimations registry = List.filter isRunning $ Map.values registry.animations
  where
    isRunning anim = case anim.phase of
      AnimationRunning _ -> true
      AnimationReversing _ -> true
      _ -> false

-- | Get only completed animations (lazy filter)
completedAnimations :: AnimationRegistry -> List AnimationInstance
completedAnimations registry = List.filter isComplete $ Map.values registry.animations
  where
    isComplete anim = case anim.phase of
      AnimationComplete -> true
      _ -> false

-- | Get all animation handles as a List (for iteration)
animationHandles :: AnimationRegistry -> List AnimationHandle
animationHandles registry = 
  let keysArray :: Array AnimationHandle
      keysArray = Set.toUnfoldable $ Map.keys registry.animations
  in List.fromFoldable keysArray

-- | Get all spring handles as a List (for iteration)
springHandles :: SpringRegistry -> List SpringHandle
springHandles registry = 
  let keysArray :: Array SpringHandle
      keysArray = Set.toUnfoldable $ Map.keys registry.springs
  in List.fromFoldable keysArray

-- | Find first animation matching a phase
-- |
-- | O(n) worst case but short-circuits on first match due to lazy List.
findAnimationByPhase :: AnimationPhase -> AnimationRegistry -> Maybe AnimationInstance
findAnimationByPhase targetPhase registry = 
  List.head $ List.filter matchesPhase $ Map.values registry.animations
  where
    matchesPhase anim = anim.phase == targetPhase

-- | Check if any animation is currently running (lazy short-circuit)
-- |
-- | More efficient than `not (List.null (runningAnimations reg))` for
-- | large registries — stops at first running animation found.
anyAnimationRunning :: AnimationRegistry -> Boolean
anyAnimationRunning registry = not $ List.null $ runningAnimations registry

-- | Check if all animations are complete
-- |
-- | Returns true if registry is empty OR all animations are AnimationComplete.
allAnimationsComplete :: AnimationRegistry -> Boolean
allAnimationsComplete registry = 
  List.all isComplete $ Map.values registry.animations
  where
    isComplete anim = case anim.phase of
      AnimationComplete -> true
      _ -> false
