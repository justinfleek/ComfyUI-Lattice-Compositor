-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // schema // temporal // animation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Animation Compounds — Types of animation definitions.
-- |
-- | Defines the high-level structures for different animation techniques:
-- |
-- | - **Transition**: Simple A to B with duration and easing.
-- | - **KeyframeAnim**: Multi-step interpolation with specific timing.
-- | - **SpringAnim**: Physics-based motion (no fixed duration).
-- | - **PhysicsAnim**: Velocity-based simulation (friction/gravity).

module Hydrogen.Schema.Temporal.Animation
  ( Animation(..)
  , transition
  , keyframeAnim
  , springAnim
  , physicsAnim
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  )

import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe)
import Hydrogen.Schema.Temporal.Duration (Duration)
import Hydrogen.Schema.Temporal.Delay (Delay)
import Hydrogen.Schema.Temporal.Easing (Easing)
import Hydrogen.Schema.Temporal.Keyframe (Keyframe)
import Hydrogen.Schema.Temporal.SpringConfig (SpringConfig)
import Hydrogen.Schema.Temporal.Iteration (Iteration)
import Hydrogen.Schema.Temporal.Direction (Direction)
import Hydrogen.Schema.Temporal.Persistence (Persistence)
import Hydrogen.Schema.Temporal.PlayState (PlayState)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // animation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Union of all animation types
data Animation a
  = Transition
      { target :: a
      , duration :: Duration
      , easing :: Easing
      , delay :: Delay
      }
  | KeyframeAnim
      { keyframes :: Array (Keyframe a)
      , duration :: Duration
      , easing :: Easing
      , delay :: Delay
      , iteration :: Iteration
      , direction :: Direction
      , persistence :: Persistence
      , playState :: PlayState
      }
  | SpringAnim
      { target :: a
      , config :: SpringConfig
      , delay :: Delay
      }
  | PhysicsAnim
      { velocity :: Number -- Initial velocity
      , friction :: Number -- 0-1
      , bounds :: Maybe (Array Number) -- [min, max]
      }

derive instance eqAnimation :: (Eq a) => Eq (Animation a)
derive instance ordAnimation :: (Ord a) => Ord (Animation a)
derive instance genericAnimation :: Generic (Animation a) _

instance showAnimation :: (Show a) => Show (Animation a) where
  show (Transition r) = "(Transition " <> show r <> ")"
  show (KeyframeAnim r) = "(KeyframeAnim " <> show r <> ")"
  show (SpringAnim r) = "(SpringAnim " <> show r <> ")"
  show (PhysicsAnim r) = "(PhysicsAnim " <> show r <> ")"

-- | Create a standard Transition
transition :: forall a. a -> Duration -> Easing -> Delay -> Animation a
transition target duration easing delay =
  Transition { target, duration, easing, delay }

-- | Create a Keyframe Animation
keyframeAnim
  :: forall a
   . Array (Keyframe a)
  -> Duration
  -> Easing
  -> Delay
  -> Iteration
  -> Direction
  -> Persistence
  -> PlayState
  -> Animation a
keyframeAnim keyframes duration easing delay iteration direction persistence playState =
  KeyframeAnim
    { keyframes
    , duration
    , easing
    , delay
    , iteration
    , direction
    , persistence
    , playState
    }

-- | Create a Spring Animation
springAnim :: forall a. a -> SpringConfig -> Delay -> Animation a
springAnim target config delay =
  SpringAnim { target, config, delay }

-- | Create a Physics Animation
physicsAnim :: forall a. Number -> Number -> Maybe (Array Number) -> Animation a
physicsAnim velocity friction bounds =
  PhysicsAnim { velocity, friction, bounds }
