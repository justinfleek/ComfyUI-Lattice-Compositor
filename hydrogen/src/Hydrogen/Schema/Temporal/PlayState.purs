-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                               // hydrogen // schema // temporal // play-state
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | PlayState Atom — Animation running state.
-- |
-- | Controls whether an animation is currently running or paused.
-- |
-- | - **Running**: Animation is active.
-- | - **Paused**: Animation is halted at current progress.

module Hydrogen.Schema.Temporal.PlayState
  ( PlayState(..)
  , playStateToString
  , playStateFromString
  , toggle
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  )

import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // play state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Animation play state
data PlayState
  = Running
  | Paused

derive instance eqPlayState :: Eq PlayState
derive instance ordPlayState :: Ord PlayState
derive instance genericPlayState :: Generic PlayState _

instance showPlayState :: Show PlayState where
  show Running = "Running"
  show Paused = "Paused"

-- | Convert PlayState to CSS string value
playStateToString :: PlayState -> String
playStateToString = case _ of
  Running -> "running"
  Paused -> "paused"

-- | Parse PlayState from CSS string value
playStateFromString :: String -> Maybe PlayState
playStateFromString = case _ of
  "running" -> Just Running
  "paused" -> Just Paused
  _ -> Nothing

-- | Toggle between Running and Paused
toggle :: PlayState -> PlayState
toggle Running = Paused
toggle Paused = Running
