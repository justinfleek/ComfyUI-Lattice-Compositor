-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // schema // temporal // step-easing
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | StepEasing — Atoms for stepped/discrete animation timing.
-- |
-- | ## CSS Steps Function
-- |
-- | CSS supports stepped timing functions:
-- |   steps(n, position)
-- |
-- | Where:
-- | - **n**: Number of steps (discrete jumps)
-- | - **position**: When the jump occurs (start, end, both, none)
-- |
-- | ## Use Cases
-- |
-- | - Sprite animations (jump between frames)
-- | - Typewriter effects (reveal characters discretely)
-- | - Retro/pixel art animations
-- | - Clock second hands (tick, not sweep)

module Hydrogen.Schema.Temporal.StepEasing
  ( -- * Steps Count
    Steps
  , steps
  , unsafeSteps
  , unwrapSteps
  , stepsToInt
  
  -- * Step Position
  , StepPosition(..)
  , stepPositionToString
  
  -- * Bounds
  , stepsBounds
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , (<>)
  , (<)
  )

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // steps
-- ═════════════════════════════════════════════════════════════════════════════

-- | Number of steps in stepped animation (>= 1)
-- |
-- | Each step is an instantaneous jump to the next value.
-- | More steps = smoother (but still discrete) animation.
newtype Steps = Steps Int

derive instance eqSteps :: Eq Steps
derive instance ordSteps :: Ord Steps

instance showSteps :: Show Steps where
  show (Steps n) = "(Steps " <> show n <> ")"

-- | Create Steps, clamping to minimum of 1
-- |
-- | ```purescript
-- | steps 5    -- Steps 5
-- | steps 0    -- Steps 1 (clamped)
-- | steps (-3) -- Steps 1 (clamped)
-- | ```
steps :: Int -> Steps
steps n
  | n < 1 = Steps 1
  | otherwise = Steps n

-- | Create Steps without bounds checking
unsafeSteps :: Int -> Steps
unsafeSteps = Steps

-- | Extract raw Int from Steps
unwrapSteps :: Steps -> Int
unwrapSteps (Steps n) = n

-- | Alias for unwrapSteps
stepsToInt :: Steps -> Int
stepsToInt = unwrapSteps

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // step position
-- ═════════════════════════════════════════════════════════════════════════════

-- | When the step jump occurs within each interval
-- |
-- | - **JumpStart**: Jump at the beginning of each interval
-- | - **JumpEnd**: Jump at the end of each interval (default CSS)
-- | - **JumpNone**: No jump at start or end (continuous at boundaries)
-- | - **JumpBoth**: Jump at both start and end (n+1 total states)
data StepPosition
  = JumpStart
  | JumpEnd
  | JumpNone
  | JumpBoth

derive instance eqStepPosition :: Eq StepPosition
derive instance ordStepPosition :: Ord StepPosition

instance showStepPosition :: Show StepPosition where
  show JumpStart = "JumpStart"
  show JumpEnd = "JumpEnd"
  show JumpNone = "JumpNone"
  show JumpBoth = "JumpBoth"

-- | Convert to CSS steps() position string
-- |
-- | ```purescript
-- | stepPositionToString JumpStart  -- "jump-start"
-- | stepPositionToString JumpEnd    -- "jump-end"
-- | ```
stepPositionToString :: StepPosition -> String
stepPositionToString JumpStart = "jump-start"
stepPositionToString JumpEnd = "jump-end"
stepPositionToString JumpNone = "jump-none"
stepPositionToString JumpBoth = "jump-both"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds for Steps
stepsBounds :: Bounded.IntBounds
stepsBounds = Bounded.intBounds 1 1000 "steps"
  "Number of discrete steps (1 minimum, practical max around 100)"
