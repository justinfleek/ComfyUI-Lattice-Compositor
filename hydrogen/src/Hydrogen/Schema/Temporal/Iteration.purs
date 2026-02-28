-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // schema // temporal // iteration
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Iteration Atom — Animation loop count.
-- |
-- | Represents how many times an animation cycle repeats.
-- |
-- | ## Constraints
-- | - Must be non-negative (>= 0)
-- | - 0 typically means "infinite" or "indefinite" in some contexts,
-- |   or "no iterations" in others depending on the engine.
-- |   (Hydrogen convention: 0 = finite zero repeats, Infinite represented separately
-- |    usually via Maybe or specific enum, but here we model the raw count).

module Hydrogen.Schema.Temporal.Iteration
  ( Iteration
  , iteration
  , unsafeIteration
  , unwrapIteration
  , iterationToInt
  , iterationBounds
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
--                                                                  // iteration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Animation iteration count (>= 0)
newtype Iteration = Iteration Int

derive instance eqIteration :: Eq Iteration
derive instance ordIteration :: Ord Iteration

instance showIteration :: Show Iteration where
  show (Iteration i) = "(Iteration " <> show i <> ")"

-- | Create Iteration, clamping to minimum of 0
iteration :: Int -> Iteration
iteration i
  | i < 0 = Iteration 0
  | otherwise = Iteration i

-- | Create Iteration without bounds checking
unsafeIteration :: Int -> Iteration
unsafeIteration = Iteration

-- | Extract raw Int from Iteration
unwrapIteration :: Iteration -> Int
unwrapIteration (Iteration i) = i

-- | Alias for unwrapIteration
iterationToInt :: Iteration -> Int
iterationToInt = unwrapIteration

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds for Iteration
iterationBounds :: Bounded.IntBounds
iterationBounds = Bounded.intBounds 0 2147483647 "iteration"
  "Animation iteration count (non-negative integer)"
