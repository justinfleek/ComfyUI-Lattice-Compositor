-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // temporal // keyframe
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Keyframe Molecule — A value at a specific point in time.
-- |
-- | Composes:
-- | - Progress (0.0 - 1.0)
-- | - Value (generic)
-- |
-- | Keyframes define the "islands of certainty" in an animation.
-- | The runtime interpolates between these points.

module Hydrogen.Schema.Temporal.Keyframe
  ( Keyframe(..)
  , keyframe
  , at
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
import Hydrogen.Schema.Temporal.Progress (Progress)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // keyframe
-- ═════════════════════════════════════════════════════════════════════════════

-- | A value anchored at a specific progress point [0, 1]
data Keyframe a = Keyframe Progress a

derive instance eqKeyframe :: (Eq a) => Eq (Keyframe a)
derive instance ordKeyframe :: (Ord a) => Ord (Keyframe a)
derive instance genericKeyframe :: Generic (Keyframe a) _

instance showKeyframe :: (Show a) => Show (Keyframe a) where
  show (Keyframe p v) = "(Keyframe " <> show p <> " " <> show v <> ")"

-- | Create a keyframe
keyframe :: forall a. Progress -> a -> Keyframe a
keyframe = Keyframe

-- | Alias for keyframe (reads naturally: "value `at` progress")
at :: forall a. a -> Progress -> Keyframe a
at v p = Keyframe p v
