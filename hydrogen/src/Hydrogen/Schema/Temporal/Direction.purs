-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // schema // temporal // direction
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Direction Atom — Animation playback direction.
-- |
-- | Controls the direction of the animation cycle:
-- |
-- | - **Normal**: Forward (0% -> 100%)
-- | - **Reverse**: Backward (100% -> 0%)
-- | - **Alternate**: Forward then Backward (0% -> 100% -> 0%)
-- | - **AlternateReverse**: Backward then Forward (100% -> 0% -> 100%)

module Hydrogen.Schema.Temporal.Direction
  ( Direction(..)
  , directionToString
  , directionFromString
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
--                                                                  // direction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Animation playback direction
data Direction
  = Normal
  | Reverse
  | Alternate
  | AlternateReverse

derive instance eqDirection :: Eq Direction
derive instance ordDirection :: Ord Direction
derive instance genericDirection :: Generic Direction _

instance showDirection :: Show Direction where
  show Normal = "Normal"
  show Reverse = "Reverse"
  show Alternate = "Alternate"
  show AlternateReverse = "AlternateReverse"

-- | Convert Direction to CSS string value
directionToString :: Direction -> String
directionToString = case _ of
  Normal -> "normal"
  Reverse -> "reverse"
  Alternate -> "alternate"
  AlternateReverse -> "alternate-reverse"

-- | Parse Direction from CSS string value
directionFromString :: String -> Maybe Direction
directionFromString = case _ of
  "normal" -> Just Normal
  "reverse" -> Just Reverse
  "alternate" -> Just Alternate
  "alternate-reverse" -> Just AlternateReverse
  _ -> Nothing
