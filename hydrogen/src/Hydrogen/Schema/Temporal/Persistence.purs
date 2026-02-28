-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // schema // temporal // persistence
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Persistence Atom — Behavior of values outside active duration.
-- |
-- | Describes the thermodynamic/state behavior of a value when the driving
-- | force (animation) is not active.
-- |
-- | This replaces the legacy CSS concept of "FillMode".
-- |
-- | ## States
-- |
-- | - **None** (Elastic): System returns to ground state (initial value).
-- |   Equivalent to CSS 'none'.
-- |
-- | - **PersistEnd** (Plastic): System retains the final high-energy state.
-- |   Equivalent to CSS 'forwards'.
-- |
-- | - **PersistStart** (Anticipatory): System assumes start state immediately
-- |   upon scheduling, before time T=0. Equivalent to CSS 'backwards'.
-- |
-- | - **PersistBoth** (Full): System is fully state-captured at both ends.
-- |   Equivalent to CSS 'both'.

module Hydrogen.Schema.Temporal.Persistence
  ( Persistence(..)
  , persistenceToString
  , persistenceFromString
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
--                                                                // persistence
-- ═════════════════════════════════════════════════════════════════════════════

-- | State persistence behavior
data Persistence
  = None
  | PersistEnd
  | PersistStart
  | PersistBoth

derive instance eqPersistence :: Eq Persistence
derive instance ordPersistence :: Ord Persistence
derive instance genericPersistence :: Generic Persistence _

instance showPersistence :: Show Persistence where
  show None = "None"
  show PersistEnd = "PersistEnd"
  show PersistStart = "PersistStart"
  show PersistBoth = "PersistBoth"

-- | Convert for legacy systems (CSS interop)
persistenceToString :: Persistence -> String
persistenceToString = case _ of
  None -> "none"
  PersistEnd -> "forwards"
  PersistStart -> "backwards"
  PersistBoth -> "both"

-- | Parse from legacy string
persistenceFromString :: String -> Maybe Persistence
persistenceFromString = case _ of
  "none" -> Just None
  "forwards" -> Just PersistEnd
  "backwards" -> Just PersistStart
  "both" -> Just PersistBoth
  _ -> Nothing
