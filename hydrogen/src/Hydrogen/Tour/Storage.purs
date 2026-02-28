-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                // hydrogen // tour // storage
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Persistence for Product Tours
-- |
-- | This module handles storing tour state in localStorage for:
-- | - "Don't show again" functionality
-- | - Snooze with expiration
-- | - Tour completion tracking
-- |
-- | All storage is namespaced under "hydrogen:tour:" to avoid conflicts.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Tour.Storage as Storage
-- | import Hydrogen.Tour.Types as T
-- |
-- | -- Check if tour should be shown
-- | shouldShow <- Storage.shouldShowTour (T.mkTourId "onboarding")
-- |
-- | -- Mark tour as completed
-- | Storage.markCompleted (T.mkTourId "onboarding")
-- |
-- | -- Snooze for 24 hours
-- | Storage.snooze (T.mkTourId "onboarding") (T.Milliseconds (24 * 60 * 60 * 1000))
-- | ```
module Hydrogen.Tour.Storage
  ( -- * Query State
    shouldShowTour
  , hasCompleted
  , hasDismissed
  , isSnoozed
    -- * Persistence
  , markCompleted
  , markDismissed
  , snooze
  , clearSnooze
  , clearTourState
    -- * Storage Keys
  , completedKey
  , dismissedKey
  , snoozeKey
  ) where

import Prelude

import Data.Maybe (Maybe(Just, Nothing), isJust, isNothing)
import Effect (Effect)
import Hydrogen.Tour.Types (Milliseconds(Milliseconds), TourId(TourId))
import Hydrogen.Util.LocalStorage as LS

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // storage keys
-- ═════════════════════════════════════════════════════════════════════════════

-- | Namespace prefix for all tour storage
storagePrefix :: String
storagePrefix = "hydrogen:tour:"

-- | Key for tour completion state
completedKey :: TourId -> String
completedKey (TourId id) = storagePrefix <> id <> ":completed"

-- | Key for tour dismissal state
dismissedKey :: TourId -> String
dismissedKey (TourId id) = storagePrefix <> id <> ":dismissed"

-- | Key for snooze expiration timestamp
snoozeKey :: TourId -> String
snoozeKey (TourId id) = storagePrefix <> id <> ":snoozed-until"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // query state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if a tour should be shown to the user
-- |
-- | Returns false if:
-- | - Tour has been completed
-- | - Tour has been dismissed (if persistent dismiss is enabled)
-- | - Tour is currently snoozed
shouldShowTour :: TourId -> Effect Boolean
shouldShowTour tourId = do
  completed <- hasCompleted tourId
  dismissed <- hasDismissed tourId
  snoozed <- isSnoozed tourId
  pure $ not completed && not dismissed && not snoozed

-- | Check if tour has been completed
hasCompleted :: TourId -> Effect Boolean
hasCompleted tourId = do
  maybeValue <- LS.getItemRaw (completedKey tourId)
  pure $ isJust maybeValue

-- | Check if tour has been dismissed
hasDismissed :: TourId -> Effect Boolean
hasDismissed tourId = do
  maybeValue <- LS.getItemRaw (dismissedKey tourId)
  pure $ isJust maybeValue

-- | Check if tour is currently snoozed
-- |
-- | Returns true if a snooze is active and hasn't expired.
-- | Automatically clears expired snoozes.
isSnoozed :: TourId -> Effect Boolean
isSnoozed tourId = do
  maybeUntil <- LS.getItem (snoozeKey tourId) :: Effect (Maybe Number)
  case maybeUntil of
    Nothing -> pure false
    Just until -> do
      now <- currentTimeMs
      if now < until
        then pure true
        else do
          -- Snooze expired, clear it
          clearSnooze tourId
          pure false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // persistence
-- ═════════════════════════════════════════════════════════════════════════════

-- | Mark a tour as completed
-- |
-- | This prevents the tour from being shown again (until cleared).
markCompleted :: TourId -> Effect Unit
markCompleted tourId = do
  now <- currentTimeMs
  LS.setItemRaw (completedKey tourId) (show now)

-- | Mark a tour as dismissed
-- |
-- | For persistent "don't show again" functionality.
markDismissed :: TourId -> Effect Unit
markDismissed tourId = do
  now <- currentTimeMs
  LS.setItemRaw (dismissedKey tourId) (show now)

-- | Snooze a tour for a duration
-- |
-- | The tour will not be shown until the snooze expires.
snooze :: TourId -> Milliseconds -> Effect Unit
snooze tourId (Milliseconds duration) = do
  now <- currentTimeMs
  let expiresAt = now + toNumber duration
  LS.setItem (snoozeKey tourId) expiresAt

-- | Clear an active snooze
clearSnooze :: TourId -> Effect Unit
clearSnooze tourId = LS.removeItem (snoozeKey tourId)

-- | Clear all state for a tour
-- |
-- | Removes completion, dismissal, and snooze state.
-- | Useful for testing or resetting tours.
clearTourState :: TourId -> Effect Unit
clearTourState tourId = do
  LS.removeItem (completedKey tourId)
  LS.removeItem (dismissedKey tourId)
  LS.removeItem (snoozeKey tourId)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get current time in milliseconds
foreign import currentTimeMs :: Effect Number

-- | Convert Int to Number
toNumber :: Int -> Number
toNumber = toNumberImpl

foreign import toNumberImpl :: Int -> Number
