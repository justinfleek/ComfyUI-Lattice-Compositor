-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // schema // gestural // gesture // phase
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | GesturePhase - lifecycle states for gesture recognizers.
-- |
-- | Models the UIKit/Android gesture recognizer state machine.
-- | All gesture types use this common phase enumeration.
-- |
-- | ## Dependencies
-- | - Prelude (Eq, Ord, Show)
-- |
-- | ## Dependents
-- | - Gestural.Gesture.Tap (uses GesturePhase)
-- | - Gestural.Gesture.LongPress (uses GesturePhase)
-- | - Gestural.Gesture.Swipe (uses GesturePhase)
-- | - Gestural.Gesture.Pan (uses GesturePhase)

module Hydrogen.Schema.Gestural.Gesture.Phase
  ( GesturePhase(Possible, Began, Changed, Ended, Cancelled, Failed)
  , allGesturePhases
  , isPossible
  , isBegan
  , isChanged
  , isEnded
  , isCancelled
  , isFailed
  , isActive
  , isTerminal
  ) where

import Prelude

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // gesture // phase
-- ═════════════════════════════════════════════════════════════════════════════

-- | Phase of gesture recognition lifecycle
-- |
-- | Models the UIKit/Android gesture recognizer state machine:
-- | - Possible: Recognizer is evaluating touches
-- | - Began: Gesture has been recognized and started
-- | - Changed: Gesture is in progress with updates
-- | - Ended: Gesture completed successfully
-- | - Cancelled: Gesture was interrupted (e.g., incoming call)
-- | - Failed: Touches did not match gesture pattern
data GesturePhase
  = Possible    -- ^ Evaluating, not yet recognized
  | Began       -- ^ Gesture recognized and started
  | Changed     -- ^ Gesture in progress, state updated
  | Ended       -- ^ Gesture completed normally
  | Cancelled   -- ^ Gesture interrupted externally
  | Failed      -- ^ Touches did not match gesture

derive instance eqGesturePhase :: Eq GesturePhase
derive instance ordGesturePhase :: Ord GesturePhase

instance showGesturePhase :: Show GesturePhase where
  show Possible = "possible"
  show Began = "began"
  show Changed = "changed"
  show Ended = "ended"
  show Cancelled = "cancelled"
  show Failed = "failed"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // enumeration
-- ═════════════════════════════════════════════════════════════════════════════

-- | All gesture phases for enumeration
allGesturePhases :: Array GesturePhase
allGesturePhases = [ Possible, Began, Changed, Ended, Cancelled, Failed ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Is gesture in possible state?
isPossible :: GesturePhase -> Boolean
isPossible Possible = true
isPossible _ = false

-- | Has gesture just begun?
isBegan :: GesturePhase -> Boolean
isBegan Began = true
isBegan _ = false

-- | Is gesture in changed state?
isChanged :: GesturePhase -> Boolean
isChanged Changed = true
isChanged _ = false

-- | Has gesture ended?
isEnded :: GesturePhase -> Boolean
isEnded Ended = true
isEnded _ = false

-- | Was gesture cancelled?
isCancelled :: GesturePhase -> Boolean
isCancelled Cancelled = true
isCancelled _ = false

-- | Did gesture fail to recognize?
isFailed :: GesturePhase -> Boolean
isFailed Failed = true
isFailed _ = false

-- | Is gesture currently active (Began or Changed)?
isActive :: GesturePhase -> Boolean
isActive Began = true
isActive Changed = true
isActive _ = false

-- | Is gesture in a terminal state (Ended, Cancelled, or Failed)?
isTerminal :: GesturePhase -> Boolean
isTerminal Ended = true
isTerminal Cancelled = true
isTerminal Failed = true
isTerminal _ = false
