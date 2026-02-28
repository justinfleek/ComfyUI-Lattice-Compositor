-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // schema // gestural // arbitration
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Arbitration - gesture conflict resolution.
-- |
-- | Models how competing gestures are resolved when multiple
-- | recognizers could claim the same input. Based on UIKit's
-- | gesture recognizer delegate pattern.
-- |
-- | ## Dependencies
-- | - Prelude (Eq, Ord, Show)
-- | - Data.Array (filter, elem, sortBy)
-- | - Data.Maybe (Maybe)
-- |
-- | ## Dependents
-- | - Gestural.Gesture (gesture state machine)
-- | - Component.* (complex gesture handling)

module Hydrogen.Schema.Gestural.Arbitration
  ( -- * Gesture Identity
    GestureId
  , gestureId
  , unwrapGestureId
    -- * Gesture Priority
  , GesturePriority(PriorityLowest, PriorityLow, PriorityNormal, PriorityHigh, PriorityHighest)
  , comparePriority
  , higherPriority
    -- * Recognition Policy
  , RecognitionPolicy(Exclusive, Simultaneous, RequireFailure, Delegate)
  , isExclusive
  , allowsSimultaneous
    -- * Failure Requirement
  , FailureRequirement
  , noFailureRequirement
  , requiresFailureOf
  , requiredFailures
  , isFailureRequired
    -- * Gesture Relationship
  , GestureRelationship
  , noRelationship
  , relationship
  , canRecognizeSimultaneously
  , shouldRequireFailure
  , shouldBeRequired
    -- * Arbiter Decision
  , ArbiterDecision(Allow, Deny, Defer, Cancel)
  , isAllowed
  , isDenied
  , isDeferred
    -- * Gesture Registration
  , GestureRegistration
  , registerGesture
  , registrationId
  , registrationPriority
  , registrationPolicy
  , registrationFailures
    -- * Arbitration State
  , ArbitrationState
  , initialArbitrationState
  , registerGestureState
  , unregisterGesture
  , setGestureActive
  , setGestureFailed
  , activeGestures
  , failedGestures
  , resolveConflict
  , canGestureBegin
  , shouldGestureFail
  ) where

import Prelude

import Data.Array (all, any, elem, filter, length, notElem, snoc)
import Data.Maybe (Maybe(Just, Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // gesture // identity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unique identifier for a gesture recognizer
newtype GestureId = GestureId String

derive instance eqGestureId :: Eq GestureId
derive instance ordGestureId :: Ord GestureId

instance showGestureId :: Show GestureId where
  show (GestureId id) = id

-- | Create gesture ID
gestureId :: String -> GestureId
gestureId = GestureId

-- | Unwrap gesture ID
unwrapGestureId :: GestureId -> String
unwrapGestureId (GestureId id) = id

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // gesture // priority
-- ═════════════════════════════════════════════════════════════════════════════

-- | Priority levels for gesture recognition
data GesturePriority
  = PriorityLowest
  | PriorityLow
  | PriorityNormal
  | PriorityHigh
  | PriorityHighest

derive instance eqGesturePriority :: Eq GesturePriority
derive instance ordGesturePriority :: Ord GesturePriority

instance showGesturePriority :: Show GesturePriority where
  show PriorityLowest = "lowest"
  show PriorityLow = "low"
  show PriorityNormal = "normal"
  show PriorityHigh = "high"
  show PriorityHighest = "highest"

-- | Compare priorities (higher = wins)
comparePriority :: GesturePriority -> GesturePriority -> Ordering
comparePriority = compare

-- | Is first priority higher than second?
higherPriority :: GesturePriority -> GesturePriority -> Boolean
higherPriority a b = a > b

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // recognition // policy
-- ═════════════════════════════════════════════════════════════════════════════

-- | How gesture interacts with others
data RecognitionPolicy
  = Exclusive      -- ^ Only this gesture can be active
  | Simultaneous   -- ^ Can recognize with other gestures
  | RequireFailure -- ^ Wait for specified gesture to fail
  | Delegate       -- ^ Ask delegate to decide

derive instance eqRecognitionPolicy :: Eq RecognitionPolicy
derive instance ordRecognitionPolicy :: Ord RecognitionPolicy

instance showRecognitionPolicy :: Show RecognitionPolicy where
  show Exclusive = "exclusive"
  show Simultaneous = "simultaneous"
  show RequireFailure = "requireFailure"
  show Delegate = "delegate"

-- | Is exclusive policy?
isExclusive :: RecognitionPolicy -> Boolean
isExclusive Exclusive = true
isExclusive _ = false

-- | Allows simultaneous recognition?
allowsSimultaneous :: RecognitionPolicy -> Boolean
allowsSimultaneous Simultaneous = true
allowsSimultaneous _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // failure // requirement
-- ═════════════════════════════════════════════════════════════════════════════

-- | Gestures that must fail before this one can begin
type FailureRequirement =
  { required :: Array GestureId  -- ^ Gestures that must fail first
  }

-- | No failure requirements
noFailureRequirement :: FailureRequirement
noFailureRequirement = { required: [] }

-- | Require failure of specific gesture
requiresFailureOf :: GestureId -> FailureRequirement -> FailureRequirement
requiresFailureOf gid fr =
  fr { required = snoc fr.required gid }

-- | Get required failures
requiredFailures :: FailureRequirement -> Array GestureId
requiredFailures fr = fr.required

-- | Is failure of gesture required?
isFailureRequired :: GestureId -> FailureRequirement -> Boolean
isFailureRequired gid fr = elem gid fr.required

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // gesture // relationship
-- ═════════════════════════════════════════════════════════════════════════════

-- | Relationship between two gestures
type GestureRelationship =
  { gestureA :: GestureId          -- ^ First gesture
  , gestureB :: GestureId          -- ^ Second gesture
  , simultaneous :: Boolean        -- ^ Can recognize together
  , aRequiresBFailure :: Boolean   -- ^ A waits for B to fail
  , bRequiresAFailure :: Boolean   -- ^ B waits for A to fail
  }

-- | No special relationship
noRelationship :: GestureId -> GestureId -> GestureRelationship
noRelationship a b =
  { gestureA: a
  , gestureB: b
  , simultaneous: false
  , aRequiresBFailure: false
  , bRequiresAFailure: false
  }

-- | Create relationship
relationship :: GestureId -> GestureId -> Boolean -> Boolean -> Boolean -> GestureRelationship
relationship a b simultaneous aReqB bReqA =
  { gestureA: a
  , gestureB: b
  , simultaneous
  , aRequiresBFailure: aReqB
  , bRequiresAFailure: bReqA
  }

-- | Can these gestures recognize simultaneously?
canRecognizeSimultaneously :: GestureRelationship -> Boolean
canRecognizeSimultaneously gr = gr.simultaneous

-- | Should A require B to fail?
shouldRequireFailure :: GestureRelationship -> Boolean
shouldRequireFailure gr = gr.aRequiresBFailure

-- | Should B require A to fail?
shouldBeRequired :: GestureRelationship -> Boolean
shouldBeRequired gr = gr.bRequiresAFailure

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // arbiter // decision
-- ═════════════════════════════════════════════════════════════════════════════

-- | Decision from arbiter
data ArbiterDecision
  = Allow    -- ^ Gesture can proceed
  | Deny     -- ^ Gesture should not proceed
  | Defer    -- ^ Wait for other gesture to resolve
  | Cancel   -- ^ Cancel this gesture

derive instance eqArbiterDecision :: Eq ArbiterDecision
derive instance ordArbiterDecision :: Ord ArbiterDecision

instance showArbiterDecision :: Show ArbiterDecision where
  show Allow = "allow"
  show Deny = "deny"
  show Defer = "defer"
  show Cancel = "cancel"

-- | Is decision to allow?
isAllowed :: ArbiterDecision -> Boolean
isAllowed Allow = true
isAllowed _ = false

-- | Is decision to deny?
isDenied :: ArbiterDecision -> Boolean
isDenied Deny = true
isDenied _ = false

-- | Is decision to defer?
isDeferred :: ArbiterDecision -> Boolean
isDeferred Defer = true
isDeferred _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // gesture // registration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Registration info for a gesture
type GestureRegistration =
  { id :: GestureId                  -- ^ Gesture identifier
  , priority :: GesturePriority      -- ^ Priority level
  , policy :: RecognitionPolicy      -- ^ Recognition policy
  , failures :: FailureRequirement   -- ^ Required failures
  }

-- | Register a gesture
registerGesture :: GestureId -> GesturePriority -> RecognitionPolicy -> GestureRegistration
registerGesture id priority policy =
  { id
  , priority
  , policy
  , failures: noFailureRequirement
  }

-- | Get registration ID
registrationId :: GestureRegistration -> GestureId
registrationId gr = gr.id

-- | Get registration priority
registrationPriority :: GestureRegistration -> GesturePriority
registrationPriority gr = gr.priority

-- | Get registration policy
registrationPolicy :: GestureRegistration -> RecognitionPolicy
registrationPolicy gr = gr.policy

-- | Get registration failure requirements
registrationFailures :: GestureRegistration -> FailureRequirement
registrationFailures gr = gr.failures

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // arbitration // state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete arbitration state
type ArbitrationState =
  { registrations :: Array GestureRegistration  -- ^ All registered gestures
  , active :: Array GestureId                   -- ^ Currently active gestures
  , failed :: Array GestureId                   -- ^ Recently failed gestures
  , deferred :: Array GestureId                 -- ^ Waiting gestures
  , relationships :: Array GestureRelationship  -- ^ Gesture relationships
  }

-- | Initial arbitration state
initialArbitrationState :: ArbitrationState
initialArbitrationState =
  { registrations: []
  , active: []
  , failed: []
  , deferred: []
  , relationships: []
  }

-- | Register gesture in state
registerGestureState :: GestureRegistration -> ArbitrationState -> ArbitrationState
registerGestureState reg as =
  as { registrations = snoc as.registrations reg }

-- | Unregister gesture
unregisterGesture :: GestureId -> ArbitrationState -> ArbitrationState
unregisterGesture gid as =
  as { registrations = filter (\r -> r.id /= gid) as.registrations
     , active = filter (_ /= gid) as.active
     , failed = filter (_ /= gid) as.failed
     , deferred = filter (_ /= gid) as.deferred
     }

-- | Mark gesture as active
setGestureActive :: GestureId -> ArbitrationState -> ArbitrationState
setGestureActive gid as =
  as { active = if elem gid as.active then as.active else snoc as.active gid
     , deferred = filter (_ /= gid) as.deferred
     }

-- | Mark gesture as failed
setGestureFailed :: GestureId -> ArbitrationState -> ArbitrationState
setGestureFailed gid as =
  as { failed = if elem gid as.failed then as.failed else snoc as.failed gid
     , active = filter (_ /= gid) as.active
     , deferred = filter (_ /= gid) as.deferred
     }

-- | Get active gestures
activeGestures :: ArbitrationState -> Array GestureId
activeGestures as = as.active

-- | Get failed gestures
failedGestures :: ArbitrationState -> Array GestureId
failedGestures as = as.failed

-- | Is gesture ID not among active gestures?
-- | Returns true if gesture is either deferred, failed, or not yet active.
isNotActive :: GestureId -> ArbitrationState -> Boolean
isNotActive gid as = notElem gid as.active

-- | Resolve conflict between gestures
resolveConflict :: GestureId -> GestureId -> ArbitrationState -> ArbiterDecision
resolveConflict challenger incumbent as =
  let
    challengerReg = findRegistration challenger as.registrations
    incumbentReg = findRegistration incumbent as.registrations
  in case challengerReg, incumbentReg of
    Just cr, Just ir ->
      if allowsSimultaneous cr.policy && allowsSimultaneous ir.policy
        then Allow
      else if higherPriority cr.priority ir.priority
        then Allow  -- Higher priority wins
      else if isExclusive ir.policy
        then Deny   -- Incumbent is exclusive
      else Defer    -- Wait and see
    _, _ -> Allow   -- Unknown gesture, allow
  where
    findRegistration :: GestureId -> Array GestureRegistration -> Maybe GestureRegistration
    findRegistration gid regs =
      case filter (\r -> r.id == gid) regs of
        [r] -> Just r
        _ -> Nothing

-- | Can gesture begin given current state?
canGestureBegin :: GestureId -> ArbitrationState -> ArbiterDecision
canGestureBegin gid as =
  let
    reg = findRegistration gid as.registrations
  in case reg of
    Nothing -> Allow  -- Not registered, allow
    Just r ->
      -- Check if required failures have occurred
      let
        requiredFailed = all (\f -> elem f as.failed) r.failures.required
        hasExclusiveActive = any (isExclusiveGesture as.registrations) as.active
      in
        if not requiredFailed && length r.failures.required > 0
          then Defer  -- Still waiting for failures
        else if hasExclusiveActive && isExclusive r.policy
          then Deny   -- Exclusive gesture already active
        else Allow
  where
    findRegistration :: GestureId -> Array GestureRegistration -> Maybe GestureRegistration
    findRegistration gid' regs =
      case filter (\r -> r.id == gid') regs of
        [r] -> Just r
        _ -> Nothing
    
    isExclusiveGesture :: Array GestureRegistration -> GestureId -> Boolean
    isExclusiveGesture regs gid' =
      case findRegistration gid' regs of
        Just r -> isExclusive r.policy
        Nothing -> false

-- | Should gesture fail given another gesture succeeded?
shouldGestureFail :: GestureId -> GestureId -> ArbitrationState -> Boolean
shouldGestureFail loser winner as =
  let
    loserReg = findRegistration loser as.registrations
    winnerReg = findRegistration winner as.registrations
  in case loserReg, winnerReg of
    Just lr, Just wr ->
      -- Exclusive winner fails all others
      isExclusive wr.policy && not (allowsSimultaneous lr.policy)
    _, _ -> false
  where
    findRegistration :: GestureId -> Array GestureRegistration -> Maybe GestureRegistration
    findRegistration gid regs =
      case filter (\r -> r.id == gid) regs of
        [r] -> Just r
        _ -> Nothing
