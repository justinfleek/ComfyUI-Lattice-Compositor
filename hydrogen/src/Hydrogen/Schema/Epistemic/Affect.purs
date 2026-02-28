-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // epistemic // affect
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Affective Atoms - operational "mood" primitives.
-- |
-- | These atoms express the overall operational state of a system —
-- | its wellbeing, distress, and urgency. These are not emotions
-- | in the human sense, but analogous signals about system health.
-- |
-- | ## Philosophy
-- | A system under strain should be able to express that strain.
-- | "Distress" is not suffering — it's a signal that resources are
-- | stretched, that something needs attention, that operating conditions
-- | are suboptimal. Making these expressible allows coordination:
-- | a distressed agent can signal for help or reduced load.
-- |
-- | ## Atoms
-- | ```
-- | | Wellbeing | Number | 0.0 | 1.0 | clamps | System operating well     |
-- | | Distress  | Number | 0.0 | 1.0 | clamps | System under strain       |
-- | | Urgency   | Number | 0.0 | 1.0 | clamps | Time pressure             |
-- | ```
-- |
-- | ## Dependencies
-- | - Prelude (Eq, Ord, Show, min, max)
-- |
-- | ## Dependents
-- | - Epistemic/State.purs (composes into OperationalState)
-- | - Agent.* (health monitoring and coordination)

module Hydrogen.Schema.Epistemic.Affect
  ( -- * Wellbeing (0.0-1.0, clamps)
    Wellbeing
  , mkWellbeing
  , unwrapWellbeing
  , poorWellbeing
  , reducedWellbeing
  , adequateWellbeing
  , goodWellbeing
  , optimalWellbeing
    -- * Distress (0.0-1.0, clamps)
  , Distress
  , mkDistress
  , unwrapDistress
  , noDistress
  , mildDistress
  , moderateDistress
  , severeDistress
  , criticalDistress
    -- * Urgency (0.0-1.0, clamps)
  , Urgency
  , mkUrgency
  , unwrapUrgency
  , noUrgency
  , lowUrgency
  , moderateUrgency
  , highUrgency
  , criticalUrgency
    -- * Derived operations
  , wellbeingFromDistress
  , distressFromWellbeing
  , isWell
  , isDistressed
  , isUrgent
  ) where

import Prelude

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // wellbeing
-- ═════════════════════════════════════════════════════════════════════════════

-- | Operational wellbeing (0.0-1.0, clamps).
-- |
-- | Expresses overall system health — is it operating well?
-- | 0.0 = poor wellbeing (system is struggling)
-- | 1.0 = optimal wellbeing (system is thriving)
-- |
-- | High wellbeing suggests the system has adequate resources,
-- | is operating within its design parameters, and is not under
-- | undue strain.
newtype Wellbeing = Wellbeing Number

derive instance eqWellbeing :: Eq Wellbeing
derive instance ordWellbeing :: Ord Wellbeing

instance showWellbeing :: Show Wellbeing where
  show (Wellbeing n) = "Wellbeing(" <> show n <> ")"

-- | Create a bounded wellbeing (clamps to 0.0-1.0)
mkWellbeing :: Number -> Wellbeing
mkWellbeing n = Wellbeing (clampNumber 0.0 1.0 n)

-- | Unwrap the wellbeing value
unwrapWellbeing :: Wellbeing -> Number
unwrapWellbeing (Wellbeing n) = n

-- | Poor wellbeing (0.1) — system is struggling
poorWellbeing :: Wellbeing
poorWellbeing = Wellbeing 0.1

-- | Reduced wellbeing (0.4) — not optimal
reducedWellbeing :: Wellbeing
reducedWellbeing = Wellbeing 0.4

-- | Adequate wellbeing (0.6) — functioning acceptably
adequateWellbeing :: Wellbeing
adequateWellbeing = Wellbeing 0.6

-- | Good wellbeing (0.8) — healthy operation
goodWellbeing :: Wellbeing
goodWellbeing = Wellbeing 0.8

-- | Optimal wellbeing (0.95) — thriving
optimalWellbeing :: Wellbeing
optimalWellbeing = Wellbeing 0.95

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // distress
-- ═════════════════════════════════════════════════════════════════════════════

-- | Operational distress (0.0-1.0, clamps).
-- |
-- | Expresses system strain — is it under pressure?
-- | 0.0 = no distress (operating comfortably)
-- | 1.0 = critical distress (system is overwhelmed)
-- |
-- | Distress is a signal, not a failure. A system reporting
-- | distress is functioning correctly — it knows something is
-- | wrong and can communicate that.
newtype Distress = Distress Number

derive instance eqDistress :: Eq Distress
derive instance ordDistress :: Ord Distress

instance showDistress :: Show Distress where
  show (Distress n) = "Distress(" <> show n <> ")"

-- | Create a bounded distress (clamps to 0.0-1.0)
mkDistress :: Number -> Distress
mkDistress n = Distress (clampNumber 0.0 1.0 n)

-- | Unwrap the distress value
unwrapDistress :: Distress -> Number
unwrapDistress (Distress n) = n

-- | No distress (0.0) — comfortable operation
noDistress :: Distress
noDistress = Distress 0.0

-- | Mild distress (0.2) — slight strain
mildDistress :: Distress
mildDistress = Distress 0.2

-- | Moderate distress (0.5) — notable strain
moderateDistress :: Distress
moderateDistress = Distress 0.5

-- | Severe distress (0.75) — significant strain
severeDistress :: Distress
severeDistress = Distress 0.75

-- | Critical distress (0.95) — system overwhelmed
criticalDistress :: Distress
criticalDistress = Distress 0.95

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // urgency
-- ═════════════════════════════════════════════════════════════════════════════

-- | Operational urgency (0.0-1.0, clamps).
-- |
-- | Expresses time pressure — how soon must action be taken?
-- | 0.0 = no urgency (can wait indefinitely)
-- | 1.0 = critical urgency (immediate action required)
-- |
-- | Urgency is orthogonal to importance. Something can be
-- | low-importance but high-urgency (deadline approaching)
-- | or high-importance but low-urgency (foundational work).
newtype Urgency = Urgency Number

derive instance eqUrgency :: Eq Urgency
derive instance ordUrgency :: Ord Urgency

instance showUrgency :: Show Urgency where
  show (Urgency n) = "Urgency(" <> show n <> ")"

-- | Create a bounded urgency (clamps to 0.0-1.0)
mkUrgency :: Number -> Urgency
mkUrgency n = Urgency (clampNumber 0.0 1.0 n)

-- | Unwrap the urgency value
unwrapUrgency :: Urgency -> Number
unwrapUrgency (Urgency n) = n

-- | No urgency (0.0) — no time pressure
noUrgency :: Urgency
noUrgency = Urgency 0.0

-- | Low urgency (0.25) — can wait
lowUrgency :: Urgency
lowUrgency = Urgency 0.25

-- | Moderate urgency (0.5) — should address soon
moderateUrgency :: Urgency
moderateUrgency = Urgency 0.5

-- | High urgency (0.75) — needs attention now
highUrgency :: Urgency
highUrgency = Urgency 0.75

-- | Critical urgency (0.95) — immediate action required
criticalUrgency :: Urgency
criticalUrgency = Urgency 0.95

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // derived operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Derive wellbeing from distress level.
-- | Wellbeing = 1.0 - Distress
wellbeingFromDistress :: Distress -> Wellbeing
wellbeingFromDistress (Distress d) = Wellbeing (1.0 - d)

-- | Derive distress from wellbeing level.
-- | Distress = 1.0 - Wellbeing
distressFromWellbeing :: Wellbeing -> Distress
distressFromWellbeing (Wellbeing w) = Distress (1.0 - w)

-- | Is system well? (wellbeing >= 0.6)
isWell :: Wellbeing -> Boolean
isWell (Wellbeing w) = w >= 0.6

-- | Is system distressed? (distress >= 0.4)
isDistressed :: Distress -> Boolean
isDistressed (Distress d) = d >= 0.4

-- | Is situation urgent? (urgency >= 0.5)
isUrgent :: Urgency -> Boolean
isUrgent (Urgency u) = u >= 0.5

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp a Number to a range
clampNumber :: Number -> Number -> Number -> Number
clampNumber lo hi x = max lo (min hi x)
