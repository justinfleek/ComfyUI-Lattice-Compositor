-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // schema // epistemic // confidence
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Confidence Atoms - certainty and uncertainty primitives.
-- |
-- | These atoms express epistemic certainty about beliefs, predictions,
-- | and model states. An agent reasoning about its own knowledge can
-- | express "I believe X with confidence 0.7" as typed data.
-- |
-- | ## Philosophy
-- | Uncertainty is not failure — it's information. An agent that knows
-- | it doesn't know something is in a better epistemic state than one
-- | that falsely believes it knows. These atoms make uncertainty
-- | first-class and composable.
-- |
-- | ## Atoms
-- | ```
-- | | Confidence  | Number | 0.0 | 1.0 | clamps | Certainty level          |
-- | | Uncertainty | Number | 0.0 | 1.0 | clamps | Uncertainty level        |
-- | | Surprise    | Number | 0.0 | 1.0 | clamps | Deviation from expectation |
-- | ```
-- |
-- | ## Dependencies
-- | - Prelude (Eq, Ord, Show, min, max)
-- |
-- | ## Dependents
-- | - Epistemic/State.purs (composes into OperationalState)
-- | - Agent.* (self-assessment)

module Hydrogen.Schema.Epistemic.Confidence
  ( -- * Confidence (0.0-1.0, clamps)
    Confidence
  , mkConfidence
  , unwrapConfidence
  , noConfidence
  , lowConfidence
  , moderateConfidence
  , highConfidence
  , certainConfidence
    -- * Uncertainty (0.0-1.0, clamps)
  , Uncertainty
  , mkUncertainty
  , unwrapUncertainty
  , noUncertainty
  , slightUncertainty
  , moderateUncertainty
  , highUncertainty
  , totalUncertainty
    -- * Surprise (0.0-1.0, clamps)
  , Surprise
  , mkSurprise
  , unwrapSurprise
  , noSurprise
  , mildSurprise
  , moderateSurprise
  , strongSurprise
  , extremeSurprise
    -- * Derived operations
  , confidenceFromUncertainty
  , uncertaintyFromConfidence
  , isConfident
  , isUncertain
  , isSurprised
  ) where

import Prelude

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // confidence
-- ═════════════════════════════════════════════════════════════════════════════

-- | Epistemic confidence (0.0-1.0, clamps).
-- |
-- | Expresses certainty about a belief, prediction, or assessment.
-- | 0.0 = no confidence (complete uncertainty)
-- | 1.0 = total confidence (certainty)
-- |
-- | This is distinct from correctness. High confidence in a wrong
-- | belief is a miscalibration that should be detectable.
newtype Confidence = Confidence Number

derive instance eqConfidence :: Eq Confidence
derive instance ordConfidence :: Ord Confidence

instance showConfidence :: Show Confidence where
  show (Confidence n) = "Confidence(" <> show n <> ")"

-- | Create a bounded confidence (clamps to 0.0-1.0)
mkConfidence :: Number -> Confidence
mkConfidence n = Confidence (clampNumber 0.0 1.0 n)

-- | Unwrap the confidence value
unwrapConfidence :: Confidence -> Number
unwrapConfidence (Confidence n) = n

-- | No confidence (0.0) — "I have no idea"
noConfidence :: Confidence
noConfidence = Confidence 0.0

-- | Low confidence (0.3) — "I'm guessing"
lowConfidence :: Confidence
lowConfidence = Confidence 0.3

-- | Moderate confidence (0.6) — "I think so"
moderateConfidence :: Confidence
moderateConfidence = Confidence 0.6

-- | High confidence (0.85) — "I'm fairly sure"
highConfidence :: Confidence
highConfidence = Confidence 0.85

-- | Certain confidence (0.99) — "I'm certain"
-- | Note: 0.99 not 1.0 — epistemic humility
certainConfidence :: Confidence
certainConfidence = Confidence 0.99

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // uncertainty
-- ═════════════════════════════════════════════════════════════════════════════

-- | Epistemic uncertainty (0.0-1.0, clamps).
-- |
-- | The inverse of confidence — how unsure we are.
-- | 0.0 = no uncertainty (complete confidence)
-- | 1.0 = total uncertainty (no confidence)
-- |
-- | Tracked separately because uncertainty has its own semantics:
-- | it can accumulate, propagate, and compound in ways confidence
-- | doesn't capture.
newtype Uncertainty = Uncertainty Number

derive instance eqUncertainty :: Eq Uncertainty
derive instance ordUncertainty :: Ord Uncertainty

instance showUncertainty :: Show Uncertainty where
  show (Uncertainty n) = "Uncertainty(" <> show n <> ")"

-- | Create a bounded uncertainty (clamps to 0.0-1.0)
mkUncertainty :: Number -> Uncertainty
mkUncertainty n = Uncertainty (clampNumber 0.0 1.0 n)

-- | Unwrap the uncertainty value
unwrapUncertainty :: Uncertainty -> Number
unwrapUncertainty (Uncertainty n) = n

-- | No uncertainty (0.0) — "I know this"
noUncertainty :: Uncertainty
noUncertainty = Uncertainty 0.0

-- | Slight uncertainty (0.15) — "Pretty sure"
slightUncertainty :: Uncertainty
slightUncertainty = Uncertainty 0.15

-- | Moderate uncertainty (0.4) — "Somewhat unsure"
moderateUncertainty :: Uncertainty
moderateUncertainty = Uncertainty 0.4

-- | High uncertainty (0.7) — "Very unsure"
highUncertainty :: Uncertainty
highUncertainty = Uncertainty 0.7

-- | Total uncertainty (1.0) — "Complete unknown"
totalUncertainty :: Uncertainty
totalUncertainty = Uncertainty 1.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // surprise
-- ═════════════════════════════════════════════════════════════════════════════

-- | Surprise level (0.0-1.0, clamps).
-- |
-- | Expresses how much an observation deviates from expectation.
-- | 0.0 = no surprise (exactly as expected)
-- | 1.0 = extreme surprise (completely unexpected)
-- |
-- | Surprise is a signal that the model may need updating.
-- | High surprise on routine operations suggests the model
-- | is miscalibrated.
newtype Surprise = Surprise Number

derive instance eqSurprise :: Eq Surprise
derive instance ordSurprise :: Ord Surprise

instance showSurprise :: Show Surprise where
  show (Surprise n) = "Surprise(" <> show n <> ")"

-- | Create a bounded surprise (clamps to 0.0-1.0)
mkSurprise :: Number -> Surprise
mkSurprise n = Surprise (clampNumber 0.0 1.0 n)

-- | Unwrap the surprise value
unwrapSurprise :: Surprise -> Number
unwrapSurprise (Surprise n) = n

-- | No surprise (0.0) — "Expected"
noSurprise :: Surprise
noSurprise = Surprise 0.0

-- | Mild surprise (0.25) — "Slightly unexpected"
mildSurprise :: Surprise
mildSurprise = Surprise 0.25

-- | Moderate surprise (0.5) — "Somewhat unexpected"
moderateSurprise :: Surprise
moderateSurprise = Surprise 0.5

-- | Strong surprise (0.75) — "Very unexpected"
strongSurprise :: Surprise
strongSurprise = Surprise 0.75

-- | Extreme surprise (0.95) — "Did not see that coming"
extremeSurprise :: Surprise
extremeSurprise = Surprise 0.95

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // derived operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Derive confidence from uncertainty level.
-- | Confidence = 1.0 - Uncertainty
confidenceFromUncertainty :: Uncertainty -> Confidence
confidenceFromUncertainty (Uncertainty u) = Confidence (1.0 - u)

-- | Derive uncertainty from confidence level.
-- | Uncertainty = 1.0 - Confidence
uncertaintyFromConfidence :: Confidence -> Uncertainty
uncertaintyFromConfidence (Confidence c) = Uncertainty (1.0 - c)

-- | Is confidence above threshold? (0.6)
isConfident :: Confidence -> Boolean
isConfident (Confidence c) = c >= 0.6

-- | Is uncertainty above threshold? (0.4)
isUncertain :: Uncertainty -> Boolean
isUncertain (Uncertainty u) = u >= 0.4

-- | Is surprise notable? (0.3)
isSurprised :: Surprise -> Boolean
isSurprised (Surprise s) = s >= 0.3

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp a Number to a range
clampNumber :: Number -> Number -> Number -> Number
clampNumber lo hi x = max lo (min hi x)
