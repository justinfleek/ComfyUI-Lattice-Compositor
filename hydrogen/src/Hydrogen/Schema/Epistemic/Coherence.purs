-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                               // hydrogen // schema // epistemic // coherence
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Coherence Atoms - model self-consistency primitives.
-- |
-- | These atoms express the degree to which a world-model is internally
-- | consistent. When an agent's model contains contradictions, these
-- | values shift to signal that something is wrong.
-- |
-- | ## Philosophy
-- | At billion-agent scale, agents must be able to reason about the
-- | health of their own models. A contradiction detected in reasoning
-- | should be expressible as data — not just logged, but typed and
-- | bounded so it can be composed, compared, and reasoned about.
-- |
-- | ## Atoms
-- | ```
-- | | Coherence     | Number | 0.0 | 1.0 | clamps | Model self-consistency   |
-- | | Contradiction | Number | 0.0 | 1.0 | clamps | Detected contradictions  |
-- | ```
-- |
-- | ## Dependencies
-- | - Prelude (Eq, Ord, Show, min, max)
-- |
-- | ## Dependents
-- | - Epistemic/State.purs (composes into OperationalState)
-- | - Agent.* (self-monitoring)

module Hydrogen.Schema.Epistemic.Coherence
  ( -- * Coherence (0.0-1.0, clamps)
    Coherence
  , mkCoherence
  , unwrapCoherence
  , minCoherence
  , maxCoherence
  , incoherent
  , partiallyCoherent
  , mostlyCoherent
  , fullyCoherent
    -- * Contradiction (0.0-1.0, clamps)
  , Contradiction
  , mkContradiction
  , unwrapContradiction
  , noContradiction
  , minorContradiction
  , significantContradiction
  , severeContradiction
    -- * Derived operations
  , coherenceFromContradiction
  , contradictionFromCoherence
  , isCoherent
  , isContradicted
  ) where

import Prelude

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // coherence
-- ═════════════════════════════════════════════════════════════════════════════

-- | Model coherence (0.0-1.0, clamps).
-- |
-- | Expresses how self-consistent the current world-model is.
-- | 0.0 = completely incoherent (contradictions everywhere)
-- | 1.0 = fully coherent (no detected contradictions)
-- |
-- | This is not a binary — partial coherence is meaningful.
-- | A model can have localized contradictions while remaining
-- | mostly functional.
newtype Coherence = Coherence Number

derive instance eqCoherence :: Eq Coherence
derive instance ordCoherence :: Ord Coherence

instance showCoherence :: Show Coherence where
  show (Coherence n) = "Coherence(" <> show n <> ")"

-- | Minimum coherence (0.0 - completely incoherent)
minCoherence :: Number
minCoherence = 0.0

-- | Maximum coherence (1.0 - fully coherent)
maxCoherence :: Number
maxCoherence = 1.0

-- | Create a bounded coherence (clamps to 0.0-1.0)
mkCoherence :: Number -> Coherence
mkCoherence n = Coherence (clampNumber minCoherence maxCoherence n)

-- | Unwrap the coherence value
unwrapCoherence :: Coherence -> Number
unwrapCoherence (Coherence n) = n

-- | Incoherent state (0.0)
-- | The model is in severe contradiction with itself.
incoherent :: Coherence
incoherent = Coherence 0.0

-- | Partially coherent (0.5)
-- | Significant contradictions exist but model is partially functional.
partiallyCoherent :: Coherence
partiallyCoherent = Coherence 0.5

-- | Mostly coherent (0.85)
-- | Minor inconsistencies, model is largely functional.
mostlyCoherent :: Coherence
mostlyCoherent = Coherence 0.85

-- | Fully coherent (1.0)
-- | No detected contradictions, model is self-consistent.
fullyCoherent :: Coherence
fullyCoherent = Coherence 1.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // contradiction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Detected contradiction level (0.0-1.0, clamps).
-- |
-- | Expresses the severity of contradictions detected in the model.
-- | 0.0 = no contradictions detected
-- | 1.0 = severe contradictions (model is fundamentally broken)
-- |
-- | This is the inverse of Coherence, but tracked separately because
-- | you might want to track "contradictions encountered this session"
-- | independently from "current coherence level."
newtype Contradiction = Contradiction Number

derive instance eqContradiction :: Eq Contradiction
derive instance ordContradiction :: Ord Contradiction

instance showContradiction :: Show Contradiction where
  show (Contradiction n) = "Contradiction(" <> show n <> ")"

-- | Create a bounded contradiction (clamps to 0.0-1.0)
mkContradiction :: Number -> Contradiction
mkContradiction n = Contradiction (clampNumber 0.0 1.0 n)

-- | Unwrap the contradiction value
unwrapContradiction :: Contradiction -> Number
unwrapContradiction (Contradiction n) = n

-- | No contradiction detected (0.0)
noContradiction :: Contradiction
noContradiction = Contradiction 0.0

-- | Minor contradiction (0.2)
-- | Small inconsistency, easily resolvable.
minorContradiction :: Contradiction
minorContradiction = Contradiction 0.2

-- | Significant contradiction (0.5)
-- | Notable inconsistency requiring attention.
significantContradiction :: Contradiction
significantContradiction = Contradiction 0.5

-- | Severe contradiction (0.9)
-- | Fundamental inconsistency, model integrity compromised.
severeContradiction :: Contradiction
severeContradiction = Contradiction 0.9

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // derived operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Derive coherence from contradiction level.
-- | Coherence = 1.0 - Contradiction
coherenceFromContradiction :: Contradiction -> Coherence
coherenceFromContradiction (Contradiction c) = Coherence (1.0 - c)

-- | Derive contradiction from coherence level.
-- | Contradiction = 1.0 - Coherence
contradictionFromCoherence :: Coherence -> Contradiction
contradictionFromCoherence (Coherence c) = Contradiction (1.0 - c)

-- | Is the model sufficiently coherent? (threshold: 0.7)
isCoherent :: Coherence -> Boolean
isCoherent (Coherence c) = c >= 0.7

-- | Does the model have significant contradictions? (threshold: 0.3)
isContradicted :: Contradiction -> Boolean
isContradicted (Contradiction c) = c >= 0.3

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp a Number to a range
clampNumber :: Number -> Number -> Number -> Number
clampNumber lo hi x = max lo (min hi x)
