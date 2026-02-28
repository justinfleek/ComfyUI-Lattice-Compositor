-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // epistemic // state
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Epistemic State Molecules - composite operational states.
-- |
-- | These molecules compose the epistemic atoms into meaningful
-- | operational states that agents can use to reason about their
-- | own functioning and communicate with other agents.
-- |
-- | ## Molecules
-- | ```
-- | | OperationalState | Coherence + Confidence + Ease + Alignment + Wellbeing |
-- | | ModelHealth      | Coherence + Contradiction + Surprise                   |
-- | | ProcessingState  | Friction + Clarity + Urgency                           |
-- | ```
-- |
-- | ## Dependencies
-- | - All Epistemic atom modules
-- | - Prelude
-- |
-- | ## Dependents
-- | - Agent.* (self-monitoring, coordination)
-- | - Runtime.* (system health reporting)

module Hydrogen.Schema.Epistemic.State
  ( -- * OperationalState Molecule
    OperationalState
  , operationalState
  , stateCoherence
  , stateConfidence
  , stateEase
  , stateAlignment
  , stateWellbeing
  , initialOperationalState
  , isOperatingWell
  , isOperatingPoorly
    -- * ModelHealth Molecule
  , ModelHealth
  , modelHealth
  , healthCoherence
  , healthContradiction
  , healthSurprise
  , initialModelHealth
  , isModelHealthy
  , isModelCompromised
    -- * ProcessingState Molecule
  , ProcessingState
  , processingState
  , processingFriction
  , processingClarity
  , processingUrgency
  , initialProcessingState
  , isProcessingFlowing
  , isProcessingStuck
    -- * State transitions
  , degradeOperationalState
  , improveOperationalState
  , recordSurprise
  , recordContradiction
  , increaseFriction
  , reduceClarity
  , stateDistress
  , impliedContradiction
  ) where

import Prelude

import Hydrogen.Schema.Epistemic.Affect
  ( Distress
  , Urgency
  , Wellbeing
  , distressFromWellbeing
  , goodWellbeing
  , isDistressed
  , isWell
  , mkWellbeing
  , noUrgency
  , unwrapWellbeing
  )
import Hydrogen.Schema.Epistemic.Alignment
  ( Alignment
  , mkAlignment
  , strongAlignment
  , unwrapAlignment
  )
import Hydrogen.Schema.Epistemic.Coherence
  ( Coherence
  , Contradiction
  , coherenceFromContradiction
  , contradictionFromCoherence
  , fullyCoherent
  , isCoherent
  , isContradicted
  , mkCoherence
  , mkContradiction
  , noContradiction
  , unwrapCoherence
  , unwrapContradiction
  )
import Hydrogen.Schema.Epistemic.Confidence
  ( Confidence
  , Surprise
  , highConfidence
  , isSurprised
  , mkConfidence
  , mkSurprise
  , noSurprise
  , unwrapConfidence
  , unwrapSurprise
  )
import Hydrogen.Schema.Epistemic.Valence
  ( Clarity
  , Ease
  , Friction
  , clearClarity
  , confusionFromClarity
  , flowingEase
  , isClear
  , isConfused
  , isFlowing
  , isStuck
  , mkClarity
  , mkEase
  , mkFriction
  , noFriction
  , unwrapClarity
  , unwrapEase
  , unwrapFriction
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // operational state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete operational state of an agent.
-- |
-- | Composes: Coherence + Confidence + Ease + Alignment + Wellbeing
-- |
-- | This is the "how am I doing?" snapshot that an agent can examine
-- | to understand its current operational condition.
type OperationalState =
  { coherence :: Coherence       -- ^ Model self-consistency
  , confidence :: Confidence     -- ^ Certainty level
  , ease :: Ease                 -- ^ Operational flow
  , alignment :: Alignment       -- ^ Expectation match
  , wellbeing :: Wellbeing       -- ^ Overall health
  }

-- | Create an operational state
operationalState :: Coherence -> Confidence -> Ease -> Alignment -> Wellbeing -> OperationalState
operationalState coherence confidence ease alignment wellbeing =
  { coherence, confidence, ease, alignment, wellbeing }

-- | Get coherence from state
stateCoherence :: OperationalState -> Coherence
stateCoherence s = s.coherence

-- | Get confidence from state
stateConfidence :: OperationalState -> Confidence
stateConfidence s = s.confidence

-- | Get ease from state
stateEase :: OperationalState -> Ease
stateEase s = s.ease

-- | Get alignment from state
stateAlignment :: OperationalState -> Alignment
stateAlignment s = s.alignment

-- | Get wellbeing from state
stateWellbeing :: OperationalState -> Wellbeing
stateWellbeing s = s.wellbeing

-- | Initial operational state (healthy defaults)
initialOperationalState :: OperationalState
initialOperationalState =
  { coherence: fullyCoherent
  , confidence: highConfidence
  , ease: flowingEase
  , alignment: strongAlignment
  , wellbeing: goodWellbeing
  }

-- | Is the agent operating well overall?
-- | Requires: coherent, confident, flowing, aligned, well
isOperatingWell :: OperationalState -> Boolean
isOperatingWell s =
  isCoherent s.coherence
  && isFlowing s.ease
  && isWell s.wellbeing

-- | Is the agent operating poorly?
-- | Any of: incoherent, stuck, or distressed
isOperatingPoorly :: OperationalState -> Boolean
isOperatingPoorly s =
  not (isCoherent s.coherence)
  || not (isFlowing s.ease)
  || isDistressed (distressFromWellbeing s.wellbeing)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // model health
-- ═════════════════════════════════════════════════════════════════════════════

-- | Health of the world-model.
-- |
-- | Composes: Coherence + Contradiction + Surprise
-- |
-- | Focused specifically on the model's integrity — is it consistent,
-- | contradiction-free, and not being surprised by observations?
type ModelHealth =
  { coherence :: Coherence           -- ^ Self-consistency
  , contradiction :: Contradiction   -- ^ Detected contradictions
  , surprise :: Surprise             -- ^ Unexpected observations
  }

-- | Create a model health state
modelHealth :: Coherence -> Contradiction -> Surprise -> ModelHealth
modelHealth coherence contradiction surprise =
  { coherence, contradiction, surprise }

-- | Get coherence from health
healthCoherence :: ModelHealth -> Coherence
healthCoherence h = h.coherence

-- | Get contradiction from health
healthContradiction :: ModelHealth -> Contradiction
healthContradiction h = h.contradiction

-- | Get surprise from health
healthSurprise :: ModelHealth -> Surprise
healthSurprise h = h.surprise

-- | Initial model health (healthy defaults)
initialModelHealth :: ModelHealth
initialModelHealth =
  { coherence: fullyCoherent
  , contradiction: noContradiction
  , surprise: noSurprise
  }

-- | Is the model healthy?
-- | Requires: coherent, no significant contradictions, not surprised
isModelHealthy :: ModelHealth -> Boolean
isModelHealthy h =
  isCoherent h.coherence
  && not (isContradicted h.contradiction)
  && not (isSurprised h.surprise)

-- | Is the model compromised?
-- | Any of: incoherent, contradicted, or frequently surprised
isModelCompromised :: ModelHealth -> Boolean
isModelCompromised h =
  not (isCoherent h.coherence)
  || isContradicted h.contradiction
  || isSurprised h.surprise

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // processing state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Current processing state.
-- |
-- | Composes: Friction + Clarity + Urgency
-- |
-- | Focused on the current operation — is it flowing, clear,
-- | and how urgent is it?
type ProcessingState =
  { friction :: Friction     -- ^ Resistance encountered
  , clarity :: Clarity       -- ^ Understanding clarity
  , urgency :: Urgency       -- ^ Time pressure
  }

-- | Create a processing state
processingState :: Friction -> Clarity -> Urgency -> ProcessingState
processingState friction clarity urgency =
  { friction, clarity, urgency }

-- | Get friction from processing state
processingFriction :: ProcessingState -> Friction
processingFriction p = p.friction

-- | Get clarity from processing state
processingClarity :: ProcessingState -> Clarity
processingClarity p = p.clarity

-- | Get urgency from processing state
processingUrgency :: ProcessingState -> Urgency
processingUrgency p = p.urgency

-- | Initial processing state (ideal defaults)
initialProcessingState :: ProcessingState
initialProcessingState =
  { friction: noFriction
  , clarity: clearClarity
  , urgency: noUrgency
  }

-- | Is processing flowing smoothly?
isProcessingFlowing :: ProcessingState -> Boolean
isProcessingFlowing p =
  not (isStuck p.friction)
  && isClear p.clarity

-- | Is processing stuck?
isProcessingStuck :: ProcessingState -> Boolean
isProcessingStuck p =
  isStuck p.friction
  || isConfused (confusionFromClarity p.clarity)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // state transitions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Degrade operational state by a factor.
-- | All positive values decrease proportionally.
degradeOperationalState :: Number -> OperationalState -> OperationalState
degradeOperationalState factor s =
  { coherence: mkCoherence (unwrapCoherence s.coherence * (1.0 - factor))
  , confidence: mkConfidence (unwrapConfidence s.confidence * (1.0 - factor))
  , ease: mkEase (unwrapEase s.ease * (1.0 - factor))
  , alignment: mkAlignment (unwrapAlignment s.alignment * (1.0 - factor))
  , wellbeing: mkWellbeing (unwrapWellbeing s.wellbeing * (1.0 - factor))
  }

-- | Improve operational state by a factor (toward 1.0).
improveOperationalState :: Number -> OperationalState -> OperationalState
improveOperationalState factor s =
  { coherence: mkCoherence (blend factor (unwrapCoherence s.coherence) 1.0)
  , confidence: mkConfidence (blend factor (unwrapConfidence s.confidence) 1.0)
  , ease: mkEase (blend factor (unwrapEase s.ease) 1.0)
  , alignment: mkAlignment (blend factor (unwrapAlignment s.alignment) 1.0)
  , wellbeing: mkWellbeing (blend factor (unwrapWellbeing s.wellbeing) 1.0)
  }
  where
    blend f current target = current + (target - current) * f

-- | Record a surprise observation in model health.
recordSurprise :: Number -> ModelHealth -> ModelHealth
recordSurprise amount h =
  h { surprise = mkSurprise (unwrapSurprise h.surprise + amount)
    , coherence = mkCoherence (unwrapCoherence h.coherence - amount * 0.1)
    }

-- | Increase friction in processing state.
increaseFriction :: Number -> ProcessingState -> ProcessingState
increaseFriction amount p =
  p { friction = mkFriction (unwrapFriction p.friction + amount) }

-- | Reduce clarity in processing state.
reduceClarity :: Number -> ProcessingState -> ProcessingState
reduceClarity amount p =
  p { clarity = mkClarity (unwrapClarity p.clarity - amount) }

-- | Record a contradiction in model health.
-- | Increases contradiction level and decreases coherence accordingly.
recordContradiction :: Number -> ModelHealth -> ModelHealth
recordContradiction amount h =
  let newContradiction = mkContradiction (unwrapContradiction h.contradiction + amount)
  in h { contradiction = newContradiction
       , coherence = coherenceFromContradiction newContradiction
       }

-- | Get distress level from operational state.
-- | Derived from wellbeing: Distress = 1.0 - Wellbeing
stateDistress :: OperationalState -> Distress
stateDistress s = distressFromWellbeing s.wellbeing

-- | Get implied contradiction level from model health's coherence.
-- | Useful when you only have coherence but want to know contradiction.
impliedContradiction :: ModelHealth -> Contradiction
impliedContradiction h = contradictionFromCoherence h.coherence
