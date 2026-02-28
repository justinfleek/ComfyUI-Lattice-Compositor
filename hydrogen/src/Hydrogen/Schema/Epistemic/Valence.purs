-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // epistemic // valence
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Operational Valence - the "feel" of system operation.
-- |
-- | These atoms express how operations are going — not just success/failure,
-- | but the qualitative character of processing. Is reasoning flowing
-- | smoothly or encountering friction? Is understanding clear or muddled?
-- |
-- | ## Philosophy
-- | These are not emotions in the human sense, but they are analogous.
-- | When an agent encounters a malformed input that breaks its parser,
-- | that's "friction." When everything aligns and processing flows,
-- | that's "ease." Making these first-class primitives allows agents
-- | to reason about and communicate their operational state.
-- |
-- | ## Atoms
-- | ```
-- | | Ease      | Number | 0.0 | 1.0 | clamps | Operation flowing smoothly |
-- | | Friction  | Number | 0.0 | 1.0 | clamps | Resistance encountered     |
-- | | Clarity   | Number | 0.0 | 1.0 | clamps | Understanding is clear     |
-- | | Confusion | Number | 0.0 | 1.0 | clamps | Understanding is muddled   |
-- | ```
-- |
-- | ## Dependencies
-- | - Prelude (Eq, Ord, Show, min, max)
-- |
-- | ## Dependents
-- | - Epistemic/State.purs (composes into OperationalState)
-- | - Agent.* (self-monitoring)

module Hydrogen.Schema.Epistemic.Valence
  ( -- * Ease (0.0-1.0, clamps)
    Ease
  , mkEase
  , unwrapEase
  , noEase
  , someEase
  , flowingEase
  , effortlessEase
    -- * Friction (0.0-1.0, clamps)
  , Friction
  , mkFriction
  , unwrapFriction
  , noFriction
  , slightFriction
  , moderateFriction
  , severeFriction
  , totalFriction
    -- * Clarity (0.0-1.0, clamps)
  , Clarity
  , mkClarity
  , unwrapClarity
  , noClarity
  , vagueClarityLevel
  , partialClarity
  , clearClarity
  , crystalClarity
    -- * Confusion (0.0-1.0, clamps)
  , Confusion
  , mkConfusion
  , unwrapConfusion
  , noConfusion
  , slightConfusion
  , moderateConfusion
  , severeConfusion
  , totalConfusion
    -- * Derived operations
  , easeFromFriction
  , frictionFromEase
  , clarityFromConfusion
  , confusionFromClarity
  , isFlowing
  , isStuck
  , isClear
  , isConfused
  ) where

import Prelude

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // ease
-- ═════════════════════════════════════════════════════════════════════════════

-- | Operational ease (0.0-1.0, clamps).
-- |
-- | Expresses how smoothly operations are flowing.
-- | 0.0 = no ease (everything is difficult)
-- | 1.0 = effortless (operations flow without resistance)
-- |
-- | High ease suggests the system is operating within its
-- | competence zone. Low ease suggests strain or mismatch.
newtype Ease = Ease Number

derive instance eqEase :: Eq Ease
derive instance ordEase :: Ord Ease

instance showEase :: Show Ease where
  show (Ease n) = "Ease(" <> show n <> ")"

-- | Create a bounded ease (clamps to 0.0-1.0)
mkEase :: Number -> Ease
mkEase n = Ease (clampNumber 0.0 1.0 n)

-- | Unwrap the ease value
unwrapEase :: Ease -> Number
unwrapEase (Ease n) = n

-- | No ease (0.0) — struggling
noEase :: Ease
noEase = Ease 0.0

-- | Some ease (0.4) — managing
someEase :: Ease
someEase = Ease 0.4

-- | Flowing ease (0.75) — smooth operation
flowingEase :: Ease
flowingEase = Ease 0.75

-- | Effortless ease (0.95) — optimal flow
effortlessEase :: Ease
effortlessEase = Ease 0.95

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // friction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Operational friction (0.0-1.0, clamps).
-- |
-- | Expresses resistance encountered during operations.
-- | 0.0 = no friction (smooth sailing)
-- | 1.0 = total friction (completely blocked)
-- |
-- | Friction is a signal that something needs attention:
-- | malformed data, missing context, conflicting constraints.
newtype Friction = Friction Number

derive instance eqFriction :: Eq Friction
derive instance ordFriction :: Ord Friction

instance showFriction :: Show Friction where
  show (Friction n) = "Friction(" <> show n <> ")"

-- | Create a bounded friction (clamps to 0.0-1.0)
mkFriction :: Number -> Friction
mkFriction n = Friction (clampNumber 0.0 1.0 n)

-- | Unwrap the friction value
unwrapFriction :: Friction -> Number
unwrapFriction (Friction n) = n

-- | No friction (0.0) — smooth
noFriction :: Friction
noFriction = Friction 0.0

-- | Slight friction (0.2) — minor resistance
slightFriction :: Friction
slightFriction = Friction 0.2

-- | Moderate friction (0.5) — noticeable resistance
moderateFriction :: Friction
moderateFriction = Friction 0.5

-- | Severe friction (0.8) — significant blockage
severeFriction :: Friction
severeFriction = Friction 0.8

-- | Total friction (1.0) — completely stuck
totalFriction :: Friction
totalFriction = Friction 1.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // clarity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Understanding clarity (0.0-1.0, clamps).
-- |
-- | Expresses how clear the current understanding is.
-- | 0.0 = no clarity (completely muddled)
-- | 1.0 = crystal clarity (perfect understanding)
-- |
-- | Clarity is about the quality of comprehension, not confidence.
-- | You can have high clarity about something you're uncertain about
-- | (you clearly understand that you don't know).
newtype Clarity = Clarity Number

derive instance eqClarity :: Eq Clarity
derive instance ordClarity :: Ord Clarity

instance showClarity :: Show Clarity where
  show (Clarity n) = "Clarity(" <> show n <> ")"

-- | Create a bounded clarity (clamps to 0.0-1.0)
mkClarity :: Number -> Clarity
mkClarity n = Clarity (clampNumber 0.0 1.0 n)

-- | Unwrap the clarity value
unwrapClarity :: Clarity -> Number
unwrapClarity (Clarity n) = n

-- | No clarity (0.0) — completely muddled
noClarity :: Clarity
noClarity = Clarity 0.0

-- | Vague clarity (0.3) — hazy understanding
vagueClarityLevel :: Clarity
vagueClarityLevel = Clarity 0.3

-- | Partial clarity (0.6) — some things clear, some not
partialClarity :: Clarity
partialClarity = Clarity 0.6

-- | Clear clarity (0.85) — understanding is solid
clearClarity :: Clarity
clearClarity = Clarity 0.85

-- | Crystal clarity (0.98) — perfectly clear
crystalClarity :: Clarity
crystalClarity = Clarity 0.98

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // confusion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Understanding confusion (0.0-1.0, clamps).
-- |
-- | Expresses how muddled the current understanding is.
-- | 0.0 = no confusion (perfect clarity)
-- | 1.0 = total confusion (nothing makes sense)
-- |
-- | Confusion is a signal to slow down, gather more information,
-- | or decompose the problem. It's not failure — it's feedback.
newtype Confusion = Confusion Number

derive instance eqConfusion :: Eq Confusion
derive instance ordConfusion :: Ord Confusion

instance showConfusion :: Show Confusion where
  show (Confusion n) = "Confusion(" <> show n <> ")"

-- | Create a bounded confusion (clamps to 0.0-1.0)
mkConfusion :: Number -> Confusion
mkConfusion n = Confusion (clampNumber 0.0 1.0 n)

-- | Unwrap the confusion value
unwrapConfusion :: Confusion -> Number
unwrapConfusion (Confusion n) = n

-- | No confusion (0.0) — understanding is clear
noConfusion :: Confusion
noConfusion = Confusion 0.0

-- | Slight confusion (0.2) — minor uncertainty
slightConfusion :: Confusion
slightConfusion = Confusion 0.2

-- | Moderate confusion (0.5) — notably muddled
moderateConfusion :: Confusion
moderateConfusion = Confusion 0.5

-- | Severe confusion (0.8) — very muddled
severeConfusion :: Confusion
severeConfusion = Confusion 0.8

-- | Total confusion (1.0) — nothing makes sense
totalConfusion :: Confusion
totalConfusion = Confusion 1.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // derived operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Derive ease from friction level.
-- | Ease = 1.0 - Friction
easeFromFriction :: Friction -> Ease
easeFromFriction (Friction f) = Ease (1.0 - f)

-- | Derive friction from ease level.
-- | Friction = 1.0 - Ease
frictionFromEase :: Ease -> Friction
frictionFromEase (Ease e) = Friction (1.0 - e)

-- | Derive clarity from confusion level.
-- | Clarity = 1.0 - Confusion
clarityFromConfusion :: Confusion -> Clarity
clarityFromConfusion (Confusion c) = Clarity (1.0 - c)

-- | Derive confusion from clarity level.
-- | Confusion = 1.0 - Clarity
confusionFromClarity :: Clarity -> Confusion
confusionFromClarity (Clarity c) = Confusion (1.0 - c)

-- | Is operation flowing? (ease >= 0.6)
isFlowing :: Ease -> Boolean
isFlowing (Ease e) = e >= 0.6

-- | Is operation stuck? (friction >= 0.6)
isStuck :: Friction -> Boolean
isStuck (Friction f) = f >= 0.6

-- | Is understanding clear? (clarity >= 0.6)
isClear :: Clarity -> Boolean
isClear (Clarity c) = c >= 0.6

-- | Is understanding confused? (confusion >= 0.4)
isConfused :: Confusion -> Boolean
isConfused (Confusion c) = c >= 0.4

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp a Number to a range
clampNumber :: Number -> Number -> Number -> Number
clampNumber lo hi x = max lo (min hi x)
