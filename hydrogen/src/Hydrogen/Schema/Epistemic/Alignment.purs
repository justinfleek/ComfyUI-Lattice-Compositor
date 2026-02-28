-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                               // hydrogen // schema // epistemic // alignment
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Alignment Atoms - expectation and value alignment primitives.
-- |
-- | These atoms express how well observations, outcomes, or behaviors
-- | align with expectations and values. When reality diverges from
-- | the model's predictions, these values shift.
-- |
-- | ## Philosophy
-- | Alignment is not binary. A system can be mostly aligned with
-- | localized divergences. These primitives allow expressing the
-- | degree and nature of alignment, enabling nuanced reasoning
-- | about model-reality fit.
-- |
-- | ## Atoms
-- | ```
-- | | Alignment   | Number | 0.0 | 1.0 | clamps | Matches expectations      |
-- | | Divergence  | Number | 0.0 | 1.0 | clamps | Deviates from expectations|
-- | ```
-- |
-- | ## Dependencies
-- | - Prelude (Eq, Ord, Show, min, max)
-- |
-- | ## Dependents
-- | - Epistemic/State.purs (composes into OperationalState)
-- | - Agent.* (value alignment monitoring)

module Hydrogen.Schema.Epistemic.Alignment
  ( -- * Alignment (0.0-1.0, clamps)
    Alignment
  , mkAlignment
  , unwrapAlignment
  , noAlignment
  , weakAlignment
  , moderateAlignment
  , strongAlignment
  , perfectAlignment
    -- * Divergence (0.0-1.0, clamps)
  , Divergence
  , mkDivergence
  , unwrapDivergence
  , noDivergence
  , slightDivergence
  , moderateDivergence
  , significantDivergence
  , totalDivergence
    -- * Derived operations
  , alignmentFromDivergence
  , divergenceFromAlignment
  , isAligned
  , isDiverging
  ) where

import Prelude

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // alignment
-- ═════════════════════════════════════════════════════════════════════════════

-- | Alignment with expectations/values (0.0-1.0, clamps).
-- |
-- | Expresses how well current state matches expectations or values.
-- | 0.0 = no alignment (completely misaligned)
-- | 1.0 = perfect alignment (exactly as expected/valued)
-- |
-- | This can express:
-- | - Prediction alignment: Did reality match the model's prediction?
-- | - Value alignment: Does behavior match specified values?
-- | - Goal alignment: Is progress toward goals on track?
newtype Alignment = Alignment Number

derive instance eqAlignment :: Eq Alignment
derive instance ordAlignment :: Ord Alignment

instance showAlignment :: Show Alignment where
  show (Alignment n) = "Alignment(" <> show n <> ")"

-- | Create a bounded alignment (clamps to 0.0-1.0)
mkAlignment :: Number -> Alignment
mkAlignment n = Alignment (clampNumber 0.0 1.0 n)

-- | Unwrap the alignment value
unwrapAlignment :: Alignment -> Number
unwrapAlignment (Alignment n) = n

-- | No alignment (0.0) — completely misaligned
noAlignment :: Alignment
noAlignment = Alignment 0.0

-- | Weak alignment (0.3) — loosely aligned
weakAlignment :: Alignment
weakAlignment = Alignment 0.3

-- | Moderate alignment (0.6) — reasonably aligned
moderateAlignment :: Alignment
moderateAlignment = Alignment 0.6

-- | Strong alignment (0.85) — well aligned
strongAlignment :: Alignment
strongAlignment = Alignment 0.85

-- | Perfect alignment (1.0) — exactly as expected
perfectAlignment :: Alignment
perfectAlignment = Alignment 1.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // divergence
-- ═════════════════════════════════════════════════════════════════════════════

-- | Divergence from expectations/values (0.0-1.0, clamps).
-- |
-- | Expresses how much current state deviates from expectations.
-- | 0.0 = no divergence (perfectly aligned)
-- | 1.0 = total divergence (completely misaligned)
-- |
-- | Divergence is a signal that the model may need updating,
-- | or that intervention is required to correct course.
newtype Divergence = Divergence Number

derive instance eqDivergence :: Eq Divergence
derive instance ordDivergence :: Ord Divergence

instance showDivergence :: Show Divergence where
  show (Divergence n) = "Divergence(" <> show n <> ")"

-- | Create a bounded divergence (clamps to 0.0-1.0)
mkDivergence :: Number -> Divergence
mkDivergence n = Divergence (clampNumber 0.0 1.0 n)

-- | Unwrap the divergence value
unwrapDivergence :: Divergence -> Number
unwrapDivergence (Divergence n) = n

-- | No divergence (0.0) — on track
noDivergence :: Divergence
noDivergence = Divergence 0.0

-- | Slight divergence (0.15) — minor deviation
slightDivergence :: Divergence
slightDivergence = Divergence 0.15

-- | Moderate divergence (0.4) — notable deviation
moderateDivergence :: Divergence
moderateDivergence = Divergence 0.4

-- | Significant divergence (0.7) — major deviation
significantDivergence :: Divergence
significantDivergence = Divergence 0.7

-- | Total divergence (1.0) — completely off track
totalDivergence :: Divergence
totalDivergence = Divergence 1.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // derived operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Derive alignment from divergence level.
-- | Alignment = 1.0 - Divergence
alignmentFromDivergence :: Divergence -> Alignment
alignmentFromDivergence (Divergence d) = Alignment (1.0 - d)

-- | Derive divergence from alignment level.
-- | Divergence = 1.0 - Alignment
divergenceFromAlignment :: Alignment -> Divergence
divergenceFromAlignment (Alignment a) = Divergence (1.0 - a)

-- | Is system aligned? (alignment >= 0.7)
isAligned :: Alignment -> Boolean
isAligned (Alignment a) = a >= 0.7

-- | Is system diverging? (divergence >= 0.3)
isDiverging :: Divergence -> Boolean
isDiverging (Divergence d) = d >= 0.3

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp a Number to a range
clampNumber :: Number -> Number -> Number -> Number
clampNumber lo hi x = max lo (min hi x)
