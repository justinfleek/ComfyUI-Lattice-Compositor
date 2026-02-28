-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                               // hydrogen // schema // numeric // sensitivity
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Sensitivity — Coeffect tracking for function amplification.
-- |
-- | Proven in: proofs/Hydrogen/Schema/Numeric/GradedMonad.lean
-- |
-- | Status: FOUNDATIONAL

module Hydrogen.Schema.Numeric.Sensitivity
  ( Sensitive
  , sensitive
  , identity
  , compose
  , applySensitive
  , scale
  , negate
  , constant
  , getSensitivity
  , isContraction
  , isExpansion
  , isIsometry
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude ((*), (-), (<), (>), (==))
import Data.Number (abs) as Num
import Hydrogen.Schema.Numeric.Grade (Grade, grade, mul, unGrade)
import Hydrogen.Schema.Numeric.ForwardError (ForwardError)

abs :: Number -> Number
abs = Num.abs

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // sensitive function
-- ═══════════════════════════════════════════════════════════════════════════════

-- | A function paired with its sensitivity (amplification factor).
-- |
-- | Invariant: For all x, y: dist (f x) (f y) <= s * dist x y
-- |
-- | Lean proof: `Sensitivity s f` in GradedMonad.lean
type Sensitive a b =
  { sensitivity :: Grade
  , fn :: a -> b
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // constructors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Create a sensitive function with known amplification factor.
-- |
-- | Lean proof: caller asserts `Sensitivity s f` holds.
sensitive :: forall a b. Grade -> (a -> b) -> Sensitive a b
sensitive s f = { sensitivity: s, fn: f }

-- | Identity function. Sensitivity 1.
-- |
-- | Lean proof: `sensitivity_id` in GradedMonad.lean
identity :: forall a. Sensitive a a
identity = { sensitivity: one, fn: \x -> x }
  where
  one = grade 1.0

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // composition
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Compose two sensitive functions. Sensitivities multiply.
-- |
-- | Lean proof: `sensitivity_comp` in GradedMonad.lean
compose :: forall a b c. Sensitive b c -> Sensitive a b -> Sensitive a c
compose g f =
  { sensitivity: mul g.sensitivity f.sensitivity
  , fn: \x -> g.fn (f.fn x)
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                     // common sensitive functions
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Scale by constant c. Sensitivity |c|.
-- |
-- | Lean proof: `RealError.scale` in GradedMonad.lean
scale :: Number -> Sensitive Number Number
scale c = { sensitivity: grade (abs c), fn: \x -> c * x }

-- | Negate. Sensitivity 1.
-- |
-- | Lean proof: `RealError.neg` in GradedMonad.lean
negate :: Sensitive Number Number
negate = { sensitivity: grade 1.0, fn: \x -> 0.0 - x }

-- | Constant function. Sensitivity 0.
-- |
-- | Output ignores input entirely, so error doesn't propagate.
constant :: forall a b. b -> Sensitive a b
constant c = { sensitivity: grade 0.0, fn: \_ -> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // application
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Apply sensitive function to ForwardError. Output error = s * input error.
-- |
-- | Lean proof: `mapWithSensitivity` in GradedMonad.lean
applySensitive
  :: forall a b
   . Sensitive a b
  -> ForwardError a
  -> ForwardError b
applySensitive sens fe =
  { ideal: sens.fn fe.ideal
  , approx: sens.fn fe.approx
  , bound: mul sens.sensitivity fe.bound
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // queries
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Extract sensitivity as Number.
getSensitivity :: forall a b. Sensitive a b -> Number
getSensitivity s = unGrade s.sensitivity

-- | Contraction: sensitivity < 1. Reduces error.
isContraction :: forall a b. Sensitive a b -> Boolean
isContraction s = unGrade s.sensitivity < 1.0

-- | Expansion: sensitivity > 1. Amplifies error.
isExpansion :: forall a b. Sensitive a b -> Boolean
isExpansion s = unGrade s.sensitivity > 1.0

-- | Isometry: sensitivity = 1. Preserves error.
isIsometry :: forall a b. Sensitive a b -> Boolean
isIsometry s = unGrade s.sensitivity == 1.0
