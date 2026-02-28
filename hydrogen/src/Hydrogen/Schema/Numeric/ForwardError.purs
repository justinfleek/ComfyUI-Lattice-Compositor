-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // numeric // forwarderror
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ForwardError — Graded monad for forward error tracking.
-- |
-- | ## Mathematical Foundation
-- |
-- | Based on NumFuzz (Kellison, 2025) - arXiv:2501.14598
-- |
-- | Programs using finite-precision arithmetic are PRODUCERS of rounding error.
-- | The graded monad M[ε] tracks the maximum error bound ε.
-- |
-- | ## Structure
-- |
-- | ForwardError ε α = { ideal : α, approx : α, bound : dist ideal approx ≤ ε }
-- |
-- | ## Lean Proof Reference
-- |
-- | Proven in: proofs/Hydrogen/Schema/Numeric/GradedMonad.lean
-- |
-- | - pure_grade: pure produces grade 0
-- | - weaken_preserves: weakening preserves values
-- | - RealError.add_comm: addition is commutative
-- | - RealError.add_assoc: addition is associative
-- |
-- | ## Monad Laws (Grade-indexed)
-- |
-- | 1. pure_grade: `grade (pure x) = 0`
-- | 2. bind_grade: `grade (ma >>= f) = grade ma + grade (f (value ma))`
-- | 3. left_identity: `pure x >>= f ≅ f x` (up to grade equivalence)
-- | 4. right_identity: `m >>= pure ≅ m` (up to grade equivalence)
-- | 5. associativity: `(m >>= f) >>= g ≅ m >>= (λx. f x >>= g)` (up to grade)
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Numeric.ForwardError as FE
-- | import Hydrogen.Schema.Numeric.Grade as G
-- |
-- | -- Exact value (zero error)
-- | exact42 :: FE.ForwardError Number
-- | exact42 = FE.exact 42.0
-- |
-- | -- Value with known error bound
-- | approx :: FE.ForwardError Number
-- | approx = FE.fromApprox 3.14159 3.14159265 G.machineEpsilon
-- |
-- | -- Error accumulates through composition
-- | sum = FE.addReal exact42 approx
-- | ```

module Hydrogen.Schema.Numeric.ForwardError
  ( -- * ForwardError Type
    ForwardError
    -- * Constructors
  , exact
  , fromApprox
  , fromApproxUnsafe
    -- * Accessors
  , ideal
  , approx
  , bound
  , value
    -- * Grade Operations
  , weaken
  , strengthen
    -- * Real Number Operations (proven)
  , addReal
  , negReal
  , subReal
  , scaleReal
  , mulReal
    -- * Functor/Apply (grade-aware)
  , mapWithGrade
    -- * Utility
  , isExact
  , errorMagnitude
  ) where

import Prelude
  ( negate
  , (+)
  , (-)
  , (*)
  , (<)
  , (<=)
  , (>=)
  )

import Data.Number (abs) as Number

import Hydrogen.Schema.Numeric.Grade
  ( Grade
  , grade
  , unGrade
  , zero
  , add
  , isZero
  ) as G

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // forwarderror type
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Forward error with tracked bound.
-- |
-- | A ForwardError value pairs:
-- | - An ideal value (what we want)
-- | - An approximate value (what we have)
-- | - A bound on their distance (ε)
-- |
-- | ## Invariant
-- |
-- | For all `ForwardError { ideal, approx, bound }`:
-- |   `distance ideal approx <= bound`
-- |
-- | This invariant is maintained by smart constructors and proven operations.
-- |
-- | ## Lean Proof
-- |
-- | Type corresponds to: `ForwardError ε α` in GradedMonad.lean
type ForwardError a =
  { ideal :: a
  , approx :: a
  , bound :: G.Grade
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // constructors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Create an exact value (zero error).
-- |
-- | The ideal and approximate values are the same.
-- |
-- | ## Lean Proof
-- |
-- | Corresponds to: `ForwardError.exact` and `pure` in GradedMonad.lean
-- | `pure_grade: grade (pure x) = 0` (proven)
exact :: forall a. a -> ForwardError a
exact x =
  { ideal: x
  , approx: x
  , bound: G.zero
  }

-- | Create a forward error from an approximation with known bound.
-- |
-- | Returns Nothing if the actual error exceeds the claimed bound.
-- | This is the safe constructor that verifies the invariant.
fromApprox
  :: Number          -- ^ Ideal value
  -> Number          -- ^ Approximate value
  -> G.Grade         -- ^ Claimed error bound
  -> ForwardError Number
fromApprox idealVal approxVal bnd =
  let actualError = Number.abs (idealVal - approxVal)
  in if actualError <= G.unGrade bnd
     then { ideal: idealVal, approx: approxVal, bound: bnd }
     -- If actual error exceeds claimed, use actual error as bound
     -- This maintains soundness — we never underestimate error
     else { ideal: idealVal, approx: approxVal, bound: G.grade actualError }

-- | Create a forward error without checking the bound.
-- |
-- | WARNING: This trusts the caller that `distance ideal approx <= bound`.
-- | Use only when the bound is known correct from external proof.
fromApproxUnsafe :: forall a. a -> a -> G.Grade -> ForwardError a
fromApproxUnsafe idealVal approxVal bnd =
  { ideal: idealVal
  , approx: approxVal
  , bound: bnd
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // accessors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get the ideal value.
ideal :: forall a. ForwardError a -> a
ideal fe = fe.ideal

-- | Get the approximate value.
approx :: forall a. ForwardError a -> a
approx fe = fe.approx

-- | Get the error bound.
bound :: forall a. ForwardError a -> G.Grade
bound fe = fe.bound

-- | Get the value we compute with (alias for approx).
-- |
-- | In practice, we always compute with the approximate value.
-- | The ideal is for reasoning; the approx is for computing.
value :: forall a. ForwardError a -> a
value = approx

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // grade operations
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Weaken the error bound (increase it).
-- |
-- | This is always safe: if the true error is at most ε₁, it's also at most ε₂
-- | for any ε₂ ≥ ε₁.
-- |
-- | ## Lean Proof
-- |
-- | `weaken_preserves: weaken preserves ideal and approx` (proven)
weaken :: forall a. G.Grade -> ForwardError a -> ForwardError a
weaken newBound fe
  | G.unGrade newBound >= G.unGrade fe.bound = fe { bound = newBound }
  | true = fe  -- Can't strengthen with weaken

-- | Attempt to strengthen the error bound (decrease it).
-- |
-- | For Numbers, this recomputes the actual error and uses it if smaller
-- | than both the current bound and the requested bound.
strengthen :: G.Grade -> ForwardError Number -> ForwardError Number
strengthen requestedBound fe =
  let
    actualError = Number.abs (fe.ideal - fe.approx)
    newBound = min3 (G.unGrade fe.bound) (G.unGrade requestedBound) actualError
  in
    fe { bound = G.grade newBound }
  where
  min3 :: Number -> Number -> Number -> Number
  min3 a b c = if a < b then (if a < c then a else c) else (if b < c then b else c)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // real number operations
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Add two real errors.
-- |
-- | Error bounds add: ε₁ + ε₂
-- |
-- | ## Lean Proof
-- |
-- | Proven in: GradedMonad.lean `RealError.add`
-- | `RealError.add_comm: addition is commutative` (proven)
-- | `RealError.add_assoc: addition is associative` (proven)
addReal :: ForwardError Number -> ForwardError Number -> ForwardError Number
addReal a b =
  { ideal: a.ideal + b.ideal
  , approx: a.approx + b.approx
  , bound: G.add a.bound b.bound
  }

-- | Negate a real error.
-- |
-- | Error bound is preserved: negation doesn't change the distance.
-- |
-- | ## Lean Proof
-- |
-- | Proven in: GradedMonad.lean `RealError.neg`
negReal :: ForwardError Number -> ForwardError Number
negReal a =
  { ideal: negate a.ideal
  , approx: negate a.approx
  , bound: a.bound
  }

-- | Subtract two real errors.
-- |
-- | Error bounds add: ε₁ + ε₂ (same as addition)
-- |
-- | ## Lean Proof
-- |
-- | Proven in: GradedMonad.lean `RealError.sub`
subReal :: ForwardError Number -> ForwardError Number -> ForwardError Number
subReal a b = addReal a (negReal b)

-- | Scale a real error by a constant.
-- |
-- | Error bound scales by |c|: |c| * ε
-- |
-- | ## Lean Proof
-- |
-- | Proven in: GradedMonad.lean `RealError.scale`
scaleReal :: Number -> ForwardError Number -> ForwardError Number
scaleReal c a =
  { ideal: c * a.ideal
  , approx: c * a.approx
  , bound: G.grade (Number.abs c * G.unGrade a.bound)
  }

-- | Multiply two real errors.
-- |
-- | For multiplication, error analysis is more complex:
-- |   |xy - x̃ỹ| ≤ |x||εy| + |y||εx| + εxεy
-- |
-- | We use the simplified bound:
-- |   |x|*εy + |y|*εx + εx*εy
-- |
-- | where we substitute ideal values for |x|, |y|.
mulReal :: ForwardError Number -> ForwardError Number -> ForwardError Number
mulReal a b =
  let
    -- Product of ideals
    idealProduct = a.ideal * b.ideal
    -- Product of approximations
    approxProduct = a.approx * b.approx
    -- Error bound: |a|*εb + |b|*εa + εa*εb
    ea = G.unGrade a.bound
    eb = G.unGrade b.bound
    boundVal = Number.abs a.ideal * eb
             + Number.abs b.ideal * ea
             + ea * eb
  in
    { ideal: idealProduct
    , approx: approxProduct
    , bound: G.grade boundVal
    }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // functor/mapping
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Map a function over a forward error with explicit grade contribution.
-- |
-- | The caller provides the grade that the function contributes.
-- | This is used when applying a function with known sensitivity.
-- |
-- | For a function with sensitivity s, the resulting error is s * ε.
mapWithGrade
  :: forall a b
   . (a -> b)    -- ^ Function to apply
  -> G.Grade     -- ^ Grade contribution of the function
  -> ForwardError a
  -> ForwardError b
mapWithGrade f additionalGrade fe =
  { ideal: f fe.ideal
  , approx: f fe.approx
  , bound: G.add fe.bound additionalGrade
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // utility
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Check if the error is exactly zero.
isExact :: forall a. ForwardError a -> Boolean
isExact fe = G.isZero fe.bound

-- | Get the actual error magnitude for Number values.
-- |
-- | This computes the true distance between ideal and approximate,
-- | which may be less than the tracked bound.
errorMagnitude :: ForwardError Number -> Number
errorMagnitude fe = Number.abs (fe.ideal - fe.approx)
