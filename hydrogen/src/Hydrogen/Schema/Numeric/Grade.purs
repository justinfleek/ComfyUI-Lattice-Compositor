-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // schema // numeric // grade
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Grade — Non-negative error bound for graded types.
-- |
-- | ## Mathematical Foundation
-- |
-- | Error bounds must be non-negative (ε ≥ 0). This module provides a Grade
-- | type that enforces this invariant by construction.
-- |
-- | ## Lean Proof Reference
-- |
-- | Proven in: proofs/Hydrogen/Schema/Numeric/GradedMonad.lean
-- |
-- | - Grade.add_assoc: (a + b) + c = a + (b + c)
-- | - Grade.add_zero: a + 0 = a
-- | - Grade.zero_add: 0 + a = a
-- |
-- | ## Algebra
-- |
-- | Grades form a commutative monoid under addition:
-- | - Identity: zero (exact computation)
-- | - Operation: addition (error accumulation)
-- |
-- | Grades also support multiplication (for sensitivity scaling).
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Numeric.Grade as G
-- |
-- | -- Create grades (negative values become zero)
-- | eps1 = G.grade 0.001
-- | eps2 = G.grade 0.002
-- |
-- | -- Combine grades
-- | combined = eps1 <> eps2  -- Grade 0.003
-- | ```

module Hydrogen.Schema.Numeric.Grade
  ( -- * Grade Type
    Grade
  , unGrade
    -- * Constructors
  , grade
  , zero
  , machineEpsilon
  , olverEpsilon
    -- * Operations
  , add
  , mul
  , max
    -- * Predicates
  , isZero
  , isExact
  ) where

import Prelude
  ( class Eq
  , class Monoid
  , class Ord
  , class Ring
  , class Semigroup
  , class Semiring
  , class Show
  , compare
  , negate
  , show
  , (+)
  , (*)
  , (-)
  , (/)
  , (<)
  , (<>)
  , (==)
  , (>=)
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // grade type
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Non-negative grade representing an error bound.
-- |
-- | The newtype wrapper ensures grades are always non-negative.
-- | Smart constructor `grade` enforces this invariant.
-- |
-- | ## Invariant
-- |
-- | For all `Grade x`: `x >= 0`
-- |
-- | This is enforced by the smart constructor, not exposed raw constructor.
newtype Grade = Grade Number

-- | Extract the underlying number from a grade.
-- |
-- | Guaranteed to return a non-negative value.
unGrade :: Grade -> Number
unGrade (Grade x) = x

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // instances
-- ═══════════════════════════════════════════════════════════════════════════════

derive instance eqGrade :: Eq Grade

instance ordGrade :: Ord Grade where
  compare (Grade a) (Grade b) = compare a b

instance showGrade :: Show Grade where
  show (Grade x) = "Grade " <> show x

-- | Grades form a semigroup under addition.
-- |
-- | This models error accumulation: when we compose computations,
-- | their errors add.
instance semigroupGrade :: Semigroup Grade where
  append (Grade a) (Grade b) = Grade (a + b)

-- | Grades form a monoid with zero as identity.
-- |
-- | Zero represents exact computation (no error).
instance monoidGrade :: Monoid Grade where
  mempty = zero

-- | Grades form a semiring.
-- |
-- | Addition: error accumulation (sequential composition)
-- | Multiplication: sensitivity scaling
instance semiringGrade :: Semiring Grade where
  add (Grade a) (Grade b) = Grade (a + b)
  zero = Grade 0.0
  mul (Grade a) (Grade b) = Grade (a * b)
  one = Grade 1.0

-- | Grades form a ring (though negative results become zero).
-- |
-- | Subtraction is provided but clamps to zero, preserving non-negativity.
instance ringGrade :: Ring Grade where
  sub (Grade a) (Grade b) = grade (a - b)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // constructors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Smart constructor for grades.
-- |
-- | Negative values are clamped to zero, ensuring the invariant holds.
-- |
-- | ```purescript
-- | grade 0.001  -- Grade 0.001
-- | grade (-5.0) -- Grade 0.0 (clamped)
-- | ```
grade :: Number -> Grade
grade x = if x < 0.0 then Grade 0.0 else Grade x

-- | Zero grade — represents exact computation.
-- |
-- | A computation with grade zero produces no error.
-- | This is the identity for grade addition.
-- |
-- | ## Lean Proof
-- |
-- | `Grade.zero_add: 0 + ε = ε` (proven)
-- | `Grade.add_zero: ε + 0 = ε` (proven)
zero :: Grade
zero = Grade 0.0

-- | Machine epsilon for IEEE binary64 (double precision).
-- |
-- | Value: 2^(-53) ≈ 1.11e-16
-- |
-- | This is the smallest ε such that 1.0 + ε > 1.0 in double precision.
-- | It represents the inherent quantization of floating-point arithmetic.
machineEpsilon :: Grade
machineEpsilon = Grade (pow 2.0 (-53.0))

-- | Olver's epsilon for relative precision analysis.
-- |
-- | Value: u/(1-u) where u = 2^(-53)
-- |
-- | This is the effective relative error bound used in Olver's
-- | model for floating-point arithmetic. For practical purposes,
-- | it's approximately equal to machineEpsilon.
-- |
-- | Reference: Olver, F. W. J. "A New Approach to Error Arithmetic"
olverEpsilon :: Grade
olverEpsilon =
  let u = pow 2.0 (-53.0)
  in Grade (u / (1.0 - u))

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // operations
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Add two grades (error accumulation).
-- |
-- | When computations are composed sequentially, their errors add.
-- |
-- | ## Lean Proof
-- |
-- | `Grade.add_assoc: (a + b) + c = a + (b + c)` (proven)
add :: Grade -> Grade -> Grade
add (Grade a) (Grade b) = Grade (a + b)

-- | Multiply two grades (sensitivity scaling).
-- |
-- | When a function with sensitivity s is applied to a value with
-- | error ε, the output has error s * ε.
mul :: Grade -> Grade -> Grade
mul (Grade a) (Grade b) = Grade (a * b)

-- | Maximum of two grades (parallel composition).
-- |
-- | When computations run in parallel and we take the maximum error.
max :: Grade -> Grade -> Grade
max (Grade a) (Grade b) = if a >= b then Grade a else Grade b

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // predicates
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Check if a grade is exactly zero.
-- |
-- | Zero grade indicates exact computation with no error.
isZero :: Grade -> Boolean
isZero (Grade x) = x == 0.0

-- | Alias for isZero — check if computation is exact.
isExact :: Grade -> Boolean
isExact = isZero

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Power function for Number.
-- |
-- | Used to compute machine epsilon as 2^(-53).
foreign import pow :: Number -> Number -> Number
