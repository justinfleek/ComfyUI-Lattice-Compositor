-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // layout // constraint // index
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Constraint — Linear constraints for layout verification.
-- |
-- | Proven in: proofs/Hydrogen/Layout/Presburger.lean
-- |
-- | Status: FOUNDATIONAL

module Hydrogen.Layout.Constraint
  ( Var
  , LinTerm
  , linZero
  , linConst
  , linVar
  , linScale
  , linAdd
  , linNeg
  , linSub
  , Rel(..)
  , LinConstraint
  , leZero
  , eqZero
  , geZero
  , le
  , eq
  , ge
  , Formula(..)
  , conj
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude ((*), (+), negate, map, (<>))
import Data.Array (uncons)
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // variables
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Variable identifier for layout constraints.
-- |
-- | Lean: `abbrev Var := String`
type Var = String

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // linear term
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Linear term: c₁x₁ + c₂x₂ + ... + cₙxₙ + k
-- |
-- | Lean: `structure LinTerm where coeffs : List (Var × Int); constant : Int`
type LinTerm =
  { coeffs :: Array (Tuple Var Int)
  , constant :: Int
  }

-- | Zero term.
linZero :: LinTerm
linZero = { coeffs: [], constant: 0 }

-- | Constant term.
linConst :: Int -> LinTerm
linConst k = { coeffs: [], constant: k }

-- | Single variable with coefficient 1.
linVar :: Var -> LinTerm
linVar x = { coeffs: [Tuple x 1], constant: 0 }

-- | Scale a term by integer.
linScale :: Int -> LinTerm -> LinTerm
linScale c t =
  { coeffs: map (\(Tuple x k) -> Tuple x (c * k)) t.coeffs
  , constant: c * t.constant
  }

-- | Add two terms.
linAdd :: LinTerm -> LinTerm -> LinTerm
linAdd t1 t2 =
  { coeffs: t1.coeffs <> t2.coeffs
  , constant: t1.constant + t2.constant
  }

-- | Negate a term.
linNeg :: LinTerm -> LinTerm
linNeg = linScale (-1)

-- | Subtract terms.
linSub :: LinTerm -> LinTerm -> LinTerm
linSub t1 t2 = linAdd t1 (linNeg t2)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // constraint
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Comparison relation.
-- |
-- | Lean: `inductive Rel | eq | le | lt | ge | gt`
data Rel
  = RelEq   -- =
  | RelLe   -- ≤
  | RelLt   -- <
  | RelGe   -- ≥
  | RelGt   -- >

-- | Linear constraint: term `rel` 0
-- |
-- | Example: x + 2y - 10 ≤ 0 means x + 2y ≤ 10
-- |
-- | Lean: `structure Constraint where lhs : LinTerm; rel : Rel`
type LinConstraint =
  { lhs :: LinTerm
  , rel :: Rel
  }

-- | Create constraint: term ≤ 0
leZero :: LinTerm -> LinConstraint
leZero t = { lhs: t, rel: RelLe }

-- | Create constraint: term = 0
eqZero :: LinTerm -> LinConstraint
eqZero t = { lhs: t, rel: RelEq }

-- | Create constraint: term ≥ 0
geZero :: LinTerm -> LinConstraint
geZero t = { lhs: t, rel: RelGe }

-- | Create constraint: t1 ≤ t2
le :: LinTerm -> LinTerm -> LinConstraint
le t1 t2 = leZero (linSub t1 t2)

-- | Create constraint: t1 = t2
eq :: LinTerm -> LinTerm -> LinConstraint
eq t1 t2 = eqZero (linSub t1 t2)

-- | Create constraint: t1 ≥ t2
ge :: LinTerm -> LinTerm -> LinConstraint
ge t1 t2 = geZero (linSub t1 t2)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // formula
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Presburger formula (quantifier-free fragment).
-- |
-- | Lean: `inductive Formula | atom | and | or | not | tt | ff`
data Formula
  = Atom LinConstraint
  | And Formula Formula
  | Or Formula Formula
  | Not Formula
  | Tt   -- true
  | Ff   -- false

-- | Conjunction of constraint list.
conj :: Array LinConstraint -> Formula
conj cs = case uncons cs of
  Nothing -> Tt
  Just { head: c, tail: rest } ->
    case uncons rest of
      Nothing -> Atom c
      Just _ -> And (Atom c) (conj rest)
