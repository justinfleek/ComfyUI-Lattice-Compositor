-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // hydrogen // layout // verify // index
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Verify — Satisfiability checking for layout constraints.
-- |
-- | Uses Fourier-Motzkin elimination for linear arithmetic over rationals.
-- | For integer constraints, this provides a sound (but incomplete) check:
-- | if FM says UNSAT over rationals, then definitely UNSAT over integers.
-- |
-- | ## Why Fourier-Motzkin?
-- |
-- | At billion-agent scale, we need agents to quickly determine:
-- | "Can this layout even fit?" before wasting compute on optimization.
-- |
-- | FM elimination is:
-- | - Complete for linear arithmetic over reals/rationals
-- | - Sound for integers (UNSAT propagates, SAT may be spurious)
-- | - Pure and deterministic (no FFI, no randomness)
-- | - Polynomial in practice for layout constraints
-- |
-- | ## Architecture
-- |
-- | ```
-- | Formula → normalize → eliminateAll → checkFeasibility → VerifyResult
-- | ```
-- |
-- | Status: FOUNDATIONAL

module Hydrogen.Layout.Verify
  ( -- * Verification Result
    VerifyResult(..)
  , Witness
    
    -- * Satisfiability Checking
  , verifySat
  , verifyFormula
  
    -- * Constraint Normalization
  , NormalConstraint
  , normalizeConstraint
  , normalizeFormula
  
    -- * Fourier-Motzkin Elimination
  , eliminate
  , eliminateAll
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , Unit
  , unit
  , otherwise
  , negate
  , ($)
  , (&&)
  , (||)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (<=)
  , (==)
  , (/=)
  , (>)
  , (>=)
  , (<>)
  , (<<<)
  , compare
  , not
  )

import Data.Array (filter, concatMap, null, all, any, sortBy, uncons, length)
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..), fst, snd)
import Data.Foldable (foldl)

import Hydrogen.Layout.Constraint
  ( Var
  , LinTerm
  , LinConstraint
  , Rel(..)
  , Formula(..)
  , linZero
  , linConst
  , linVar
  , linScale
  , linAdd
  , linNeg
  , linSub
  , leZero
  , eqZero
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                        // result
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Witness: variable assignments that satisfy the constraints.
-- | Empty if UNSAT or if we only proved SAT without constructing a witness.
type Witness = Array (Tuple Var Number)

-- | Verification result for constraint satisfiability.
data VerifyResult
  = Sat Witness      -- ^ Satisfiable, with optional witness
  | Unsat            -- ^ Definitely unsatisfiable
  | Unknown          -- ^ Could not determine (e.g., integer constraints)

derive instance eqVerifyResult :: Eq VerifyResult

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // normalized form
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Normalized constraint: Σ aᵢxᵢ ≤ b
-- |
-- | All constraints are converted to this form:
-- | - `t ≤ 0` becomes coefficients with constant on right
-- | - `t ≥ 0` becomes `-t ≤ 0`
-- | - `t = 0` becomes two constraints: `t ≤ 0` and `-t ≤ 0`
-- | - `t < 0` becomes `t + ε ≤ 0` (approximated as `t ≤ -1` for integers)
-- | - `t > 0` becomes `-t < 0`
type NormalConstraint =
  { coeffs :: Array (Tuple Var Number)  -- Variable coefficients
  , bound :: Number                      -- Upper bound (RHS)
  }

-- | Normalize a linear constraint to standard form.
normalizeConstraint :: LinConstraint -> Array NormalConstraint
normalizeConstraint c = case c.rel of
  RelLe -> [toNormal c.lhs]
  RelLt -> [toNormalStrict c.lhs]
  RelGe -> [toNormal (linNeg c.lhs)]
  RelGt -> [toNormalStrict (linNeg c.lhs)]
  RelEq -> [toNormal c.lhs, toNormal (linNeg c.lhs)]
  where
    -- Convert LinTerm to NormalConstraint: Σ aᵢxᵢ + k ≤ 0 → Σ aᵢxᵢ ≤ -k
    toNormal :: LinTerm -> NormalConstraint
    toNormal t =
      { coeffs: toNumberCoeffs t.coeffs
      , bound: negate (toNumber t.constant)
      }
    
    -- Strict inequality: approximate t < 0 as t ≤ -1 (for integer soundness)
    toNormalStrict :: LinTerm -> NormalConstraint
    toNormalStrict t =
      { coeffs: toNumberCoeffs t.coeffs
      , bound: negate (toNumber t.constant) - 1.0
      }
    
    toNumberCoeffs :: Array (Tuple Var Int) -> Array (Tuple Var Number)
    toNumberCoeffs = mapArray (\(Tuple v i) -> Tuple v (toNumber i))

-- | Normalize a formula to conjunction of normalized constraints.
-- |
-- | Note: This flattens the formula, treating Or/Not pessimistically.
-- | For full Boolean satisfiability, we'd need DPLL. This handles
-- | the common case of pure conjunctions.
normalizeFormula :: Formula -> Maybe (Array NormalConstraint)
normalizeFormula formula = case formula of
  Tt -> Just []
  Ff -> Nothing
  Atom c -> Just (normalizeConstraint c)
  And f1 f2 -> case Tuple (normalizeFormula f1) (normalizeFormula f2) of
    Tuple (Just cs1) (Just cs2) -> Just (cs1 <> cs2)
    _ -> Nothing
  Or _ _ -> Nothing   -- Disjunction requires case splitting (not implemented)
  Not _ -> Nothing    -- Negation requires complementation (not implemented)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                      // fourier-motzkin elimination
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Eliminate a single variable from constraints using Fourier-Motzkin.
-- |
-- | Given constraints involving variable x:
-- | - Lower bounds: aᵢx ≤ bᵢ where aᵢ > 0, so x ≤ bᵢ/aᵢ
-- | - Upper bounds: aⱼx ≤ bⱼ where aⱼ < 0, so x ≥ bⱼ/aⱼ
-- |
-- | For each pair (lower, upper), we get: bⱼ/aⱼ ≤ x ≤ bᵢ/aᵢ
-- | Which implies: bⱼ/aⱼ ≤ bᵢ/aᵢ (transitivity constraint)
eliminate :: Var -> Array NormalConstraint -> Array NormalConstraint
eliminate x constraints =
  let
    -- Partition by coefficient sign
    hasX = filter (hasVar x) constraints
    noX = filter (not <<< hasVar x) constraints
    
    -- Upper bounds: coefficient > 0 (x ≤ b/a)
    upper = filter (\c -> getCoeff x c > 0.0) hasX
    
    -- Lower bounds: coefficient < 0 (x ≥ b/a, i.e., -x ≤ -b/a)
    lower = filter (\c -> getCoeff x c < 0.0) hasX
    
    -- Generate transitivity constraints
    transitivity = concatMap (\u -> mapArray (combine x u) lower) upper
  in
    noX <> transitivity

-- | Combine upper and lower bound constraints to eliminate variable.
-- |
-- | Upper: ax ≤ b (a > 0)
-- | Lower: cx ≤ d (c < 0)
-- |
-- | From upper: x ≤ b/a
-- | From lower: x ≥ d/c (since c < 0)
-- |
-- | Combined: d/c ≤ b/a → ad ≤ bc (multiply by ac, note c < 0 flips)
-- | Actually: multiply upper by |c| and lower by a, add them
combine :: Var -> NormalConstraint -> NormalConstraint -> NormalConstraint
combine x upper lower =
  let
    a = getCoeff x upper  -- a > 0
    c = getCoeff x lower  -- c < 0
    
    -- Scale upper by |c| = -c, scale lower by a
    scaledUpper = scaleConstraint (negate c) upper
    scaledLower = scaleConstraint a lower
    
    -- Add them (x terms cancel: a*(-c)*x + (-c)*a*x = 0... wait)
    -- Actually: a*(-c) + c*a = -ac + ac = 0 ✓
    combined = addConstraints scaledUpper scaledLower
  in
    removeVar x combined

-- | Eliminate all variables, returning constraints over constants only.
eliminateAll :: Array NormalConstraint -> Array NormalConstraint
eliminateAll constraints =
  let
    vars = allVars constraints
  in
    foldl (\cs v -> eliminate v cs) constraints vars

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // feasibility check
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Check if constant-only constraints are feasible.
-- |
-- | After eliminating all variables, we have constraints of form: 0 ≤ b
-- | These are feasible iff all b ≥ 0.
checkFeasibility :: Array NormalConstraint -> VerifyResult
checkFeasibility constraints =
  let
    -- All constraints should now be constant-only: 0 ≤ bound
    constantOnly = all (\c -> null c.coeffs) constraints
  in
    if not constantOnly
      then Unknown  -- Should not happen if elimination worked
      else if all (\c -> c.bound >= 0.0) constraints
        then Sat []  -- Feasible (witness construction not implemented)
        else Unsat   -- Some constraint 0 ≤ b with b < 0

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // interface
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Verify satisfiability of a formula.
verifyFormula :: Formula -> VerifyResult
verifyFormula formula = case normalizeFormula formula of
  Nothing -> Unknown  -- Could not normalize (contains Or/Not)
  Just constraints -> verifySat constraints

-- | Verify satisfiability of normalized constraints.
verifySat :: Array NormalConstraint -> VerifyResult
verifySat constraints =
  let
    eliminated = eliminateAll constraints
  in
    checkFeasibility eliminated

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Check if constraint mentions variable.
hasVar :: Var -> NormalConstraint -> Boolean
hasVar x c = any (\(Tuple v _) -> v == x) c.coeffs

-- | Get coefficient of variable in constraint (0 if not present).
getCoeff :: Var -> NormalConstraint -> Number
getCoeff x c = case filter (\(Tuple v _) -> v == x) c.coeffs of
  [Tuple _ coeff] -> coeff
  _ -> 0.0

-- | Scale constraint by factor.
scaleConstraint :: Number -> NormalConstraint -> NormalConstraint
scaleConstraint k c =
  { coeffs: mapArray (\(Tuple v a) -> Tuple v (k * a)) c.coeffs
  , bound: k * c.bound
  }

-- | Add two constraints.
addConstraints :: NormalConstraint -> NormalConstraint -> NormalConstraint
addConstraints c1 c2 =
  { coeffs: c1.coeffs <> c2.coeffs  -- Will merge later
  , bound: c1.bound + c2.bound
  }

-- | Remove variable from constraint (set coefficient to 0, remove from list).
removeVar :: Var -> NormalConstraint -> NormalConstraint
removeVar x c =
  { coeffs: filter (\(Tuple v _) -> v /= x) c.coeffs
  , bound: c.bound
  }

-- | Get all variables from constraints.
allVars :: Array NormalConstraint -> Array Var
allVars constraints =
  let
    allCoeffs = concatMap (\c -> c.coeffs) constraints
    vars = mapArray fst allCoeffs
  in
    uniqueArray vars

-- | Remove duplicates from array (preserves first occurrence).
uniqueArray :: forall a. Eq a => Array a -> Array a
uniqueArray arr = foldl addIfNew [] arr
  where
    addIfNew acc x = if elemArray x acc then acc else acc <> [x]

-- | Check if element is in array.
elemArray :: forall a. Eq a => a -> Array a -> Boolean
elemArray x arr = any (\y -> x == y) arr

-- | Map over array.
mapArray :: forall a b. (a -> b) -> Array a -> Array b
mapArray f = foldl (\acc x -> acc <> [f x]) []

-- | Convert Int to Number.
toNumber :: Int -> Number
toNumber i = toNumberGo i 0.0
  where
    toNumberGo :: Int -> Number -> Number
    toNumberGo n acc
      | n == 0 = acc
      | n > 0 = toNumberGo (n - 1) (acc + 1.0)
      | otherwise = toNumberGo (n + 1) (acc - 1.0)
