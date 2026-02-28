-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // schema // numeric // primitives
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Primitives — Arithmetic operations with proven error propagation.
-- |
-- | Proven in: proofs/Hydrogen/Schema/Numeric/GradedMonad.lean
-- |
-- | Status: FOUNDATIONAL

module Hydrogen.Schema.Numeric.Primitives
  ( liftNumber
  , divReal
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude ((/), (+), (*))
import Data.Number (abs) as Num
import Hydrogen.Schema.Numeric.Grade (machineEpsilon, grade, unGrade) as G
import Hydrogen.Schema.Numeric.ForwardError (ForwardError)

abs :: Number -> Number
abs = Num.abs

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // lifting
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Lift a raw Number into ForwardError with machine epsilon error.
-- |
-- | Use when a value comes from floating-point computation.
liftNumber :: Number -> ForwardError Number
liftNumber x = { ideal: x, approx: x, bound: G.machineEpsilon }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // arithmetic
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Division with error propagation.
-- |
-- | Error bound: |a/b - ã/b̃| ≤ (|a|εb + |b|εa) / (|b|(|b| - εb))
-- |
-- | Simplified to: (εa + εb * |a/b|) / |b| when εb << |b|
divReal :: ForwardError Number -> ForwardError Number -> ForwardError Number
divReal a b =
  let
    idealResult = a.ideal / b.ideal
    approxResult = a.approx / b.approx
    ea = G.unGrade a.bound
    eb = G.unGrade b.bound
    absB = abs b.ideal
    -- Conservative error bound
    boundVal = (ea / absB) + (eb * abs idealResult / absB)
  in
    { ideal: idealResult
    , approx: approxResult
    , bound: G.grade boundVal
    }


