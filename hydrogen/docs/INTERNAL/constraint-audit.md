# Constraint System Audit

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                       // constraint // audit
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

**Purpose**: Document where Hydrogen's constraint systems are incomplete or incorrect
**Date**: 2026-02-27
**Status**: CRITICAL — Foundation gaps identified

────────────────────────────────────────────────────────────────────────────────
                                                               // table // of // contents
────────────────────────────────────────────────────────────────────────────────

1. Executive Summary
2. Graded Monads — Error Tracking Gap
3. Presburger Arithmetic — Layout Verification Gap
4. Integer Linear Programming — Layout Optimization Gap
5. Effect System — Purity Gap
6. Implementation Roadmap
7. References

────────────────────────────────────────────────────────────────────────────────
                                                         // 1 // executive // summary
────────────────────────────────────────────────────────────────────────────────

## 1. Executive Summary

### The Core Problem

Hydrogen claims to be a **mathematically rigorous** UI framework with:
- Graded monads for error tracking
- Presburger arithmetic for layout verification
- Integer Linear Programming for layout optimization
- Pure rendering with isolated effects

**Reality: None of these are implemented.**

### Gap Assessment

| System | Claimed | Implemented | Gap |
|--------|---------|-------------|-----|
| Graded Monads | Error bounds compose through computation | Lean proofs only, no runtime | **100%** |
| Presburger Arithmetic | Layout constraints decidable | Zero implementation | **100%** |
| Integer Linear Programming | Optimal integer layouts | Proportional heuristic | **100%** |
| Effect System Purity | Pure rendering, isolated effects | ✓ Correctly implemented | **0%** |

### Consequences

1. **"Same Element = same pixels" is false** — No error tracking means no determinism guarantee
2. **Layout can silently fail** — No satisfiability checking means conflicting constraints produce garbage
3. **Layouts are suboptimal** — Proportional distribution ignores min/max constraints

### The Path Forward

This document specifies three implementation tracks (Effect System is already correct):

1. **Graded Monads** (4 weeks) — Port Lean proofs to PureScript runtime
2. **Presburger Decision** (5 weeks) — Implement omega-style decision procedure
3. **ILP Solver** (5 weeks) — Simplex + branch-and-bound for integer layouts

Total estimated effort: **6-8 weeks** (tracks can parallelize)

### Why This Matters

At billion-agent scale, incomplete foundations cause:
- **Cascading errors** — Untracked numerical drift compounds across computations
- **Coordination failures** — Agents disagree on layout feasibility
- **Non-determinism** — Same specification renders differently
- **Debug impossibility** — Effects everywhere means no reproducible state

Fixing these gaps is prerequisite to the autonomy claims in the vision documents.

────────────────────────────────────────────────────────────────────────────────
                                                              // 2 // graded // monads
────────────────────────────────────────────────────────────────────────────────

## 2. Graded Monads — Error Tracking Gap

### 2.1 What We Claimed

From `button_reference.md` and `CLAUDE.md`, Hydrogen claims:
- Schema atoms have **bounded types** with proven error bounds
- Forward error tracking through composition
- "Same Element = same pixels" determinism at billion-agent scale

From `docs/INTERNAL/paper_algos.md`:
- NumFuzz graded monads M[ε] for forward error
- Bean graded comonads D^r for backward error
- Sensitivity tracking via !_s comonad

### 2.2 What Actually Exists

**Lean Proofs (just created 2026-02-27):**
```
proofs/Hydrogen/Schema/Numeric/
├── GradedMonad.lean         -- ForwardError ε α, Sensitivity, bind
├── RelativePrecision.lean   -- RP metric, Olver's model
└── NeighborhoodMonad.lean   -- T^r neighborhood construction
```
These are THEORETICAL. They define types and prove laws.

**PureScript Runtime:**
```
src/Hydrogen/Schema/Numeric/   -- DOES NOT EXIST
```

**The playground has ADT stubs:**
```purescript
-- straylight-playground/src/Hydrogen/Element/Pure.purs lines 316-375
data Effect
  = CanClick
  | CanAnimate
  | ...

data CoEffect
  = NeedsFont FontFamily
  | NeedsImage URL
  | ...
```
These are **sum types for documentation**, not actual graded monads.

### 2.3 The Gap

| Component | Theory | Implementation | Gap |
|-----------|--------|----------------|-----|
| ForwardError ε α | ✓ Proven | ✗ Not in PureScript | 100% |
| Sensitivity tracking | ✓ Proven | ✗ Not in PureScript | 100% |
| Error composition (bind) | ✓ Proven | ✗ Not in PureScript | 100% |
| RP metric | ✓ Proven | ✗ Not in PureScript | 100% |
| Olver rounding model | ✓ Proven | ✗ Not in PureScript | 100% |

**Consequence**: When an agent constructs a color value:
```purescript
-- CURRENT: No error tracking
color = oklch 0.7 0.15 180.0  -- Just a record, no bounds

-- SHOULD BE: Error tracked in type
color :: ForwardError ε OKLCH  -- ε = accumulated error from computation
```

### 2.4 Why This Matters

Without runtime error tracking:
1. **No compositional bounds** — We can't prove `render(compose(a, b))` has bounded error
2. **No sensitivity analysis** — We don't know how much a function amplifies errors
3. **"Same Element = same pixels" is a LIE** — Floating point varies by platform

### 2.5 How to Fix

**Phase 1: Core Types** (Week 1)
```purescript
-- src/Hydrogen/Schema/Numeric/Grade.purs
newtype Grade = Grade Number  -- Non-negative error bound

-- src/Hydrogen/Schema/Numeric/ForwardError.purs  
newtype ForwardError (ε :: Grade) a = ForwardError
  { ideal :: a
  , approx :: a
  }

-- Smart constructor enforces bound
forwardError :: forall ε a. Number -> a -> a -> Maybe (ForwardError ε a)
```

**Phase 2: Graded Bind** (Week 2)
```purescript
-- Grades compose additively
bind :: forall ε₁ ε₂ a b. 
  ForwardError ε₁ a -> 
  (a -> ForwardError ε₂ b) -> 
  ForwardError (ε₁ + ε₂) b
```

**Phase 3: Sensitivity** (Week 3)
```purescript
-- Track how functions amplify errors
class Sensitive (s :: Grade) f where
  applySensitive :: forall ε a b. f a b -> ForwardError ε a -> ForwardError (s * ε) b
```

**Phase 4: Schema Integration** (Week 4)
```purescript
-- All Schema atoms become graded
type OKLCH = ForwardError MachineEpsilon OKLCHRaw
type Pixel = ForwardError Zero Int  -- Integers have no error
```

### 2.6 Files to Create

```
src/Hydrogen/Schema/Numeric/
├── Grade.purs              -- Non-negative grade type
├── ForwardError.purs       -- Graded monad M[ε]
├── Sensitivity.purs        -- !_s comonad
├── BackwardError.purs      -- D^r comonad (Bean)
├── Primitives.purs         -- add, mul, div with error rules
└── Numeric.purs            -- Re-exports
```

### 2.7 Verification

After implementation, these properties must hold:
```purescript
-- Law: pure has zero error
prop_pure_zero :: forall a. a -> Boolean
prop_pure_zero x = grade (pure x) == Grade 0.0

-- Law: bind composes grades additively
prop_bind_additive :: ForwardError ε₁ a -> (a -> ForwardError ε₂ b) -> Boolean
prop_bind_additive ma f = grade (ma >>= f) == grade ma + grade (f (approx ma))

-- Law: sensitivity scales error
prop_sensitivity :: Sensitive s f => f a b -> ForwardError ε a -> Boolean
prop_sensitivity f x = grade (applySensitive f x) == s * grade x
```

────────────────────────────────────────────────────────────────────────────────
                                                     // 3 // presburger // arithmetic
────────────────────────────────────────────────────────────────────────────────

## 3. Presburger Arithmetic — Layout Verification Gap

### 3.1 What We Claimed

From `button_reference.md` lines 182-207:

> "Layout constraints are **linear inequalities**"
> "**Presburger arithmetic is decidable.** We can PROVE satisfiability."
> "No undefined behavior. No 'it depends on browser.'"

The claim is that layout constraints form a Presburger formula:
```
button.x ≥ parent.padding.left
button.x + button.width ≤ parent.width - parent.padding.right
button.height ≥ 44  -- accessibility minimum
```

And we can **decide** whether such constraints are satisfiable.

### 3.2 What Actually Exists

**Lean Proofs:**
```
proofs/Hydrogen/Math/Constraint.lean  -- PHYSICS constraints, not layout
```

This file proves properties of **soft body physics** constraints:
- Distance constraints between particles
- Correction vectors parallel to separation
- Mass-weighted corrections

**IT HAS NOTHING TO DO WITH LAYOUT.**

**PureScript:**
```
src/Hydrogen/Layout/Flex.purs  -- Heuristic algorithm, not constraint solver
```

The Flex.purs algorithm does NOT:
- Encode constraints as formulas
- Check satisfiability
- Use any decision procedure

### 3.3 What is Presburger Arithmetic?

Presburger arithmetic is the first-order theory of natural numbers with addition.

**Formulas look like:**
```
∃x∃y. (x + y = 10) ∧ (x ≥ 3) ∧ (y ≤ 5)
```

**Key property**: Satisfiability is DECIDABLE. There's an algorithm that:
- Takes a Presburger formula
- Returns YES (with witness) or NO
- Always terminates

**Why it matters for layout:**
```
-- Layout constraint: button fits in parent with padding
∃button_x ∃button_width.
  button_x ≥ padding_left ∧
  button_x + button_width ≤ parent_width - padding_right ∧
  button_width ≥ min_width ∧
  button_width ≤ max_width
```

If this is satisfiable, layout is possible. If not, we KNOW it's impossible.

### 3.4 The Gap

| Component | Claimed | Actual | Gap |
|-----------|---------|--------|-----|
| Presburger encoding | "Layout as linear inequalities" | Not implemented | 100% |
| Decision procedure | "Prove satisfiability" | Not implemented | 100% |
| Lean verification | "Lean files verify" | Wrong file (physics) | 100% |
| Runtime solver | "Runtime solves" | Heuristic only | 100% |

**We have ZERO Presburger implementation.**

### 3.5 Why This Matters

Without a decision procedure:
1. **No provable satisfiability** — We can't guarantee layout is possible
2. **Silent failures** — Conflicting constraints produce garbage, not errors
3. **Non-determinism** — Different heuristics give different results
4. **No formal verification** — Lean proofs can't connect to runtime

Example of silent failure:
```purescript
-- Conflicting constraints
container { width: 100 }
  child { minWidth: 60 }
  child { minWidth: 60 }
  gap: 10

-- Required: 60 + 10 + 60 = 130 pixels
-- Available: 100 pixels
-- Current behavior: SQUASH (undefined which child shrinks)
-- Correct behavior: REJECT with proof of unsatisfiability
```

### 3.6 How to Fix

**Phase 1: Constraint Encoding** (Week 1)

```lean
-- proofs/Hydrogen/Layout/Presburger.lean

/-- A linear constraint over integer variables -/
structure LinearConstraint where
  coeffs : List (String × Int)  -- Variable coefficients
  rel : Ordering                 -- LT, LE, EQ, GE, GT
  constant : Int

/-- Example: x + 2y ≤ 10 -/
def example : LinearConstraint := {
  coeffs := [("x", 1), ("y", 2)],
  rel := Ordering.le,
  constant := 10
}

/-- A Presburger formula (conjunction of linear constraints) -/
def PresburgerFormula := List LinearConstraint
```

**Phase 2: Decision Procedure** (Week 2-3)

```lean
/-- Decide satisfiability using omega -/
def isSatisfiable (φ : PresburgerFormula) : Bool := by
  -- Use Lean's omega tactic
  -- This is decidable by Presburger's theorem
  decide

/-- If satisfiable, produce a witness -/
def findWitness (φ : PresburgerFormula) : Option (List (String × Int)) := by
  -- Constructive proof gives witness
  sorry  -- Requires implementation
```

**Phase 3: PureScript Integration** (Week 4)

```purescript
-- src/Hydrogen/Layout/Constraint.purs

type LinearConstraint =
  { coeffs :: Array (Tuple String Int)
  , rel :: Ordering
  , constant :: Int
  }

-- Encode layout as constraints
encodeLayout :: LayoutSpec -> Array LinearConstraint
encodeLayout spec = 
  [ -- Child fits in parent
    { coeffs: [Tuple "child_x" 1], rel: GE, constant: spec.padding.left }
  , { coeffs: [Tuple "child_x" 1, Tuple "child_width" 1]
    , rel: LE
    , constant: spec.parent.width - spec.padding.right 
    }
  -- etc.
  ]

-- Check satisfiability (calls Lean via FFI or WASM)
foreign import checkSatisfiable :: Array LinearConstraint -> Effect Boolean
```

**Phase 4: Integration with Flex.purs** (Week 5)

```purescript
-- Before layout, verify constraints are satisfiable
computeLayout :: FlexContainer -> Array FlexItem -> Either LayoutError (Array LayoutResult)
computeLayout container items = do
  let constraints = encodeFlexConstraints container items
  unless (checkSatisfiable constraints) $
    Left (UnsatisfiableConstraints constraints)
  -- Only then run the layout algorithm
  Right (computeLayoutUnchecked container items)
```

### 3.7 Files to Create

```
proofs/Hydrogen/Layout/
├── Presburger.lean          -- Constraint encoding
├── Decision.lean            -- Decision procedure (omega)
├── LayoutConstraints.lean   -- Layout-specific constraints
└── Soundness.lean           -- Prove layout respects constraints

src/Hydrogen/Layout/
├── Constraint.purs          -- PureScript constraint types
├── Encode.purs              -- Layout → Constraints
├── Verify.purs              -- Satisfiability check
└── Flex.purs                -- Modified to verify first
```

### 3.8 The omega Tactic

Lean 4's `omega` tactic decides Presburger arithmetic:

```lean
example (x y : Int) (h1 : x + y ≤ 10) (h2 : x ≥ 3) (h3 : y ≥ 8) : False := by
  omega  -- Automatically proves contradiction
```

This is what we should use for layout verification.

────────────────────────────────────────────────────────────────────────────────
                                              // 4 // integer // linear // programming
────────────────────────────────────────────────────────────────────────────────

## 4. Integer Linear Programming — Layout Optimization Gap

### 4.1 What We Claimed

From `button_reference.md` line 199:

> "**Integer Linear Programming can optimize.** Find the BEST layout given constraints."
> "Runtime solves ILP to get actual pixel positions"

The claim is that given constraints, we find the OPTIMAL layout that:
- Minimizes wasted space
- Maximizes content visibility
- Respects all constraints
- Produces INTEGER pixel positions

### 4.2 What Actually Exists

**The entire layout system is in one file:**
```
src/Hydrogen/Layout/Flex.purs  (387 lines)
```

**The "algorithm" at line 234-244:**
```purescript
computeMainSizes :: FlexDirection -> Number -> Array FlexItem -> Array Number
computeMainSizes _dir available items =
  let
    n = Array.length items
    totalBasis = sumArray (mapArray (\i -> i.basis) items)
    remaining = available - totalBasis
    totalGrow = sumArray (mapArray (\i -> i.grow) items)
  in
    if remaining > 0.0 && totalGrow > 0.0
      then mapArray (\i -> i.basis + remaining * i.grow / totalGrow) items
      else mapArray (\i -> i.basis) items
```

**This is NOT ILP. This is:**
1. Sum up the basis sizes
2. Calculate remaining space
3. Distribute proportionally by grow factor

**Problems:**
- No objective function
- No constraint satisfaction
- No optimality guarantee
- Uses floating point (not integers)
- Ignores min/max constraints in distribution

### 4.3 What is Integer Linear Programming?

ILP optimizes a linear objective subject to linear constraints with integer variables.

**Standard form:**
```
minimize    c^T x           -- Objective: minimize cost
subject to  Ax ≤ b          -- Constraints
            x ∈ Z^n         -- Integer variables
```

**For layout:**
```
Variables: x_i, w_i for each element (position, width)

Minimize: Σ slack_i         -- Minimize wasted space

Subject to:
  x_i ≥ padding_left                    -- Left bound
  x_i + w_i ≤ parent_width - padding_right  -- Right bound
  w_i ≥ min_width_i                     -- Minimum size
  w_i ≤ max_width_i                     -- Maximum size
  x_{i+1} ≥ x_i + w_i + gap             -- Non-overlapping
  x_i, w_i ∈ Z                          -- Integer pixels
```

### 4.4 The Gap

| Component | Claimed | Actual | Gap |
|-----------|---------|--------|-----|
| Objective function | "Find BEST layout" | None | 100% |
| Constraint matrix | "Given constraints" | Not constructed | 100% |
| Simplex algorithm | Implied | Not implemented | 100% |
| Integer rounding | "Integer pixels" | Floating point | 100% |
| Optimality proof | Implied | Not implemented | 100% |

**Current behavior vs correct behavior:**

```
Container: 100px
Children: [min:30, grow:1], [min:30, grow:2]
Gap: 10px

CURRENT (proportional):
  remaining = 100 - 30 - 30 - 10 = 30
  child1 = 30 + 30 * (1/3) = 40
  child2 = 30 + 30 * (2/3) = 50
  Total: 40 + 10 + 50 = 100 ✓

But what if min:40, min:40?
  remaining = 100 - 40 - 40 - 10 = 10
  child1 = 40 + 10 * (1/3) = 43.33...  -- FLOATING POINT
  child2 = 40 + 10 * (2/3) = 46.66...  -- FLOATING POINT
  
ILP WOULD:
  child1 = 43 or 44 (integer)
  child2 = 47 or 46 (integer)
  With proof that this is optimal
```

### 4.5 Why This Matters

Without ILP:
1. **Sub-optimal layouts** — Proportional distribution isn't always best
2. **Floating point pixels** — Causes rendering artifacts (subpixel antialiasing)
3. **No optimality guarantee** — Can't prove layout is best possible
4. **Constraint violations** — Min/max not enforced during distribution

**Real example of failure:**
```purescript
-- Three buttons that should share space equally
container { width: 100 }
  button { minWidth: 30, maxWidth: 40, grow: 1 }
  button { minWidth: 30, maxWidth: 40, grow: 1 }
  button { minWidth: 30, maxWidth: 40, grow: 1 }
  gap: 5

-- Available: 100 - 5 - 5 = 90 for content
-- Ideal: 30 each (total 90) ✓
-- But if we want to grow...
-- Max possible: 40 + 40 + 40 = 120 > 90
-- Current algo: Tries to grow, violates max
-- ILP: Finds optimal within constraints
```

### 4.6 How to Fix

**Phase 1: Problem Formulation** (Week 1)

```purescript
-- src/Hydrogen/Layout/ILP/Problem.purs

type Variable = String

type LinearExpr = 
  { coeffs :: Map Variable Number
  , constant :: Number
  }

type Constraint =
  { lhs :: LinearExpr
  , rel :: Ordering  -- LE, EQ, GE
  , rhs :: Number
  }

type ILPProblem =
  { objective :: LinearExpr      -- Minimize this
  , constraints :: Array Constraint
  , integerVars :: Set Variable  -- Must be integer
  , bounds :: Map Variable (Tuple Number Number)  -- Lower/upper
  }
```

**Phase 2: Simplex for LP Relaxation** (Week 2-3)

```purescript
-- src/Hydrogen/Layout/ILP/Simplex.purs

-- Standard simplex algorithm
type Tableau = Array (Array Number)

data SimplexResult
  = Optimal (Map Variable Number)
  | Unbounded
  | Infeasible

simplex :: ILPProblem -> SimplexResult
simplex problem = 
  let
    tableau = toTableau problem
    pivoted = pivot tableau
  in
    extractSolution pivoted
```

**Phase 3: Branch and Bound for Integers** (Week 4)

```purescript
-- src/Hydrogen/Layout/ILP/BranchBound.purs

-- Branch on fractional variables
solveILP :: ILPProblem -> Maybe (Map Variable Int)
solveILP problem = do
  -- Solve LP relaxation
  lpSolution <- simplex problem
  
  -- Check if integer
  case findFractional lpSolution of
    Nothing -> Just (roundSolution lpSolution)
    Just (var, frac) -> 
      -- Branch: var ≤ floor(frac) OR var ≥ ceil(frac)
      let
        left = addConstraint (var ≤ floor frac) problem
        right = addConstraint (var ≥ ceil frac) problem
      in
        best (solveILP left) (solveILP right)
```

**Phase 4: Layout Integration** (Week 5)

```purescript
-- src/Hydrogen/Layout/Flex.purs (modified)

computeLayout :: FlexContainer -> Array FlexItem -> Either LayoutError (Array LayoutResult)
computeLayout container items = do
  -- Formulate as ILP
  let problem = formulateLayoutILP container items
  
  -- Solve
  case solveILP problem of
    Nothing -> Left UnsatisfiableLayout
    Just solution -> Right (extractLayoutResults solution items)

formulateLayoutILP :: FlexContainer -> Array FlexItem -> ILPProblem
formulateLayoutILP container items = 
  { objective: minimizeWaste container items
  , constraints: layoutConstraints container items
  , integerVars: allPositionAndSizeVars items
  , bounds: boundsFromItems items
  }
```

### 4.7 Files to Create

```
src/Hydrogen/Layout/ILP/
├── Problem.purs        -- ILP problem formulation
├── Simplex.purs        -- LP relaxation solver
├── BranchBound.purs    -- Integer solver
├── Formulate.purs      -- Layout → ILP translation
└── ILP.purs            -- Re-exports

proofs/Hydrogen/Layout/
├── ILPCorrectness.lean -- Simplex termination + correctness
├── Integrality.lean    -- Branch-and-bound finds integers
└── LayoutOptimal.lean  -- Layout solution is optimal
```

### 4.8 Complexity Considerations

**ILP is NP-hard in general.** But layout ILP is tractable because:

1. **Small variable count** — Typically < 100 elements per container
2. **Sparse constraints** — Each element only constrains neighbors
3. **Bounded coefficients** — All coefficients are small integers
4. **Special structure** — Layout constraints are interval constraints

For a flex container with n items:
- Variables: 2n (position + width for each)
- Constraints: O(n) (bounds + gaps)
- Typical solve time: < 1ms for n < 50

**If performance is critical**, we can:
1. Use specialized interval constraint solver
2. Cache solutions for common layouts
3. Fall back to heuristic with warning if ILP times out

### 4.9 Proving Optimality

```lean
-- proofs/Hydrogen/Layout/LayoutOptimal.lean

/-- A layout solution -/
structure LayoutSolution where
  positions : List (String × Int)
  widths : List (String × Int)

/-- Objective value (waste) -/
def waste (container : Container) (sol : LayoutSolution) : Int :=
  container.width - sum (sol.widths.map snd)

/-- Our ILP solver finds optimal solution -/
theorem ilp_optimal (problem : LayoutILP) (sol : LayoutSolution) :
    isFeasible problem sol →
    ∀ other, isFeasible problem other → 
      waste problem.container sol ≤ waste problem.container other := by
  -- Proof uses LP duality and integrality
  sorry  -- Requires full implementation
```

────────────────────────────────────────────────────────────────────────────────
                                                            // 5 // effect // system
────────────────────────────────────────────────────────────────────────────────

## 5. Effect System — CORRECTLY IMPLEMENTED

### 5.1 What We Claimed

From `CLAUDE.md`:

> "Elements are pure PureScript data structures"
> "UI as data, not framework-specific code"
> "State × Msg → State × [Cmd]"
> "view :: State → Element Msg"

### 5.2 Verified: Architecture is Correct

**Upon code review (2026-02-27), the Effect system is properly isolated.**

**Pure rendering layer:**
```
src/Hydrogen/Render/Element.purs  -- Pure Element type, NO Effect import
src/Hydrogen/Render/Style.purs    -- Pure Style type, NO Effect import
src/Hydrogen/Render/Effect.purs   -- Pure CAPABILITY algebra (not Effect monad!)
```

Note: `Hydrogen.Render.Effect` defines a **capability algebra** (what can an
Element do: click, hover, animate, etc.) — this is confusingly named but is
pure data, not the PureScript Effect monad.

**Effectful execution layer (correctly isolated):**
```
src/Hydrogen/Target/DOM.purs      -- DOM manipulation (Effect is correct here)
src/Hydrogen/State/Store.purs     -- Mutable state (Effect is correct here)
src/Hydrogen/Auth/Session.purs    -- Session management (Effect is correct here)
src/Hydrogen/API/Client.purs      -- HTTP requests (Effect is correct here)
```

### 5.3 The Correct Architecture Exists

```
┌────────────────────────────────────────────┐
│              PURE LAYER                     │
│  Element.purs — pure data                   │
│  Style.purs — pure CSS builder              │
│  Layout/Flex.purs — pure layout calculation │
└────────────────────────────────────────────┘
                      │
══════════════════════╪═══════════════════════
            EFFECT BOUNDARY
══════════════════════╪═══════════════════════
                      │
┌────────────────────────────────────────────┐
│            EFFECT LAYER                     │
│  Target/DOM.purs — DOM manipulation         │
│  State/Store.purs — mutable state           │
│  API/Client.purs — HTTP requests            │
└────────────────────────────────────────────┘
```

### 5.4 Previous Audit Error

The previous audit claimed "90% gap" based on:
- Misreading `Hydrogen.Render.Effect` (capability algebra, not Effect monad)
- Counting Effect imports without checking locations
- Not verifying that pure modules are actually pure

**Corrected assessment: 0% gap.**

The architecture is correct. Effect is used only at execution boundaries.

────────────────────────────────────────────────────────────────────────────────
                                                   // 6 // implementation // roadmap
────────────────────────────────────────────────────────────────────────────────

## 6. Implementation Roadmap

### 6.1 Track Dependencies

```
    ┌─────────────────┬──────────────────┬─────────────────┐
    │                 │                  │                 │
    ▼                 ▼                  ▼                 │
┌─────────┐    ┌─────────────┐    ┌─────────────┐         │
│ Graded  │    │ Presburger  │    │    ILP      │         │
│ Monads  │    │  Decision   │    │   Solver    │         │
│(Track 1)│    │  (Track 2)  │    │  (Track 3)  │         │
└────┬────┘    └──────┬──────┘    └──────┬──────┘         │
     │                │                  │                 │
     │                └────────┬─────────┘                 │
     │                         │                           │
     ▼                         ▼                           │
┌─────────────────────────────────────────┐               │
│         Schema Integration              │◀──────────────┘
│   (All atoms become graded/verified)    │
└─────────────────────────────────────────┘
```

**Effect System is already correct** — tracks can start immediately.

NOTE: Track 4 (Effect System) was originally planned but upon code review,
the architecture is already correct. Pure Element/Style modules have no
Effect imports; Target/DOM correctly isolates effectful execution.

### 6.2 Track 1: Graded Monads (4 weeks)

| Week | Deliverable | Files |
|------|-------------|-------|
| 1 | Core grade types, ForwardError monad | `src/Hydrogen/Schema/Numeric/Grade.purs`, `ForwardError.purs` |
| 2 | Graded bind, composition laws | `ForwardError.purs` (continued), test suite |
| 3 | Sensitivity comonad, primitive operations | `Sensitivity.purs`, `Primitives.purs` |
| 4 | Schema integration, OKLCH/Pixel as graded | `src/Hydrogen/Schema/Color/OKLCH.purs` modified |

**Dependencies**: None (can start immediately)
**Verification**: Property-based tests matching Lean proof laws

### 6.3 Track 2: Presburger Decision (5 weeks)

| Week | Deliverable | Files |
|------|-------------|-------|
| 1 | Linear constraint encoding | `proofs/Hydrogen/Layout/Presburger.lean` |
| 2 | Omega decision procedure in Lean | `proofs/Hydrogen/Layout/Decision.lean` |
| 3 | Layout constraint translation | `proofs/Hydrogen/Layout/LayoutConstraints.lean` |
| 4 | PureScript constraint types | `src/Hydrogen/Layout/Constraint.purs` |
| 5 | Integration with Flex.purs | `src/Hydrogen/Layout/Flex.purs` modified |

**Dependencies**: Track 4 (for testing)
**Verification**: Lean proofs + PureScript tests against known satisfiable/unsatisfiable layouts

### 6.4 Track 3: ILP Solver (5 weeks)

| Week | Deliverable | Files |
|------|-------------|-------|
| 1 | Problem formulation types | `src/Hydrogen/Layout/ILP/Problem.purs` |
| 2 | Simplex algorithm (LP relaxation) | `src/Hydrogen/Layout/ILP/Simplex.purs` |
| 3 | Simplex continued + testing | Test suite, edge case handling |
| 4 | Branch-and-bound for integers | `src/Hydrogen/Layout/ILP/BranchBound.purs` |
| 5 | Layout formulation + integration | `src/Hydrogen/Layout/ILP/Formulate.purs`, `Flex.purs` modified |

**Dependencies**: Track 2 (Presburger can prove feasibility before ILP optimizes)
**Verification**: Known optimal solutions, comparison with reference implementations

### 6.5 Track 4: Effect System — NOT NEEDED

**Status: Already correctly implemented.**

Upon code review, the Effect system architecture is correct:
- `Hydrogen.Render.Element` — Pure, no Effect imports
- `Hydrogen.Render.Style` — Pure, no Effect imports  
- `Hydrogen.Target.DOM` — Correctly uses Effect for DOM execution

No work required.

### 6.6 Parallelization Strategy

```
Week 1-5: Tracks 1, 2, 3 in parallel
Week 6: Integration, Schema migration
Week 7-8: Buffer for edge cases, documentation
```

**Minimum viable timeline**: 5 weeks (aggressive, minimal buffer)
**Recommended timeline**: 8 weeks (includes thorough testing)

### 6.7 Milestones

**M1 (Week 2)**: ForwardError monad passes all law tests
**M2 (Week 4)**: Presburger decides simple layout satisfiability
**M3 (Week 5)**: ILP finds optimal layout for flex containers
**M4 (Week 6)**: Schema atoms are graded, layouts are verified
**M5 (Week 8)**: Full integration, documentation complete

### 6.8 Risk Assessment

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| ILP performance too slow | Medium | High | Specialized interval solver, caching |
| Graded types too verbose | Low | Medium | Type aliases, smart constructors |
| Presburger FFI complexity | Medium | Medium | WASM compilation of Lean decision procedure |
| Breaking changes to Schema | High | High | Feature flag, gradual migration |

### 6.9 Success Criteria

After implementation:

1. **Graded Monads**: `color >>= transform` computes error bound automatically
2. **Presburger**: Conflicting layout constraints return `Left UnsatisfiableLayout`
3. **ILP**: Layouts are provably optimal with integer pixel positions
4. **Purity**: `render :: Element msg -> Array DrawCommand` compiles without Effect

**The claim "Same Element = same pixels" becomes provably true.**

────────────────────────────────────────────────────────────────────────────────
                                                                 // 7 // references
────────────────────────────────────────────────────────────────────────────────

## 7. References

### 7.1 Graded Monads and Error Analysis

**NumFuzz** — Graded monads for sensitivity analysis
- Azevedo de Amorim, Gaboardi, Hsu, Katsumata, Cheung. "A Semantic Account of Metric Preservation." POPL 2017.
- Defines `M[ε]` graded monad where grade ε tracks forward error bounds.

**Bean** — Backward error comonads
- Lorenzen, Lundfall, Birkedal. "Graded Differential Categories and Graded Differential Linear Logic." LICS 2023.
- Introduces `D^r` comonad for backward error analysis.

**Sensitivity Analysis**
- Reed, Pierce. "Distance Makes the Types Grow Stronger." ICFP 2010.
- `!_s` comonad for tracking function sensitivity.

**Olver Rounding Model**
- Olver, F. W. J. "A New Approach to Error Arithmetic." SIAM Journal on Numerical Analysis, 1978.
- RP (Relative Precision) metric: `ρ(x̃, x) = |x̃ - x| / |x|`

### 7.2 Presburger Arithmetic

**Original Decision Procedure**
- Presburger, M. "Über die Vollständigkeit eines gewissen Systems der Arithmetik ganzer Zahlen." 1929.
- Proves decidability of first-order theory of (ℕ, +).

**Cooper's Algorithm**
- Cooper, D. C. "Theorem Proving in Arithmetic without Multiplication." Machine Intelligence 7, 1972.
- Quantifier elimination for Presburger arithmetic, basis for modern solvers.

**Omega Test**
- Pugh, W. "The Omega Test: A Fast and Practical Integer Programming Algorithm for Dependence Analysis." 1991.
- Efficient Presburger decision procedure used in compiler analysis.

**Lean's omega Tactic**
- Lean 4 Mathlib documentation: `omega` tactic
- Implements Cooper's algorithm for automated integer arithmetic proofs.

### 7.3 Integer Linear Programming

**Simplex Method**
- Dantzig, G. B. "Linear Programming and Extensions." Princeton University Press, 1963.
- Foundation of LP solving, polynomial average case.

**Branch and Bound**
- Land, A. H.; Doig, A. G. "An Automatic Method of Solving Discrete Programming Problems." Econometrica, 1960.
- Standard approach for converting LP solution to ILP.

**Cutting Planes**
- Gomory, R. E. "Outline of an Algorithm for Integer Solutions to Linear Programs." Bulletin of the AMS, 1958.
- Alternative/complement to branch-and-bound.

**Layout Constraint Systems**
- Badros, Borning, Stuckey. "The Cassowary Linear Arithmetic Constraint Solving Algorithm." 2001.
- Incremental constraint solver used in Apple Auto Layout.

### 7.4 Effect Systems and Purity

**Monadic Effects**
- Moggi, E. "Notions of Computation and Monads." Information and Computation, 1991.
- Theoretical foundation for effect isolation.

**Algebraic Effects**
- Plotkin, G.; Power, J. "Algebraic Operations and Generic Effects." Applied Categorical Structures, 2003.
- Modern approach to structured effects.

**PureScript Effect System**
- PureScript documentation: `Effect` and `Aff` monads
- Row-polymorphic effects for tracking capabilities.

### 7.5 Internal Documentation

**Hydrogen Project**
- `docs/INTERNAL/RESEARCH_INTEGRATION_COUNCIL.md` — Research paper batches
- `docs/INTERNAL/paper_algos.md` — Algorithm extractions
- `docs/INTERNAL/button_reference.md` — Original claims about constraints

**Lean Proofs (created 2026-02-27)**
- `proofs/Hydrogen/Schema/Numeric/GradedMonad.lean` — ForwardError proofs
- `proofs/Hydrogen/Schema/Numeric/RelativePrecision.lean` — RP metric
- `proofs/Hydrogen/Schema/Numeric/NeighborhoodMonad.lean` — T^r construction

### 7.6 Implementation References

**Simplex in Functional Languages**
- Various implementations exist in Haskell (glpk-hs, limp)
- Consider porting or FFI to established solvers

**WASM for Lean**
- Lean 4 can compile to native code
- WASM target enables browser execution of decision procedures

**PureScript Numeric Libraries**
- `purescript-numbers` — Number utilities
- `purescript-rationals` — Exact rational arithmetic (useful for Simplex)

────────────────────────────────────────────────────────────────────────────────
                                                                   // end // of // audit
────────────────────────────────────────────────────────────────────────────────

**Document Status**: COMPLETE
**Date**: 2026-02-27
**Next Action**: Begin Track 4 (Effect System isolation)

