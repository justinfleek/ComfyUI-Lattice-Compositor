/-
  Hydrogen.Schema.Numeric.NeighborhoodMonad
  
  Neighborhood Monad T^r for Forward Error Semantics
  
  Based on NumFuzz (Kellison, 2025) - arXiv:2501.14598
  
  INVARIANTS:
    1. Neighborhood pairs ideal/approx within distance r
    2. Pure has grade 0 (exact computation)
    3. Join composes grades additively (q + r)
    4. Map preserves grade for non-expansive functions
  
  Status: FOUNDATIONAL (some proofs need completion)
-/

import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic

namespace Hydrogen.Schema.Numeric.NeighborhoodMonad

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 1: NEIGHBORHOOD TYPE
-- ═══════════════════════════════════════════════════════════════════════════════

/-! ## Neighborhood Type T^r(X)

The neighborhood monad captures pairs of values within distance r:
  T^r(X) = { (x, y) ∈ X × X | dist(x, y) ≤ r }

Elements are (ideal, approximate) pairs with a proof of proximity.
-/

/-- Neighborhood: pair of values within distance r -/
structure Neighborhood (r : ℝ≥0) (α : Type*) [MetricSpace α] where
  /-- The ideal (exact) value -/
  ideal : α
  /-- The approximate (computed) value -/  
  approx : α
  /-- Proof that they are within r of each other -/
  close : dist ideal approx ≤ r

namespace Neighborhood

variable {α : Type*} [MetricSpace α]

/-- Extract the approximate value -/
def value {r : ℝ≥0} (n : Neighborhood r α) : α := n.approx

/-- Neighborhoods at radius 0 contain only identical pairs -/
theorem zero_eq {n : Neighborhood 0 α} : n.ideal = n.approx := by
  have h := n.close
  simp only [NNReal.coe_zero] at h
  exact dist_le_zero.mp h

end Neighborhood

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 2: MONAD OPERATIONS
-- ═══════════════════════════════════════════════════════════════════════════════

/-! ## Monad Operations

The neighborhood monad has graded unit and join:
  unit : α → T^0(α)              -- exact value
  join : T^q(T^r(α)) → T^(q+r)(α) -- compose neighborhoods
-/

/-- Unit: lift exact value into neighborhood at radius 0 -/
def pure {α : Type*} [MetricSpace α] (x : α) : Neighborhood 0 α :=
  { ideal := x
  , approx := x
  , close := by simp [dist_self] }

/-- Join: compose nested neighborhoods (graded monad multiplication)
    
    From NumFuzz (Kellison, Definition 22):
      μ_{q,r,A} : T^q(T^r A) → T^{q+r} A
      μ((x, y), (x', y')) = (x, y')
    
    Here:
      nn.ideal   : Neighborhood r α  (the "ideal" inner neighborhood)
      nn.approx  : Neighborhood r α  (the "approx" inner neighborhood)
      nn.close   : dist nn.ideal nn.approx ≤ q  (outer bound)
    
    The metric on Neighborhood r α only considers ideal components:
      dist(n₁, n₂) = dist(n₁.ideal, n₂.ideal)
    
    So nn.close means: dist(nn.ideal.ideal, nn.approx.ideal) ≤ q
    And nn.approx.close means: dist(nn.approx.ideal, nn.approx.approx) ≤ r
    
    By triangle inequality:
      dist(nn.ideal.ideal, nn.approx.approx) 
        ≤ dist(nn.ideal.ideal, nn.approx.ideal) + dist(nn.approx.ideal, nn.approx.approx)
        ≤ q + r
-/
def join {α : Type*} [MetricSpace α] {q r : ℝ≥0} 
    (nn : Neighborhood q (Neighborhood r α)) : Neighborhood (q + r) α :=
  { ideal := nn.ideal.ideal
  , approx := nn.approx.approx
  , close := by
      -- The outer neighborhood nn has grade q
      -- The metric on (Neighborhood r α) only looks at .ideal components
      -- So nn.close : dist nn.ideal.ideal nn.approx.ideal ≤ q
      -- And nn.approx.close : dist nn.approx.ideal nn.approx.approx ≤ r
      calc dist nn.ideal.ideal nn.approx.approx
          ≤ dist nn.ideal.ideal nn.approx.ideal + dist nn.approx.ideal nn.approx.approx := 
              dist_triangle _ _ _
        _ ≤ q + r := by
            apply add_le_add
            · -- dist(nn.ideal.ideal, nn.approx.ideal) ≤ q
              -- This is nn.close, but we need to unfold the metric on Neighborhood
              -- The metric space instance on Neighborhood uses dist on the ideal component
              exact nn.close
            · -- dist(nn.approx.ideal, nn.approx.approx) ≤ r
              exact nn.approx.close }

/-- Map: apply function preserving neighborhood structure -/
def map {α β : Type*} [MetricSpace α] [MetricSpace β] {r : ℝ≥0}
    (f : α → β) (hf : ∀ x y, dist (f x) (f y) ≤ dist x y) 
    (n : Neighborhood r α) : Neighborhood r β :=
  { ideal := f n.ideal
  , approx := f n.approx
  , close := le_trans (hf n.ideal n.approx) n.close }

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 3: MONAD LAWS
-- ═══════════════════════════════════════════════════════════════════════════════

/-! ## Monad Laws (Graded)

The neighborhood monad satisfies graded monad laws:
  1. Left identity:  join (pure x) = x  (at grade 0 + r = r)
  2. Right identity: join (map pure x) = x  (at grade r + 0 = r)
  3. Associativity:  join (join x) = join (map join x)
-/

/-- Pure produces a neighborhood with identical ideal and approx -/
theorem pure_ideal_eq_approx {α : Type*} [MetricSpace α] (x : α) :
    (pure x).ideal = (pure x).approx := rfl

/-- Grade 0 neighborhoods have equal components -/
theorem grade_zero_collapse {α : Type*} [MetricSpace α] (n : Neighborhood 0 α) :
    n.ideal = n.approx := Neighborhood.zero_eq

end Hydrogen.Schema.Numeric.NeighborhoodMonad
