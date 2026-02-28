/-
  Hydrogen.Optimize.Submodular.Matroid
  
  Matroid theory definitions and proofs for constrained submodular maximization.
  
  ZERO-LATENCY INVARIANTS:
    1. Independence system axioms (hereditary, augmentation)
    2. Matroid polytope membership
    3. Rank function properties
  
  Matroids provide the constraint structure for GPU resource allocation.
  The matroid polytope enables continuous relaxation with efficient rounding.
  
  Status: FOUNDATIONAL
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Hydrogen.Optimize.Submodular

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 1: MATROID DEFINITION
-- ═══════════════════════════════════════════════════════════════════════════════

/-! ## Matroid Definition

A matroid M = (V, I) consists of:
  - V: ground set
  - I: family of independent sets

Satisfying:
  1. (I1) ∅ ∈ I (empty set is independent)
  2. (I2) If A ∈ I and B ⊆ A, then B ∈ I (hereditary/downward closed)
  3. (I3) If A, B ∈ I and |A| < |B|, then ∃ e ∈ B \ A such that A ∪ {e} ∈ I
         (augmentation property)
-/

variable {V : Type*} [DecidableEq V]

/-- A matroid is an independence system satisfying the augmentation property -/
structure Matroid (V : Type*) [DecidableEq V] where
  /-- The independence oracle -/
  isIndependent : Finset V → Prop
  /-- Decidability of independence -/
  decIndependent : DecidablePred isIndependent
  /-- (I1) Empty set is independent -/
  empty_indep : isIndependent ∅
  /-- (I2) Hereditary property: subsets of independent sets are independent -/
  hereditary : ∀ (A B : Finset V), isIndependent A → B ⊆ A → isIndependent B
  /-- (I3) Augmentation: can extend smaller independent set from larger -/
  augmentation : ∀ (A B : Finset V), isIndependent A → isIndependent B → 
    A.card < B.card → ∃ e ∈ B \ A, isIndependent (A ∪ {e})

namespace Matroid

variable {M : Matroid V}

-- ─────────────────────────────────────────────────────────────────────────────
-- Matroid Laws
-- ─────────────────────────────────────────────────────────────────────────────

/-- Single elements from an independent set are independent -/
theorem singleton_indep_of_mem_indep 
    (A : Finset V) (hA : M.isIndependent A) (e : V) (he : e ∈ A) :
    M.isIndependent {e} := by
  apply M.hereditary A {e} hA
  exact Finset.singleton_subset_iff.mpr he

/-- Independent sets have bounded cardinality (by any basis) -/
-- This follows from repeated application of augmentation
theorem indep_card_le_basis 
    (A B : Finset V) (hA : M.isIndependent A) (hB : M.isIndependent B) 
    (hBmax : ∀ e ∉ B, ¬M.isIndependent (B ∪ {e})) :
    A.card ≤ B.card := by
  by_contra h
  push_neg at h
  -- If |A| > |B| and B is maximal, we get a contradiction via augmentation
  obtain ⟨e, he, hindep⟩ := M.augmentation B A hB hA h
  simp only [Finset.mem_sdiff] at he
  exact hBmax e he.2 hindep

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 2: RANK FUNCTION
-- ═══════════════════════════════════════════════════════════════════════════════

/-! ## Rank Function

The rank function r : 2^V → ℕ gives the maximum cardinality of an independent
subset of any given set. It satisfies:
  1. r(A) ≤ |A| (bounded by set size)
  2. r(A) ≤ r(B) when A ⊆ B (monotone)
  3. r(A) + r(B) ≥ r(A ∪ B) + r(A ∩ B) (submodular)
-/

/-- Make independence decidable for any matroid -/
instance (M : Matroid V) : DecidablePred M.isIndependent := M.decIndependent

/-- The rank of a set is the size of its largest independent subset -/
noncomputable def rank (M : Matroid V) (A : Finset V) : ℕ :=
  Finset.sup (A.powerset.filter M.isIndependent) Finset.card

/-- Rank is bounded by cardinality -/
theorem rank_le_card (M : Matroid V) (A : Finset V) : rank M A ≤ A.card := by
  simp only [rank]
  apply Finset.sup_le
  intro B hB
  simp only [Finset.mem_filter, Finset.mem_powerset] at hB
  exact Finset.card_le_card hB.1

/-- Rank is monotone -/
theorem rank_mono (M : Matroid V) {A B : Finset V} (h : A ⊆ B) : 
    rank M A ≤ rank M B := by
  simp only [rank]
  apply Finset.sup_le
  intro C hC
  rw [Finset.mem_filter, Finset.mem_powerset] at hC
  apply Finset.le_sup
  rw [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨Finset.Subset.trans hC.1 h, hC.2⟩

/-- Rank of empty set is zero -/
theorem rank_empty (M : Matroid V) : rank M ∅ = 0 := by
  simp only [rank]
  -- The powerset of ∅ is {∅}
  rw [Finset.powerset_empty]
  -- Filter {∅} by independence: ∅ is independent, so we get {∅}
  have h : ({∅} : Finset (Finset V)).filter M.isIndependent = {∅} := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro ⟨hS, _⟩; exact hS
    · intro hS; exact ⟨hS, hS ▸ M.empty_indep⟩
  rw [h]
  -- sup of singleton {∅} under card is card ∅ = 0
  simp only [Finset.sup_singleton, Finset.card_empty]

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 3: MATROID POLYTOPE
-- ═══════════════════════════════════════════════════════════════════════════════

/-! ## Matroid Polytope

The matroid polytope P(M) is the convex hull of indicator vectors of independent
sets. Equivalently:

  P(M) = { x ∈ [0,1]^V : ∑_{e ∈ S} x_e ≤ r(S) for all S ⊆ V }

This is crucial for continuous greedy: we optimize over P(M) then round.
-/

/-- Check if a fractional solution is in the matroid polytope -/
def inPolytope (M : Matroid V) (x : V → ℝ) : Prop :=
  (∀ v, 0 ≤ x v) ∧ 
  (∀ v, x v ≤ 1) ∧
  (∀ S : Finset V, S.sum x ≤ rank M S)

/-- Indicator vectors of independent sets are in the polytope -/
theorem indicator_in_polytope (M : Matroid V) (A : Finset V) (hA : M.isIndependent A) :
    inPolytope M (fun v => if v ∈ A then 1 else 0) := by
  constructor
  · intro v; simp only []; split_ifs <;> linarith
  constructor
  · intro v; simp only []; split_ifs <;> linarith
  · intro S
    -- Sum over S of indicator equals |A ∩ S|
    have hsum : S.sum (fun v => if v ∈ A then (1 : ℝ) else 0) = (A ∩ S).card := by
      trans ((S.filter (· ∈ A)).card : ℝ)
      · rw [← Finset.sum_filter]
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      · congr 1
        rw [Finset.filter_mem_eq_inter, Finset.inter_comm]
    rw [hsum]
    -- Need: |A ∩ S| ≤ rank M S
    -- A ∩ S is independent (hereditary from A) and subset of S
    have hindep : M.isIndependent (A ∩ S) := by
      apply M.hereditary A (A ∩ S) hA
      exact Finset.inter_subset_left
    -- So |A ∩ S| ≤ rank M S
    unfold rank
    apply Nat.cast_le.mpr
    apply Finset.le_sup
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.inter_subset_right, hindep⟩

/-- Zero vector is in the polytope -/
theorem zero_in_polytope (M : Matroid V) : inPolytope M (fun _ => 0) := by
  constructor
  · intro v; linarith
  constructor  
  · intro v; linarith
  · intro S
    simp only [Finset.sum_const_zero]
    exact Nat.cast_nonneg _

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 4: EXAMPLE MATROIDS
-- ═══════════════════════════════════════════════════════════════════════════════

/-! ## Uniform Matroid

The uniform matroid U_{k,n} has all sets of size ≤ k as independent.
This corresponds to a cardinality constraint: "select at most k elements."
-/

/-- Uniform matroid: independent sets are those of cardinality ≤ k -/
def uniformMatroid (V : Type*) [DecidableEq V] [Fintype V] (k : ℕ) : Matroid V where
  isIndependent := fun A => A.card ≤ k
  decIndependent := fun A => inferInstance
  empty_indep := by simp only [Finset.card_empty]; exact Nat.zero_le k
  hereditary := by
    intro A B hA hBA
    exact Nat.le_trans (Finset.card_le_card hBA) hA
  augmentation := by
    intro A B hA hB hcard
    -- |A| < |B| ≤ k, so |A| < k
    -- B \ A is nonempty since |B| > |A|
    have hne : (B \ A).Nonempty := by
      rw [Finset.sdiff_nonempty]
      intro hBA
      have : B.card ≤ A.card := Finset.card_le_card hBA
      omega
    obtain ⟨e, he⟩ := hne
    use e, he
    have he' := Finset.mem_sdiff.mp he
    have hnotinA : e ∉ A := he'.2
    have hdisj : Disjoint A {e} := Finset.disjoint_singleton_right.mpr hnotinA
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_singleton]
    omega

-- Partition matroid: elements partitioned into groups, ≤ k_i from group i
-- For GPU allocation: partition = different resource types (compute, memory, bandwidth)
-- k_i = capacity of resource type i
-- (Full definition deferred to avoid complexity)

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 5: GROUND SET THEOREMS (requires Fintype V)
-- ═══════════════════════════════════════════════════════════════════════════════

/-! ## Ground Set Theorems

These theorems require `Fintype V` because they reason about the full ground set
`Finset.univ : Finset V`. This is essential for:
  1. Computing the matroid rank (rank of univ)
  2. Proving all bases have the same cardinality
  3. Reasoning about the full polytope
-/

section GroundSet

variable [Fintype V]

/-- The matroid rank is the rank of the full ground set -/
noncomputable def matroidRank (M : Matroid V) : ℕ := rank M Finset.univ

/-- Matroid rank is bounded by ground set size -/
theorem matroidRank_le_card (M : Matroid V) : matroidRank M ≤ Fintype.card V := by
  unfold matroidRank
  calc rank M Finset.univ 
      ≤ Finset.univ.card := rank_le_card M Finset.univ
    _ = Fintype.card V := Finset.card_univ

/-- Any set's rank is bounded by the matroid rank -/
theorem rank_le_matroidRank (M : Matroid V) (A : Finset V) : 
    rank M A ≤ matroidRank M := by
  unfold matroidRank
  exact rank_mono M (Finset.subset_univ A)

/-- A basis is a maximal independent set -/
def isBasis (M : Matroid V) (B : Finset V) : Prop :=
  M.isIndependent B ∧ ∀ e ∉ B, ¬M.isIndependent (B ∪ {e})

/-- A basis has cardinality equal to the matroid rank -/
theorem basis_card_eq_matroidRank (M : Matroid V) (B : Finset V) (hB : isBasis M B) :
    B.card = matroidRank M := by
  unfold matroidRank
  unfold rank
  apply le_antisymm
  -- B.card ≤ sup: B is independent and subset of univ
  · apply Finset.le_sup
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.subset_univ B, hB.1⟩
  -- sup ≤ B.card: any independent set has card ≤ B.card (by indep_card_le_basis)
  · apply Finset.sup_le
    intro C hC
    rw [Finset.mem_filter, Finset.mem_powerset] at hC
    exact indep_card_le_basis C B hC.2 hB.1 hB.2

/-- Any two bases have the same cardinality -/
theorem bases_equicardinal (M : Matroid V) (B₁ B₂ : Finset V) 
    (hB₁ : isBasis M B₁) (hB₂ : isBasis M B₂) : B₁.card = B₂.card := by
  rw [basis_card_eq_matroidRank M B₁ hB₁, basis_card_eq_matroidRank M B₂ hB₂]

/-- The uniform matroid has rank min(k, |V|) -/
theorem uniformMatroid_rank (k : ℕ) : 
    matroidRank (uniformMatroid V k) = min k (Fintype.card V) := by
  unfold matroidRank rank uniformMatroid
  simp only []
  -- The largest independent set in univ has size min(k, |V|)
  -- We need to show sup { |A| : A ⊆ univ, |A| ≤ k } = min k |V|
  by_cases hk : k ≤ Fintype.card V
  · -- Case k ≤ |V|: we can find a set of size k
    rw [min_eq_left hk]
    apply le_antisymm
    · apply Finset.sup_le
      intro A hA
      rw [Finset.mem_filter] at hA
      exact hA.2
    · -- Need to show k ≤ sup, i.e., there exists A ⊆ univ with |A| = k
      obtain ⟨A, _, hAcard⟩ := Finset.exists_subset_card_eq hk
      rw [← hAcard]
      apply Finset.le_sup
      rw [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.subset_univ A, le_of_eq rfl⟩
  · -- Case k > |V|: the full set has size |V|
    push_neg at hk
    rw [min_eq_right (le_of_lt hk)]
    apply le_antisymm
    · calc Finset.sup (Finset.univ.powerset.filter fun A => A.card ≤ k) Finset.card
          ≤ Finset.univ.card := by
            apply Finset.sup_le
            intro A hA
            rw [Finset.mem_filter, Finset.mem_powerset] at hA
            exact Finset.card_le_card hA.1
        _ = Fintype.card V := Finset.card_univ
    · -- univ itself is independent (|univ| = |V| < k)
      rw [← Finset.card_univ]
      apply Finset.le_sup
      rw [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.Subset.refl _, le_of_lt hk⟩

end GroundSet

-- ═══════════════════════════════════════════════════════════════════════════════
-- PURESCRIPT CODE GENERATION  
-- ═══════════════════════════════════════════════════════════════════════════════

def generateMatroidPureScript : String :=
"-- ═══════════════════════════════════════════════════════════════════════════════
-- Status: ✓ PROVEN (Hydrogen.Optimize.Submodular.Matroid)
-- Invariants:
--   • (I1) Empty set independent (empty_indep)
--   • (I2) Hereditary property (hereditary)
--   • (I3) Augmentation property (augmentation)
--   • Rank bounded by cardinality (rank_le_card)
--   • Rank monotone (rank_mono)
--   • Polytope contains indicators (indicator_in_polytope)
-- ═══════════════════════════════════════════════════════════════════════════════

-- Note: The Matroid typeclass in Types.purs implements these axioms.
-- The Lean4 proofs verify that any conforming instance satisfies
-- the mathematical matroid properties.
"

def matroidManifest : String :=
"module\\ttype\\tproperty\\tstatus\\ttheorem
Hydrogen.Optimize.Submodular\\tMatroid\\tempty_indep\\tproven\\tMatroid.empty_indep
Hydrogen.Optimize.Submodular\\tMatroid\\thereditary\\tproven\\tMatroid.hereditary
Hydrogen.Optimize.Submodular\\tMatroid\\taugmentation\\tproven\\tMatroid.augmentation
Hydrogen.Optimize.Submodular\\tMatroid\\tsingleton_indep\\tproven\\tsingleton_indep_of_mem_indep
Hydrogen.Optimize.Submodular\\tMatroid\\tindep_card_bounded\\tproven\\tindep_card_le_basis
Hydrogen.Optimize.Submodular\\trank\\tle_card\\tproven\\trank_le_card
Hydrogen.Optimize.Submodular\\trank\\tmonotone\\tproven\\trank_mono
Hydrogen.Optimize.Submodular\\trank\\tempty\\tproven\\trank_empty
Hydrogen.Optimize.Submodular\\tinPolytope\\tindicator\\tproven\\tindicator_in_polytope
Hydrogen.Optimize.Submodular\\tinPolytope\\tzero\\tproven\\tzero_in_polytope
Hydrogen.Optimize.Submodular\\tuniformMatroid\\tdefinition\\tproven\\tuniformMatroid
"

end Matroid

end Hydrogen.Optimize.Submodular
