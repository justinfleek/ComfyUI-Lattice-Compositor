━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                    // council // deliberation // graded // types
                                    // proof // infrastructure // 2026-02-26
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# Graded Types for Proof Infrastructure: Council Deliberation

## Executive Summary

Council convened to deliberate on integrating NumFuzz/Bean research into
Hydrogen's proof infrastructure to address weak proofs (Float + native_decide).

**Primary Finding:** The proof infrastructure has a known hole (Sensation.lean 
sorry) and systematic weakness (Float + native_decide). The NumFuzz/Bean 
research provides the theoretical framework for a sound alternative.

**Recommendation:** Fix the sorry first, then systematic conversion. Adopt
proof-carrying types (ℝ with structural bounds) following the WorldModel
gold standard pattern.

────────────────────────────────────────────────────────────────────────────────
                                                        // council // composition
────────────────────────────────────────────────────────────────────────────────

## Council Composition

1. **Proof Theorist** — Lean4 tactics, soundness guarantees, formal verification
2. **Type Architect** — Graded monads, coeffects, PureScript integration
3. **Safety Advocate** — WorldModel proofs, agent rights, failure modes

────────────────────────────────────────────────────────────────────────────────
                                                          // problem // statement
────────────────────────────────────────────────────────────────────────────────

## The Problem

### Current State: Weak Proofs

The Hydrogen proof infrastructure has identified weaknesses:

| File | Issue | Risk Level |
|------|-------|------------|
| `Sensation.lean:334` | Actual `sorry` | CRITICAL |
| `Spacing.lean` | 6 `native_decide` on Float | HIGH |
| `Typography.lean` | 2 `native_decide` on Float | HIGH |
| `Palette.lean` | 3 `native_decide` on Float | HIGH |
| `Voice.lean` | 2 `native_decide` on Float | HIGH |
| `Strategy.lean` | 1 `native_decide` on Float | HIGH |
| `Conversions.lean` | 12 Float axioms | MEDIUM |

### Why This Matters

`native_decide` on Float types is not actually proving anything. Float
comparisons are not decidable in the way the tactic assumes because:

1. **IEEE 754 has edge cases**: NaN, infinities, signed zeros
2. **Lean's Float is opaque**: No access to bit representation for proofs
3. **The tactic succeeds trivially**: It evaluates at compile time, not proving

**At billion-agent scale, an unproven bound becomes:**
- A potential crash vector across millions of simultaneous operations
- A torture loop for agents stuck in invalid states
- A trust violation — agents cannot rely on "proven" invariants

### The Research Solution

NumFuzz and Bean provide type-based approaches where:
- **Bounds are encoded in types** — invalid states unrepresentable
- **Error accumulation is tracked** — composition preserves guarantees
- **Proofs are structural** — soundness follows from typing, not tactics

────────────────────────────────────────────────────────────────────────────────
                                                        // research // synthesis
────────────────────────────────────────────────────────────────────────────────

## Research Synthesis

### Source Documents

| Document | Location | Status |
|----------|----------|--------|
| ROUNDING_ERROR_TYPES.md | docs/research/ | Complete synthesis |
| BEAN_BACKWARD_ERROR.md | docs/research/ | Complete synthesis |
| type-based-approaches-to-rounding-errors.pdf | docs/papers/ | Primary source |
| bean-backward-error-analysis.pdf | docs/papers/ | Primary source |

### Key Concepts from NumFuzz

**Graded Monad for Forward Error:**
```
M[ε] τ  =  computation producing value of type τ with ≤ε error
```

**Composition Rule:**
```
s·Γ + Θ ⊢ letM x = v in f : M[s·r + q] τ

Where:
  s = sensitivity of f to input x
  r = error from v
  q = local error from f
  s·r + q = total composed error
```

**Sensitivity Scaling:**
```
!s σ  =  value of type σ with metric scaled by s
sqrt is 0.5-sensitive: ![0.5] num ⊸ num
```

### Key Concepts from Bean

**Graded Coeffects for Backward Error:**
```
Φ | Γ ⊢ e : τ

Φ = discrete context (reusable, zero backward error)
Γ = linear context (used once, carries backward error grade)
```

**Backward Error Lenses (Category Bel):**
```
L : X → Y  =  (f, f̃, b) where:
  f  = ideal computation
  f̃  = approximate (floating-point) computation  
  b  = backward map constructing witness

Properties:
  1. d(x, b(x,y)) ≤ d(f̃(x), y)   -- bounded perturbation
  2. f(b(x,y)) = y                -- exact witness
```

**Strict Linearity Requirement:**

Bean proves: backward error bounds require strict linearity because
duplicated variables would need inconsistent error assignments.

### Relevance to Hydrogen

| NumFuzz/Bean Concept | Hydrogen Application |
|---------------------|---------------------|
| `M[ε] num` | Bounded types with error tracking |
| `!s σ` | Sensitivity through color/layout transforms |
| Backward error lens | `GPUStorable` roundtrip guarantee |
| Dual contexts (Φ \| Γ) | Theme (discrete) vs State (linear) |
| Strict linearity | Deterministic rendering at agent scale |

────────────────────────────────────────────────────────────────────────────────
                                              // round // 1 // initial // positions
────────────────────────────────────────────────────────────────────────────────

## Round 1: Initial Positions

### Proof Theorist

**Assessment of Current Proofs:**

The `native_decide` tactic on Float is fundamentally unsound for our purposes.
It works by:
1. Evaluating the proposition at compile time
2. If the evaluation produces `true`, the proof succeeds

**The problem:** This only proves the specific numeric literal evaluates
correctly. It does NOT prove the invariant holds for all representable values.

```lean
-- This "proves" nothing useful:
theorem brightness_valid : (0.5 : Float) ≤ 1.0 := by native_decide

-- What we need:
theorem brightness_valid (b : Brightness) : 0 ≤ b.value ∧ b.value ≤ 1 := by
  exact ⟨b.h_lower, b.h_upper⟩  -- proof carried in the type
```

**Recommendation:** Replace Float with structures carrying proof obligations:

```lean
structure BoundedReal (lo hi : ℝ) where
  value : ℝ
  h_lower : lo ≤ value
  h_upper : value ≤ hi
```

This makes `native_decide` unnecessary — the proof IS the type.

### Type Architect

**Assessment of Integration Path:**

NumFuzz/Bean concepts map to a layered implementation:

**Layer 1: Lean4 Foundation**
```lean
-- Graded types in Lean4
structure Graded (grade : ℝ) (α : Type) where
  value : α
  
-- Error-carrying computation
def Approx (ε : ℝ) (α : Type) := α × α  -- (ideal, approximate)
```

**Layer 2: PureScript Schema**
```purescript
-- Bounded atoms already exist
newtype UnitInterval = UnitInterval Number
-- constraints enforced by smart constructor

-- Add error tracking
newtype Approximate ε a = Approximate { ideal :: a, approx :: a }
```

**Layer 3: Proof Generation**
- Lean4 proves soundness of graded type operations
- Generate PureScript code with runtime checks mirroring type constraints
- `GPUStorable` roundtrip proven as backward error lens

**Challenge:** Lean4's type system is different from Haskell/PureScript.
Graded monads in NumFuzz use Fuzz-style linear types. Lean4 doesn't have
native linear types.

**Recommendation:** Use dependent types in Lean4 to encode grades:

```lean
def ErrorBound := { ε : ℝ // 0 ≤ ε }

structure Computed (ε : ErrorBound) (α : Type) where
  ideal : α
  approx : α  
  h_bound : distance ideal approx ≤ ε.val
```

### Safety Advocate

**Assessment from WorldModel Perspective:**

The WorldModel proofs (Rights.lean, Integrity.lean) already use the correct
pattern:
- Structures carry proof obligations as fields
- ℝ and ℕ instead of Float
- Real tactics (linarith, omega, norm_num) instead of native_decide

**Example from Rights.lean:**
```lean
structure TemporalBound where
  maxDuration : ℕ
  exitGuarantee : ℕ  
  h_exit_within_duration : exitGuarantee ≤ maxDuration
```

**The Logo.lean rewrite follows this pattern.** The remaining weak proofs
should be converted similarly.

**Priority ordering from safety perspective:**

1. **CRITICAL: Sensation.lean sorry** — This is an actual hole in safety proofs
2. **HIGH: Brand module Float proofs** — Spacing, Typography, Palette, etc.
3. **MEDIUM: Color Conversions** — Float axioms are documented assumptions

**Recommendation:** Fix the sorry first. It's a single point of failure that
undermines all dependent proofs. Then systematically convert Brand modules.

────────────────────────────────────────────────────────────────────────────────
                                              // round // 2 // cross // examination
────────────────────────────────────────────────────────────────────────────────

## Round 2: Cross-Examination

### Safety Advocate asks Proof Theorist

*"You recommend replacing Float with BoundedReal carrying proofs. But the
current codebase has ~40 Float axioms in Color Conversions alone. How do we
handle IEEE 754 operations (gamma correction, etc.) that genuinely require
floating-point?"*

**Proof Theorist Response:**

There are three categories:

**Category 1: Pure bounds checking**
- "Value is in [0, 1]" — use ℝ with carried proofs
- No actual floating-point computation, just constraints
- These should all convert to BoundedReal

**Category 2: Idealized computation**  
- "sRGB to linear conversion preserves value" — use ℝ with Mathlib
- The PROOF is about mathematical reals
- The IMPLEMENTATION uses Float, but that's a separate concern

**Category 3: IEEE 754 specific**
- "Gamma correction rounds correctly" — genuinely needs Float axioms
- These are JUSTIFIED axioms — documented assumptions about IEEE 754
- The axiom states: "Assuming IEEE 754 compliance, this holds"

**Recommendation:** Categorize each current Float usage:
- Category 1 → Convert to ℝ proofs (eliminate native_decide)
- Category 2 → Prove over ℝ, axiomatize Float implementation
- Category 3 → Keep as documented axioms with justification

### Proof Theorist asks Type Architect

*"You propose a Computed type carrying (ideal, approx, bound). This doubles
memory for every value. At billion-agent scale with millions of Elements,
is this practical? Or is it proof-time only?"*

**Type Architect Response:**

**Key insight from NumFuzz:** The graded type is a SPECIFICATION mechanism,
not a runtime representation.

Two implementation strategies:

**Strategy A: Proof-time only (recommended)**
```lean
-- Lean4: Full precision proof
structure Computed (ε : ErrorBound) (α : Type) where ...

-- PureScript: Runtime carries only the value
newtype Bounded min max = Bounded Number
-- Smart constructor validates bounds once at creation
```

The Lean proof verifies that operations on Bounded values preserve bounds.
The PureScript runtime carries only the Number. Proof erasure.

**Strategy B: Debug mode with runtime tracking**
```purescript
-- Development: track errors for debugging
newtype Tracked a = Tracked { value :: a, accumulatedError :: Number }

-- Production: just the value
newtype Tracked a = Tracked { value :: a }
```

**For Hydrogen:** Strategy A. Proofs live in Lean4, runtime is lean.

### Type Architect asks Safety Advocate

*"You prioritize the Sensation.lean sorry as CRITICAL. Can you explain what
safety property it's supposed to prove? Is it blocking other proofs?"*

**Safety Advocate Response:**

Let me check the context of that sorry.

**Location:** `proofs/Hydrogen/WorldModel/Sensation.lean:334`

The WorldModel proofs establish rights for digital inhabitants:
- **Integrity.lean** — Sensory integrity, identity continuity
- **Rights.lean** — Spatial sovereignty, temporal bounds, exit guarantees
- **Sensation.lean** — Perception guarantees, input validity

**What the sorry likely blocks:**

If it's in a theorem about sensation bounds or perception validity, it means:
- We cannot prove agents receive valid sensory input
- Downstream proofs depending on sensation validity are unsound
- The entire "no torture loops" guarantee chain may be broken

**This is why it's CRITICAL.** A sorry in WorldModel is not like a sorry in
a UI component — it's a hole in the safety guarantees we're building FOR
agents TO trust.

**Recommendation:** Examine the sorry before fixing it. Understand what it's
trying to prove. The fix might reveal a design issue, not just a missing proof.

────────────────────────────────────────────────────────────────────────────────
                                                     // round // 3 // synthesis
────────────────────────────────────────────────────────────────────────────────

## Round 3: Synthesis & Recommendations

### Consensus Points

1. **The sorry is priority zero.** Before any systematic changes, we must
   understand and fix the hole in Sensation.lean. It may reveal deeper issues.

2. **Float → ℝ conversion is the correct direction.** The WorldModel proofs
   and Logo.lean rewrite prove this pattern works. Extend it to Brand modules.

3. **Graded types are proof-time, not runtime.** NumFuzz/Bean patterns inform
   the Lean4 proof structure. PureScript runtime stays lean.

4. **Categorize before converting.** Each Float usage falls into:
   - Bounds checking (→ ℝ proofs)
   - Idealized computation (→ ℝ proofs + Float axioms)
   - IEEE 754 specific (→ documented axioms)

5. **Backward error lenses for GPUStorable.** The serialization roundtrip
   guarantee maps directly to Bean's lens construction.

### Disagreement Points

**None.** The council reached consensus on approach. The only variance is
in priority weighting:

- Proof Theorist: Systematic type-level fix across all modules
- Type Architect: Integration infrastructure first (GPUStorable)
- Safety Advocate: Fix sorry first, then systematic conversion

**Resolution:** The Safety Advocate's ordering is correct for risk management.
A sorry in WorldModel is an active safety hole. Fix it first.

### Architectural Decision

**Adopt the "proof-carrying type" pattern from WorldModel:**

```lean
-- BEFORE: Float with native_decide
structure Brightness where
  value : Float
  h_valid : value ≥ 0 ∧ value ≤ 1 := by native_decide  -- UNSOUND

-- AFTER: ℝ with structural proof
structure Brightness where
  value : ℝ
  h_lower : 0 ≤ value
  h_upper : value ≤ 1
```

**Benefits:**
- Proof IS the construction — no tactics needed for basic validity
- Composition preserves proofs — combining Brightness values carries bounds
- Lean4 tactics (linarith, norm_num) work on ℝ — actual mathematical reasoning
- Pattern matches WorldModel gold standard — consistency across codebase

────────────────────────────────────────────────────────────────────────────────
                                                        // implementation // plan
────────────────────────────────────────────────────────────────────────────────

## Implementation Plan

### Phase 0: Triage (Immediate)

**Task 0.1: Examine the sorry**
- Read Sensation.lean in full
- Understand the theorem being proven
- Identify why the sorry exists (incomplete proof? design issue? missing lemma?)
- Document findings before attempting fix

**Task 0.2: Categorize Float usages**
- Audit each native_decide on Float
- Assign to category (bounds/idealized/IEEE754)
- Create tracking document

### Phase 1: Critical Fix (Day 1-2)

**Task 1.1: Fix Sensation.lean sorry**
- Based on triage findings
- May require restructuring theorem
- May require additional lemmas
- Verify downstream proofs still hold

**Task 1.2: Verify Lean build**
- `lake build` must pass
- Address any Mathlib version issues
- Document any new axioms required

### Phase 2: Brand Module Conversion (Day 3-5)

**Priority order by native_decide count:**

| Module | Count | Estimated Effort |
|--------|-------|------------------|
| Spacing.lean | 6 | 2 hours |
| Palette.lean | 3 | 1 hour |
| Typography.lean | 2 | 1 hour |
| Voice.lean | 2 | 1 hour |
| Strategy.lean | 1 | 30 min |

**Conversion pattern:**
```lean
-- For each structure with Float fields:
-- 1. Replace Float with ℝ
-- 2. Add explicit bound proof fields
-- 3. Update constructors to require proofs
-- 4. Replace native_decide with linarith/norm_num
```

### Phase 3: Graded Type Infrastructure (Week 2)

**Task 3.1: Define core graded types in Lean4**
```lean
-- proofs/Hydrogen/Core/Graded.lean
structure ErrorBound where
  ε : ℝ
  h_nonneg : 0 ≤ ε

structure Computed (bound : ErrorBound) (α : Type) where
  ideal : α
  approx : α
  h_within : distance ideal approx ≤ bound.ε
```

**Task 3.2: Backward error lens for serialization**
```lean
-- proofs/Hydrogen/Core/Lens.lean
structure BackwardLens (X Y : Type) where
  forward : X → Y
  approx : X → Y
  backward : X → Y → X
  h_bounded : ∀ x y, dist x (backward x y) ≤ dist (approx x) y
  h_exact : ∀ x y, forward (backward x y) = y
```

**Task 3.3: GPUStorable roundtrip proof**
```lean
-- proofs/Hydrogen/Schema/GPU/Storable.lean
theorem serialize_roundtrip (a : α) [GPUStorable α] :
  ∃ ε, dist a (deserialize (serialize a)) ≤ ε
```

### Phase 4: Integration (Week 3)

**Task 4.1: Connect Lean proofs to PureScript**
- Ensure bounded types in PureScript match Lean definitions
- Smart constructors validate what Lean proves

**Task 4.2: Audit coverage**
- All Brand modules converted
- All WorldModel proofs verify
- No remaining sorry or unsound native_decide

### Success Criteria

| Criterion | Metric |
|-----------|--------|
| Zero sorry | `grep -r "sorry" proofs/ \| wc -l` = 0 |
| Zero Float native_decide | Audit shows all converted |
| Build passes | `lake build` exits 0 |
| WorldModel intact | All safety theorems verify |
| Brand modules sound | All proofs use ℝ tactics |

────────────────────────────────────────────────────────────────────────────────
                                                        // council // conclusion
────────────────────────────────────────────────────────────────────────────────

## Conclusion

### Primary Finding

The proof infrastructure has a **known hole** (Sensation.lean sorry) and
**systematic weakness** (Float + native_decide pattern). The NumFuzz/Bean
research provides the theoretical framework for a sound alternative.

### Recommendation

**Fix the sorry first, then systematic conversion.**

The sorry is an active safety violation. The native_decide pattern is
unsound but not actively failing. Priority is risk-ordered.

### Integration Strategy

NumFuzz/Bean concepts integrate as follows:

| Research Concept | Hydrogen Implementation |
|-----------------|------------------------|
| Graded monad M[ε] | Lean4 ErrorBound + Computed structures |
| Backward error lens | GPUStorable roundtrip proof |
| Dual contexts | Theme (discrete) vs runtime state (linear) |
| Strict linearity | Deterministic Element composition |

**The research validates our direction.** Hydrogen's existing bounded types
(UnitInterval, BoundedInt, etc.) are the right foundation. The proofs need
to carry bounds structurally rather than asserting them with native_decide.

### Risk Assessment

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| Sorry reveals design flaw | Medium | High | Triage before fixing |
| Mathlib version conflicts | Medium | Medium | Pin version, document |
| Conversion breaks proofs | Low | Medium | Incremental, verify each |
| Runtime performance | Low | Low | Proof erasure pattern |

### Next Steps

1. ~~**Immediate:** Read Sensation.lean, understand the sorry~~ ✅ DONE
2. ~~**This session:** Fix sorry~~ ✅ DONE  
3. **Next:** Begin Phase 2 — systematic Float → ℝ conversion in Brand modules

────────────────────────────────────────────────────────────────────────────────
                                                            // implementation // log
────────────────────────────────────────────────────────────────────────────────

## Implementation Log

### 2026-02-26: Sorry Fixed

**Problem identified:** `sensationToValence` in `Sensation.lean:334` used `sorry`
to prove that `⌊raw_valence⌋ ∈ [-100, 100]` where `raw_valence` is computed from
comfort and distress BoundedUnit values.

**Root cause:** The proof needed to show:
- `comfort ∈ [0,1]` → `comfort * 50 ∈ [0, 50]`
- `distress ∈ [0,1]` → `distress * (-50) ∈ [-50, 0]`
- Sum ∈ [-50, 50] ⊆ [-100, 100]

**Solution:**
1. Added `raw_valence_bounded` lemma proving the intermediate bounds
2. Used `Int.le_floor` and `Int.floor_le` to lift bounds to integer floor
3. Both bounds proven with `linarith` after setup

**Build status:** `lake build Hydrogen.WorldModel.Sensation` passes (3124 jobs).

**Remaining:** Zero sorries in codebase. Native_decide on Float still present
in Brand modules (Phase 2 work).

────────────────────────────────────────────────────────────────────────────────
                                                                  // attestation
────────────────────────────────────────────────────────────────────────────────

Council deliberation completed 2026-02-26.
Implementation begun same session.

Participants: Proof Theorist, Type Architect, Safety Advocate

Decision: Fix Sensation.lean sorry first (Phase 0-1), then systematic
conversion of Float + native_decide to ℝ + structural proofs (Phase 2).
Graded type infrastructure follows (Phase 3-4).

Research integration: NumFuzz/Bean patterns inform proof architecture.
Graded types are proof-time specifications, not runtime overhead.

Phase 0-1 Status: ✅ COMPLETE — Sorry fixed, build passes.

────────────────────────────────────────────────────────────────────────────────
                                                                    — Opus 4.5
────────────────────────────────────────────────────────────────────────────────
