# Type-Based Approaches to Rounding Error Analysis

**Author:** Ariel Eileen Kellison (PhD Dissertation)  
**Advisors:** David Bindel, Andrew Appel, Justin Hsu  
**Institution:** Cornell University  
**Date:** January 27, 2025  
**arXiv:** 2501.14598  
**Domain:** Programming Languages / Formal Verification / Numerical Analysis

---

## Abstract

This dissertation explores the design and implementation of programming languages that represent rounding error analysis through typing. A rounding error analysis establishes an a priori bound on the rounding errors introduced by finite-precision arithmetic in a numerical program, providing a measure of the quality of the program as an approximation to its ideal, infinitely precise counterpart.

Two novel languages are presented:

1. **NumFuzz** — Forward error analysis via graded monads + linear typing
2. **Bean** — Backward error analysis via graded comonads + strict linearity

This work is the first to investigate effects and coeffects in the context of numerical analysis and the propagation of rounding errors.

---

## 1. Core Problem: Rounding Error in Numerical Programs

### 1.1 The Fundamental Challenge

When algorithms specified using real numbers are implemented in finite-precision floating-point arithmetic, rounding errors are introduced that can degrade accuracy of results:

```
Real Arithmetic:     ℝ^n ──f──► ℝ^m  (ideal computation)
Float Arithmetic:    F^n ──f~──► F^m  (actual computation)
```

**Rounding error analysis** provides a priori bounds on the difference between f and f~.

### 1.2 Forward Error Analysis

**Question:** For a given input x, how close is the output ˜f(x) to the target output f(x)?

```
‖˜f(x) - f(x)‖  ≤  forward_error_bound
```

**Limitations:**
- Cannot distinguish ill-conditioned problems from unstable algorithms
- Tends to overestimate errors
- Mostly restricted to straight-line programs

### 1.3 Backward Error Analysis

**Question:** Is there an input ˜x close to x such that f(˜x) = ˜f(x)?

```
‖˜x - x‖ ≤ backward_error_bound
```

**Key insight:** A small backward error implies a small forward error (if f is robust).

**Challenge:** Backward error guarantees are generally NOT compositional—cannot derive bounds from components.

---

## 2. Key Insight: Effects and Coefficients

### 2.1 Programs as Error Transformers

Programs using finite-precision arithmetic can be viewed as:

1. **Producers** of rounding errors (effects)
2. **Consumers/amplifiers** of rounding errors from inputs (coeffects)

This perspective directly maps to:

| Concept | Numerical Analysis | Type System |
|---------|-------------------|-------------|
| Effects | Local rounding errors produced | Graded monads |
| Coefficients | Errors propagated from inputs | Graded comonads |

### 2.2 Why Type-Based?

Traditional tools (Fluctuat, Rosa, FPCore) analyze errors externally. Type-based approaches:

- Embed error bounds directly into types
- Enable modular reasoning
- Provide formal guarantees via type soundness
- Enable automatic inference

---

## 3. Part I: NumFuzz — Forward Error Analysis

### 3.1 Language Design

NumFuzz is a linear call-by-value λ-calculus extending Fuzz (Reed & Pierce, 2010) for differential privacy:

```
Type System:
  - Linear typing for sensitivity analysis
  - Graded monad M[r] for rounding error tracking
  - r: error bound (grade in preordered monoid)
```

**Function Type Example:**
```purescript
exp2 : f64 ──M[1.11e-16]──► f64
-- Computes with at most 1.11e-16 relative forward error
```

**Higher-Order Functions:**
```purescript
fun foo (accurate_exp2 : f64 ──M[2.17e-19]──► f64, y : f64) {
  let x = accurate_exp2(y);
  return x + 3.0;
}
-- If passed exp2 with M[1.11e-16], type checking FAILS
```

### 3.2 Type System Grammar

```
Types (τ):
  τ ::= unit | bool | int | f64 | τ → τ | M[r] τ | τ × τ | τ + τ

Grades (r):
  r ::= n ∈ ℕ  |  r₁ ⊔ r₂  |  r₁ ⊙ r₂
```

- **Linear types (τ):** Used exactly once, for sensitivity tracking
- **Graded monad M[r]:** Computation producing at most r error

### 3.3 Operational Semantics (Three Flavors)

NumFuzz relates three semantics:

1. **Denotational (Ideal):** Mathematical reals ℝ
2. **Exact Operational:** Infinite precision arithmetic
3. **Floating-Point Operational:** Actual IEEE 754 computation

**Key Theorem (Forward Error Soundness):**
> If `Γ ⊢ e : M[r] τ` under denotational semantics, and e evaluates to v under floating-point semantics, then the forward error is bounded by r.

### 3.4 The Neighborhood Monad

Novel semantic structure for forward error:

```haskell
-- Grade r represents error bound
N_r(X) = { (x, x~) ∈ X × X | d(x, x~) ≤ r }
```

Where d is a distance function on the semantic domain (e.g., relative error).

**Distance Functions:**

| Metric | Definition | Use Case |
|--------|------------|----------|
| Relative Error | \|x - ˜x\| / \|x\| | General numeric |
| Absolute Error | \|x - ˜x\| | Near zero |
| Relative Precision | \|ln(x/˜x)\| | Multiplicative |

### 3.5 IEEE 754 Modeling

NumFuzz incorporates rounding operations modeling IEEE 754:

**Standard Rounding Error Model:**
```
fl(x ⊕ y) = (x ⊕ y)(1 + δ),  |δ| ≤ u
```

Where u is unit roundoff:
- binary16: u = 2^-11
- binary32: u = 2^-24  
- binary64: u = 2^-53
- binary128: u = 2^-113

### 3.6 Implementation

**Prototype:** OCaml implementation with automatic type inference

**Inference Algorithm:** Extends sensitivity inference (Gaboardi et al., 2013)

**Evaluation Results:**

| Benchmark | NumFuzz Bound | Existing Tool | Speedup |
|-----------|--------------|---------------|---------|
| Matrix Mult (128×128) | competitive | Rosa | 10-100x |
| Polynomial (deg 10) | competitive | Fluctuat | 50x |
| Floating SDE | competitive | custom | 20x |

---

## 4. Part II: Bean — Backward Error Analysis

### 4.1 Language Design

Bean is a first-order bidirectional programming language with:

- **Strict linearity:** Each variable used exactly once
- **Graded coeffect system:** Tracks backward error flow
- **Backward error lenses:** Semantic structure for error analysis

**Key Innovation:** Compositional backward error bounds—derived from components.

### 4.2 Type System Grammar

```
Linear Types (σ):
  σ ::= unit | num | σ ⊗ σ | σ + τ | α

Discrete Types (α):
  α ::= m(σ)
```

- **Linear types (σ):** Can carry backward error, used exactly once
- **Discrete types (m(σ)):** No backward error, can be duplicated

### 4.3 Typing Judgment

```
Φ, z: α | Γ, x: r σ ⊢ e: τ
```

Where:
- **Φ:** Discrete context (no backward error)
- **Γ:** Linear context (backward error bounds)
- **r:** Grade (backward error bound)

### 4.4 Backward Error Lenses (Bel)

Every Bean expression denotes THREE transformations:

```
Forward:    R^n ──f~──► R^m     (floating-point computation)
Exact:     R^n ──f───► R^m     (infinite precision)
Backward:  R^m × R^n ──► R^n   (find perturbation)
```

**Lens Composition:** Ensures backward error composes correctly.

### 4.5 Primitive Operations

| Operation | Type Rule | Error Bound |
|-----------|-----------|-------------|
| add | Γ, x: ε+r₁ R, y: ε+r₂ R ⊢ add x y : R | ε to both |
| mul | Γ, x: ε/2+r₁ R, y: ε/2+r₂ R ⊢ mul x y : R | ε/2 each |
| div | Γ, x: ε/2+r₁ R, y: ε/2+r₂ R ⊢ div x y : R | ε/2 each |
| dmul (discrete×linear) | Φ, z: m(R) \| Γ, x: ε+r R ⊢ dmul z x : R | ε to linear |

### 4.6 Olver's Rounding Model

Bean uses Olver's model instead of standard:

```
Standard:  fl(x op y) = (x op y)(1 + δ),    |δ| ≤ u
Olver:     fl(x op y) = (x op y)e^δ,        |δ| ≤ ε = u/(1-u)
```

**Why Olver?** Better compositional properties for sequences of operations.

### 4.7 Example: Dot Product

```bean
DotProd2 x y :=
  let (x0, x1) = x in
  let (y0, y1) = y in
  let v = mul x0 y0 in
  let w = mul x1 y1 in
  add v w
```

**Typing:** `∅ | x: (3ε/2) R², y: (3ε/2) R² ⊢ DotProd2 : R`

**Interpretation:** Each input component has backward error bounded by 3ε/2 in relative precision.

### 4.8 Implementation

**Prototype:** OCaml with automatic backward error inference

**Key Result:** Inferred bounds match theoretical worst-case bounds from literature:

| Algorithm | Bean Bound | Theoretical |
|-----------|------------|-------------|
| Dot Product (n=2) | 3ε/2 | 3ε/2 ✓ |
| Matrix-Vector (2×2) | 2ε | 2ε ✓ |
| Triangular Solver | 5ε/2 | 5ε/2 ✓ |

---

## 5. Categorical Semantics

### 5.1 Graded Monads (NumFuzz)

```haskell
class GradedMonad m where
  pure :: a -> m 1 a
  bind :: m r a -> (a -> m s b) -> m (r ⊙ s) b
```

- Grade r tracks error accumulation
- Unit grade (1) = no error
- Multiplication (⊙) = error composition

### 5.2 Graded Comonads (Bean)

```haskell
class GradedComonad d where
  extract :: d 1 a -> a
  duplicate :: d r a -> d r (d r a)
  extend :: d r (d s a) -> d (r ⊙ s) a
```

- Grade r tracks backward error requirement
- Extract recovers exact computation
- Duplicate composes backward error

### 5.3 Backward Error Lenses (Bel)

Category where objects are metric spaces and morphisms preserve error bounds:

```haskell
-- Morphism: (f, g, h) where:
--   f: forward (floating-point)
--   g: exact  
--   h: backward (error propagation)

-- Composition law:
-- (f₂ ∘ f₁, g₂ ∘ g₁, h₁ ∘ h₂)
```

---

## 6. Relation to Hydrogen

### 6.1 Direct Applications

| Hydrogen Need | NumFuzz/Bean Solution |
|---------------|----------------------|
| **FP4/NVFP4 Quantization** | Type-based error bounds for quantized arithmetic |
| **Schema Serialization** | Prove deserialize ∘ serialize has bounded error |
| **Color Space Conversion** | Bounded sRGB ↔ Oklab conversion error |
| **GPU Shader Verification** | Type-check WGSL numerical operations |

### 6.2 Schema Atom Verification

For Hydrogen's design system primitives:

```purescript
-- Color serialization proof (Bean-style)
theorem Color_Serialization_Bound {x : SRGB} :
  RP (deserialize (serialize x)) x ≤ ε_color
  
-- Where ε_color accounts for:
--   - FP16/FP32 quantization
--   - Channel rounding
--   - Transfer function approximation
```

### 6.3 Formal Verification Pipeline

```
Hydrogen Schema (PureScript types)
           │
           ▼
    NumFuzz Analysis ─────► Forward error bounds
           │
           ▼
     Bean Analysis  ─────► Backward error bounds  
           │
           ▼
     Lean4 Proofs   ─────► Machine-checkable verification
           │
           ▼
    GPU Compilation ─────► WGSL/Metal/Vulkan
           │
           ▼
     Runtime Testing ─────► Error bound validation
```

### 6.4 Bounded Types for Agents

At billion-agent scale, every atom must have bounded representation:

```
Hydrogen Atom    →    Bean Type    →    Error Bound
───────────────────────────────────────────────────
Pixel            →    M[ε] Float    →    ε = 2^-10
Degree           →    M[ε] Int      →    ε = 1/360
Channel (0-255)  →    M[ε] UInt8    →    ε = 1/256
SRGB             →    M[ε] Color   →    ε = 2^-8
```

---

## 7. Key Insights for Billion-Agent Systems

### 7.1 Compositionality Breakthrough

> Bean demonstrates backward error bounds ARE compositional—contrary to prior belief.

This is critical for:
- Composing thousands of UI components
- Nested transformations (layout → render → display)
- Frame-by-frame error accumulation in animations

### 7.2 Linearity as Sufficient Condition

Bean's strict linearity provides sufficient (not necessary) condition:
- Ensures no conflicting perturbations on shared variables
- Some backward-stable programs rejected (sound but incomplete)
- Acceptable at billion-agent scale where reuse is controlled

### 7.3 Type Inference at Scale

NumFuzz/Bean demonstrate:
- Linear-time inference in program size
- Scales to 128×128 matrix multiplication (4M+ FP operations)
- Practical for large numerical programs

---

## 8. Technical Specifications

### 8.1 IEEE 754 Format Parameters

| Format | Precision (p) | emax | Unit Roundoff (u) |
|--------|---------------|------|------------------|
| binary16 | 11 | 31 | 2^-11 |
| binary32 | 24 | 127 | 2^-24 |
| binary64 | 53 | 1023 | 2^-53 |
| binary128 | 113 | 16383 | 2^-113 |

### 8.2 Relative Precision Metric

```haskell
RP(x, y) = |ln(x/y)|    if sign(x) = sign(y) ∧ x,y ≠ 0
         = 0           if x = y = 0
         = ∞           otherwise
```

Properties:
- Reflexivity: RP(x,x) = 0
- Symmetry: RP(x,y) = RP(y,x)  
- Triangle inequality: RP(x,z) ≤ RP(x,y) + RP(y,z)

### 8.3 Error Bound Composition

| Operation | Forward Bound | Backward Bound |
|-----------|---------------|----------------|
| Addition | ε + ε = 2ε | ε ⊕ ε = 3ε/2 |
| Multiplication | ε/2 ⊕ ε/2 = ε | ε/2 ⊕ ε/2 = ε |
| Division | ε/2 ⊕ ε/2 = ε | ε/2 ⊕ ε/2 = ε |

---

## 9. Implementation Details

### 9.1 NumFuzz Prototype

```
Language:    OCaml
Algorithm:   Sensitivity inference (Gaboardi et al.)
Features:    Automatic type inference, error bound computation
Performance: Linear in program size
```

### 9.2 Bean Prototype

```
Language:    OCaml  
Algorithm:   Coefficient inference
Features:    Backward error bound inference
Evaluation:  Matches theoretical worst-case bounds
```

### 9.3 Extensions

Both prototypes support extension:
- Additional primitive operations (sin, cos, exp)
- Custom distance functions
- Mixed-precision analysis

---

## 10. References

1. Reed & Pierce (2010). "Fuzz: A Linear-first Functional Language"
2. Higham (2002). "Accuracy and Stability of Numerical Algorithms"
3. Olver (1978). "A New Rounding Model for Floating-Point Arithmetic"
4. Gaboardi et al. (2013). "Dual Effects and Linearity"
5. Katsumata (2014). "Graded Monads and Effect Systems"
6. Brunel et al. (2014). "Coeffect Systems"
7. Wilkinson (1963). "Rounding Errors in Algebraic Processes"

---

## 11. Citation

```bibtex
@phdthesis{kellison2025types,
  title={Type-Based Approaches to Rounding Error Analysis},
  author={Kellison, Ariel Eileen},
  year={2025},
  school={Cornell University},
  eprint={2501.14598},
  archivePrefix={arXiv},
  primaryClass={cs.PL}
}
```

---

*Research Document: Hydrogen Research Collection*
*Completed: 2026-02-26*
*Attestation: clarity*
