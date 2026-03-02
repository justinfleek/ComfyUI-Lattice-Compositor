# Bean: A Language for Backward Error Analysis

**arXiv:** 2501.14550  
**Authors:** Ariel E. Kellison, Laura Zielinski, David Bindel (Cornell University), Justin Hsu (Cornell + Imperial College London)  
**Date:** October 24, 2025  
**Domain:** Programming Languages / Numerical Analysis / Formal Verification

---

## Abstract

Bean is a typed first-order programming language designed to express **quantitative bounds on backward error** through floating-point computations. It is the **first tool to statically derive sound backward error bounds** automatically.

**Key Innovation:** Combines a graded coeffect system with strict linearity to track backward error flow through programs, with a novel categorical semantics based on "backward error lenses."

> **Slogan:** "A backward stable program gives exactly the right solution to nearly the right problem."

---

## 1. Problem: Why Backward Error Matters

### 1.1 Forward Error vs Backward Error

| Analysis Type | Question | Limitation |
|---------------|----------|------------|
| **Forward Error** | How far is computed from exact? | Can't distinguish ill-conditioned problems from unstable algorithms |
| **Backward Error** | What input perturbation would produce this output? | Separates problem conditioning from algorithm stability |

### 1.2 Definition: Backward Stability

A floating-point implementation ˜f: F^n → F^m of a real-valued function f: R^n → R^m is **backward stable** if for every input x ∈ F^n, there exists an input ˜x ∈ R^n such that:

```
f(˜x) = ˜f(x)  and  d(x, ˜x) ≤ αu
```

Where:
- d: extended metric
- α: small constant
- u: unit roundoff (2^-53 for IEEE binary64)

### 1.3 The Gap

| Tool | Forward Error | Backward Error | Static | Sound |
|------|--------------|----------------|--------|-------|
| Fluctuat | ✓ | ✗ | ✓ | ✓ |
| Rosa | ✓ | ✗ | ✓ | ✓ |
| FPCore | ✓ | ✗ | ✗ | N/A |
| **Bean** | ✓ | ✓ | ✓ | ✓ |

**Bean is the FIRST tool to statically derive sound backward error bounds.**

---

## 2. Methodology: Bean Type System

### 2.1 Three Ingredients

#### 1. Coeffects
Track per-variable backward error bounds:

```
∅ | x : (3ε/2) R^2, y : (3ε/2) R^2 ⊢ DotProd2 : R
```

The annotation `(3ε/2)` expresses the backward error bound for that variable.

#### 2. Distances
Each type has a distance function d_σ: σ × σ → R≥0 ∪ {∞}

For numeric type R, uses **Relative Precision Metric**:
```
RP(x, y) = |ln(x/y)|  if sign(x) = sign(y) and x,y ≠ 0
          = 0          if x = y = 0
          = ∞           otherwise
```

#### 3. Linearity
Prevents duplication of variables carrying backward error:

```purescript
-- NOT allowed in Bean (duplication loses error info):
let x = a in (x, x)

-- MUST use (linearity):
let x = a in f x  -- x used exactly once
```

### 2.2 Types Grammar

```
σ, τ ::= unit | num | σ ⊗ σ | σ + τ | α    (linear types)
α    ::= m(σ)                              (discrete types)
```

- **Linear types (σ)**: Can have backward error
- **Discrete types (m(σ))**: Cannot have backward error, can be duplicated

### 2.3 Typing Judgment

```
Φ, z: α | Γ, x: r σ ⊢ e: τ
```

Where:
- Φ: discrete typing context (no backward error)
- Γ: linear typing context (carries backward error bounds)
- r ∈ R≥0: backward error bound (grade)

---

## 3. Core Semantics: Backward Error Lenses

### 3.1 Category of Backward Error Lenses (Bel)

Every Bean expression denotes **three transformations**:

```
Input Space R^n  ──Forward──►  Output Space R^m
     │                              │
     │ backward                    │ backward
     ▼                              ▼
Perturbed Input  ──Exact──►  Exact Output
```

### 3.2 Mathematical Formalization

**Forward transform:** Floating-point computation
```
˜f(x) = computed result
```

**Exact transform:** Infinite-precision computation
```
f(x) = ideal result
```

**Backward transform:** Error propagation
```
Find ˜x such that f(˜x) = ˜f(x)
```

### 3.3 Soundness Theorem (Theorem 3.1)

> Let e be a well-typed Bean program:
> ```
> z1: α1, ..., zn: αn | x1: r1 σ1, ..., xm: rm σm ⊢ e: τ
> ```
> 
> If e evaluates to v under approximate floating-point semantics, then:
> 1. There exist perturbed values (˜kj) such that e also evaluates to v under exact, infinite-precision semantics
> 2. The distance between each kj and ˜kj is at most rj

---

## 4. Primitive Operations and Error Bounds

### 4.1 Arithmetic Rules

| Operation | Typing Rule | Backward Error |
|-----------|-------------|----------------|
| **Add** | Γ, x: ε+r1 R, y: ε+r2 R ⊢ add x y : R | ε added to both operands |
| **Sub** | Γ, x: ε+r1 R, y: ε+r2 R ⊢ sub x y : R | ε added to both operands |
| **Mul** | Γ, x: ε/2+r1 R, y: ε/2+r2 R ⊢ mul x y : R | ε/2 per operand |
| **Div** | Γ, x: ε/2+r1 R, y: ε/2+r2 R ⊢ div x y : R + unit | ε/2 per operand |
| **DMul** (discrete×linear) | Φ, z: m(R) \| Γ, x: ε+r R ⊢ dmul z x : R | ε to linear operand |

### 4.2 Unit Roundoff

For IEEE binary64 (round-to-nearest):
```
ε = u / (1 - u) = 2^-53 / (1 - 2^-53) ≈ 2^-53
```

### 4.3 Olver's Rounding Model

 Bean uses Olver's model instead of standard model:

```
Standard:  fl(x op y) = (x op y)(1 + δ),    |δ| ≤ u
Olver:     fl(x op y) = (x op y)e^δ,        |δ| ≤ ε = u/(1-u)
```

**Why Olver?** Better compositional properties for error propagation through sequences of operations.

---

## 5. Example Programs

### 5.1 Dot Product (2D)

```bean
DotProd2 x y :=
  let (x0, x1) = x in
  let (y0, y1) = y in
  let v = mul x0 y0 in
  let w = mul x1 y1 in
  add v w
```

**Typing:**
```
∅ | x : (3ε/2) R^2, y : (3ε/2) R^2 ⊢ DotProd2 : R
```

**Interpretation:** Each input component has backward error bounded by 3ε/2 in relative precision.

### 5.2 Matrix-Vector Product (2×2)

```bean
MatVecEx ((a00, a01), (a10, a11)) (z0, z1) :=
  let s0 = dmul z0 a00 in
  let s1 = dmul z1 a01 in
  let s2 = dmul z0 a10 in
  let s3 = dmul z1 a11 in
  let u0 = add s0 s1 in
  let u1 = add s2 s3 in
  (u0, u1)
```

**Result:** Each matrix element accumulates 2ε backward error.

### 5.3 Polynomial Evaluation: Naive vs Horner

| Method | Typing | Bound |
|--------|--------|-------|
| Naive | z: R \| a: 3ε R^3 ⊢ PolyVal : R | 3ε |
| Horner | z: R \| a: 4ε R^3 ⊢ Horner : R | 4ε |

**Surprising Result:** Horner's method (often considered more stable) can incur *greater* backward error with respect to coefficients, though fewer operations.

### 5.4 Triangular Linear Solver

```bean
LinSolve ((a00, a01), (a10, a11)) (b0, b1) :=
  let x0_or_err = div b0 a00 in
  case x0_or_err of
    inl(x0) => 
      dlet d_x0 = !x0 in
      let s0 = dmul d_x0 a10 in
      let s1 = sub b1 s0 in
      let x1_or_err = div s1 a11 in
      case x1_or_err of
        inl(x1) => inl(d_x0, x1)
        inr(err) => inr(err)
    inr(err) => inr(err)
```

**Typing:** `A: (5ε/2) R^2×2, b: (3ε/2) R^2 ⊢ LinSolve : R^2 + unit`

---

## 6. Relation to Hydrogen

### 6.1 GPU Computation Verification

For **WebGPU shaders** with Float16/Float32/Float64:

| Hydrogen Need | Bean Solution |
|---------------|---------------|
| Quantized arithmetic (FP4, NVFP4) | Track quantization error accumulation |
| Serialization roundtrip | Prove `deserialize(serialize(x)) = x` |
| Color conversion bounds | Prove sRGB ↔ Oklab bounds |

### 6.2 Schema Atom Serialization

```purescript
-- Bean-style proof needed:
-- For all x: Color, deserialize(serialize(x)) has bounded backward error

theorem Color_Serialization_Bound {x : Color} :
  RP (deserialize (serialize x)) x ≤ ε_color
```

### 6.3 Lean4 Integration

Bean's categorical semantics (backward error lenses) maps directly to Lean4:

| Bean Concept | Lean4 Equivalent |
|--------------|------------------|
| Coeffect grades | Prop / ℕ (error bounds) |
| Distance functions | Metric spaces |
| Linear types | Affine logic |
| Backward error lens | Roundtrip function |

### 6.4 Formal Verification Pipeline

```
Hydrogen Schema (PureScript)
        │
        ▼
  Lean4 Proofs (Bean-style)
        │
        ▼
  GPU Compilation (WGSL)
        │
        ▼
  Runtime Verification
```

---

## 7. Implementation

### 7.1 Prototype

- **Language:** OCaml
- **Algorithm:** Based on sensitivity inference (de Amorim et al.)
- **Features:** Automatic coefficient inference

### 7.2 Evaluation Results

| Algorithm | Bean Inferred Bound | Theoretical Worst-Case |
|-----------|--------------------|------------------------|
| Dot Product (n=2) | 3ε/2 | 3ε/2 ✓ |
| Matrix-Vector (2×2) | 2ε | 2ε ✓ |
| Polynomial (degree 10) | varies | matches ✓ |
| Triangular Solver | 5ε/2 | matches ✓ |

**Conclusion:** Bean automatically infers bounds that match worst-case theoretical bounds from literature.

---

## 8. Key Insights for Billion-Agent Systems

### 8.1 Error Compositionality

> Bean demonstrates that backward error bounds ARE compositional—contrary to prior belief in numerical analysis community.

This is **critical** for:
- Composing thousands of agents
- Nested transformations
- Frame-by-frame accumulation

### 8.2 Linearity as Sufficient Condition

Bean's linearity provides a **sufficient but not necessary** condition:
- Ensures no incompatible perturbations on shared variables
- Rejects some backward-stable programs (sound but not complete)
- Sufficient for billion-agent scale where variables aren't reused

---

## 9. References

1. Higham & Higham "Backward Error and Condition Number"
2. Olver "A New Rounding Model"
3. Girard "Linear Logic"
4. Hughes "Graded Coefficients"
5. de Amorim et al. "Sensitivity Analysis"
6. Karras "EDM Noise Schedules"
7. Wilkinson "Rounding Errors in Algebraic Processes"

---

## 10. Citation

```bibtex
@misc{kellison2025bean,
  title={Bean: A Language for Backward Error Analysis},
  author={Ariel E. Kellison and Laura Zielinski and David Bindel and Justin Hsu},
  year={2025},
  eprint={2501.14550},
  archivePrefix={arXiv},
  primaryClass={cs.PL}
}
```

---
*Research Document: Hydrogen Research Collection*
*Completed: 2026-02-26*
*Attestation: clarity*
