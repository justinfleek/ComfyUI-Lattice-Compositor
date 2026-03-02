# Type-Based Approaches to Rounding Error Analysis

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                      // paper // synthesis
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

**Source:** PhD Dissertation, Cornell University
**Author:** Ariel Eileen Kellison
**Advisors:** David Bindel, Andrew Appel, Justin Hsu
**Collaborators:** Laura Zielinski (Bean implementation)
**Year:** 2024

**Artifacts:**
- NumFuzz: https://github.com/ak-2485/NumFuzz
- Bean: https://github.com/ak-2485/NumFuzz/tree/bean

────────────────────────────────────────────────────────────────────────────────
                                                              // overview
────────────────────────────────────────────────────────────────────────────────

## Core Thesis

Programs using finite-precision arithmetic can be viewed as computations that:
- **Produce** rounding error (effects)
- **Consume and amplify** rounding errors from inputs (coeffects)

This perspective enables type-based analysis where:
- **Graded monadic types** track effects (forward error)
- **Graded comonadic types** track coeffects (sensitivity / backward error)

## Two Languages

| Language | Error Type | Type Mechanism | Semantic Model |
|----------|------------|----------------|----------------|
| **NumFuzz** | Forward error | Graded monad | Neighborhood monad on Met |
| **Bean** | Backward error | Graded coeffects | Backward error lenses (Bel) |

────────────────────────────────────────────────────────────────────────────────
                                                     // forward // vs // backward
────────────────────────────────────────────────────────────────────────────────

## Forward vs Backward Error

Given ideal program P and approximate program P̃:

```
        Domain X                    Codomain Y
        
        x ∈ X ─────────P──────────→ y ∈ Y
        │                           │
        │ δx (backward error)       │ δy (forward error)
        │                           │
        x̃ ∈ X ─────────P──────────→ ỹ ∈ Y
                       ↑
                       P̃
```

**Forward Error (δy):** Distance between computed output P̃(x) and ideal output P(x)
- "How wrong is my answer?"
- Most programs have some forward error bound (even if large)

**Backward Error (δx):** Smallest input perturbation making P(x̃) = P̃(x)
- "What problem did I actually solve?"
- Not all programs have backward error bounds
- Small backward error implies small forward error (if P is well-conditioned)

────────────────────────────────────────────────────────────────────────────────
                                                              // numfuzz
────────────────────────────────────────────────────────────────────────────────

## NumFuzz: Forward Error Analysis

### Type Syntax

```
σ, τ ::= unit                    -- unit type
       | num                     -- numeric type (reals with metric)
       | σ & τ                   -- additive product (shared context)
       | σ ⊗ τ                   -- multiplicative product (split context)
       | σ + τ                   -- sum type
       | σ ⊸ τ                   -- linear function (1-sensitive)
       | !s σ                    -- graded comonad (s-scaled metric)
       | M[q] τ                  -- graded monad (≤q error)
```

### Key Insight: Sensitivity + Local Error = Global Error

A **c-sensitive function** amplifies input distances by at most c:

```
d_Y(f(x), f(y)) ≤ c · d_X(x, y)
```

When composing rounded computations:
- Input error gets **amplified by sensitivity**
- Plus **local rounding error** from the operation
- Total error = sensitivity × input_error + local_error

### Core Typing Rules

**Rounding introduces error:**
```
        Γ ⊢ v : num
    ─────────────────────  (Rnd)
    Γ ⊢ rnd v : M[ε] num
```

**Monadic sequencing composes errors:**
```
    Γ ⊢ v : M[r] σ       Θ, x :s σ ⊢ f : M[q] τ
    ───────────────────────────────────────────────  (MLet)
    s · Γ + Θ ⊢ letM x = v in f : M[s·r + q] τ
```

The grade `s·r + q` captures:
- `s·r` = input error `r` amplified by sensitivity `s`
- `q` = local error from `f`

**Comonadic scaling:**
```
        Γ ⊢ v : σ
    ─────────────────  (! I)
    s · Γ ⊢ [v] : !s σ
```

### Additive vs Multiplicative Products

**Additive Product (&):** Components share context
```
    Γ ⊢ v : σ       Γ ⊢ w : τ
    ─────────────────────────────  (& I)
    Γ ⊢ ⟨v, w⟩ : σ & τ
```
Sensitivity = max(sensitivity_v, sensitivity_w)

**Multiplicative Product (⊗):** Components split context
```
    Γ ⊢ v : σ       Θ ⊢ w : τ
    ─────────────────────────────  (⊗ I)
    Γ + Θ ⊢ (v, w) : σ ⊗ τ
```
Sensitivity = sensitivity_v + sensitivity_w

**Consequence for primitives:**
```
add : (num & num) ⊸ num      -- addition is 1-sensitive in each arg
mul : (num ⊗ num) ⊸ num      -- multiplication sensitivities add
```

────────────────────────────────────────────────────────────────────────────────
                                                    // neighborhood // monad
────────────────────────────────────────────────────────────────────────────────

## The Neighborhood Monad

**Definition (Kellison, Definition 22):**

Let R = (R≥0 ∪ {∞}, ≤, +) be a preordered monoid.

The neighborhood monad T^r : Met → Met is defined by:

**Objects:**
```
|T^r M| = { (x, y) ∈ M × M | d_M(x, y) ≤ r }
```
Elements are pairs of values within distance r.

**Metric:**
```
d_{T^r M}((x, y), (x', y')) = d_M(x, x')
```
Distance only considers the first (ideal) components.

**Unit:**
```
η_A : A → T^0 A
η_A(x) = (x, x)
```
Exact computation: ideal = approximate.

**Multiplication:**
```
μ_{q,r,A} : T^q(T^r A) → T^{r+q} A
μ((x, y), (x', y')) = (x, y')
```
Compose by taking outer ideal, inner approximate.

**Interpretation:** Values of type M[r] τ are pairs (ideal_value, fp_value) where
the distance between them is bounded by r.

────────────────────────────────────────────────────────────────────────────────
                                                    // relative // precision
────────────────────────────────────────────────────────────────────────────────

## Relative Precision Metric

**Definition (Olver, 1978):**

```
              │ |ln(x̃/x)|    if sgn(x̃) = sgn(x) and x̃, x ≠ 0
RP(x, x̃) =   │ 0            if x̃ = x = 0
              │ ∞            otherwise
```

**Why not relative error?**

Relative error `|x̃ - x|/|x|` is NOT a metric:
- Not symmetric
- Doesn't satisfy triangle inequality

Relative precision IS an extended pseudometric:
- Reflexive: RP(x, x) = 0
- Symmetric: RP(x, y) = RP(y, x)
- Triangle inequality: RP(x, z) ≤ RP(x, y) + RP(y, z)

**Relationship to relative error:**

For RP(x, x̃) = α with α < 1:
```
err_rel = |e^α - 1| ≤ α / (1 - α)
```

**Connection to rounding models:**

Standard model: `ρ(x op y) = (x op y)(1 + δ)`, |δ| ≤ u
Alternative model: `ρ(x op y) = (x op y)e^δ`, |δ| ≤ u/(1-u)

The alternative model with exponential error aligns naturally with RP.

────────────────────────────────────────────────────────────────────────────────
                                                    // soundness // theorem
────────────────────────────────────────────────────────────────────────────────

## Forward Error Soundness

**Theorem (Kellison, Corollary 1):**

Let `∅ ⊢ e : M[r] num` be a well-typed closed program. Then:

1. Under ideal semantics: `e ↦*_id ret v_id`
2. Under FP semantics: `e ↦*_fp ret v_fp`
3. Error bound holds: `d_num(v_id, v_fp) ≤ r`

**The type guarantees the error bound.**

**Proof structure:**
1. Termination via logical relations (strong normalization)
2. Computational soundness: stepping preserves semantics
3. Pairing lemma: metric semantics = (ideal semantics, FP semantics)
4. Definition of neighborhood monad: pairs are within stated distance

────────────────────────────────────────────────────────────────────────────────
                                                    // primitive // operations
────────────────────────────────────────────────────────────────────────────────

## Instantiation for IEEE 754

**Numeric type:** num = (R>0, RP)  (positive reals with relative precision)

**Rounding function:** ρ_RU (round towards +∞)

**Unit roundoff:** u = 2^(-p+1) where p is precision
- binary64: u ≈ 2.22 × 10^(-16)

**Primitive operations (non-expansive maps):**

```purescript
-- Without rounding (ideal)
add  : (num & num) ⊸ num         -- 1-sensitive per argument
mul  : (num ⊗ num) ⊸ num         -- sensitivities sum
div  : (num ⊗ num) ⊸ num         -- sensitivities sum  
sqrt : ![0.5] num ⊸ num          -- 0.5-sensitive

-- With rounding (produces error)
addfp  : (num & num) ⊸ M[u] num
mulfp  : (num ⊗ num) ⊸ M[u] num
divfp  : (num ⊗ num) ⊸ M[u] num
sqrtfp : ![0.5] num ⊸ M[u] num
```

**Example: Squaring function**

```
pow2 : ![2] num ⊸ M[ε] num
pow2 = λx. rnd(mul(x, x))
```

- 2-sensitive because x² has derivative 2x (linearized sensitivity)
- Produces ε error from single rounding

**Example: Fourth power via composition**

```
pow4 : num ⊸ M[3ε] num
pow4 = λx. letM y = pow2 x in pow2 y
```

Error analysis:
- First pow2: produces ε error
- That error fed to second pow2 (2-sensitive): amplified to 2ε
- Second pow2: produces ε local error
- Total: 2ε + ε = 3ε

────────────────────────────────────────────────────────────────────────────────
                                                    // implementation
────────────────────────────────────────────────────────────────────────────────

## Implementation Results

**Algorithm:** Bottom-up sensitivity inference based on Gaboardi et al. (2013)

**Complexity:** Linear in program size

**Performance benchmarks:**

| Benchmark | Operations | NumFuzz Time | FPTaylor Time | Gappa Time |
|-----------|------------|--------------|---------------|------------|
| Horner50 | 100 | 9ms | 5s | - |
| MatMul16 | 7,936 | 40ms | - | - |
| MatMul64 | 520,192 | 10s | - | - |
| MatMul128 | 4,177,920 | 18min | - | - |

**Bound quality:** Competitive with FPTaylor/Gappa, often within 2x of optimal.

**Strength:** Bounds hold for ALL positive real inputs (not just specified intervals).

────────────────────────────────────────────────────────────────────────────────
                                                    // hydrogen // relevance
────────────────────────────────────────────────────────────────────────────────

## Relevance to Hydrogen

### 1. Graded Types for Bounded Schema Atoms

NumFuzz's `M[ε]` pattern directly maps to Hydrogen's bounded types:

```purescript
-- NumFuzz style
M[ε] num  -- computation producing value with ≤ε error

-- Hydrogen analog
Bounded min max behavior num  -- value within [min, max] with behavior
```

The graded monad tracks how errors compose. Hydrogen could track how
**approximations compose** through the rendering pipeline.

### 2. Sensitivity as Design Space Distance

The `!s` comonad scales metrics. For Hydrogen:

```purescript
-- Color interpolation sensitivity
lerp : ![0.5] Color ⊸ ![0.5] Color ⊸ Ratio ⊸ Color

-- Layout constraint sensitivity  
constrain : ![1] Dimension ⊸ Constraint ⊸ Dimension
```

This could inform how changes propagate through:
- Color space conversions (perceptual uniformity)
- Layout constraint solving
- Animation interpolation

### 3. Additive vs Multiplicative Composition

The `&` vs `⊗` distinction matters for Element composition:

```purescript
-- Shared state (additive): sensitivity = max
Container : (Element & Element) ⊸ Element

-- Independent state (multiplicative): sensitivity = sum  
Parallel : (Element ⊗ Element) ⊸ Element
```

### 4. Neighborhood Monad for Approximation

The (ideal, approximate) pair pattern could model:

```purescript
-- Design intent vs rendered result
Approximate r Element = { ideal : Element, rendered : Element, bound : r }

-- Ensures rendered output is "close enough" to design intent
```

### 5. GPU Buffer Error Tracking

For WebGPU rendering, track precision loss:

```purescript
-- Float32 buffer with known precision bounds
GPUBuffer : M[float32_epsilon] (Array Float32)

-- Composition through shader pipeline
shader : M[ε1] Texture ⊸ M[ε2] Uniforms ⊸ M[ε1 + ε2 + shader_error] Fragment
```

### 6. Serialization Roundtrip Guarantees

For `GPUStorable` typeclass:

```purescript
-- Roundtrip within epsilon
serialize   : a → M[0] ByteArray           -- exact
deserialize : ByteArray → M[ε] a           -- may lose precision
roundtrip   : a → M[ε] a                   -- bounded total error
```

────────────────────────────────────────────────────────────────────────────────
                                                              // bean
────────────────────────────────────────────────────────────────────────────────

## Bean: Backward Error Analysis

Bean is a first-order programming language for **backward error analysis** — determining
the smallest input perturbation that makes the approximate output equal to the ideal output.

### Why Backward Error Matters

**Forward error:** "How wrong is my answer?"
**Backward error:** "What problem did I actually solve?"

The relationship:
```
forward_error ≤ condition_number × backward_error
```

A program can have:
- Large forward error but small backward error → problem is ill-conditioned
- Large backward error → algorithm is unstable

**Key insight from Kellison:** Backward error bounds are NOT compositional in general.
But they ARE compositional when variables are not duplicated with conflicting error
assignments. This motivates strict linearity.

### Type Syntax

```
α ::= dnum | α ⊗ α                    -- discrete types (no backward error)
σ ::= unit | α | num | σ ⊗ σ | σ + σ  -- linear types (can have backward error)

Γ ::= ∅ | Γ, x :r σ                   -- linear context with grades
Φ ::= ∅ | Φ, z : α                    -- discrete context (no grades)
```

**Dual context judgment:** `Φ | Γ ⊢ e : τ`
- Variables in Φ: can be duplicated, cannot have backward error
- Variables in Γ: cannot be duplicated, can have backward error

### Core Insight: Why Strict Linearity?

Consider `h(x) = ax² + bx`. The variable `x` appears in both subexpressions.

For `f(x) = ax²`: backward stability requires `x̃_f = x·e^δ₂`
For `g(x) = bx`: backward stability requires `x̃_g = x·e^(δ₃/2)`

**Problem:** There is no single `x̃` that works for both simultaneously!

**Solution:** Bean's strict linearity ensures we never need to reconcile multiple
backward error requirements for the same variable.

**Escape hatch:** Discrete variables (marked with `!`) can be duplicated because
they carry zero backward error.

### Primitive Operations

```
-- Addition: ε backward error to each input
(Add) Φ | Γ, x :ε+r₁ num, y :ε+r₂ num ⊢ add x y : num

-- Multiplication: ε/2 backward error to each input  
(Mul) Φ | Γ, x :ε/2+r₁ num, y :ε/2+r₂ num ⊢ mul x y : num

-- Discrete multiplication: all error to linear arg
(DMul) Φ, z : dnum | Γ, x :ε+r num ⊢ dmul z x : num
```

The grades accumulate through composition via the `r + Γ` operation.

### Let Binding (Key Rule)

```
    Φ | Γ ⊢ e : τ       Φ | Δ, x :r τ ⊢ f : σ
    ─────────────────────────────────────────────  (Let)
    Φ | r + Γ, Δ ⊢ let x = e in f : σ
```

When `e` is substituted for `x` (used with grade `r`), the backward error `r`
propagates to all variables in `Γ`.

────────────────────────────────────────────────────────────────────────────────
                                              // backward // error // lenses
────────────────────────────────────────────────────────────────────────────────

## Backward Error Lenses (Novel Construction)

**Definition (Kellison, Definition 28):**

A backward error lens `L : X → Y` is a triple `(f, f̃, b)` where:

- `f : X → Y` — the **forward map** (ideal computation)
- `f̃ : X → Y` — the **approximation map** (floating-point computation)  
- `b : X × Y → X` — the **backward map** (constructs the witness)

Subject to two properties:

**Property 1 (Bounded backward error):**
```
∀x ∈ X, y ∈ Y.  d_X(x, b(x, y)) ≤ d_Y(f̃(x), y)
```
The backward map produces a point close to the original input.

**Property 2 (Exact witness):**
```
∀x ∈ X, y ∈ Y.  f(b(x, y)) = y
```
The backward error witness is exact: applying the ideal function to the
perturbed input gives exactly the target output.

### The Category Bel

**Objects:** Generalized distance spaces `(M, d : M × M → R ∪ {±∞})`
with non-positive self-distance: `d(x, x) ≤ 0`.

**Morphisms:** Backward error lenses satisfying Properties 1 and 2.

**Identity:** `(id_X, id_X, π₂)` — identity forward, identity approx, project second

**Composition:** Given `(f₁, f̃₁, b₁) : X → Y` and `(f₂, f̃₂, b₂) : Y → Z`:

```
f   = f₁ ; f₂                           -- compose forwards
f̃   = f̃₁ ; f̃₂                           -- compose approximations
b   = (x, z) ↦ b₁(x, b₂(f̃₁(x), z))      -- chain backward maps
```

### Why Generalized Distances?

Standard metrics have `d(x, x) = 0`. But Bel allows `d(x, x) ≤ 0` (possibly negative).

**Purpose:** Enable compositional reasoning. The graded comonad **shifts** the metric:
```
D^r : (X, d_X) ↦ (X, d_X - r)
```

This creates "slack" in the lens conditions to accommodate non-zero backward error.

### Tensor Product in Bel

Given lenses `(f, f̃, b) : A → X` and `(g, g̃, b') : B → Y`:

```
(f ⊗ g)(a, b)     = (f(a), g(b))
(f̃ ⊗ g̃)(a, b)     = (f̃(a), g̃(b))
(b ⊗ b')((a,b), (x,y)) = (b(a,x), b'(b,y))
```

With metric: `d_{X⊗Y}((x₁,y₁), (x₂,y₂)) = max(d_X(x₁,x₂), d_Y(y₁,y₂))`

**Critical:** Bel does NOT have a Cartesian product (no diagonal map `A → A × A`).
This is the categorical manifestation of why backward error is not compositional
for duplicated variables.

### Discrete Objects (Escape Hatch)

A space is **discrete** if `d(x₁, x₂) = ∞` for all `x₁ ≠ x₂`.

For discrete objects, we CAN define a diagonal:
```
t_X : X → X ⊗ X
t_X(x) = (x, x)
b_t(x, (x₁, x₂)) = x
```

**Why it works:** The lens conditions only need to hold for points at finite distance.
In a discrete space, only identical points are at finite distance.
So `x₁ = x₂ = x`, and reconciliation is trivial.

### The Graded Comonad

```
D^r : Bel → Bel
D^r(X, d_X) = (X, d_X - r)
```

**Object map:** Shift the metric down by r.
**Arrow map:** Identity on underlying functions.

**Key operations:**
- Counit `ε : D⁰X → X` — identity
- Comultiplication `δ : D^{q+r}X → D^q(D^r X)` — identity
- Weakening `m_{q≤r} : D^r X → D^q X` — identity (for q ≤ r)

**No contraction map** `D^{r+s}A → D^r A ⊗ D^s A` — same reason as no diagonal.

### Lens for Addition

```
L_add : D^ε(R) ⊗ D^ε(R) → R

f_add(x₁, x₂)     = x₁ + x₂
f̃_add(x₁, x₂)     = (x₁ + x₂)·e^δ,  |δ| ≤ ε
b_add((x₁,x₂), x₃) = (x₃·x₁/(x₁+x₂), x₃·x₂/(x₁+x₂))
```

The backward map distributes the error proportionally.

### Lens for Multiplication

```
L_mul : D^{ε/2}(R) ⊗ D^{ε/2}(R) → R

f_mul(x₁, x₂)     = x₁ · x₂
f̃_mul(x₁, x₂)     = x₁ · x₂ · e^δ,  |δ| ≤ ε
b_mul((x₁,x₂), x₃) = (x₁·√(x₃/(x₁x₂)), x₂·√(x₃/(x₁x₂)))
```

Each input gets half the error (hence ε/2 grade).

────────────────────────────────────────────────────────────────────────────────
                                              // backward // soundness
────────────────────────────────────────────────────────────────────────────────

## Backward Error Soundness

**Theorem (Kellison, Theorem 10):**

Let `Φ | x₁ :r₁ σ₁, ..., xₙ :rₙ σₙ ⊢ e : σ` be well-typed.

For any substitutions `p̄ ⊨ Φ` and `k̄ ⊨ Γ`, if:
```
e[p̄/dom(Φ)][k̄/dom(Γ)] ⇓_ap v
```

Then there exists `l̄ ⊨ Γ` such that:
```
e[p̄/dom(Φ)][l̄/dom(Γ)] ⇓_id v
```

And for each `kᵢ ∈ k̄` and `lᵢ ∈ l̄`:
```
d_{σᵢ}(kᵢ, lᵢ) ≤ rᵢ
```

**In words:** If the approximate computation produces `v`, then there exist
perturbed inputs `l̄` such that the ideal computation also produces `v`,
and each input perturbation is bounded by its grade.

**Proof structure:**
1. Interpret Bean in Bel via Definition 31
2. Define ΛS (intermediate language) with ideal/approximate semantics
3. Use forgetful functors `U_id, U_ap : Bel → Set` to project
4. Pairing lemma relates Bel interpretation to ΛS interpretation
5. Soundness + adequacy of ΛS
6. Backward map constructs the witness

────────────────────────────────────────────────────────────────────────────────
                                              // bean // examples
────────────────────────────────────────────────────────────────────────────────

## Example: Dot Product

```
DotProd2 x y :=
  let (x0, x1) = x in
  let (y0, y1) = y in
  let v = mul x0 y0 in
  let w = mul x1 y1 in
  add v w
```

**Typing judgment:**
```
∅ | x :3ε/2 R², y :3ε/2 R² ⊢ DotProd2 x y : R
```

**Analysis:**
- Each `mul` contributes ε/2 per input
- `add` contributes ε per input
- Total per vector: ε/2 + ε = 3ε/2

## Example: Polynomial Evaluation

**Naive (PolyVal):** `z : R | a :3ε R³ ⊢ PolyVal a z : R`
**Horner:** `z : R | a :4ε R³ ⊢ Horner a z : R`

Surprisingly, Horner has **worse** worst-case backward error despite fewer operations!

But per-coefficient analysis reveals more:
```
-- PolyVal: uniform error across coefficients
z : R | a₀ :2ε R, a₁ :3ε R, a₂ :3ε R ⊢ PolyVal' : R

-- Horner: error concentrates on high-order coefficients  
z : R | a₀ :ε R, a₁ :3ε R, a₂ :4ε R ⊢ Horner' : R
```

Bean enables fine-grained stability analysis.

## Example: Linear Solver (with control flow)

```
LinSolve ((a00, a01), (a10, a11)) (b0, b1) :=
  let x0_or_err = div b0 a00 in
  case x0_or_err of
    inl (x0) =>
      dlet d_x0 = !x0 in        -- promote to discrete for reuse
      let s0 = dmul d_x0 a10 in
      let s1 = sub b1 s0 in
      let x1_or_err = div s1 a11 in
      case x1_or_err of
        inl (x1) => inl (d_x0, x1)
        | inr (err) => inr err
    | inr (err) => inr err
```

**Type:** `A :5ε/2 R²ˣ², b :3ε/2 R² ⊢ LinSolve A b : R² + err`

Demonstrates: conditionals, error handling, discrete promotion for reuse.

────────────────────────────────────────────────────────────────────────────────
                                              // bean // implementation
────────────────────────────────────────────────────────────────────────────────

## Implementation Results

**Algorithm:** Bottom-up coeffect inference (adapts Fuzz inference)

**Complexity:** Linear in program size

**Benchmarks (matching theoretical worst-case bounds):**

| Benchmark | Input Size | Ops | Bean Bound | Theoretical | Time |
|-----------|------------|-----|------------|-------------|------|
| DotProd | 500 | 999 | 5.55e-14 | 5.55e-14 | 30s |
| Horner | 500 | 1000 | 1.11e-13 | 1.11e-13 | 10s |
| MatVecMul | 50×50 | 4950 | 5.55e-15 | 5.55e-15 | 1000s |
| Sum | 1000 | 999 | 1.11e-13 | 1.11e-13 | 30s |

**Key result:** Bean's inferred bounds exactly match worst-case theoretical bounds
from Higham (2002).

**Comparison to dynamic analysis (Fu et al. 2015):**

| Benchmark | Bean | Fu et al. | 
|-----------|------|-----------|
| cos [0.0001, 0.01] | 1.33e-15 | 5.43e-09 |
| sin [0.0001, 0.01] | 1.44e-15 | 1.10e-16 |

Bean provides tighter sound bounds than heuristic dynamic analysis.

────────────────────────────────────────────────────────────────────────────────
                                              // hydrogen // applications
────────────────────────────────────────────────────────────────────────────────

## Applications to Hydrogen

### 1. Backward Error Lenses for Serialization

The `GPUStorable` roundtrip guarantee is exactly a backward error lens:

```purescript
-- Lens for serialization roundtrip
L_serialize : Schema.a → ByteArray

f(x)   = serialize(x)           -- ideal: exact encoding
f̃(x)   = serialize_fp(x)        -- approximate: may quantize
b(x,y) = deserialize(y)         -- backward: reconstruct from bytes

-- Property 2 guarantees: deserialize(serialize_fp(x)) recovers x̃
-- Property 1 guarantees: d(x, x̃) ≤ ε
```

This formalizes the TODO from `docs/TODO_PAPERS.md`:
> Lean4 proof: `deserialize (serialize x) = x`

### 2. Dual Contexts for Element Composition

Bean's `Φ | Γ` dual context maps to Hydrogen's architecture:

```purescript
-- Discrete context Φ: configuration that doesn't change
-- Linear context Γ: state that flows through rendering

renderElement : 
  Config       -- Φ: theme, breakpoints, fonts (reusable)
  | State :ε   -- Γ: current values (linear, has error)
  ⊢ Element
```

### 3. Strict Linearity for Deterministic Rendering

Bean proves: backward error bounds require strict linearity.

For Hydrogen at billion-agent scale:
- Each Element must produce **deterministic output**
- Duplicating state creates **divergent error bounds**
- Linear types prevent this by construction

```purescript
-- FORBIDDEN: duplicating state with different error requirements
bad : State → Element ⊗ Element  -- no diagonal!

-- ALLOWED: discrete config can be shared
good : Config | State → Element
```

### 4. Compositional Error Through Pipeline

Bean's let-binding shows error propagation:

```purescript
-- Each stage adds its error, scaled by downstream sensitivity
pipeline : Input :r → Output

-- Stage 1 error r₁ affects all downstream
-- Stage 2 error r₂ affects stages 3+
-- Total: r₁·s₂·s₃ + r₂·s₃ + r₃
```

For rendering pipeline:
```
Layout → Paint → Composite → Rasterize → Display

-- Errors accumulate through each stage
-- Sensitivity tells us how much each stage amplifies upstream errors
```

### 5. Discrete/Linear for Design Tokens

Bean's type distinction maps to design system architecture:

```purescript
-- Design tokens are discrete (exact, reusable)
tokens : Discrete TokenScale

-- Computed values are linear (have error, used once)
computedSize : Linear Dimension

-- Safe: discrete tokens inform linear computation
applyToken : Token | Size :ε ⊢ StyledSize
```

### 6. The Category Bel for Bidirectional Transforms

Hydrogen needs bidirectional transforms for:
- State ↔ Element (view function and its "inverse")
- Schema ↔ JSON (serialization)
- Design ↔ Code (Figma import/export)

Backward error lenses provide the mathematical foundation:
```
f   : ideal transform
f̃   : approximate transform (may lose information)
b   : backward transform (reconstructs with bounded error)
```

### 7. Practical Type Annotations

From Bean's implementation, we learn that:
- Grade inference is linear-time (scalable)
- Users specify which variables carry error
- System computes optimal bounds automatically

For Hydrogen:
```purescript
-- User specifies: "color has precision loss"
render : Theme | color :ε Color ⊢ Pixel

-- System infers: total pipeline error is 3ε
-- (from composition of color → linear RGB → sRGB → quantized)
```

────────────────────────────────────────────────────────────────────────────────
                                                    // key // algorithms
────────────────────────────────────────────────────────────────────────────────

## Key Algorithms

### Sensitivity Inference (NumFuzz)

**Input:** Term `e`, context skeleton `Γ•`
**Output:** Annotated context `Γ`, type `σ` such that `Γ ⊢ e : σ`

```
Algorithm: Bottom-up inference
1. For each subterm, compute minimal required sensitivity
2. Combine using context operations (+, ·, max)
3. Compare against declared bounds via subtyping

Complexity: O(n) where n = |e|
```

### Coeffect Inference (Bean)

**Input:** Term `e`, context skeleton `Φ | Γ•`
**Output:** Annotated context `Γ`, type `σ` such that `Φ | Γ ⊢ e : σ`

```
Algorithm: Bottom-up with linearity check
1. Recursively infer grades for subterms
2. Ensure dom(Γ₁) ∩ dom(Γ₂) = ∅ (strict linearity)
3. Combine grades via r + Γ operation

Complexity: O(n) where n = |e|
```

### Backward Map Construction

Given composition `(f₁, f̃₁, b₁) ; (f₂, f̃₂, b₂)`:

```
b(x, z) = b₁(x, b₂(f̃₁(x), z))

Steps:
1. Apply f̃₁ to get intermediate approximate result
2. Apply b₂ to find witness for second stage
3. Apply b₁ to find witness for first stage
```

This is the key insight: backward maps compose by chaining.

────────────────────────────────────────────────────────────────────────────────
                                                    // references
────────────────────────────────────────────────────────────────────────────────

## Key References

**Primary Source:**
- Kellison (2024) — "Type-Based Approaches to Rounding Error Analysis", PhD Dissertation

**Foundational Type Systems:**
- Reed & Pierce (2010) — Fuzz: sensitivity type systems for differential privacy
- Katsumata (2014) — Graded monads and categorical semantics
- Brunel et al. (2014) — Coeffects: context-dependent computation
- Gaboardi et al. (2016) — Combining effects and coeffects
- Benton (1994) — Linear/Non-Linear logic (dual contexts)

**Numerical Analysis:**
- Higham (2002) — "Accuracy and Stability of Numerical Algorithms"
- Olver (1978) — Relative precision metric
- IEEE 754-2019 — Floating-point arithmetic standard
- Corless & Fillion (2013) — Backward error and residual methods

**Lenses and Bidirectional Programming:**
- Foster et al. (2007) — Lenses for bidirectional transformations
- Riley (2018) — Categories of lenses
- Hedges (2018) — Survey of lens applications

**Implementation:**
- Gaboardi et al. (2013) — Sensitivity inference algorithm
- de Amorim et al. (2014) — Bottom-up inference for Fuzz
- Fu et al. (2015) — Dynamic backward error analysis

**Formal Verification:**
- Kellison et al. (2023) — LAProof: formal proofs of backward error in Coq
- Boldo & Melquiond (2011) — Flocq: floating-point in Coq

────────────────────────────────────────────────────────────────────────────────
                                                    // summary
────────────────────────────────────────────────────────────────────────────────

## Summary for Hydrogen Implementation

### From NumFuzz:
1. **Graded monads** track error accumulation through composition
2. **Sensitivity scaling** via `!s` comonad
3. **Neighborhood monad** pairs (ideal, approximate) values
4. **Additive vs multiplicative** products for different composition patterns

### From Bean:
1. **Backward error lenses** for bidirectional transforms with guarantees
2. **Strict linearity** prevents non-compositional error scenarios
3. **Dual contexts** separate reusable config from linear state
4. **Metric shifting** via graded comonad enables bounded error

### Implementation Path:
1. Define `GPUStorable` as backward error lens
2. Track precision through rendering pipeline
3. Use dual contexts for Theme | State separation
4. Prove serialization roundtrip in Lean4 using lens properties
5. Inference algorithm for automatic bound computation

───────────────────────────────────────────────────────────────────────────────
                                                 // chapter // 5 // conclusion
───────────────────────────────────────────────────────────────────────────────

## Chapter 5: Conclusion

This chapter concludes our investigation of designing languages that unify the tasks of writing
numerical programs and reasoning about their accuracy.

### Summary of Contributions

In **Chapter 3**, we demonstrated that it is possible to design a language for forward error analysis
with **NumFuzz**, a higher-order functional programming language with a linear type system that can
express quantitative bounds on forward error. NumFuzz combines a sensitivity type system with a
novel graded monad to track the forward relative error of programs. We proposed a metric semantics
for NumFuzz and proved a central soundness theorem using this semantics, which guarantees that
well-typed programs with graded monadic type adhere to the relative error bound specified by their
type. A prototype implementation of NumFuzz illustrates that type-based approaches to rounding
error analysis can provide strong theoretical guarantees while being useful in practice, narrowing the
gap between rigorous analysis and realistic numerical computations.

In **Chapter 4**, we presented **Bean**, a programming language for backward error analysis.
As the first static analysis tool for backward error analysis, Bean demonstrates the feasibility of
using static analysis techniques to automatically infer backward error bounds and ensure the backward
stability of programs. A key insight from our development of Bean is that the composition of two
backward stable programs remains backward stable provided they do not assign backward error to
shared variables. Thus, to ensure that Bean programs satisfy a backward stability guarantee, Bean
employs a strict linear type system that restricts the duplication of variables.

We established the soundness of Bean by developing the category of backward error lenses — **Bel** —
and interpreting Bean programs as morphisms in this category. This semantic foundation distinguishes
Bean from Fuzz-like languages, including NumFuzz, which interpret programs in the category of metric
spaces. Using Bel, we formulated and proved a soundness theorem for Bean, which guarantees that
well-typed programs have bounded backward error. A prototype implementation of Bean demonstrates
that our approach can be used to infer accurate per-variable backward error bounds.

───────────────────────────────────────────────────────────────────────────────
                                               // future // work // numfuzz
───────────────────────────────────────────────────────────────────────────────

## Future Work: NumFuzz (Section 3.9)

### Extensions to the Type System

1. **Higher-order functions:** The current NumFuzz restricts higher-order functions to be 1-sensitive.
   Extending to general sensitivity annotations would enable more precise analysis of function-valued
   computations.

2. **Recursive programs:** Adding recursion while preserving termination guarantees requires careful
   handling of potential infinite computations. Potential approaches include:
   - Syntactic termination guarantees (structural recursion)
   - Metric-theoretic fixed-point operators

3. **Polymorphism:** Adding parametric polymorphism would enable generic libraries with uniform
   error bounds across different numeric types.

### Implementation Improvements

1. **Smarter bound improvement:** The current prototype uses naive bound computation. Incorporating
   constraint solving techniques (similar to FPTaylor) could yield tighter bounds.

2. **Parallel analysis:** The sensitivity inference algorithm is embarrassingly parallel across program
   subterms. GPU acceleration could enable analysis of larger programs.

3. **Incremental reanalysis:** For interactive applications, incremental type-checking could provide
   feedback as users edit programs.

### Integration with Verified Toolchains

1. **Coq extraction:** Generating Coq code from NumFuzz programs with proofs of error bounds.

2. **Flocq integration:** Using the Flocq library for formal verification of floating-point properties.

3. **Automated theorem proving:** Integrating with SMT solvers for automatic bound verification.

───────────────────────────────────────────────────────────────────────────────
                                               // future // work // bean
───────────────────────────────────────────────────────────────────────────────

## Future Work: Bean (Section 4.8)

### Language Extensions

1. **Higher-order functions:** Adding function types while maintaining backward error semantics.
   The challenge lies in composing backward error through function closures.

2. **First-class arrays:** Supporting array operations with per-element backward error tracking.
   This enables analysis of matrix operations beyond what linear algebra libraries provide.

3. **Exception handling:** Incorporating NaN and infinity propagation while maintaining backward
   error guarantees.

4. **Control flow:** Extending to loops and recursion with termination guarantees and error bounds.

### Semantic Extensions

1. **Relaxed linearity:** Investigating whether affine types (allowing discarding of variables)
   could provide useful backward error analysis with less programmer burden.

2. **Probabilistic backward error:** Developing a semantic framework for probabilistic backward
   error analysis that accounts for stochastic rounding.

3. **Relative backward error:** Extending Bean to track relative backward error using the RP metric.

### Practical Improvements

1. **User-defined primitives:** Allowing users to specify backward error lenses for custom numerical
   operations beyond the built-in primitives.

2. **Automatic discrete promotion:** Developing heuristics to automatically identify when variables
   can be safely promoted to discrete type without losing useful error bounds.

3. **Error visualization:** Tools that visualize the backward error propagation through program
   dependence graphs.

### Connection to Verified Compilation

1. **Compiling to verified numerical code:** Using Bean annotations to guide compilation to
   verified floating-point implementations.

2. **Roundoff verification:** Integrating Bean's backward error bounds with static analysis tools
   like Fluctuat and Gappa.

───────────────────────────────────────────────────────────────────────────────
                                                         // bibliography
───────────────────────────────────────────────────────────────────────────────

## Bibliography

[1] Rosa Abbasi and Eva Darulova. 2023. Modular Optimization-Based Roundoff Error Analysis of
Floating-Point Programs. In Static Analysis, Manuel V. Hermenegildo and Jose F. Morales (Eds.).
Springer Nature Switzerland, Cham, 41-64.

[2] S. Abramsky and N. Tzevelekos. 2011. Introduction to Categories and Categorical Logic. In New
Structures for Physics, Bob Coecke (Ed.). Springer Berlin Heidelberg, Berlin, Heidelberg, 1-94.

[3] Mehrdad Aliasgari, Marina Blanton, Yihua Zhang, and Aaron Steele. 2013. Secure Computation
on Floating Point Numbers. In 20th Annual Network and Distributed System Security Symposium,
NDSS 2013, San Diego, California, USA, February 24-27, 2013. The Internet Society.

[4] E. Anderson, Z. Bai, C. Bischof, S. Blackford, J. Demmel, J. Dongarra, J. Du Croz, A. Greenbaum,
S. Hammarling, A. McKenney, and D. Sorensen. 1999. LAPACK Users' Guide (third ed.).
Society for Industrial and Applied Mathematics, Philadelphia, PA.

[5] Andrew W. Appel and Ariel E. Kellison. 2024. VCFloat2: Floating-Point Error Analysis in Coq.
In Proceedings of the 13th ACM SIGPLAN International Conference on Certified Programs and
Proofs (London, UK) (CPP 2024). Association for Computing Machinery, New York, NY, USA,
14-29.

[6] Robert Atkey. 2009. Parameterised Notions of Computation. Journal of Functional Programming
19, 3-4 (2009), 335-376.

[7] Steve Awodey. 2010. Category Theory (2nd ed.). Oxford University Press.

[8] Arthur Azevedo de Amorim, Marco Gaboardi, Justin Hsu, Shin-ya Katsumata, and Ikram Cherigui.
2017. A semantic account of metric preservation. SIGPLAN Not. 52, 1 (Jan 2017), 545-556.

[9] P. N. Benton. 1994. A Mixed Linear and Non-Linear Logic: Proofs, Terms and Models (Extended
Abstract). In Selected Papers from the 8th International Workshop on Computer Science Logic
(CSL '94). Springer-Verlag, Berlin, Heidelberg, 121-135.

[10] L Susan Blackford, Antoine Petitet, Roldan Pozo, Karin Remington, R Clint Whaley, James
Demmel, Jack Dongarra, Iain Duff, Sven Hammarling, Greg Henry, et al. 2002. An updated set
of basic linear algebra subprograms (BLAS). ACM Trans. Math. Software 28, 2 (2002), 135-151.

[11] Aaron Bohannon, J. Nathan Foster, Benjamin C. Pierce, Alexandre Pilkiewicz, and Alan Schmitt.
2008. Boomerang: resourceful lenses for string data. In Proceedings of the 35th Annual ACM
SIGPLAN-SIGACT Symposium on Principles of Programming Languages (POPL '08). Association
for Computing Machinery, New York, NY, USA, 407-419.

[12] Sylvie Boldo, Claude-Pierre Jeannerod, Guillaume Melquiond, and Jean-Michel Muller. 2023.
Floating-point arithmetic. Acta Numerica 32 (2023), 203-290.

[13] Sylvie Boldo and Guillaume Melquiond. 2011. Flocq: A Unified Library for Proving Floating-Point
Algorithms in Coq. In Proceedings of the 2011 IEEE 20th Symposium on Computer Arithmetic
(ARITH '11). IEEE Computer Society, USA, 243-252.

[14] Sylvie Boldo and Guillaume Melquiond. 2017. Computer Arithmetic and Formal Proofs. ISTE
Press - Elsevier. 326 pages.

[15] Folkmar Bornemann. 2007. A Model for Understanding Numerical Stability. IMA J. Numer. Anal.
27, 2 (2007), 219-231.

[16] Aloïs Brunel, Marco Gaboardi, Damiano Mazza, and Steve Zdancewic. 2014. A Core Quantitative
Coeffect Calculus. In Programming Languages and Systems, Zhong Shao (Ed.). Springer Berlin
Heidelberg, Berlin, Heidelberg, 351-370.

[17] Alexandre Chapoutot. 2010. Interval Slopes as a Numerical Abstract Domain for Floating-Point
Variables. In Static Analysis, Radhia Cousot and Matthieu Martel (Eds.). Springer Berlin Heidelberg,
Berlin, Heidelberg, 184-200.

[18] Alexandre Chapoutot and Matthieu Martel. 2009. Abstract Simulation: A Static Analysis of
Simulink Models. In 2009 International Conference on Embedded Software and Systems. 83-92.

[19] Konstantinos Chatzikokolakis, Daniel Gebler, Catuscia Palamidessi, and Lili Xu. 2014. Generalized
Bisimulation Metrics. In CONCUR 2014 - Concurrency Theory, Paolo Baldan and Daniele Gorla
(Eds.). Springer Berlin Heidelberg, Berlin, Heidelberg, 32-46.

[20] Liqian Chen, Antoine Mine, and Patrick Cousot. 2008. A Sound Floating-Point Polyhedra Abstract
Domain. In Programming Languages and Systems, G. Ramalingam (Ed.). Springer Berlin Heidelberg,
Berlin, Heidelberg, 3-18.

[21] Liqian Chen, Antoine Mine, Ji Wang, and Patrick Cousot. 2009. Interval Polyhedra: An Abstract
Domain to Infer Interval Linear Relationships. In Proceedings of the 16th International Symposium
on Static Analysis (SAS '09). Springer-Verlag, Berlin, Heidelberg, 309-325.

[22] Liqian Chen, Antoine Mine, Ji Wang, and Patrick Cousot. 2010. An Abstract Domain to Discover
Interval Linear Equalities. In 11th International Conference on Verification, Model Checking, and
Abstract Interpretation (VMCAI'10). Springer, Spain, 112-128.

[23] Yuanfeng Chen, Gaofeng Huang, Junjie Shi, Xiang Xie, and Yilin Yan. 2020. Rosetta: A
Privacy-Preserving Framework Based on TensorFlow.

[24] Michael P. Connolly, Nicholas J. Higham, and Theo Mary. 2021. Stochastic Rounding and Its
Probabilistic Backward Error Analysis. SIAM Journal on Scientific Computing 43, 1 (2021),
A566-A585.

[25] George Constantinides, Fredrik Dahlqvist, Zvonimir Rakamaric, and Rocco Salvia. 2021. Rigor-
ous Roundoff Error Analysis of Probabilistic Floating-Point Computations. In Computer Aided
Verification, Alexandra Silva and K. Rustan M. Leino (Eds.). Springer International Publishing,
Cham, 626-650.

[26] Robert M. Corless and Nicolas Fillion. 2013. A Graduate Introduction to Numerical Methods.
Springer New York, New York, NY, USA.

[27] Patrick Cousot, Radhia Cousot, Jerome Feret, Laurent Mauborgne, Antoine Mine, David Monniaux,
and Xavier Rival. 2005. The ASTREE Analyzer. In Programming Languages and Systems, Mooly
Sagiv (Ed.). Springer Berlin Heidelberg, Berlin, Heidelberg, 21-30.

[28] Raphaelle Crubille and Ugo Dal Lago. 2015. Metric reasoning about λ-terms: The affine case.
In Proceedings of the 2015 30th Annual ACM/IEEE Symposium on Logic in Computer Science
(LICS '15). IEEE Computer Society, USA, 633-644.

[29] Germund Dahlquist and Åke Bjorck. 2008. Numerical Methods in Scientific Computing, Volume I.
Society for Industrial and Applied Mathematics, Philadelphia, PA, USA.

[30] Ugo Dal Lago and Francesco Gavazzo. 2022a. Effectful program distancing. Proc. ACM Program.
Lang. 6, POPL, Article 19 (Jan 2022), 30 pages.

[31] Ugo Dal Lago and Francesco Gavazzo. 2022b. A Relational Theory of Effects and Coeffeets.
Proc. ACM Program. Lang. 6, POPL, Article 31 (Jan 2022), 28 pages.

[32] Nasrine Damouche, Matthieu Martel, Pavel Panchekha, Chen Qiu, Alexander Sanchez-Stern, and
Zachary Tatlock. 2017. Toward a Standard Benchmark Format and Suite for Floating-Point
Analysis. In Proceedings of the 10th International Workshop on Numerical Software Verification
(NSV 2017). Springer, 63-77.

[33] Loris D'Antoni, Marco Gaboardi, Emilio Jesús Gallego Arias, Andreas Haeberlen, and Benjamin
Pierce. 2013. Sensitivity Analysis Using Type-Based Constraints. In Proceedings of the 1st
Annual Workshop on Functional Programming Concepts in Domain-Specific Languages (FPCDSL
'13). Association for Computing Machinery, New York, NY, USA, 43-50.

[34] Eva Darulova, Anastasiia Izycheva, Fariha Nasir, Fabian Ritter, Heiko Becker, and Robert Bastian.
2018. Daisy - Framework for Analysis and Optimization of Numerical Programs (Tool Paper).
In International Conference on Tools and Algorithms for Construction and Analysis of Systems.

[35] Eva Darulova and Viktor Kuncak. 2014. Sound Compilation of Reals. In Proceedings of the 41st
ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages (POPL '14). Association
for Computing Machinery, New York, NY, USA, 235-248.

[36] Eva Darulova and Viktor Kuncak. 2017. Towards a Compiler for Reals. ACM Trans. Program.
Lang. Syst. 39, 2, Article 8 (Mar 2017), 28 pages.

[37] Arnab Das, Ian Briggs, Ganesh Gopalakrishnan, Sriram Krishnamoorthy, and Pavel Panchekha.
2020. Scalable yet rigorous floating-point error analysis. In Proceedings of the International
Conference for High Performance Computing, Networking, Storage and Analysis (SC '20). IEEE
Press, New York, NY, USA, Article 51, 14 pages.

[38] Marc Daumas and Guillaume Melquiond. 2010. Certification of Bounds on Expressions Involving
Rounded Operators. ACM Trans. Math. Softw. 37, 1, Article 2 (Jan 2010), 20 pages.

[39] Arthur Azevedo de Amorim, Marco Gaboardi, Emilio Jesús Gallego Arias, and Justin Hsu. 2014.
Really Natural Linear Indexed Type Checking. In Proceedings of the 26nd 2014 International
Symposium on Implementation and Application of Functional Languages (IFL '14). Association for
Computing Machinery, Boston, MA, USA, Article 5, 12 pages.

[40] Arthur Azevedo de Amorim, Marco Gaboardi, Justin Hsu, and Shin-ya Katsumata. 2021. Probabilistic
relational reasoning via metrics. In Proceedings of the 34th Annual ACM/IEEE Symposium on
Logic in Computer Science (LICS '19). IEEE Press, Vancouver, Canada, Article 40, 19 pages.

[41] Luiz Henrique de Figueiredo and Jorge Stolfi. 2004. Affine Arithmetic: Concepts and Applications.
Numerical Algorithms 37, 1 (2004), 147-158.

[42] Valeria de Paiva. 1991. The Dialectica Categories. Ph. D. Dissertation. University of Cambridge.

[43] Sebastian Fischer, ZhenJiang Hu, and Hugo Pacheco. 2015. The Essence of Bidirectional Programming.
Science China Information Sciences 58, 5 (2015), 1-21.

[44] Brendan Fong, David I. Spivak, and Rémy Tuyères. 2019. Backprop as Functor: A Compositional
Perspective on Supervised Learning. In 34th Annual ACM/IEEE Symposium on Logic in Computer
Science (LICS 2019). IEEE, 1-13.

[45] John Nathan Foster. 2009. Bidirectional Programming Languages. Ph. D. Dissertation. University
of Pennsylvania.

[46] J. Nathan Foster, Michael B. Greenwald, Jonathan T. Moore, Benjamin C. Pierce, and Alan
Schmitt. 2007. Combinators for Bidirectional Tree Transformations: A Linguistic Approach to the
View-Update Problem. ACM Trans. Program. Lang. Syst. 29, 3 (May 2007), 17-es.

[47] Nate Foster, Kazutaka Matsuda, and Janis Voigtlander. 2012. Three Complementary Approaches
to Bidirectional Programming. Generic and Indexed Programming: International Spring School,
SSGIP 2010, Oxford, UK, March 22-26, 2010, Revised Lectures. Springer, 1-46.

[48] Martin Franz and Stefan Katzenbeisser. 2011. Processing Encrypted Floating Point Signals. In
Proceedings of the Thirteenth ACM Multimedia Workshop on Multimedia and Security (MM & Sec
'11). Association for Computing Machinery, New York, NY, USA, 103-108.

[49] Zhoulai Fu, Zhaojun Bai, and Zhendong Su. 2015. Automated Backward Error Analysis for
Numerical Code. In Proceedings of the 2015 ACM SIGPLAN International Conference on Object-Oriented
Programming, Systems, Languages, and Applications (OOPSLA 2015). Association for Computing
Machinery, Pittsburgh, PA, USA, 639-654.

[50] S. Fujii, S. Katsumata, and P.-A. Mellies. 2016. Towards a Formal Theory of Graded Monads.
In Foundations of Software Science and Computation Structures (FOSSACS). Springer, 513-530.

[51] Marco Gaboardi, Andreas Haeberlen, Justin Hsu, Arjun Narayan, and Benjamin C. Pierce. 2013.
Linear Dependent Types for Differential Privacy. In Proceedings of the 40th Annual ACM SIGPLAN-SIGACT
Symposium on Principles of Programming Languages (POPL '13). Association for Computing
Machinery, Rome, Italy, 357-370.

[52] Marco Gaboardi, Shin-ya Katsumata, Dominic Orchard, Flavien Breuvart, and Tarmo Uustalu.
2016. Combining effects and coeffects via grading. SIGPLAN Not. 51, 9 (Sep 2016), 476-489.

[53] Sanjam Garg, Abhishek Jain, Zhengzhong Jin, and Yinuo Zhang. 2022. Succinct Zero Knowledge
for Floating Point Computations. In Proceedings of the 2022 ACM SIGSAC Conference on Computer
and Communications Security (CCS '22). Association for Computing Machinery, Los Angeles,
CA, USA, 1203-1216.

[54] Attila Gati. 2012. Miller Analyzer for Matlab: A Matlab Package for Automatic Roundoff
Analysis. Computing and Informatics 31, 4 (2012), 713-726.

[55] Francesco Gavazzo. 2018. Quantitative Behavioural Reasoning for Higher-order Effectful Programs:
Applicative Distances. In Proceedings of the 33rd Annual ACM/IEEE Symposium on Logic in
Computer Science (LICS '18). Association for Computing Machinery, Oxford, United Kingdom,
452-461.

[56] Francesco Gavazzo. 2019. Coinductive Equivalences and Metrics for Higher-order Languages with
Algebraic Effects. Ph. D. Thesis. Alma Mater Studiorum Universita di Bologna.

[57] Neil Ghani, Jules Hedges, Viktor Winschel, and Philipp Zahn. 2018. Compositional Game Theory.
In Proceedings of the 33rd Annual ACM/IEEE Symposium on Logic in Computer Science (LICS
'18). Association for Computing Machinery, Oxford, United Kingdom, 472-481.

[58] D. R. Ghica and A. I. Smith. 2014. Bounded Linear Types in a Resource Semiring. In Proceedings
of the 23rd European Symposium on Programming (ESOP 2014). Springer, 331-350.

[59] David K. Gifford and John M. Lucassen. 1986. Integrating functional and imperative programming.
In Proceedings of the 1986 ACM Conference on LISP and Functional Programming. Association
for Computing Machinery, Cambridge, Massachusetts, USA, 28-38.

[60] Jean-Yves Girard. 1987. Linear Logic. Theoretical Computer Science 50 (1987), 1-102.

[61] Jean-Yves Girard, Yves Lafont, and Paul Taylor. 1992. Bounded Linear Logic: A Modular Approach
to Polynomial-Time Computability. In Proceedings of the 7th Annual IEEE Symposium on Logic in
Computer Science (LICS '92). IEEE Computer Society, 15-25.

[62] Eric Goubault and Sylvie Putot. 2011. Static Analysis of Finite Precision Computations. In
Verification, Model Checking, and Abstract Interpretation (VMCAI). Springer, 232-247.

[63] Leopold Haller, Alberto Griggio, Martin Brain, and Daniel Kroening. 2012. Deciding Floating-Point
Logic with Systematic Abstraction. In Formal Methods in Computer-Aided Design (FMCAD 2012),
Cambridge, UK. IEEE, 131-140.

[64] John Harrison. 1997a. Floating Point Verification in HOL Light: The Exponential Function. In
International Conference on Algebraic Methodology and Software Technology (AMAST). Springer,
246-260.

[65] John Harrison. 1997b. Floating-Point Verification using Theorem Proving. In 14th International
Conference on Theorem Proving in Higher Order Logics (TPHOLs). Springer, 3-17.

[66] John Harrison. 1999. A Machine-Checked Theory of Floating Point Arithmetic. In International
Conference on Theorem Proving in Higher Order Logics (TPHOLs). Springer, 113-130.

[67] John Harrison. 2000. Formal Verification of Floating Point Trigonometric Functions. In Formal
Methods and Computer-Aided Design (FMCAD 2000). Springer, 217-233.

[68] Jules Hedges. 2018. Lenses for philosophers.

[69] Nicholas J. Higham. 2002. Accuracy and Stability of Numerical Algorithms (2nd ed.). Society for
Industrial and Applied Mathematics.

[70] Nicholas J. Higham and Theo Mary. 2019. A New Approach to Probabilistic Rounding Error
Analysis. SIAM Journal on Scientific Computing 41, 5 (2019), A2815-A2835.

[71] Martin Hofmann, Benjamin Pierce, and Daniel Wagner. 2011. Symmetric lenses. In Proceedings of
the 38th Annual ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages
(POPL '11). Association for Computing Machinery, Austin, Texas, USA, 371-384.

[72] Andreas Hohmann and Peter Deuflhard. 2003. Numerical Analysis in Modern Scientific Computing:
An Introduction. Springer.

[73] Chun-Yi Hu, Nicholas M. Patrikalakis, and Xiuzi Ye. 1996. Robust interval solid modelling Part I:
representations. Computer-Aided Design 28, 10 (1996), 807-817.

[74] IEEE Computer Society. 2019. IEEE Standard for Floating-Point Arithmetic. IEEE Std 754-2019.

[75] Ilse C. F. Ipsen and Hua Zhou. 2020. Probabilistic Error Analysis for Inner Products. SIAM J.
Matrix Anal. Appl. 41, 4 (2020), 1726-1741.

[76] William Kahan. 1996. The Improbability of Probabilistic Error Analyses for Numerical Computations.

[77] Liina Kamm and Jan Willemson. 2015. Secure floating point arithmetic and private satellite collision
analysis. International Journal of Information Security 14, 6 (2015), 531-548.

[78] Shin-ya Katsumata. 2014. Parametric Effect Monads and Semantics of Effect Systems. In Proceedings
of the 41st ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages (POPL
2014). Association for Computing Machinery, San Diego, California, USA, 633-646.

[79] Shin-ya Katsumata. 2018. A Double Category Theoretic Analysis of Graded Linear Exponential
Comonads. In Foundations of Software Science and Computation Structures. Springer, 110-127.

[80] Ariel E. Kellison and Andrew W. Appel. 2022. Verified Numerical Methods for Ordinary Differential
Equations. In Software Verification and Formal Methods for ML-Enabled Autonomous Systems. Springer,
147-163.

[81] Ariel E. Kellison, Andrew W. Appel, Mohit Tekriwal, and David Bindel. 2023. LAProof: A Library
of Formal Proofs of Accuracy and Correctness for Linear Algebra Programs. In 2023 IEEE 30th
Symposium on Computer Arithmetic (ARITH). IEEE Computer Society, Los Alamitos, CA, USA, 36-43.

[82] Ariel E. Kellison and Justin Hsu. 2024. Numerical Fuzz: A Type System for Rounding Error Analysis.
Proc. ACM Program. Lang. 8, PLDI, Article 226 (June 2024), 25 pages.

[83] Hsiang-Shang Ko and Zhenjiang Hu. 2017. An axiomatic basis for bidirectional programming.
Proceedings of the ACM on Programming Languages 2, POPL (2017), 1-29.

[84] Tom Leinster. 2014. Basic Category Theory. Cambridge University Press.

[85] Paul Blain Levy, John Power, and Hayo Thielecke. 2003. Modelling environments in call-by-value
programming languages. Information and Computation 185, 2 (2003), 182-210.

[86] Xiaoye S. Li, James W. Demmel, David H. Bailey, Greg Henry, Yozo Hida, Jimmy Iskandar, William
Kahan, Suh Y. Kang, Anil Kapur, Michael C. Martin, Brandon J. Thompson, Teresa Tung, and Daniel
J. Yoo. 2002. Design, implementation and testing of extended and mixed precision BLAS. ACM
Trans. Math. Softw. 28, 2 (2002), 152-205.

[87] Joannes M. Lucassen. 1987. Types and effects: Towards the integration of functional and imperative
programming. Technical Report. MIT Laboratory for Computer Science.

[88] J. M. Lucassen and D. K. Gifford. 1988. Polymorphic effect systems. In Proceedings of the 15th
ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages (POPL '88). Association
for Computing Machinery, New York, NY, USA, 47-57.

[89] Victor Magron, George A. Constantinides, and Alastair F. Donaldson. 2017. Certified Roundoff
Error Bounds Using Semidefinite Programming. ACM Trans. Math. Softw. 43, 4 (2017), 34:1-34:31.

[90] Guillaume Melquiond, Marc Daumas. 2010. Certification of Bounds on Expressions Involving Rounded
Operators. ACM Trans. Math. Softw. 37, 1 (2010), 2:1-2:20.

[91] Matthieu Martel. 2018. Strongly Typed Numerical Computations. In International Conference on
Formal Methods and Software Engineering (ICFEM). Springer, 197-214.

[92] Webb Miller and David Spooner. 1978. Algorithm 532: software for roundoff analysis. ACM Trans.
Math. Softw. 4, 4 (1978), 388-390.

[93] Antoine Mine. 2004. Relational abstract domains for the detection of floating-point run-time errors.
In European Symposium on Programming. Springer, 3-17.

[94] E. Moggi. 1989. Computational lambda-calculus and monads. In Proceedings. Fourth Annual
Symposium on Logic in Computer Science. 14-23.

[95] Eugenio Moggi. 1991. Notions of computation and monads. Information and Computation 93, 1
(1991), 55-92.

[96] Ramon E Moore, R Baker Kearfott, and Michael J Cloud. 2009. Introduction to interval analysis.
SIAM.

[97] Mariano M. Moscato, Laura Titolo, Marco A. Feliú, and César A. Muñoz. 2019. Provably Correct
Floating-Point Implementation of a Point-in-Polygon Algorithm. In Formal Methods – The Next
30 Years. Springer International Publishing, Cham, 21-37.

[98] Jean-Michel Muller. 2016. Elementary Functions: Algorithms and Implementation (3rd ed.). Birkhäuser
Basel.

[99] Jean-Michel Muller, Nicolas Brunie, Florent de Dinechin, Claude-Pierre Jeannerod, Mioara Joldes,
Vincent Lefevre, Guillaume Melquiond, Nathalie Revol, and Serge Torres. 2018. Handbook of
Floating-Point Arithmetic, 2nd edition. Birkhäuser Boston. 632 pages.

[100] Alan Mycroft, Dominic Orchard, and Tomas Petricek. 2015. Effect Systems Revisited–Control-Flow
Algebra and Semantics. In Essays Dedicated to Hanne Riis Nielson and Flemming Nielson on the
Occasion of Their 60th Birthdays. Springer-Verlag, Berlin, Heidelberg, 1-32.

───────────────────────────────────────────────────────────────────────────────
                                                    // bibliography // continued
───────────────────────────────────────────────────────────────────────────────

[101] Joseph P. Near, David Darais, Chike Abuah, Tim Stevens, Pranav Gaddamadugu, Lun Wang,
Neel Somani, Mu Zhang, Nikhil Sharma, Alex Shan, and Dawn Song. 2019. Duet: an expressive
higher-order language and linear type system for statically enforcing differential privacy. Proc.
ACM Program. Lang. 3, OOPSLA, Article 172 (Oct. 2019), 30 pages.

[102] Flemming Nielson and Hanne Riis Nielson. 1999. Type and Effect Systems. In Correct System
Design: Recent Insights and Advances. Springer Berlin Heidelberg, Berlin, Heidelberg, 114-136.

[103] Flemming Nielson, Hanne Riis Nielson, and Chris Hankin. 1999. Principles of Program Analysis.
Springer, Berlin, Heidelberg.

[104] Dianne P. O'Leary. 2009. Scientific Computing with Case Studies. Society for Industrial and Applied
Mathematics, Philadelphia, PA.

[105] F. W. J. Olver. 1978. A New Approach to Error Arithmetic. SIAM J. Numer. Anal. 15, 2 (1978),
368-393.

[106] F. W. J. Olver. 1982. Further developments of rp and ap error analysis. IMA J. Numer. Anal. 2, 3
(1982), 249-274.

[107] F. W. J. Olver and J. H. Wilkinson. 1982. A Posteriori Error Bounds for Gaussian Elimination.
IMA J. Numer. Anal. 2, 4 (1982), 377-406.

[108] Dominic Orchard, Tomas Petricek, and Alan Mycroft. 2014. The Semantic Marriage of Monads
and Effects. CoRR abs/1401.5391 (2014).

[109] Dominic A. Orchard, Philip Wadler, and Harley D. Eades. 2020. Unifying Graded and Parameterised
Monads. In Proceedings of the 2020 Workshop on Mathematically Structured Functional Programming
(MSFP 2020) at ETAPS.

[110] Tomas Petricek. 2016. Context-aware programming languages. Ph. D. Dissertation.

[111] Tomas Petricek, Dominic Orchard, and Alan Mycroft. 2013. Coeffects: Unified static analysis of
context-dependence. In Automata, Languages, and Programming: 40th International Colloquium,
ICALP 2013. Springer, 385-397.

[112] T. Petricek, D. Orchard, and A. Mycroft. 2014. Coeffects: A Calculus of Context-Dependent
Computation. In Proceedings of the 19th ACM SIGPLAN International Conference on Functional
Programming (ICFP 2014). ACM, 123-135.

[113] J. D. Pryce. 1984. A New Measure of Relative Error for Vectors. SIAM J. Numer. Anal. 21, 1
(1984), 202-215.

[114] J. D. Pryce. 1985. Multiplicative Error Analysis of Matrix Transformation Algorithms. IMA
J. Numer. Anal. 5, 4 (1985), 437-445.

[115] Tahina Ramananandro, Paul Mountcastle, Benoît Meister, and Richard Lethin. 2016. A unified
Coq framework for verifying C programs with floating-point computations. In Proceedings of the
5th ACM SIGPLAN Conference on Certified Programs and Proofs (CPP 2016). Association for
Computing Machinery, St. Petersburg, FL, USA, 15-26.

[116] Jason Reed and Benjamin C. Pierce. 2010. Distance Makes the Types Grow Stronger: A Calculus
for Differential Privacy. In Proceedings of the 15th ACM SIGPLAN International Conference on
Functional Programming (ICFP 2010). ACM, 157-168.

[117] Mitchell Riley. 2018. Categories of Optics. arXiv:1809.00738 [math.CT]

[118] João Rivera, Franz Franchetti, and Markus Püschel. 2024. Floating-Point TVPI Abstract Domain.
Proc. ACM Program. Lang. 8, PLDI, Article 165 (2024), 25 pages.

[119] Eric Schkufza, Rahul Sharma, and Alex Aiken. 2014. Stochastic optimization of floating-point
programs with tunable precision. In Proceedings of the 35th ACM SIGPLAN Conference on Programming
Language Design and Implementation (PLDI '14). Association for Computing Machinery,
Edinburgh, United Kingdom, 53-64.

[120] Benjamin Sherman, Jesse Michel, and Michael Carbin. 2019. Sound and robust solid modeling via
exact real arithmetic and continuity. Proc. ACM Program. Lang. 3, ICFP, Article 99 (2019), 29 pages.

[121] Alexey Solovyev, Marek S. Baranowski, Ian Briggs, Charles Jacobsen, Zvonimir Rakamaric, and
Ganesh Gopalakrishnan. 2019. Rigorous Estimation of Floating-Point Round-Off Errors with
Symbolic Taylor Expansions. ACM Trans. Program. Lang. Syst. 41, 1 (2019), 2:1-2:39.

[122] Sylvie Boldo, François Clément, Jean-Christophe Filliâtre, Micaela Mayero, Guillaume Melquiond,
and Pierre Weis. 2014. Trusting computations: A mechanized proof from partial differential equations
to actual program. Comput. Math. Appl. 68, 3 (2014), 325-352.

[123] Jean-Pierre Talpin. 1993. Theoretical and Practical Aspects of Type and Effect Inference. Ph. D.
Dissertation. Ecole des Mines de Paris and University Paris VI.

[124] Jean-Pierre Talpin and Pascal Jouvelot. 1992. Polymorphic Type, Region, and Effect Inference.
Journal of Functional Programming 2, 3 (July 1992), 245-271.

[125] Jean-Pierre Talpin and Pascal Jouvelot. 1994. The Type and Effect Discipline. Information and
Computation 111, 2 (1994), 245-296.

[126] R. Tate. 2013. The Sequential Semantics of Producer Effect Systems. In Proceedings of the
Symposium on Principles of Programming Languages (POPL '13). ACM, New York, NY, USA, 15-26.

[127] Mohit Tekriwal. 2023. A Mechanized Error Analysis Framework for End-to-End Verification of
Numerical Programs. Ph. D. Dissertation. University of Michigan.

[128] Mohit Tekriwal, Andrew W. Appel, Ariel E. Kellison, David Bindel, and Jean-Baptiste Jeannin.
2023. Verified Correctness, Accuracy, And Convergence Of A Stationary Iterative Linear Solver:
Jacobi Method. In International Conference on Intelligent Computer Mathematics (CICM). Springer,
206-221.

[129] Laura Titolo, Marco A. Feliú, Mariano M. Moscato, and César A. Muñoz. 2018. An Abstract
Interpretation Framework for the Round-Off Error Analysis of Floating-Point Programs. In International
Conference on Verification, Model Checking, and Abstract Interpretation (VMCAI 2018). Springer,
516-537.

[130] Laura Titolo, Mariano Moscato, Marco A. Feliu, Paolo Masci, and César A. Muñoz. 2024.
Rigorous Floating-Point Round-Off Error Analysis in PRECiSA 4.0. In Formal Methods: 26th International
Symposium (FM 2024). Springer-Verlag, Milan, Italy, 20-38.

[131] Cassia Torczon, Emmanuel Suarez Acevedo, Shubh Agrawal, Joey Velez-Ginorio, and Stéphanie
Weirich. 2024. Effects and Coeffects in Call-by-Push-Value. Proc. ACM Program. Lang. 8, OOPSLA2,
Article 310 (Oct 2024), 27 pages.

[132] Anh-Hoang Truong, Huy-Vu Tran, and Bao-Ngoc Nguyen. 2014. Finding Round-Off Error Using
Symbolic Execution. In Knowledge and Systems Engineering. Springer, 415-428.

[133] Philip Wadler. 1990. Linear Types Can Change the World!

[134] Philip Wadler and Peter Thiemann. 2003. The marriage of effects and monads. ACM Trans.
Comput. Logic 4, 1 (Jan 2003), 1-32.

[135] Chenkai Weng, Kang Yang, Xiang Xie, Jonathan Katz, and Xiao Wang. 2021. Mystique: Efficient
Conversions for Zero-Knowledge Proofs with Applications to Machine Learning. In 30th USENIX
Security Symposium (USENIX Security 21). USENIX Association, 501-518.

[136] James Wood and Robert Atkey. 2022. A Framework for Substructural Type Systems. In Programming
Languages and Systems: 31st European Symposium on Programming (ESOP 2022). Springer-Verlag,
Berlin, Heidelberg, 376-402.

[137] June Wunder, Arthur Azevedo de Amorim, Patrick Baillot, and Marco Gaboardi. 2023. Bunched
Fuzz: Sensitivity for Vector Metrics. In Proceedings of the 32nd European Symposium on Programming
(ESOP 2023). Springer, 451-478.

[138] Lei Yu. 2013. A Formal Model of IEEE Floating Point Arithmetic. Archive of Formal Proofs.

[139] A. Ziv. 1982. Relative Distance–An Error Measure in Round-Off Error Analysis. Math. Comp. 39
(1982), 563-569.

───────────────────────────────────────────────────────────────────────────────
                                              // appendix // a1 // numfuzz
───────────────────────────────────────────────────────────────────────────────

## Appendix A.1: Termination (Strong Normalization)

This appendix gives the proof of Theorem 2, which verifies that NumFuzz is strongly normalizing
using a logical relations argument.

### Lemma 19

Let `Γ ⊢ e : M_u τ` be a well-typed term, and let `v₁, v₂` be well-typed substitutions of closed
values such that `v₁, v₂ ⊨ Γ`. If `e[v₁/dom(Γ)] ∈ VR^m_{M_u τ}` for some `m ∈ N` and
`e[v₂/dom(Γ)] ∈ RM_u τ`, then `e[v₂/dom(Γ)] ∈ VR^m_{M_u τ}`.

### Theorem 2 (Strong Normalization)

If `∅ ⊢ e : τ` then there exists `v ∈ CV(τ)` such that `e ↦* v`.

**Proof.** We first prove the following stronger statement. Let `Γ, x₁:s₁ σ₁, ..., xₙ:sₙ σₙ` be a typing
environment and let `w̄` denote the values `w₁, ..., wₙ`. If `Γ ⊢ e : τ` and `wᵢ ∈ R_Γ(xᵢ)` for every
`xᵢ ∈ dom(Γ), then `e[w̄/dom(Γ)] ∈ R_τ`. The proof follows by induction on the derivation `Γ ⊢ e : τ`.

We consider the monadic cases, as the non-monadic cases are standard. The base cases (Const),
(Ret), and (Rnd) follow by definition, and (MSub) follows by Lemma 5. The case for (MLet)
requires some detail.

The rule is:
```
(MLet)
    Γ ⊢ v : M_r σ      Θ, x :_s σ ⊢ f : M_q τ
    ─────────────────────────────────────────────
    s · Γ + Θ ⊢ letM x = v in f : M_{s·r+q} τ
```

We proceed by cases on `v`. The key subcases are:
- `v ≡ rnd k` with `k ∈ R`
- `v ≡ ret v'` with `v' ∈ VR_σ`
- `v ≡ letM y = rnd k in g`

Each subcase proceeds by applying the induction hypothesis and Lemmas 3, 4, and 19 to show
that the reducibility predicate is preserved. The critical observation is that the monadic
bind operation composes error bounds according to the grade arithmetic: `s·r + q`.

### Lemma 20

If `∅ ⊢ e : τ` then `e ∈ R_τ`.

### Lemma 21

If `e ∈ R_τ` then there exists a `v ∈ CV(τ)` such that `e ↦* v`.

The proof of termination (Theorem 2) then follows from Lemma 21 and Lemma 20.

───────────────────────────────────────────────────────────────────────────────
                                              // appendix // a2 // numfuzz
───────────────────────────────────────────────────────────────────────────────

## Appendix A.2: The Neighborhood Monad

This appendix provides the details verifying that the neighborhood monad forms an R-strong
graded monad on Met.

### Lemma 6

Let `q, r ∈ R`. For any metric space `A`, the maps `(q ≤ r)_A`, `η_A`, and `μ_{q,r,A}` are nonexpansive
maps and natural in `A`.

**Proof.** Non-expansiveness and naturality for the subeffecting maps `(q ≤ r)_A : T_q A → T_r A`
and the unit maps `η_A : A → T_0 A` are straightforward. We describe the checks for the
multiplication map `μ_{q,r,A}`.

First, we check that the multiplication map has the claimed domain and codomain:
```
d_A(x, x') ≤ q   (by definition of T_q)
d_A(x', y') ≤ r  (by definition of T_r)
────────────────
d_A(x, y') ≤ r + q   (triangle inequality)
```

Second, we check non-expansiveness:
```
d_{T^{r+q}_A}(μ((x, y), (x', y')), μ((w, z), (w', z')))
= d_{T^{r+q}_A}((x, y'), (w, z'))    (def. μ)
= d_A(x, w)                           (def. d_{T^{r+q}_A})
= d_{T^r_A}((x, y), (w, z))           (def. d_{T^r_A})
= d_{T^q(T^r_A)}(((x, y), (x', y')), ((w, z), (w', z')))  (def. d_{T^q(T^r_A)})
```

### Lemma 8 (R-Strong Graded Monad)

The neighborhood monad together with the tensorial strength maps `str_{A,B} : A ⊗ T_r B → T_r(A ⊗ B)`
defined as:
```
str_r,A,B(a, (b, b')) = ((a, b), (a, b'))
```
forms an R-strong graded monad on Met.

───────────────────────────────────────────────────────────────────────────────
                                              // appendix // a3 // numfuzz
───────────────────────────────────────────────────────────────────────────────

## Appendix A.3: Interpreting NumFuzz Terms

This appendix provides the constructions of the interpretation of NumFuzz terms.

### Term Interpretations

**(Unit).** `[[()]] : unit` sends all points in `[[Γ]]` to `★ ∈ [[unit]]`.

**(Var).** `[[x]] : τ` maps `[[Γ]]` to the x-th component of `[[τ]]`.

**(Abs).** Let `f = [[Γ, x:_1 σ ⊢ e : τ]] : [[Γ]] ⊗ D_1[[σ]] → [[τ]]`. Define:
```
[[Γ ⊢ λx. e : σ ⊸ τ]] = λ(f)
```

**(App).** Let `f = [[Γ ⊢ v : σ ⊸ τ]]` and `g = [[Θ ⊢ w : σ]]`. Define:
```
[[Γ + Θ ⊢ v w : τ]] = c_{[[Γ]],[[Θ]]}; (f ⊗ g); ev
```

**(& I).** `[[Γ ⊢ ⟨v, w⟩ : σ & τ]] = ⟨[[v]], [[w]]⟩`

**(& E).** `[[Γ ⊢ π_i v : τ_i]] = [[v]]; π_i`

**(⊗ I).** `[[Γ + Θ ⊢ (v, w) : σ ⊗ τ]] = c_{[[Γ]],[[Θ]]}; (f ⊗ g)`

**(⊗ E).** For elimination, construct the appropriate dependent map using the comonad `D_s`.

**(! I).** `[[s·Γ ⊢ [v] : !s σ]] = m; D_s([[v]])`

**(! E).** `[[t·Γ + Θ ⊢ let [x] = v in e : τ]] = m; D_m f; δ^{-1}_{m,n,[[σ]]}`

───────────────────────────────────────────────────────────────────────────────
                                              // appendix // a4 // numfuzz
───────────────────────────────────────────────────────────────────────────────

## Appendix A.4: Denotational Semantics

This appendix provides basic lemmas about the denotational semantics.

### Lemma 22 (Weakening)

Let `Γ, Γ' ⊢ e : τ` be a well-typed term. Then for any context, there is a derivation of
`Γ, Δ, Γ' ⊢ e : τ` with semantics `[[Γ, Γ']] ⊢ e : τ ∘ π`, where `π : [[Γ, Δ, Γ']] → [[Γ, Γ']]`
projects the components in `Γ` and `Γ'`.

**Proof.** By induction on the typing derivation.

### Lemma 23 (Subsumption)

Let `Γ ⊢ e : M_r τ` be a well-typed program of monadic type, where the typing derivation concludes
with the subsumption rule. Then either `e` is of the form `ret v` or `rnd k`, or there is a derivation
of `Γ ⊢ e : M_r τ` with the same semantics that does not conclude with the subsumption rule.

**Proof.** By straightforward induction using the fact that subsumption is transitive and the
subsumption map `(r ≤ s)_A` is the identity function.

### Lemma 24 (Substitution)

Let `Γ, Δ, Γ' ⊢ e : τ` be a well-typed term, and let `v̄ : Δ` be a well-typed substitution of closed
values. Then there is a derivation of `Γ, Γ' ⊢ e[v̄/dom(Δ)] : τ` with semantics:
```
[[Γ, Γ']] ⊢ e[v̄/dom(Δ)] : τ = (id ⊗ [[∅ ⊢ v̄ : Δ]] ⊗ id); [[Γ, Δ, Γ']] ⊢ e : τ
```

**Proof.** By induction on the typing derivation. The cases for Rnd, Ret, and MLet differ from Fuzz
and require careful handling of the monadic semantics.

### Lemma 25 (Computational Soundness)

Let `∅ ⊢ e : τ` be a well-typed closed term, and suppose `e ↦ e'`. Then there is a derivation of
`∅ ⊢ e' : τ`, and the semantics of both derivations are equal:
```
[[⊢ e : τ]] = [[⊢ e' : τ]]
```

**Proof.** By case analysis on the step rule. For the beta-reduction steps for programs of non-monadic
type, preservation follows by the soundness theorem. The two step rules for programs of monadic
type (MLet_q and MLet_Assoc) are shown by appealing to properties of the graded monad `T_r`.

───────────────────────────────────────────────────────────────────────────────

                                                        — Synthesized 2026-02-26
                                                        — Source: Kellison (2024)
                                                        — Full paper complete

───────────────────────────────────────────────────────────────────────────────
                                              // appendix // b1 // bean
───────────────────────────────────────────────────────────────────────────────

## Appendix B.1: The Category of Backward Error Lenses

This appendix verifies that the composition in the category Bel of backward error lenses is well-defined.

### Composition of Error Lenses

Let `L1 = (f₁, f̃₁, b₁) : X → Y` and `L2 = (f₂, f̃₂, b₂) : Y → Z`. The composition `L2 ◦ L1` is defined as:

**Forward map:**
```
f : x ↦→ (f₁ ; f₂)(x)
```

**Approximation map:**
```
f̃ : x ↦→ (f̃₁ ; f̃₂)(x)
```

**Backward map:**
```
b : (x, z) ↦→ b₁(x, b₂(f̃₁(x), z))
```

### Well-Definedness Proof

We must show the domain is well-defined: for all `x ∈ X` and `z ∈ Z`, assuming `d_Z(f̃(x), z) ≠ ∞`, we must show `d_Y(f̃₁(x), b₂(f̃₁(x), z)) ≠ ∞`.

This follows from Property 1 for `L2`:
```
d_Y(f̃₁(x), b₂(f̃₁(x), z)) ≤ d_Z(f̃₂(f̃₁(x)), z) = d_Z(f̃(x), z) ≠ ∞
```

### Lens Properties for Composition

**Property 1 (Bounded backward error):**
```
d_X(x, b(x, z)) = d_X(x, b₁(x, b₂(f̃₁(x), z)))
                ≤ d_Y(f̃₁(x), b₂(f̃₁(x), z))     (Property 1 for L1)
                ≤ d_Z(f̃₂(f̃₁(x)), z)            (Property 1 for L2)
                = d_Z(f̃(x), z)
```

**Property 2 (Exact witness):**
```
f(b(x, z)) = f₂(f₁(b₁(x, b₂(f̃₁(x), z)))))
            = f₂(b₂(f̃₁(x), z))                  (Property 2 for L1)
            = z                                   (Property 2 for L2)
```

───────────────────────────────────────────────────────────────────────────────
                                              // appendix // b2 // bean
───────────────────────────────────────────────────────────────────────────────

## Appendix B.2: Basic Constructions in Bel

### B.2.1 Tensor Product

Given morphisms `(f, f̃, b) : A → X` and `(g, g̃, b') : B → Y`, the tensor product lens `(f, f̃, b) ⊗ (g, g̃, b') : A ⊗ B → X ⊗ Y` is defined by:

**Forward map:**
```
(f ⊗ g)(a₁, a₂) = (f(a₁), g(a₂))
```

**Approximation map:**
```
(f̃ ⊗ g̃)(a₁, a₂) = (f̃(a₁), g̃(a₂))
```

**Backward map:**
```
(b ⊗ b')((a₁, a₂), (x₁, x₂)) = (b(a₁, x₁), b'(a₂, x₂))
```

**Lens Properties:**

Property 1:
```
d_{A⊗B}((a₁, a₂), b⊗((a₁, a₂), (x₁, x₂)))
= max(d_A(a₁, b(a₁, x₁)), d_B(a₂, b'(a₂, x₂)))
≤ max(d_X(f̃(a₁), x₁), d_Y(g̃(a₂), x₂))
= d_{X⊗Y}((f̃ ⊗ g̃)(a₁, a₂), (x₁, x₂))
```

### Lemma 14: Tensor Product as Bifunctor

The tensor product operation on lenses induces a bifunctor on Bel. Functoriality follows by checking preservation of composition and identities.

### Associator

```
α_X,Y,Z : X ⊗ (Y ⊗ Z) → (X ⊗ Y) ⊗ Z
f_α(x, (y, z)) = ((x, y), z)
f̃_α(x, (y, z)) = ((x, y), z)
b_α(((x, (y, z)), ((a, b), c))) = (a, (b, c))
```

### Unitors

```
λ_X : I ⊗ X → X
f_λ(★, x) = x
f̃_λ(★, x) = x
b_λ((★, x), x') = (★, x')
```

The fact that `d_I(★, ★) = -∞` is essential for Property 1:
```
d_{I⊗X}(x, b_λ((★, x), x')) ≤ d_X(f̃_λ(★, x), x')
max(-∞, d_X(x, x')) ≤ d_X(x, x')
```

### Symmetry

```
γ_X,Y : X ⊗ Y → Y ⊗ X
f_γ(x, y) = (y, x)
f̃_γ(x, y) = (y, x)
b_γ((x, y), (y', x')) = (x', y')
```

### B.2.2 Coproducts

**Injection 1:**
```
inl : X → X + Y
f_inl(x) = inl x
f̃_inl(x) = inl x
b_inl((x, z)) = inl x₀  where z = inl x₀
```

**Copairing:**
```
[g, h] : X + Y → C
f_g,h(z) = f_g(x)  if z = inl x
           f_h(y)  if z = inr y
```

───────────────────────────────────────────────────────────────────────────────
                                              // appendix // b3 // bean
───────────────────────────────────────────────────────────────────────────────

## Appendix B.3: Interpreting Bean Terms

This section details the constructions for interpreting Bean terms.

### Case (Var)

For `Γ = x₀:q₀ σ₀, ..., x_{i-1}:q_{i-1} σ_{i-1}`, define:
```
[[Φ | Γ, x:r σ ⊢ x : σ]] = π_i ∘ (ε_{σ₀} ⊗ ... ⊗ ε_{σ} ∘ (m_{0≤r,σ₀} ⊗ ... ⊗ m_{0≤r,σ})
```

### Case (DVar)

Define as projection `π_i` for discrete variables.

### Case (Unit)

```
[[Φ | Γ ⊢ () : unit]] = L_unit : tuple → singleton in I = ({★}, 0)
f_unit(x̄) = ★
f̃_unit(x̄) = ★
b_unit(x, ★) = x
```

### Case (⊗ I)

Given `h₁ = [[Φ | Γ ⊢ e : σ]]` and `h₂ = [[Φ | Δ ⊢ f : τ]]`:
```
[[Φ | Γ, Δ ⊢ (e, f) : σ ⊗ τ]] = (h₁ ⊗ h₂) ∘ (t_{[[Φ]]} ⊗ id)
```

### Case (⊗ E_σ)

Given the maps for the premises, construct using the comonad `D_r` and diagonal.

### Case (+ E)

Given maps for the case analysis, construct using the distribution map:
```
Θ_{X,Y,Z} : X ⊗ (Y + Z) → (X ⊗ Y) + (X ⊗ Z)
f_Θ(x, w) = inl(x, y)   if w = inl y
           = inr(x, z)   if w = inr z
b_Θ((x, w), u) = ... (defined by cases)
```

### Case (Add)

See Section 4.3 for the full definition of the addition lens.

### Case (Sub)

Similar to Add:
```
L_sub : D_ε(R) ⊗ D_ε(R) → R
f_sub(x₁, x₂) = x₁ - x₂
f̃_sub(x₁, x₂) = (x₁ - x₂)·e^δ, |δ| ≤ ε
b_sub((x₁, x₂), x₃) = (x₃·x₁/(x₁-x₂), x₃·x₂/(x₁-x₂))
```

### Case (Mul)

See Section 4.3.

### Case (Div)

```
L_div : D_{ε/2}(R) ⊗ D_{ε/2}(R) → (R + ⋄)
f_div(x₁, x₂) = x₁/x₂   if x₂ ≠ 0
              = ⋄       otherwise
f̃_div(x₁, x₂) = x₁·e^δ/x₂  if x₂ ≠ 0; |δ| ≤ ε
                = ⋄          otherwise
b_div((x₁, x₂), x) = ... (defined by cases)
```

### Case (DMul)

```
L_dmul : R_α ⊗ D_ε R → R
f_dmul(x₁, x₂) = x₁·x₂
f̃_dmul(x₁, x₂) = x₁·x₂·e^δ, |δ| ≤ ε
b_dmul((x₁, x₂), x₃) = (x₁, x₃/x₁)
```

───────────────────────────────────────────────────────────────────────────────
                                              // appendix // b4 // bean
───────────────────────────────────────────────────────────────────────────────

## Appendix B.4: Interpreting ΛS Terms

This appendix provides constructions for the interpretation of ΛS terms.

### Case (Var), (Unit), (Const)

Define as projections and constant functions.

### Case (⊗ I)

Given `h₁ : L_Φ × L_Γ → L_σ` and `h₂ : L_Φ × L_Δ → L_τ`:
```
[[Φ, Γ, Δ ⊢ (e, f) : σ ⊗ τ]] = (d_{L_Φ}, id_{L_Γ}, id_{L_Δ}); (h₁, h₂)
```

### Case (⊗ E)

Construct using projections and composition.

### Case (+ E)

Use the distribution map in Set:
```
Θ^S_{X,Y,Z} : X × (Y + Z) → (X × Y) + (X × Z)
```

### Case (Let)

```
[[Φ, Γ, Δ ⊢ let x = e in f : τ]] = (t_{L_Φ}, id_{L_Γ×L_Δ}); (h₁, id_{L_Φ×L_Δ}); h₂
```

### Case (Op)

For `op ∈ {add, sub, mul, dmul}`:
```
[[Φ, Γ, Δ ⊢ op e f : num]] = d_{L_Φ}; (h₁, h₂); op
```

───────────────────────────────────────────────────────────────────────────────
                                              // appendix // b5 // bean
───────────────────────────────────────────────────────────────────────────────

## Appendix B.5: Details for Soundness

### Lemma 16: Embedding Bean into ΛS

Let `Φ | Γ ⊢ e : τ` be a well-typed Bean term. Then there is a derivation `Φ, Γ° ⊢ e : τ` in ΛS.

**Proof.** By induction on the Bean derivation. Most cases are immediate. The Add case:
```
(Var)  Φ, Γ, x : num ⊢ x : num
(Var)  Φ, Γ, y : num ⊢ y : num
(Add)  Φ, Γ, x : num, y : num ⊢ add x y : num
```

### Lemma 18: Semantic Embedding

```
U_id[[Φ | Γ ⊢ e : σ]] = L_{Φ, Γ°} ⊢ e : σ_id
U_ap[[Φ | Γ ⊢ e : σ]] = L_{Φ, Γ°} ⊢ e : σ_ap
```

### Theorem 6: Substitution

Let `Γ ⊢ e : τ` be a well-typed ΛS term. Then for any well-typed substitution `γ̄` of closed values, there is a derivation `∅ ⊢ e[γ̄/dom(Γ)] : τ`.

### Theorem 8: Soundness of Ideal Semantics

Let `Γ ⊢ e : τ` be a well-typed ΛS term. Then for any well-typed substitution `γ̄ ⊨ Γ`, if `e[γ̄] ⇓_id v`, then `L_Γ ⊢ e : τ M_id(γ̄) = L_v M_id`.

### Theorem 9: Adequacy

If `L_Γ ⊢ e : τ M_id(γ̄) = L_v M_id`, then `e[γ̄] ⇓_id v`.

───────────────────────────────────────────────────────────────────────────────
                                              // appendix // b6 // bean
───────────────────────────────────────────────────────────────────────────────

## Appendix B.6: Proof of Backward Error Soundness

### Theorem 10: Main Backward Error Soundness

Let `Φ | x₁:r₁ σ₁, ..., xₙ:rₙ σₙ = Γ ⊢ e : σ` be well-typed. Then for any substitutions `p̄ ⊨ Φ` and `k̄ ⊨ Γ°`, if `e[p̄/dom(Φ)][k̄/dom(Γ)] ⇓_ap v`, then there exists `l̄ ⊨ Γ°` such that:

1. `e[p̄/dom(Φ)][l̄/dom(Γ)] ⇓_id v`
2. `d_{σᵢ}(kᵢ, lᵢ) ≤ rᵢ` for each `kᵢ ∈ k̄` and `lᵢ ∈ l̄`

**Proof.** From the lens semantics, we have the triple `(f, f̃, b)`. Using the backward map, define `(s̄, l̄) = b((p̄, k̄), v)`.

From Property 2 of lenses:
```
f L(s̄, l̄)_id = f(b((p̄, k̄), v))_id = v
```

We show the backward error result:
```
L_{Φ, Γ} ⊢ e : σ M_ap(p̄, k̄)_ap = U_ap[[e]](p̄, k̄)
                                   = f̃(p̄, k̄)
                                   = v
                                   = f(l̄)_id
```

From Property 1:
```
d_{Φ⊗Γ}((p̄, k̄), b((p̄, k̄), v)) ≤ d_σ(f̃(p̄, k̄), v)
```

Assuming `d_σ(v, v) ≠ ∞` (satisfied by standard metrics), we have:
```
max(d_Φ(p̄, s̄), d_Γ(k̄, l̄)) ≤ d_σ(v, v)
```

For discrete variables, `d_Φ(p̄, s̄) = 0`, so `p̄ = s̄`. For linear variables:
```
d_{σᵢ}(kᵢ, lᵢ) - rᵢ ≤ 0
```

Thus `d_{σᵢ}(kᵢ, lᵢ) ≤ rᵢ`.

───────────────────────────────────────────────────────────────────────────────
                                              // appendix // b7 // bean
───────────────────────────────────────────────────────────────────────────────

## Appendix B.7: Type Checking Algorithm

This appendix (authored by Laura Zielinski) presents the type-checking algorithm for Bean.

### Algorithm Overview

The algorithm is written `Φ | Γ• ; e ⇒ Γ; σ` where:
- `Γ•` is a linear context skeleton
- `e` is a Bean program
- `Γ` is the minimal linear context required to type `e`
- `σ` is the type of `e`

### Key Rules

```
(Var)     Φ | Γ•, x : σ ; x ⇒ {x : 0 σ}; σ

(⊗ I)     Φ | Γ• ; e ⇒ Γ₁; σ    Φ | Γ• ; f ⇒ Γ₂; τ
          ─────────────────────────────────────────
          dom Γ₁ ∩ dom Γ₂ = ∅
          Φ | Γ• ; (e, f) ⇒ Γ₁, Γ₂; σ ⊗ τ

(⊗ E_σ)   Φ | Γ• ; e ⇒ Γ₁; τ₁ ⊗ τ₂
           Φ | Γ•, x : τ₁, y : τ₂ ; f ⇒ Γ₂; σ
           ─────────────────────────────────────────
           dom Γ₁ ∩ dom Γ₂ = ∅
           Φ | Γ• ; let (x, y) = e in f ⇒ (r + Γ₁), Γ₂ \ {x, y}; σ

(Add)     Φ | Γ•, x : num, y : num ; add x y ⇒ {x : ε num, y : ε num}; num

(Mul)     Φ | Γ•, x : num, y : num ; mul x y ⇒ {x : ε/2 num, y : ε/2 num}; num

(DMul)    Φ, z : dnum | Γ•, x : num ; dmul z x ⇒ {x : ε num}; num
```

### Lemma 26: Type System Weakening

If `Φ | Γ ⊢ e : σ` and `Γ ⊑ Δ`, then `Φ | Δ ⊢ e : σ`.

### Lemma 27: Algorithm Weakening

If `Φ | Γ• ; e ⇒ Γ; σ` and `Γ• ⊑ Δ•`, then `Φ | Δ• ; e ⇒ Γ; σ`.

### Theorem 11: Algorithm Soundness

If `Φ | Γ• ; e ⇒ Γ; σ`, then `Γ ⊑ Γ•` and the derivation `Φ | Γ ⊢ e : σ` exists.

### Theorem 12: Algorithm Completeness

If `Φ | Γ ⊢ e : σ` is a valid derivation, then there exists `Δ ⊑ Γ` such that `Φ | Γ ; e ⇒ Δ ; σ`.

───────────────────────────────────────────────────────────────────────────────

                                                        — Synthesized 2026-02-26
                                                        — Source: Kellison (2024)
                                                        — Complete dissertation with all appendices
