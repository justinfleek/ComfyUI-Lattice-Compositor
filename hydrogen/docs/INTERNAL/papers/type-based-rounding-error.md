# Type-Based Approaches to Rounding Error Analysis

**Author:** Ariel Eileen Kellison (Cornell University, Dissertation)

**arXiv:** 2501.14598v2 [cs.PL] 27 Jan 2025

---

## Abstract

This dissertation presents **two type systems for rounding error analysis**:

1. **NumFuzz**: Forward error analysis via graded monadic types
2. **Bean**: Backward error analysis via graded comonadic types + strict linearity

**Core Insight**: Rounding error can be viewed through the lens of effects and coeffects:
- **Effects** (what programs produce): graded monads track accumulated rounding error
- **Coeffects** (how programs use inputs): graded comonads track sensitivity/perturbation

**Why This Matters for Hydrogen**: These type systems provide the formal foundation for bounded arithmetic in PureScript. When Element types use bounded numeric atoms, the type system can guarantee error bounds at compile time

## 1. Introduction

### 1.1 Forward vs Backward Error

**Forward Error**: Distance between computed output ỹ and ideal result y = f(x)
```
forward_error = d(ỹ, y)
```

**Backward Error**: Smallest perturbation δx such that f(x + δx) = ỹ
```
backward_error = min{d(x, x̃) : f(x̃) = ỹ}
```

**Relationship**:
```
forward_error ≤ condition_number × backward_error
```

**Why both matter**:
- Large forward error can come from ill-conditioned problem OR unstable algorithm
- Backward error isolates algorithm quality from problem conditioning
- A backward stable algorithm: ∀x. ∃x̃. f(x̃) = f̃(x) ∧ d(x, x̃) ≤ αu

### 1.2 Type-Based Approach

**Key Idea**: Encode error analysis in the type system itself

- Types carry numeric grades representing error bounds
- Typing rules provide compositional error propagation
- Well-typed programs are formally proven to satisfy error bounds

**Two Mechanisms**:
1. **Graded Monads** (M_q τ): Track accumulated forward error q
2. **Graded Comonads** (!_s σ): Track sensitivity amplification factor s

**Compositionality**: Error bounds for complex programs derived from primitives

## 2. Background

### 2.1 Floating-Point Arithmetic

**Standard Model** (IEEE 754): For operation ◦ ∈ {+, -, ×, /}:
```
fl(x ◦ y) = (x ◦ y)(1 + δ)  where |δ| ≤ u
```
where u = unit roundoff (e.g., u ≈ 1.1×10⁻¹⁶ for binary64)

**Alternative Model** (Olver 1978): Using relative precision:
```
fl(x ◦ y) = (x ◦ y)·e^δ  where |δ| ≤ ε = u/(1-u)
```

**Relative Precision Metric**:
```
RP(x̃, x) = |ln(x̃/x)|
```

This metric is used throughout NumFuzz and Bean because:
- Multiplicative: RP(xy, x̃ỹ) ≤ RP(x, x̃) + RP(y, ỹ)
- Composable: error bounds combine via addition

### 2.2 Graded Types

**Graded Monads** (for effects):
```
M_q τ  -- computation producing τ with at most q accumulated error
```

**Graded Comonads** (for coeffects):
```
!_s σ  -- data of type σ scaled by sensitivity factor s
```

**Key Typing Rules**:

```
-- Monadic sequencing (composes forward error)
Γ ⊢ v : M_r σ    Θ, x:_s σ ⊢ f : M_q τ
──────────────────────────────────────────
Γ + Θ ⊢ letM x = v in f : M_{s·r + q} τ

-- Comonadic elimination (scales sensitivity)
Γ ⊢ v : !_s σ    Θ, x:_{t·s} σ ⊢ e : τ
──────────────────────────────────────────
t·Γ + Θ ⊢ let [x] = v in e : τ
```

**Error Composition Formula**: `s·r + q`
- r = input error
- s = sensitivity (amplification factor)
- q = local error from operation

## 3. NumFuzz: Forward Error Analysis

### 3.1 Sensitivity Type Systems

**C-Sensitivity**: Function f: X → Y is c-sensitive if:
```
d_Y(f(x), f(y)) ≤ c · d_X(x, y)  for all x, y ∈ X
```

**In Type Systems**:
- `σ ⊸ τ` = 1-sensitive (non-expansive) function
- `!_r σ ⊸ τ` = r-sensitive function

**Example**: f(x) = x² is 2-sensitive under relative precision:
```
RP(x², y²) = |ln(x²/y²)| = 2|ln(x/y)| = 2·RP(x, y)
```

Therefore typed as: `f : !_2 num ⊸ num`

### 3.2 Type System

**NumFuzz Types**:
```
σ, τ ::= unit           -- unit type
       | num            -- numeric (reals with RP metric)
       | σ & τ          -- additive product (shared context)
       | σ ⊗ τ          -- multiplicative product (split context)
       | σ + τ          -- sum type
       | σ ⊸ τ          -- linear function (1-sensitive)
       | !_s σ          -- scaled type (s-sensitive)
       | M_q τ          -- monadic type (q error bound)
```

**Typing Environments**:
```
Γ ::= ∅ | Γ, x:_r σ    -- r = sensitivity of x
```

**Environment Operations**:
- Sum: `(Γ + Θ)(x) = Γ(x) + Θ(x)` (sensitivities add)
- Scale: `(r·Γ)(x) = r · Γ(x)`

### 3.3 Typing Rules

---

#### Algorithm 1: NumFuzz Core Rules

```
-- Constants (any sensitivity context)
(Const) Γ ⊢ k : num   where k ∈ R

-- Variable (requires sensitivity ≥ 1)
(Var) Γ, x:_s σ, Δ ⊢ x : σ   where s ≥ 1

-- Linear function intro/elim
(⊸I)  Γ, x:_1 σ ⊢ e : τ
      ────────────────────
      Γ ⊢ λx.e : σ ⊸ τ

(⊸E)  Γ ⊢ v : σ ⊸ τ    Θ ⊢ w : σ
      ─────────────────────────────
      Γ + Θ ⊢ v w : τ

-- Scaling intro/elim
(!I)  Γ ⊢ v : σ
      ─────────────
      s·Γ ⊢ [v] : !_s σ

(!E)  Γ ⊢ v : !_s σ    Θ, x:_{t·s} σ ⊢ e : τ
      ─────────────────────────────────────────
      t·Γ + Θ ⊢ let [x] = v in e : τ
```

---

#### Algorithm 2: NumFuzz Monadic Rules (Rounding Error)

```
-- Return (lifts value with zero error)
(Ret)  Γ ⊢ v : τ
       ─────────────────
       Γ ⊢ ret v : M_0 τ

-- Rounding (introduces ε error)
(Rnd)  Γ ⊢ v : num
       ─────────────────────
       Γ ⊢ rnd v : M_ε num

-- Subsumption (error bounds can be loosened)
(MSub) Γ ⊢ e : M_q τ    r ≥ q
       ────────────────────────
       Γ ⊢ e : M_r τ

-- Monadic let (THE KEY RULE - composes error)
(MLet) Γ ⊢ v : M_r σ    Θ, x:_s σ ⊢ f : M_q τ
       ────────────────────────────────────────────
       s·Γ + Θ ⊢ letM x = v in f : M_{s·r + q} τ
```

**The MLet Rule Explained**:
- `v` has error `r`
- `f` has sensitivity `s` to `x` and local error `q`
- Composed: input error `r` amplified by `s`, plus local error `q`
- Result: `s·r + q`

### 3.4 Soundness

**Main Theorem**: If `Γ ⊢ e : M_q num` then the distance between ideal and floating-point evaluation is at most `q`.

**Proof Strategy**:
1. **Denotational Semantics**: Interpret `M_q τ` as pairs `(v_ideal, v_fp)` with `d(v_ideal, v_fp) ≤ q`
2. **Operational Semantics**: Two evaluation relations `↦_id` (ideal) and `↦_fp` (floating-point)
3. **Soundness Theorem**: Connects denotational pairs to operational evaluations

**Example: pow4**
```
pow4 : num ⊸ M_{3ε} num
pow4 ≜ λx. letM y = pow2 x in pow2 y

-- Error composition:
-- First pow2: ε error
-- Second pow2: 2-sensitive, so 2ε from propagation, plus ε local
-- Total: 2ε + ε = 3ε
```

## 4. Bean: Backward Error Analysis

### 4.1 Backward Stability

**Definition**: Implementation f̃ is backward stable if:
```
∀x ∈ F^n. ∃x̃ ∈ R^n. f(x̃) = f̃(x) ∧ d(x, x̃) ≤ αu
```

**Backward Error for Primitives** (Olver model):
```
-- Addition: perturbs both inputs
a ⊕_F b = a·e^δ + b·e^δ = ã + b̃   where |δ| ≤ ε

-- Multiplication: perturbs both inputs (half each)
a ⊙_F b = a·e^{δ/2} · b·e^{δ/2} = ã · b̃   where |δ| ≤ ε

-- Multiplication (alternative): perturbs one input
a ⊙_F b = a · b·e^δ = a · b̃   where |δ| ≤ ε
```

**Why Backward Error Needs Linearity**:
- Variables cannot be freely duplicated
- Different uses may require incompatible perturbations
- Strict linearity ensures compositional backward error bounds

### 4.2 Type System

**Bean Types**:
```
α ::= dnum | α ⊗ α              -- discrete types (no backward error)
σ ::= unit | α | num | σ ⊗ σ | σ + σ   -- linear types (can have backward error)
```

**Dual Context Judgment**:
```
Φ | Γ ⊢ e : τ

where:
  Φ = discrete context (variables with NO backward error)
  Γ = linear context (variables with bounded backward error)
```

**Linear Context**: `Γ ::= ∅ | Γ, x:_r σ`
- Grade `r` = backward error bound for variable `x`
- Variables CANNOT be duplicated (strict linearity)

---

#### Algorithm 3: Bean Primitive Rules

```
-- Addition (ε backward error to each input)
(Add) Φ | Γ, x:_{ε+r₁} num, y:_{ε+r₂} num ⊢ add x y : num

-- Subtraction (same as addition)
(Sub) Φ | Γ, x:_{ε+r₁} num, y:_{ε+r₂} num ⊢ sub x y : num

-- Multiplication (ε/2 backward error to each input)
(Mul) Φ | Γ, x:_{ε/2+r₁} num, y:_{ε/2+r₂} num ⊢ mul x y : num

-- Discrete multiplication (all error to linear input)
(DMul) Φ, z: dnum | Γ, x:_{ε+r} num ⊢ dmul z x : num

-- Division (may fail)
(Div) Φ | Γ, x:_{ε/2+r₁} num, y:_{ε/2+r₂} num ⊢ div x y : num + err
```

---

#### Algorithm 4: Bean Structural Rules

```
-- Variable (linear)
(Var) Φ | Γ, x:_r σ ⊢ x : σ

-- Variable (discrete - freely duplicable)
(DVar) Φ, z: α | Γ ⊢ z : α

-- Let binding (backward error propagates)
(Let) Φ | Γ ⊢ e : τ    Φ | Δ, x:_r τ ⊢ f : σ
      ─────────────────────────────────────────
      Φ | r + Γ, Δ ⊢ let x = e in f : σ

-- Promotion to discrete (loses ability to assign backward error)
(Disc) Φ | Γ ⊢ e : num
       ─────────────────────
       Φ | Γ ⊢ !e : dnum

-- Discrete let (no backward error contribution)
(DLet) Φ | Γ ⊢ e : α    Φ, z: α | Δ ⊢ f : σ
       ───────────────────────────────────────
       Φ | Γ, Δ ⊢ dlet z = e in f : σ
```

**Key Insight**: The grade addition `r + Γ` in (Let) propagates backward error through composition

### 4.3 The Category Bel (Backward Error Lenses)

**Core Structure**: Bean's denotational semantics uses a category of "backward error lenses"

**Definition**: A backward error lens L : X → Y is a triple (f, f̃, b):
- `f : X → Y` — forward map (ideal computation)
- `f̃ : X → Y` — approximation map (floating-point)
- `b : X × Y → X` — backward map (produces perturbed input)

**Properties**:
```
Property 1: d_X(x, b(x, y)) ≤ d_Y(f̃(x), y)
  -- backward error bounded by output distance

Property 2: f(b(x, y)) = y
  -- backward map is exact witness
```

**Composition of Lenses**:
```
(f₂, f̃₂, b₂) ∘ (f₁, f̃₁, b₁) = (f, f̃, b) where:
  f(x)     = f₂(f₁(x))           -- compose forward maps
  f̃(x)     = f̃₂(f̃₁(x))           -- compose approximations
  b(x, z)  = b₁(x, b₂(f̃₁(x), z)) -- compose backward maps
```

**Why No Cartesian Product**: Cannot define diagonal Δ : A → A × A
- Would need b(a₀, (a₁, a₂)) to reconcile a₁ and a₂
- When a₁ ≠ a₂, impossible to satisfy lens property 2
- This is why Bean requires strict linearity

### 4.4 Soundness

**Main Theorem**: If `Φ | x₁:_{r₁} σ₁, ..., xₙ:_{rₙ} σₙ ⊢ e : τ` then:
- Program `e` has at most `rᵢ` backward error w.r.t. each linear variable `xᵢ`
- Program `e` has zero backward error w.r.t. discrete variables in `Φ`

**Example: Dot Product**
```
DotProd2 x y :=
  let (x0, x1) = x in
  let (y0, y1) = y in
  let v = mul x0 y0 in
  let w = mul x1 y1 in
  add v w

-- Typing:
∅ | x:_{3ε/2} R², y:_{3ε/2} R² ⊢ DotProd2 x y : R

-- Meaning: Backward error ≤ 3ε/2 for each input vector
```

**Error Derivation**:
- `mul x0 y0`: ε/2 to each component
- `mul x1 y1`: ε/2 to each component  
- `add v w`: ε to each sum component
- Total per input: ε/2 + ε = 3ε/2

## 5. Hydrogen Integration Notes

### Relevance to Bounded Types

**Direct Application**: Hydrogen's Schema atoms use bounded numeric types
- Hue: BoundedInt 0 359
- Channel: BoundedInt 0 255
- Pixel: Bounded numeric with explicit min/max

**Type-Level Error Bounds**: Could extend PureScript types with grades:
```purescript
-- Hypothetical graded type
newtype Bounded (min :: Int) (max :: Int) (error :: Nat) a = Bounded a

-- Operations carry error information
add :: Bounded m1 x1 e1 a -> Bounded m2 x2 e2 a 
    -> Bounded (m1+m2) (x1+x2) (e1+e2+epsilon) a
```

### Relevance to Lean4 Proofs

**NumFuzz/Bean patterns map to Lean4**:
```lean
-- Graded monad for forward error
structure ForwardError (ε : ℝ) (α : Type) where
  ideal : α
  approx : α  
  bound : d ideal approx ≤ ε

-- Composition theorem
theorem forward_compose {r q s : ℝ} :
  (v : ForwardError r σ) → 
  (f : σ → ForwardError q τ) →
  (sensitivity : s) →
  ForwardError (s * r + q) τ
```

### Relevance to Graded Monads

**Hydrogen already uses graded types conceptually**:
- Element tracks effects (CanClick, CanAnimate, etc.)
- Element tracks co-effects (NeedsFont, NeedsImage, etc.)

**Extension**: Add error tracking grade:
```purescript
-- Element with error grade
Element :: Effect -> CoEffect -> ErrorBound -> Type -> Type
```

### Key Takeaways for Implementation

1. **Sensitivity is multiplicative**: Error amplifies through composition by sensitivity factor
2. **Error is additive**: Local errors add to propagated errors
3. **Composition formula**: `total_error = sensitivity × input_error + local_error`
4. **Linearity preserves backward stability**: Duplicated variables break backward error guarantees
5. **Discrete/linear split**: Some data can be freely shared (zero backward error), some cannot

## Appendix: Key Algorithms

### Complete NumFuzz Error Composition

```python
def numfuzz_error_composition(program):
    """
    Compute forward error bound for NumFuzz program.
    
    Types track:
    - M_q τ: computation with at most q error
    - !_s σ: data with sensitivity factor s
    """
    match program:
        case Const(k):
            return 0  # Constants have no error
        
        case Ret(v):
            return 0  # Lifting has no error
        
        case Rnd(v):
            return EPSILON  # Single rounding = ε error
        
        case LetM(x, v, f):
            r = error_bound(v)      # Error from v
            s = sensitivity(f, x)   # Sensitivity of f to x
            q = error_bound(f)      # Local error in f
            return s * r + q        # THE KEY FORMULA
        
        case Lambda(x, body):
            # Linear function: 1-sensitive
            return error_bound(body)
        
        case App(f, arg):
            # Application: errors add
            return error_bound(f) + error_bound(arg)

def sensitivity(expr, var):
    """Compute sensitivity of expr with respect to var."""
    match expr:
        case Var(v) if v == var:
            return 1
        case Var(v):
            return 0
        case Mul(a, b) if contains(a, var) and contains(b, var):
            return 2  # x² is 2-sensitive
        case Add(a, b):
            return max(sensitivity(a, var), sensitivity(b, var))
        # ... etc
```

### Complete Bean Backward Error Derivation

```python
def bean_backward_error(typing_judgment):
    """
    Derive per-variable backward error bounds.
    
    Judgment: Φ | Γ ⊢ e : τ
    Where Γ = x₁:_{r₁} σ₁, ..., xₙ:_{rₙ} σₙ
    
    Returns: dict mapping variables to error bounds
    """
    match typing_judgment:
        case Add(x, y):
            # Each input gets ε backward error
            return {x: EPSILON, y: EPSILON}
        
        case Mul(x, y):
            # Each input gets ε/2 backward error
            return {x: EPSILON/2, y: EPSILON/2}
        
        case DMul(z, x):  # z is discrete
            # Discrete variable: 0 error
            # Linear variable: all ε error
            return {x: EPSILON}  # z not in linear context
        
        case Let(x, e, f):
            # Backward error propagates
            e_errors = backward_error(e)
            f_errors = backward_error(f)
            r = f_errors.get(x, 0)  # Error f assigns to x
            
            # Propagate r to all variables in e
            result = {v: r + err for v, err in e_errors.items()}
            result.update({v: err for v, err in f_errors.items() if v != x})
            return result
        
        case DLet(z, e, f):
            # Discrete binding: e's errors don't propagate via z
            e_errors = backward_error(e)
            f_errors = backward_error(f)
            return {**e_errors, **f_errors}

def verify_backward_stability(program, max_error):
    """
    Verify that program is backward stable with bound max_error.
    Returns True if all variable bounds ≤ max_error.
    """
    errors = bean_backward_error(program)
    return all(e <= max_error for e in errors.values())
```

### Backward Error Lens Composition

```python
@dataclass
class BackwardErrorLens:
    """
    Triple (f, f̃, b) representing a backward error lens.
    """
    forward: Callable      # f: X → Y (ideal)
    approx: Callable       # f̃: X → Y (floating-point)
    backward: Callable     # b: X × Y → X (perturbation witness)
    
    def compose(self, other: 'BackwardErrorLens') -> 'BackwardErrorLens':
        """
        Compose two lenses: (self ∘ other)
        
        self: Y → Z
        other: X → Y
        result: X → Z
        """
        def composed_forward(x):
            return self.forward(other.forward(x))
        
        def composed_approx(x):
            return self.approx(other.approx(x))
        
        def composed_backward(x, z):
            # Key: backward maps compose via intermediate value
            y_tilde = other.approx(x)
            y_perturbed = self.backward(y_tilde, z)
            return other.backward(x, y_perturbed)
        
        return BackwardErrorLens(
            composed_forward,
            composed_approx,
            composed_backward
        )
    
    def verify_properties(self, x, y):
        """
        Verify lens properties for given x, y.
        
        Property 1: d(x, b(x,y)) ≤ d(f̃(x), y)
        Property 2: f(b(x,y)) = y
        """
        x_perturbed = self.backward(x, y)
        
        # Property 1: backward error bounded
        assert distance(x, x_perturbed) <= distance(self.approx(x), y)
        
        # Property 2: exact witness
        assert self.forward(x_perturbed) == y
```

---

**Document Status**: COMPLETE
**Synthesis Date**: 2026-02-26
**Synthesized By**: Opus 4.5

