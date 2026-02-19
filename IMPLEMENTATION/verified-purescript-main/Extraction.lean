/-
  Towards Verified Extraction: CIC → F-omega (PureScript)
  
  This sketches the architecture for true proof-carrying code generation.
-/

-- ═══════════════════════════════════════════════════════════════════════════════
-- PURESCRIPT TYPE SYSTEM (F-omega subset)
-- ═══════════════════════════════════════════════════════════════════════════════

inductive Kind : Type where
  | type : Kind                      -- *
  | arr : Kind → Kind → Kind         -- κ₁ → κ₂
  deriving Repr, DecidableEq

inductive Ty : Type where
  | var : String → Ty                        -- a
  | arr : Ty → Ty → Ty                       -- τ → σ
  | app : Ty → Ty → Ty                       -- F a
  | forall_ : String → Kind → Ty → Ty        -- ∀(a :: κ). τ
  | lam : String → Kind → Ty → Ty            -- λ(a :: κ). τ  (type-level)
  deriving Repr, DecidableEq

notation:50 τ " ⟶ " σ => Ty.arr τ σ
notation:40 "∀∀ " a " : " κ " . " τ => Ty.forall_ a κ τ

-- ═══════════════════════════════════════════════════════════════════════════════
-- TYPING CONTEXT
-- ═══════════════════════════════════════════════════════════════════════════════

abbrev TyCtx := List (String × Kind)
abbrev Ctx := List (String × Ty)

def Ctx.lookup (Γ : Ctx) (x : String) : Option Ty :=
  Γ.find? (·.1 == x) |>.map (·.2)

-- ═══════════════════════════════════════════════════════════════════════════════
-- INTRINSICALLY TYPED TERMS
-- ═══════════════════════════════════════════════════════════════════════════════

-- The key insight: terms are indexed by their type!
-- This makes ill-typed terms unrepresentable.

-- Elem lives in Type (not Prop) so we can compute with it
inductive Elem : String → Ty → Ctx → Type where
  | here : Elem x τ ((x, τ) :: Γ)
  | there : Elem x τ Γ → Elem x τ ((y, σ) :: Γ)

-- Simplified term language (no polymorphism for cleaner demo)
inductive Term : Ctx → Ty → Type where
  | var : (x : String) → Elem x τ Γ → Term Γ τ
  | lam : (x : String) → (α : Ty) → Term ((x, α) :: Γ) β → Term Γ (α ⟶ β)
  | app : Term Γ (α ⟶ β) → Term Γ α → Term Γ β

-- Type substitution (simplified)
def Ty.subst (τ : Ty) (a : String) (σ : Ty) : Ty :=
  match τ with
  | .var b => if a == b then σ else .var b
  | .arr τ₁ τ₂ => .arr (τ₁.subst a σ) (τ₂.subst a σ)
  | .app τ₁ τ₂ => .app (τ₁.subst a σ) (τ₂.subst a σ)
  | .forall_ b κ τ' => if a == b then .forall_ b κ τ' else .forall_ b κ (τ'.subst a σ)
  | .lam b κ τ' => if a == b then .lam b κ τ' else .lam b κ (τ'.subst a σ)

-- ═══════════════════════════════════════════════════════════════════════════════
-- SEMANTIC INTERPRETATION (Ty → Lean Type)
-- ═══════════════════════════════════════════════════════════════════════════════

-- Map PureScript types to Lean types
-- This is partial/unsafe in general, but works for the fragment we care about

-- For a simply-typed fragment:
def interpTy : Ty → Type
  | .var _ => Unit  -- Can't interpret free type variables properly
  | .arr α β => interpTy α → interpTy β
  | _ => Unit  -- Simplified

-- Environment interpretation
def interpCtx : Ctx → Type
  | [] => Unit
  | (_, τ) :: Γ => interpTy τ × interpCtx Γ

-- ═══════════════════════════════════════════════════════════════════════════════
-- TERM INTERPRETATION (Term → Lean value)
-- ═══════════════════════════════════════════════════════════════════════════════

-- This is the key: map typed PureScript terms to Lean values

def lookupEnv : Elem x τ Γ → interpCtx Γ → interpTy τ
  | .here, (v, _) => v
  | .there elem, (_, env) => lookupEnv elem env

def interp : Term Γ τ → interpCtx Γ → interpTy τ
  | .var _ elem, env => lookupEnv elem env
  | .lam _ _ body, env => fun a => interp body (a, env)
  | .app f a, env => (interp f env) (interp a env)

-- ═══════════════════════════════════════════════════════════════════════════════
-- CODE GENERATION (Term → String)
-- ═══════════════════════════════════════════════════════════════════════════════

def codegen : Term Γ τ → String
  | .var x _ => x
  | .lam x _ body => s!"(\\{x} -> {codegen body})"
  | .app f a => s!"({codegen f} {codegen a})"

-- ═══════════════════════════════════════════════════════════════════════════════
-- THE DREAM: EXTRACTION THEOREM
-- ═══════════════════════════════════════════════════════════════════════════════

/-
  The holy grail would be:
  
  theorem extraction_preserves_semantics :
    ∀ (e : Term [] τ), 
    run_purescript (codegen e) = interp e ()
    
  This says: if we compile a closed term to PureScript and run it,
  we get the same result as interpreting it in Lean.
  
  This requires:
  1. A formal semantics of PureScript (run_purescript)
  2. A proof that codegen preserves that semantics
  
  For now, we have a weaker but still useful property:
  codegen produces well-typed PureScript (by construction)
  because Term is intrinsically typed.
-/

-- ═══════════════════════════════════════════════════════════════════════════════
-- EXAMPLE: Verified identity
-- ═══════════════════════════════════════════════════════════════════════════════

-- We can build terms and know they're well-typed

-- For simply-typed: identity at a specific type
-- identity : Unit → Unit
def identityTerm : Term [] (Ty.var "a" ⟶ Ty.var "a") :=
  .lam "x" (.var "a") (.var "x" .here)

#eval codegen identityTerm  -- "(\x -> x)"

-- The interpretation IS the Lean identity function
example : interp identityTerm () = id := rfl

-- A more interesting example: const
-- const : a → b → a
def constTerm : Term [] (Ty.var "a" ⟶ Ty.var "b" ⟶ Ty.var "a") :=
  .lam "a" (.var "a") (.lam "b" (.var "b") (.var "a" (.there .here)))

#eval codegen constTerm  -- "(\a -> (\b -> a))"

-- The interpretation IS Lean's const
example : interp constTerm () = fun a _ => a := rfl

-- ═══════════════════════════════════════════════════════════════════════════════
-- WHAT'S STILL MISSING
-- ═══════════════════════════════════════════════════════════════════════════════

/-
  To reach the dream, we need:
  
  1. FULL TYPE INTERPRETATION
     - Handle polymorphism properly (parametricity)
     - Handle type constructors (Functor, Monad, etc.)
     - Handle row types (PureScript records)
  
  2. OPERATIONAL SEMANTICS
     - Define what "running" PureScript means
     - Prove codegen output has same behavior
  
  3. TYPE CLASS COMPILATION  
     - Compile type class constraints to dictionaries
     - Prove dictionary passing preserves semantics
  
  4. EFFECTS
     - Model PureScript's effect system
     - Prove effect handling is correct
  
  The architecture exists (see Coq's extraction, or Agda2HS).
  Doing it for PureScript specifically would be novel work.
-/

-- ═══════════════════════════════════════════════════════════════════════════════
-- PRAGMATIC MIDDLE GROUND
-- ═══════════════════════════════════════════════════════════════════════════════

/-
  What we CAN do today with confidence:
  
  1. Define functions in Lean with their laws (Sem.flip, etc.)
  2. Prove laws hold (flip_flip, compose_assoc, etc.)  
  3. Generate PureScript that structurally matches
  4. Trust that structural match + same types = same behavior
  
  This is "proof-adjacent" rather than "proof-carrying":
  - We prove things about Lean models
  - We generate PureScript that looks the same
  - We trust System F-omega is a sublanguage of CIC (it is!)
  
  The gap is: we don't have a machine-checked proof that
  the generated PureScript has the same semantics.
  But for the pure, terminating, simply-typed fragment,
  this is essentially guaranteed by the structure.
-/

-- ═══════════════════════════════════════════════════════════════════════════════
-- SUMMARY
-- ═══════════════════════════════════════════════════════════════════════════════

/-
  Distance to the dream:
  
  ┌────────────────────────────────────────┬─────────┐
  │ Feature                                │ Status  │
  ├────────────────────────────────────────┼─────────┤
  │ Intrinsically typed terms              │ ✓ Done  │
  │ Code generation                        │ ✓ Done  │
  │ Semantic interpretation (simple types) │ ✓ Done  │
  │ Semantic interpretation (polymorphism) │ ◐ Hard  │
  │ Semantic interpretation (type classes) │ ✗ Todo  │
  │ PureScript operational semantics       │ ✗ Todo  │
  │ Extraction correctness theorem         │ ✗ Todo  │
  │ Row types                              │ ✗ Todo  │
  │ Effects                                │ ✗ Todo  │
  └────────────────────────────────────────┴─────────┘
  
  The good news: for pure functions with simple types,
  we're actually quite close. The proofs we write in Lean
  DO apply to the generated PureScript, even if we can't
  formally state that theorem yet.
-/
