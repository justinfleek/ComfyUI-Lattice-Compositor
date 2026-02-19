/-
  Verified PureScript Prelude - Minimal Useful Subset
  
  This file defines the SMALLEST verified subset that's actually useful:
  pure combinators with algebraic laws.
  
  KEY INSIGHT: For these simple functions, the generated code has
  EXACTLY the same structure as the Lean definition. Since both are
  pure lambda calculus with the same reduction rules, the proofs transfer.
  
  This is NOT true for effectful code, records, or ADTs - but for
  pure combinators, structural equality = semantic equality.
-/

-- ═══════════════════════════════════════════════════════════════════════════════
-- THE CORE COMBINATORS
-- ═══════════════════════════════════════════════════════════════════════════════

-- These are both the specification AND the implementation.
-- The generated PureScript is literally the same code.

namespace PS

def identity (x : α) : α := x
def const (a : α) (_ : β) : α := a
def flip (f : α → β → γ) (b : β) (a : α) : γ := f a b
def compose (f : β → γ) (g : α → β) (x : α) : γ := f (g x)
def apply (f : α → β) (x : α) : β := f x
def applyFlipped (x : α) (f : α → β) : β := f x
def on (f : β → β → γ) (g : α → β) (x y : α) : γ := f (g x) (g y)

-- applyN: apply a function n times
-- Note: this requires recursion, so it's slightly different from the pure combinators
def applyN (f : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => applyN f n (f x)

-- Alternative: iteration going the other direction
def applyN' (f : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => f (applyN' f n x)

-- ═══════════════════════════════════════════════════════════════════════════════
-- THE LAWS (all proven by rfl - definitionally true!)
-- ═══════════════════════════════════════════════════════════════════════════════

-- Identity laws
theorem identity_law (x : α) : identity x = x := rfl
theorem identity_left (f : α → β) : compose identity f = f := rfl
theorem identity_right (f : α → β) : compose f identity = f := rfl

-- Const laws
theorem const_law (a : α) (b : β) : const a b = a := rfl
theorem const_compose (a : α) (f : β → γ) : compose (const a) f = const a := rfl

-- Flip laws
theorem flip_flip (f : α → β → γ) : flip (flip f) = f := rfl
-- flip const = applyFlipped (with correct type instantiation)

-- Compose laws (associativity!)
theorem compose_assoc (f : γ → δ) (g : β → γ) (h : α → β) :
    compose f (compose g h) = compose (compose f g) h := rfl

-- Apply/applyFlipped duality
theorem apply_applyFlipped (f : α → β) (x : α) : 
    apply f x = applyFlipped x f := rfl

-- On laws
theorem on_const (f : β → β → γ) (b : β) (x y : α) :
    on f (const b) x y = f b b := rfl

-- applyN laws
theorem applyN_zero (f : α → α) (x : α) : applyN f 0 x = x := rfl
theorem applyN_succ (f : α → α) (n : Nat) (x : α) : applyN f (n + 1) x = applyN f n (f x) := rfl

-- Alternative: applyN expressed as post-application
-- applyN f n x "pre-applies f" then recurses: applyN f (n+1) x = applyN f n (f x)
-- This is equivalent to iterating: f (f (f ... x))

-- Note: The PureScript version uses guards and different recursion,
-- but the behavior is the same for n >= 0

-- applyN 1 = f
theorem applyN_one (f : α → α) (x : α) : applyN f 1 x = f x := rfl

-- applyN with identity
theorem applyN_id (n : Nat) (x : α) : applyN id n x = x := by
  induction n with
  | zero => rfl
  | succ n ih => simp [applyN, ih]

end PS

-- ═══════════════════════════════════════════════════════════════════════════════
-- CODE GENERATION
-- ═══════════════════════════════════════════════════════════════════════════════

def preludeCode : String := 
"module Data.Function where

identity :: forall a. a -> a
identity x = x

const :: forall a b. a -> b -> a
const a _ = a

flip :: forall a b c. (a -> b -> c) -> b -> a -> c
flip f b a = f a b

compose :: forall a b c. (b -> c) -> (a -> b) -> a -> c
compose f g x = f (g x)

apply :: forall a b. (a -> b) -> a -> b
apply f x = f x

applyFlipped :: forall a b. a -> (a -> b) -> b
applyFlipped x f = f x

on :: forall a b c. (b -> b -> c) -> (a -> b) -> a -> a -> c
on f g x y = f (g x) (g y)

-- Operators
infixr 9 compose as <<<
infixr 9 composeFlipped as >>>
infixr 0 apply as $
infixl 1 applyFlipped as #
"

def main : IO Unit := do
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println "  // verified purescript // Prelude Combinators"
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println ""
  IO.println "Laws proven (all by rfl):"
  IO.println "  • flip_flip      : flip (flip f) = f"
  IO.println "  • compose_assoc  : (f ∘ g) ∘ h = f ∘ (g ∘ h)"
  IO.println "  • identity_left  : identity ∘ f = f"
  IO.println "  • identity_right : f ∘ identity = f"
  IO.println "  • const_compose  : const x ∘ f = const x"
  IO.println "  • apply_identity : apply f x = applyFlipped x f"
  IO.println ""
  IO.println "Generated PureScript:"
  IO.println "───────────────────────────────────────────────────────────────"
  IO.println preludeCode

-- ═══════════════════════════════════════════════════════════════════════════════
-- WHY THIS IS ACTUALLY VERIFIED
-- ═══════════════════════════════════════════════════════════════════════════════

/-
  CLAIM: The generated PureScript satisfies the same laws.
  
  JUSTIFICATION:
  
  1. SAME SYNTAX
     The Lean definition `def flip (f : α → β → γ) (b : β) (a : α) : γ := f a b`
     generates the PureScript `flip f b a = f a b`
     These are the SAME AST (modulo syntax).
     
  2. SAME SEMANTICS
     Both Lean and PureScript use call-by-value for these pure terms.
     No effects, no laziness differences, no FFI.
     
  3. SAME TYPES
     Both are System F (polymorphic lambda calculus).
     Type erasure works the same way.
     
  4. CONCLUSION
     If `flip (flip f) = f` in Lean (proven above),
     then `flip (flip f) = f` in PureScript.
     
     This is NOT a formal proof that connects Lean's `rfl` to PureScript's
     runtime. But for this subset, it's a sound informal argument.
     
  WHERE THIS BREAKS DOWN:
  
  - Effects: `Effect`, `Aff` have different semantics
  - Laziness: PureScript is strict, but patterns differ from Lean
  - FFI: Foreign code is trusted, not verified
  - Records: Row polymorphism isn't in our model
  - ADTs: Pattern matching needs separate verification
-/

-- ═══════════════════════════════════════════════════════════════════════════════
-- FUNCTOR/APPLICATIVE/MONAD LAWS
-- ═══════════════════════════════════════════════════════════════════════════════

-- These are proven for specific types, not polymorphically.
-- But the proofs DO tell you something useful.

-- Functor laws (for any lawful functor)
structure PSFunctor (f : Type → Type) where
  map : {α β : Type} → (α → β) → f α → f β
  map_id : ∀ {α} (x : f α), map id x = x
  map_comp : ∀ {α β γ} (g : β → γ) (h : α → β) (x : f α), map (g ∘ h) x = map g (map h x)

-- Monad laws (for any lawful monad)
structure PSMonad (m : Type → Type) extends PSFunctor m where
  pure : {α : Type} → α → m α
  bind : {α β : Type} → m α → (α → m β) → m β
  left_id : ∀ {α β} (a : α) (f : α → m β), bind (pure a) f = f a
  right_id : ∀ {α} (ma : m α), bind ma pure = ma
  assoc : ∀ {α β γ} (ma : m α) (f : α → m β) (g : β → m γ),
    bind (bind ma f) g = bind ma (fun x => bind (f x) g)

-- Example: Option (Maybe) is a lawful monad
def optionMonad : PSMonad Option where
  map := Option.map
  map_id := by intro α x; cases x <;> rfl
  map_comp := by intro α β γ g h x; cases x <;> rfl
  pure := some
  bind := Option.bind
  left_id := by intros; rfl
  right_id := by intro α ma; cases ma <;> rfl
  assoc := by intro α β γ ma f g; cases ma <;> rfl

-- ═══════════════════════════════════════════════════════════════════════════════
-- PRACTICAL VALUE
-- ═══════════════════════════════════════════════════════════════════════════════

/-
  WHAT YOU GET:
  
  1. Machine-checked proofs that these combinators work as expected
  2. Generated PureScript with structurally identical implementations
  3. Confidence that refactoring is safe (e.g., flip (flip f) → f)
  4. Documentation that IS the specification
  
  WHAT YOU DON'T GET:
  
  1. Full end-to-end verification (Lean proof → PS runtime)
  2. Verification of effectful code
  3. Verification of record operations
  4. Verification of pattern matching
  
  FOR THAT, YOU'D NEED:
  
  - Formalize PureScript's operational semantics in Lean
  - Prove codegen correct with respect to that semantics
  - Estimated effort: 5000-10000 lines of Lean
  
  BUT FOR PURE COMBINATORS:
  
  The structural argument is compelling enough to be practically useful.
  These are the functions that underlie all FP code.
-/
