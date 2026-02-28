/-
  Hydrogen.Layout.Presburger
  
  Linear constraints for layout verification.
  Presburger arithmetic is decidable — we can PROVE satisfiability.
  
  Status: FOUNDATION
-/

import Mathlib.Tactic

namespace Hydrogen.Layout

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 1: LINEAR TERMS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Variable identifier for layout constraints -/
abbrev Var := String

/-- Linear term: c₁x₁ + c₂x₂ + ... + cₙxₙ + k
    Represented as coefficient map plus constant -/
structure LinTerm where
  coeffs : List (Var × Int)
  constant : Int
  deriving Repr, DecidableEq

/-- Zero term -/
def LinTerm.zero : LinTerm := ⟨[], 0⟩

/-- Constant term -/
def LinTerm.const (k : Int) : LinTerm := ⟨[], k⟩

/-- Single variable with coefficient 1 -/
def LinTerm.var (x : Var) : LinTerm := ⟨[(x, 1)], 0⟩

/-- Scale a term by integer -/
def LinTerm.scale (c : Int) (t : LinTerm) : LinTerm :=
  ⟨t.coeffs.map (fun (x, k) => (x, c * k)), c * t.constant⟩

/-- Add two terms -/
def LinTerm.add (t1 t2 : LinTerm) : LinTerm :=
  ⟨t1.coeffs ++ t2.coeffs, t1.constant + t2.constant⟩

/-- Negate a term -/
def LinTerm.neg (t : LinTerm) : LinTerm := t.scale (-1)

/-- Subtract terms -/
def LinTerm.sub (t1 t2 : LinTerm) : LinTerm := t1.add t2.neg

instance : Add LinTerm := ⟨LinTerm.add⟩
instance : Neg LinTerm := ⟨LinTerm.neg⟩
instance : Sub LinTerm := ⟨LinTerm.sub⟩
-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 2: CONSTRAINTS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Comparison relation -/
inductive Rel
  | eq   -- =
  | le   -- ≤
  | lt   -- <
  | ge   -- ≥
  | gt   -- >
  deriving Repr, DecidableEq

/-- Linear constraint: term `rel` 0
    Example: x + 2y - 10 ≤ 0 means x + 2y ≤ 10 -/
structure Constraint where
  lhs : LinTerm
  rel : Rel
  deriving Repr, DecidableEq

/-- Create constraint: term ≤ 0 -/
def Constraint.leZero (t : LinTerm) : Constraint := ⟨t, Rel.le⟩

/-- Create constraint: term = 0 -/
def Constraint.eqZero (t : LinTerm) : Constraint := ⟨t, Rel.eq⟩

/-- Create constraint: term ≥ 0 -/
def Constraint.geZero (t : LinTerm) : Constraint := ⟨t, Rel.ge⟩

/-- Create constraint: t1 ≤ t2 -/
def Constraint.le (t1 t2 : LinTerm) : Constraint := 
  Constraint.leZero (t1 - t2)

/-- Create constraint: t1 = t2 -/
def Constraint.eq (t1 t2 : LinTerm) : Constraint := 
  Constraint.eqZero (t1 - t2)

/-- Create constraint: t1 ≥ t2 -/
def Constraint.ge (t1 t2 : LinTerm) : Constraint := 
  Constraint.geZero (t1 - t2)  
-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 3: PRESBURGER FORMULA
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Presburger formula (quantifier-free fragment) -/
inductive Formula
  | atom (c : Constraint)
  | and (φ ψ : Formula)
  | or (φ ψ : Formula)
  | not (φ : Formula)
  | tt  -- true
  | ff  -- false
  deriving Repr

/-- Conjunction of constraint list -/
def Formula.conj : List Constraint → Formula
  | [] => Formula.tt
  | [c] => Formula.atom c
  | c :: cs => Formula.and (Formula.atom c) (Formula.conj cs)

/-- Valuation: variable assignment -/
abbrev Valuation := Var → Int

/-- Evaluate linear term under valuation -/
def LinTerm.eval (v : Valuation) (t : LinTerm) : Int :=
  t.coeffs.foldl (fun acc (x, c) => acc + c * v x) t.constant

/-- Evaluate relation -/
def Rel.eval (r : Rel) (n : Int) : Bool :=
  match r with
  | Rel.eq => n == 0
  | Rel.le => n ≤ 0
  | Rel.lt => n < 0
  | Rel.ge => n ≥ 0
  | Rel.gt => n > 0

/-- Evaluate constraint under valuation -/
def Constraint.eval (v : Valuation) (c : Constraint) : Bool :=
  c.rel.eval (c.lhs.eval v)

/-- Evaluate formula under valuation -/
def Formula.eval (v : Valuation) : Formula → Bool
  | atom c => c.eval v
  | and φ ψ => φ.eval v && ψ.eval v
  | or φ ψ => φ.eval v || ψ.eval v
  | not φ => !φ.eval v
  | tt => true
  | ff => false

/-- A formula is satisfiable if some valuation makes it true -/
def Formula.satisfiable (φ : Formula) : Prop :=
  ∃ v : Valuation, φ.eval v = true

/-- A formula is valid if all valuations make it true -/
def Formula.valid (φ : Formula) : Prop :=
  ∀ v : Valuation, φ.eval v = true
-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 4: DECISION VIA OMEGA
-- ═══════════════════════════════════════════════════════════════════════════════

/-! 
Lean's `omega` tactic decides Presburger arithmetic automatically.
We demonstrate its use on layout constraint examples.
-/

/-- Example: x ≥ 0 ∧ x ≤ 10 is satisfiable -/
example : ∃ x : Int, x ≥ 0 ∧ x ≤ 10 := by
  use 5
  omega

/-- Example: x ≥ 10 ∧ x ≤ 5 is unsatisfiable -/
example : ¬∃ x : Int, x ≥ 10 ∧ x ≤ 5 := by
  intro ⟨x, h1, h2⟩
  omega

/-- Layout example: button fits in container
    container_width = 100
    button_x ≥ padding (10)
    button_x + button_width ≤ container_width - padding (90)
    button_width ≥ min_width (30)
-/
example : ∃ (button_x button_width : Int),
    button_x ≥ 10 ∧
    button_x + button_width ≤ 90 ∧
    button_width ≥ 30 := by
  use 10, 30
  omega

/-- Layout example: two buttons that DON'T fit
    container = 100, padding = 10 each side (80 usable)
    two buttons min 50 each + gap 10 = 110 > 80
-/
example : ¬∃ (x1 w1 x2 w2 : Int),
    x1 ≥ 10 ∧                    -- left padding
    x1 + w1 ≤ 90 ∧               -- right padding
    w1 ≥ 50 ∧                    -- min width 1
    x2 ≥ x1 + w1 + 10 ∧          -- gap between buttons
    x2 + w2 ≤ 90 ∧               -- right padding
    w2 ≥ 50 := by                -- min width 2
  intro ⟨x1, w1, x2, w2, h1, h2, h3, h4, h5, h6⟩
  omega
-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 5: LAYOUT ENCODING
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Layout element with position and size variables -/
structure LayoutElement where
  id : String
  xVar : Var      -- position variable name
  wVar : Var      -- width variable name
  minWidth : Int
  maxWidth : Option Int
  deriving Repr

/-- Container constraints -/
structure Container where
  width : Int
  paddingLeft : Int
  paddingRight : Int
  gap : Int
  deriving Repr

/-- Generate constraints for element in container -/
def LayoutElement.constraints (c : Container) (e : LayoutElement) : List Constraint :=
  let x := LinTerm.var e.xVar
  let w := LinTerm.var e.wVar
  let minW := LinTerm.const e.minWidth
  let padL := LinTerm.const c.paddingLeft
  let padR := LinTerm.const c.paddingRight
  let containerW := LinTerm.const c.width
  [
    -- x ≥ paddingLeft
    Constraint.ge x padL,
    -- x + w ≤ containerWidth - paddingRight  
    Constraint.le (x + w) (containerW - padR),
    -- w ≥ minWidth
    Constraint.ge w minW
  ] ++ match e.maxWidth with
    | some maxW => [Constraint.le w (LinTerm.const maxW)]
    | none => []

/-- Generate gap constraint between two elements -/
def gapConstraint (gap : Int) (e1 e2 : LayoutElement) : Constraint :=
  let x1 := LinTerm.var e1.xVar
  let w1 := LinTerm.var e1.wVar
  let x2 := LinTerm.var e2.xVar
  let g := LinTerm.const gap
  -- x2 ≥ x1 + w1 + gap
  Constraint.ge x2 (x1 + w1 + g)

/-- Encode entire layout as formula -/
def encodeLayout (c : Container) (elements : List LayoutElement) : Formula :=
  let elementConstraints := elements.bind (LayoutElement.constraints c)
  let gapConstraints := match elements with
    | [] => []
    | [_] => []
    | e1 :: e2 :: rest => 
        gapConstraint c.gap e1 e2 :: 
        (rest.zip (e2 :: rest)).map (fun (prev, curr) => gapConstraint c.gap prev curr)
  Formula.conj (elementConstraints ++ gapConstraints)

end Hydrogen.Layout
