/-
  PureScript AST in Lean 4
  
  A minimal but complete AST for representing PureScript expressions,
  with pretty-printing and rfl-provable structural properties.
-/

-- ===== Core AST =====

/-- Simple PureScript expression AST -/
inductive PSExpr where
  | Var : String → PSExpr
  | Lam : String → PSExpr → PSExpr
  | App : PSExpr → PSExpr → PSExpr
  | Let : String → PSExpr → PSExpr → PSExpr
  | Lit : String → PSExpr  -- String/Int/Bool literals as strings
  deriving Repr, BEq, Inhabited

namespace PSExpr

/-- Pretty print a PSExpr to PureScript syntax -/
partial def pretty : PSExpr → String
  | .Var n => n
  | .Lam arg body => s!"\\{arg} -> {body.pretty}"
  | .App f arg => 
      let argStr := match arg with
        | .App _ _ => s!"({arg.pretty})"
        | _ => arg.pretty
      s!"{f.pretty} {argStr}"
  | .Let name val body => s!"let {name} = {val.pretty} in {body.pretty}"
  | .Lit s => s

/-- Check if an expression is a simple value (no computation) -/
def isValue : PSExpr → Bool
  | .Var _ => true
  | .Lam _ _ => true
  | .Lit _ => true
  | _ => false

/-- Count the number of lambda abstractions -/
def countLambdas : PSExpr → Nat
  | .Lam _ body => 1 + body.countLambdas
  | .App f arg => f.countLambdas + arg.countLambdas
  | .Let _ val body => val.countLambdas + body.countLambdas
  | _ => 0

/-- Collect all free variables -/
partial def freeVars (bound : List String := []) : PSExpr → List String
  | .Var n => if bound.contains n then [] else [n]
  | .Lam arg body => body.freeVars (arg :: bound)
  | .App f arg => f.freeVars bound ++ arg.freeVars bound
  | .Let name val body => val.freeVars bound ++ body.freeVars (name :: bound)
  | .Lit _ => []

end PSExpr

-- ===== Standard Combinators =====

/-- Identity: λx. x -/
def I : PSExpr := .Lam "x" (.Var "x")

/-- Constant: λx. λy. x -/
def K : PSExpr := .Lam "x" (.Lam "y" (.Var "x"))

/-- Substitution: λf. λg. λx. f x (g x) -/
def S : PSExpr := 
  .Lam "f" (.Lam "g" (.Lam "x" 
    (.App (.App (.Var "f") (.Var "x")) (.App (.Var "g") (.Var "x")))))

/-- Composition: λf. λg. λx. f (g x) -/
def B : PSExpr := 
  .Lam "f" (.Lam "g" (.Lam "x" 
    (.App (.Var "f") (.App (.Var "g") (.Var "x")))))

/-- Flip: λf. λx. λy. f y x -/
def C : PSExpr := 
  .Lam "f" (.Lam "x" (.Lam "y" 
    (.App (.App (.Var "f") (.Var "y")) (.Var "x"))))

/-- Self-application: λx. x x -/
def omega : PSExpr := .Lam "x" (.App (.Var "x") (.Var "x"))

/-- Y combinator: λf. (λx. f (x x)) (λx. f (x x)) -/
def Y : PSExpr :=
  let inner := PSExpr.Lam "x" (.App (.Var "f") (.App (.Var "x") (.Var "x")))
  .Lam "f" (.App inner inner)

-- ===== Church Encodings =====

def churchTrue : PSExpr := .Lam "t" (.Lam "f" (.Var "t"))
def churchFalse : PSExpr := .Lam "t" (.Lam "f" (.Var "f"))
def churchAnd : PSExpr := 
  .Lam "p" (.Lam "q" (.App (.App (.Var "p") (.Var "q")) churchFalse))
def churchOr : PSExpr := 
  .Lam "p" (.Lam "q" (.App (.App (.Var "p") churchTrue) (.Var "q")))
def churchNot : PSExpr := 
  .Lam "p" (.App (.App (.Var "p") churchFalse) churchTrue)

-- ===== Structural Proofs (rfl) =====

/-- Identity is structurally a single-arg lambda returning its arg -/
theorem I_structure : I = PSExpr.Lam "x" (.Var "x") := rfl

/-- K is structurally a two-arg lambda returning the first -/
theorem K_structure : K = PSExpr.Lam "x" (.Lam "y" (.Var "x")) := rfl

/-- B (composition) is equal to our compose definition -/
theorem B_is_compose : B = PSExpr.Lam "f" (.Lam "g" (.Lam "x" 
    (.App (.Var "f") (.App (.Var "g") (.Var "x"))))) := rfl

/-- I is a value -/
theorem I_is_value : I.isValue = true := rfl

/-- omega is a value -/
theorem omega_is_value : omega.isValue = true := rfl

/-- I has exactly 1 lambda -/
theorem I_has_one_lambda : I.countLambdas = 1 := rfl

/-- K has exactly 2 lambdas -/
theorem K_has_two_lambdas : K.countLambdas = 2 := rfl

/-- S has exactly 3 lambdas -/
theorem S_has_three_lambdas : S.countLambdas = 3 := rfl

/-- Church true has similar structure to K (both return first of two args) -/
theorem church_true_structure : churchTrue = PSExpr.Lam "t" (.Lam "f" (.Var "t")) := rfl

-- ===== Demo =====

def main : IO Unit := do
  IO.println "=== PureScript AST in Lean 4 ===\n"
  
  IO.println "-- Combinators --"
  IO.println s!"I = {I.pretty}"
  IO.println s!"K = {K.pretty}"
  IO.println s!"S = {S.pretty}"
  IO.println s!"B = {B.pretty}"
  IO.println s!"C = {C.pretty}"
  IO.println s!"Y = {Y.pretty}"
  IO.println s!"ω = {omega.pretty}"
  
  IO.println "\n-- Church Booleans --"
  IO.println s!"true  = {churchTrue.pretty}"
  IO.println s!"false = {churchFalse.pretty}"
  IO.println s!"and   = {churchAnd.pretty}"
  IO.println s!"or    = {churchOr.pretty}"
  IO.println s!"not   = {churchNot.pretty}"
  
  IO.println "\n-- Properties (proven with rfl) --"
  IO.println s!"I.isValue     = {I.isValue}"
  IO.println s!"I.countLambdas = {I.countLambdas}"
  IO.println s!"K.countLambdas = {K.countLambdas}"
  IO.println s!"S.countLambdas = {S.countLambdas}"
  IO.println s!"churchTrue structure matches K pattern"
  
  IO.println "\n-- Theorems --"
  IO.println "✓ I_structure : I = Lam \"x\" (Var \"x\")"
  IO.println "✓ K_structure : K = Lam \"x\" (Lam \"y\" (Var \"x\"))"
  IO.println "✓ B_is_compose"
  IO.println "✓ I_is_value : I.isValue = true"
  IO.println "✓ I_has_one_lambda : I.countLambdas = 1"
  IO.println "✓ K_has_two_lambdas : K.countLambdas = 2"
  IO.println "✓ S_has_three_lambdas : S.countLambdas = 3"
  IO.println "✓ church_true_structure"

#eval main
