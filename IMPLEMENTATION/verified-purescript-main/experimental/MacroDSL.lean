import Lean
open Lean

-- Simple DSL for generating PureScript code
syntax "purescript" ident : term
syntax "pvar" ident : term
syntax "plam" ident "=>" term : term
syntax "papp" term term : term
syntax "plet" ident "=" term "in" term : term
syntax "pif" term "then" term "else" term : term

macro_rules
  | `(purescript $name) => `(PSExpr.Var $name)
  | `(plam $arg => $body) => `(PSExpr.Lam $arg $body)
  | `(papp $f $arg) => `(PSExpr.App $f $arg)
  | `(plet $name = $value in $body) => `(PSExpr.Let $name $value $body)
  | `(pif $cond then $t else $e) => `(PSExpr.If $cond $t $e)

inductive PSExpr where
  | Var : String → PSExpr
  | Lam : String → PSExpr → PSExpr
  | App : PSExpr → PSExpr → PSExpr
  | Let : String → PSExpr → PSExpr → PSExpr
  | If : PSExpr → PSExpr → PSExpr → PSExpr
deriving Repr

def generatePS : PSExpr → String
  | .Var name => name
  | .Lam arg body => s!"(\\{arg} -> {generatePS body})"
  | .App f arg => s!"({generatePS f} ({generatePS arg}))"
  | .Let name value body => s!"let {name} = {generatePS value} in {generatePS body}"
  | .If cond then_ else_ => s!"if {generatePS cond} then {generatePS then_} else {generatePS else_}"

-- Using the DSL
#eval generatePS (purescript x)
#eval generatePS (plam x => purescript y)
#eval generatePS (papp (plam x => purescript x) (purescript y))
#eval generatePS (plet x = purescript y in purescript x)
#eval generatePS (pif (purescript x) then (purescript y) else (purescript z))

-- More complex example
def complexExample :=
  plet compose =
    plam f =>
    plam g =>
    plam x =>
    papp (papp f (papp g (purescript x))) (purescript y)

#eval generatePS complexExample
