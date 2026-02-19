import Lean
open Lean

inductive PSExpr where
  | Var : String → PSExpr
  | Int : Nat → PSExpr
  | Bool : Bool → PSExpr
  | Lam : String → PSExpr → PSExpr
  | App : PSExpr → PSExpr → PSExpr
  deriving Repr

partial def parseVar (s : String) : PSExpr × String :=
  match s.find (· == ' ') with
  | .some i => (PSExpr.Var (s.take i), s.drop i)
  | .none => (PSExpr.Var s, "")

partial def parseExpr (s : String) : PSExpr × String :=
  if s.startsWith "fun " then
    let rest := s.drop 4
    match rest.find (· == ' ') with
    | .some i =>
      let arg := rest.take i
      let rest2 := rest.drop (i + 3)
      let (body, _) := parseExpr rest2
      (PSExpr.Lam arg body, "")
    | .none => (PSExpr.Unit, s)
  else if s.startsWith "true" then (PSExpr.Bool true, s.drop 4)
  else if s.startsWith "false" then (PSExpr.Bool false, s.drop 5)
  else if s.get? 0 |>.map (·.isAlpha) |>.getD false then parseVar s
  else (PSExpr.Unit, s)

def generatePS : PSExpr → String
  | .Var name => name
  | .Int n => toString n
  | .Bool b => if b then "true" else "false"
  | .Lam arg body => s!"(\\{arg} -> {generatePS body})"
  | .App f arg => s!"({generatePS f} ({generatePS arg}))"
  | .Unit => "unit"

def transpile (leanCode : String) : String :=
  (parseExpr leanCode).1 |> generatePS

-- Tests
#eval! transpile "fun x => x"
#eval! transpile "fun f => f 5"
#eval! transpile "true"
#eval! transpile "false"
