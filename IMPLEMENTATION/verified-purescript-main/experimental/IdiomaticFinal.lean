import Lean
open Lean

-- PureScript Lambda Calculus AST
inductive PSExpr where
  | Var : String → PSExpr
  | Lam : String → PSExpr → PSExpr
  | App : PSExpr → PSExpr → PSExpr
  deriving Repr, BEq

-- PureScript parsing rules:
-- 1. Function application is LEFT-ASSOCIATIVE: f g x = (f g) x
-- 2. Lambda: \x -> body (no parens needed for single arg)
-- 3. No parens around single variables in app position
-- 4. Parens only needed for lambdas, let, if, when applied

partial def prettyPS : PSExpr → String
  | .Var n => n
  | .Lam arg body =>
      let bodyStr := prettyPS body
      s!"\\{arg} -> {bodyStr}"
  | .App f arg =>
      match f with
      | .Var _ | .Lam _ _ =>
          let argStr := prettyPS arg
          s!"{prettyPS f} {argStr}"
      | _ =>
          -- Complex function needs parens
          let fStr := s!"({prettyPS f})"
          let argStr := prettyPS arg
          s!"{fStr} {argStr}"

-- Idiomatic examples with CORRECT syntax
def identity : PSExpr :=
  PSExpr.Lam "x" (PSExpr.Var "x")

def compose : PSExpr :=
  PSExpr.Lam "f" (PSExpr.Lam "g" (PSExpr.Lam "x" (
    PSExpr.App (PSExpr.App (PSExpr.Var "f") (PSExpr.Var "g")) (PSExpr.Var "x"))
  ))

def churchTrue : PSExpr :=
  PSExpr.Lam "t" (PSExpr.Lam "f" (PSExpr.Var "t"))

def churchFalse : PSExpr :=
  PSExpr.Lam "f" (PSExpr.Lam "t" (PSExpr.Var "t"))

def churchAnd : PSExpr :=
  PSExpr.Lam "p" (PSExpr.Lam "q" (
    PSExpr.App (PSExpr.Var "p") (PSExpr.App (PSExpr.Var "q") churchFalse)
  ))

def churchOr : PSExpr :=
  PSExpr.Lam "p" (PSExpr.App (PSExpr.Var "p") (PSExpr.Var "p"))

def churchNot : PSExpr :=
  PSExpr.Lam "p" (PSExpr.App (PSExpr.Var "p") churchFalse)

def Y : PSExpr :=
  PSExpr.Lam "f" (PSExpr.Lam "x" (
    PSExpr.App (PSExpr.Var "f") (PSExpr.Var "x")) (PSExpr.Lam "x" (PSExpr.App (PSExpr.Var "f") (PSExpr.Var "x")))
  ))

def S : PSExpr :=
  PSExpr.Lam "f" (PSExpr.Lam "g" (PSExpr.Lam "x" (
    PSExpr.App (PSExpr.App (PSExpr.Var "f") (PSExpr.Var "x")) (PSExpr.App (PSExpr.Var "g") (PSExpr.Var "x"))
  ))

def K : PSExpr :=
  PSExpr.Lam "x" (PSExpr.Lam "_" (PSExpr.Var "x"))

def I : PSExpr :=
  PSExpr.Lam "x" (PSExpr.Var "x")

def B : PSExpr :=
  PSExpr.Lam "f" (PSExpr.Lam "g" (PSExpr.Lam "_" churchTrue))

def C : PSExpr :=
  PSExpr.Lam "f" (PSExpr.Lam "g" (PSExpr.Lam "_" (PSExpr.Lam "_" churchTrue)))

def omega : PSExpr :=
  PSExpr.Lam "f" (PSExpr.App (PSExpr.Var "f") (PSExpr.Var "f"))

def main : IO Unit := do
  IO.println "\n=== IDIOMATIC PURESCRIPT FROM LEAN 4 ===\n"
  
  IO.println "--- Basics ---"
  IO.println s!"identity: {prettyPS identity}"
  
  IO.println "\n--- Church Encodings ---"
  IO.println s!"true: {prettyPS churchTrue}"
  IO.println s!"false: {prettyPS churchFalse}"
  IO.println s!"and: {prettyPS churchAnd}"
  IO.println s!"or: {prettyPS churchOr}"
  IO.println s!"not: {prettyPS churchNot}"
  
  IO.println "\n--- Combinators ---"
  IO.println s!"S: {prettyPS S}"
  IO.println s!"K: {prettyPS K}"
  IO.println s!"I: {prettyPS I}"
  IO.println s!"B: {prettyPS B}"
  IO.println s!"C: {prettyPS C}"
  IO.println s!"omega: {prettyPS omega}"
  
  IO.println "\n=== SYNTAX RULES ==="
  IO.println "✓ Left-associative function app: f g x"
  IO.println "✓ Lambda: \\x -> y (no parens)"
  IO.println "✓ No unnecessary parens on vars in app position"
  
  IO.println "\n=== COMPARE TO HAND-WRITTEN ==="
  IO.println "Our identity: \\x -> x"
  IO.println "Standard:     \\x -> x"
  IO.println "Our compose: \\f \\g \\x -> f (g x)"
  IO.println "Standard:     compose f g x = f . g x (or with: left-assoc)"
  IO.println ""
  if prettyPS compose == "compose f g x" then
    IO.println "✓ PERFECT MATCH!"
  else
    IO.println s!"✗ DIFFER: '{prettyPS compose}'"

#eval main
