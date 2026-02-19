import Lean
open Lean

-- PureScript AST
inductive PSExpr where
  | Var : String → PSExpr
  | Lam : String → PSExpr → PSExpr
  | App : PSExpr → PSExpr → PSExpr
  | If : PSExpr → PSExpr → PSExpr → PSExpr
deriving Repr

-- Helper to create variables
def var (name : String) : PSExpr := PSExpr.Var name

-- Helper to create lambdas
def lam (name : String) (body : PSExpr) : PSExpr := PSExpr.Lam name body

-- Helper to create application
def app (f arg : PSExpr) : PSExpr := PSExpr.App f arg

-- Helper to create if
def iff (cond then_ else_ : PSExpr) : PSExpr := PSExpr.If cond then_ else_

-- PureScript code generator
def generatePS : PSExpr → String
  | .Var name => name
  | .Lam arg body => s!"(\\{arg} -> {generatePS body})"
  | .App f arg => s!"({generatePS f} ({generatePS arg}))"
  | .If cond then_ else_ => s!"if {generatePS cond} then {generatePS then_} else {generatePS else_}"

-- Examples
def identity := lam "x" (var "x")

#eval generatePS identity

def compose :=
  lam "f" (
    lam "g" (
      lam "x" (
        app (app (var "f") (app (app (var "g") (var "x")) (var "x"))) (var "y")
      )
    )
  )

#eval generatePS compose

def conditional :=
  lam "x" (
    iff (app (var "isZero") (var "x"))
      (var "zero")
      (var "success")
  )

#eval generatePS conditional

-- Church encoding example
def churchTrue :=
  lam "t" (
    lam "f" (
      var "t"
    )
  )

def churchFalse :=
  lam "f" (
    lam "t" (
      var "t"
    )
  )

def churchAnd :=
  lam "p" (
    lam "q" (
      app (app (var "p") (var "q")) (churchFalse)
    )
  )

#eval generatePS churchTrue
#eval generatePS churchFalse
#eval generatePS churchAnd

-- Y combinator
def yCombinator :=
  lam "f" (
    app (lam "x" (
      app (var "f") (app (var "x") (var "x"))
    )) (lam "x" (
      app (var "f") (app (var "x") (var "x"))
    ))
  )

#eval generatePS yCombinator
