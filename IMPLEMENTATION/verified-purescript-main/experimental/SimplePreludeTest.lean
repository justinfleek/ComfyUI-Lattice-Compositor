import Lean
open Lean

inductive PSExpr where
  | Var : String → PSExpr
  | Lam : String → PSExpr → PSExpr
  | App : PSExpr → PSExpr → PSExpr
  deriving Repr, BEq

partial def drop' : Nat → String → String
  | 0, s => s
  | n+1, s => drop' n (s.take n)

partial def parseIdent : String → String × String
  | s =>
    match s.find (· == ':') with
    | .some i => (s.take i, s.drop' (i + 1))
    | .none => (s, "")

partial def parseSimpleFunc : String → String × String
  | s =>
    match s.find (· == '=') with
    | .some i =>
        let (name, rest) := parseSimpleFunc (s.drop' (i + 1))
        (name, rest)
    | .none => (s, "")

partial def parseLambda : String → String → String
  | s =>
    match s.drop 4 with
    | "\\" ++ rest =>
        match rest.find (· == '>') with
        | .some i =>
          let (args, body) := parseLambdaBody (rest.drop' (i + 1))
          ("args", body)
        | .none => ("", rest)
    | _ => (s, rest)

partial def parseLambdaBody : String → String → String
  | s =>
    match s.find (· == '>') with
    | .some i =>
        let (arg, body) := parseSimpleFunc (s.drop' (i + 1))
        (arg, body)
    | .none => ("", s)

partial def simpleFuncToPS : String → PSExpr
  | name =>
    PSExpr.Lam name (PSExpr.Var "a")

partial def parseIdentity : String → PSExpr
  | s =>
    let rest := String.drop 8
    match rest with
    | "::" ++ rest' => parseTypedFunc rest
    | _ => parseSimpleFunc "identity" rest

partial def parseTypedFunc : String → PSExpr
  | s =>
    let (name, rest) := parseSimpleFunc s
    let rest2 := String.drop 1 rest
    match rest2 with
    | "." ++ rest' => simpleFuncToPS name rest2
    | _ => PSExpr.Lam name (PSExpr.Var "a")

partial def parseFuncBody : String → PSExpr
  | s =>
    match s.find (· == '->') with
    | .some i =>
        let (name, rest) := parseSimpleFunc (s.drop' (i + 2))
        (name, rest)
    | .none => (s, "")

def prettyPS : PSExpr → String
  | .Var n => n
  | .Lam arg body => s!"\\{arg} -> {prettyPS body}"
  | .App f arg =>
      let fStr := prettyPS f
      let argStr := prettyPS arg
      fStr ++ " " ++ argStr

def parsePreludeFunc : String → PSExpr
  | s =>
    let (name, rest) := parseSimpleFunc s
    PSExpr.Lam name' (PSExpr.Var "a")

def main : IO Unit := do
  IO.println "=== SIMPLE PRELUDE PARSER TEST ==="
  IO.println "Parsing identity :: forall a. a -> a"
  let result := parseIdentity "identity :: forall a. a -> a"
  IO.println s!"Parsed name: {result.1}"
  IO.println s!"Parsed params: {result.2}"
  IO.println s!"Function body: {result.2.2}"
  IO.println ""
  let pretty := prettyPS result.2.2
  IO.println "=== PRETTY PRINTED ==="
  IO.println pretty
  IO.println ""
  IO.println "=== COMPARE ==="
  IO.println "Expected: identity :: forall a. a -> a"
  IO.println s!"Got: {pretty}"
  IO.println ""
  if pretty == "identity :: forall a. a -> a" then
    IO.println "✓ PERFECT MATCH!"
  else
    IO.println "✗ DIFFERENT"

#eval main
