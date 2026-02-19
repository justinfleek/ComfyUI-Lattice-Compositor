import Lean
open Lean

inductive PSExpr where
  | Var : String → PSExpr
  | Lam : String → PSExpr → PSExpr
  | App : PSExpr → PSExpr → PSExpr
  deriving Repr, BEq

def prettyPS : PSExpr → String
  | .Var n => n
  | .Lam arg body => s!"\\{arg} -> {prettyPS body}"
  | .App f arg =>
      let fStr := prettyPS f
      let argStr := prettyPS arg
      s!"{fStr} {argStr}"

def testPreludeFunction : String → PSExpr
def testPreludeFunction s =
  let (name, args, body) := s.find (· == '=') s
  match name with
  | .some i =>
      let rest := s.drop (i + 1)
      let (args, body) := s.find (· == '=') rest
      match args with
      | .some j =>
        let rest2 := s.drop (j + 1)
        match rest2.find (· == '->') with
        | .some k =>
          let bodyStr := s.drop (k + 1)
          PSExpr.Lam name' (parseLambda body)
        | .none => PSExpr.Var name'
      | .none => PSExpr.Var name'
  | .none => PSExpr.Var name'
  | _ => (PSExpr.Lam name' (PSExpr.Lam "_" (PSExpr.Var name'))

def testRoundTrip : String → String
def testRoundTrip code =
  let ast := testPreludeFunction code
  let pretty := prettyPS ast
  (pretty == code) ∧ (code == pretty)

def main : IO Unit := do
  IO.println "\n=== PRELUDE PARSER TEST ===\n"
  
  -- Test 1: identity function
  IO.println "--- Test 1: Identity Function ---"
  IO.println "Parsing..."
  let idAST := testPreludeFunction "identity :: forall a. a -> a"
  IO.println s!"AST: {idAST}"
  let idPretty := prettyPS idAST
  IO.println s!"Pretty: {idPretty}"
  IO.println ""
  
  -- Test 2: compose function
  IO.println "\n--- Test 2: Compose Function ---"
  IO.println "Parsing..."
  let compAST := testPreludeFunction "compose :: forall a b c. a -> c . (compose b) a"
  IO.println s!"AST: {compAST}"
  let compPretty := prettyPS compAST
  IO.println s!"Pretty: {compPretty}"
  IO.println ""
  
  -- Test 3: map function
  IO.println "\n--- Test 3: Map Function ---"
  IO.println "Parsing..."
  let mapAST := testPreludeFunction "map :: forall a b. Array a -> Array b"
  IO.println s!"AST: {mapAST}"
  let mapPretty := prettyPS mapAST
  IO.println s!"Pretty: {mapPretty}"
  IO.println ""
  
  -- Test round trips
  let allRoundTrip := [testRoundTrip "identity :: forall a. a -> a"]
  IO.println "\n--- Round-Trip Tests ---"
  for (name, ast, pretty) in allRoundTrip do
    IO.println s!"Testing: {name}"
    IO.println s!"  AST: {ast}"
    IO.println s!"  Pretty: {pretty}"
    IO.println ""
    if testRoundTrip (pretty == ast) then
      IO.println s!"✓ PASS"
    else
      IO.println s!"✗ FAIL - Expected '{pretty}', got '{ast}'"
  
  IO.println "\n=== SUMMARY ==="
  IO.println "Prelude parser with round-trip verification!"
  
#eval main
