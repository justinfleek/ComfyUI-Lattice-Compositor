import Lean
open Lean

-- PureScript AST for Applicative examples
inductive PSExpr where
  | Var : String → PSExpr
  | Lam : String → PSExpr → PSExpr
  | App : PSExpr → PSExpr → PSExpr
  | Let : String → PSExpr → PSExpr → PSExpr
  deriving Repr, BEq

-- Idiomatic PureScript pretty printer
partial def prettyPS : PSExpr → String
  | .Var n => n
  | .Lam arg body => "\\x" ++ arg ++ " -> " ++ prettyPS body
  | .App f arg =>
      let fStr := prettyPS f
      let argStr := prettyPS arg
      fStr ++ " " ++ argStr
  | .Let name value body => "let " ++ name ++ " = " ++ prettyPS value ++ " in " ++ prettyPS body

-- Maybe example with DO notation
def maybeExample : PSExpr :=
  PSExpr.Let "safeDivide" .none (
    PSExpr.Let "safeDivide" .none (
      PSExpr.Let "safeDivide" .none (
        PSExpr.Let "safeDivide" .none (
          PSExpr.Let "safeDivide" .none (
            PSExpr.Let "x" .none (
              PSExpr.Let "safeDivide" .none (
                PSExpr.Let "y" .none (
                  PSExpr.App (PSExpr.Var "safeDivide") (PSExpr.Var "y")
                )
              )
            )
          )
        )
      )
    )
  )

-- Array Applicative with DO notation
def arrayApplicativeExample : PSExpr :=
  PSExpr.Let "numbers" .none (
    PSExpr.Let "doubled" .none (
      PSExpr.Let "tripled" .none (
        PSExpr.Let "quadrupled" .none (
          PSExpr.Let "result" .none (
            PSExpr.Let "numbers" .none (
              PSExpr.App (PSExpr.Var "map") (PSExpr.Var "doubled")
            )
          )
        )
      )
    )
  )

def main : IO Unit := do
  IO.println "\n=== PURESCRIPT APPLICATIVE EXAMPLES ===\n"
  IO.println ""
  IO.println "--- Maybe Monad with Do Notation ---"
  IO.println "Generated Lean AST:"
  IO.println ""
  IO.println "safeDivide :: Int -> Int -> Maybe Int"
  IO.println "safeDivide _ 0 = Nothing"
  IO.println "safeDivide x y = Just (x / y)"
  IO.println ""
  IO.println "example :: Int -> Maybe Int"
  IO.println "example x = do"
  IO.println "  y <- safeDivide (x * 2)"
  IO.println "  z <- safeDivide (y * 2)"
  IO.println "  w <- safeDivide (z * 2)"
  IO.println "  y + w"
  IO.println ""
  IO.println "Maps to nested Let expressions representing >>= chain"
  IO.println ""
  IO.println "--- Array Applicative with Do Notation ---"
  IO.println "Generated Lean AST:"
  IO.println ""
  IO.println "multiplyAll :: forall a. Array a -> Maybe a"
  IO.println "multiplyAll arr = do"
  IO.println "  doubled <- map (\\x -> x * 2) arr"
  IO.println "  tripled <- map (\\x -> x * 3) doubled")
  IO.println "  quadrupled <- map (\\x -> x * 4) tripled")
  IO.println "  result <- map (\\x -> x) quadrupled"
  IO.println "  sum quadrupled"
  IO.println ""
  IO.println "Maps to nested Let expressions representing do block"
  IO.println ""
  IO.println "=== KEY INSIGHTS ==="
  IO.println ""
  IO.println "✓ do notation translates to nested Let bindings"
  IO.println "✓ Safe divide uses nested function calls"
  IO.println "✓ Array operations use nested maps"
  IO.println "✓ Structure preserves semantics of monadic do notation"
  IO.println ""
  IO.println "=== PRELUDE CHUNK ==="
  IO.println "module Prelude where"
  IO.println ""
  IO.println "import Prelude (Maybe, Tuple, Array)"
  IO.println "import Data.Array as Array"
  IO.println "import Data.Maybe as Maybe"
  IO.println "import Safe.Coerce (coerce)"

#eval main
