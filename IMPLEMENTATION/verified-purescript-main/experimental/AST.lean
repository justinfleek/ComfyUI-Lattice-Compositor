import Lean
open Lean

-- ===== PURESCRIPT AST =====

inductive PSType where
  | TInt : PSType
  | TString : PSType
  | TBoolean : PSType
  | TUnit : PSType
  | TArray : PSType → PSType
  | TFunction : PSType → PSType → PSType
  | TRecord : List (String × PSType) → PSType
  | TTuple : List PSType → PSType
  | TTypeVar : String → PSType
  deriving Repr, BEq

inductive PSExpr where
  | Var : String → PSExpr
  | Constructor : String → PSExpr
  | Int : Int → PSExpr
  | String : String → PSExpr
  | Boolean : Bool → PSExpr
  | Unit : PSExpr
  | Array : List PSExpr → PSExpr
  | Record : List (String × PSExpr) → PSExpr
  | App : PSExpr → PSExpr → PSExpr
  | Lam : String → Maybe PSType → PSExpr → PSExpr
  | Let : String → Maybe PSType → PSExpr → PSExpr → PSExpr
  | Case : PSExpr → List (PSExpr × PSExpr) → PSExpr
  | If : PSExpr → PSExpr → PSExpr → PSExpr
  | Op : String → PSExpr → PSExpr → PSExpr
  | Accessor : PSExpr → String → PSExpr
  deriving Repr, BEq

inductive PSDecl where
  | Import : List String → PSDecl
  | Module : String → List PSDecl → PSDecl
  | Data : String → List (String × List PSType) → PSDecl
  | TypeSynonym : String → List String → PSType → PSDecl
  | Value : String → Maybe PSType → PSExpr → PSDecl
  | deriving Repr, BEq

-- ===== PRETTY PRINTER =====

def indent (n : Nat) : String :=
  String.mk n ' '

def prettyTypeAux : Nat → PSType → String
  | _, .TInt => "Int"
  | _, .TString => "String"
  | _, .TBoolean => "Boolean"
  | _, .TUnit => "Unit"
  | d, .TArray t => s!"(Array {prettyTypeAux (d + 1) t})"
  | d, .TFunction a b => 
    let aStr := prettyTypeAux (d + 1) a
    let bStr := prettyTypeAux (d + 1) b
    s!"({aStr} -> {bStr})"
  | _, .TRecord fields =>
    let fieldsStr := fields.map (fun (n, t) => s!"{n} :: {prettyTypeAux 0 t}")
    let inner := String.join ", " fieldsStr
    s!"{inner}"
  | _, .TTuple ts =>
    let tsStr := ts.map (fun t => prettyTypeAux (d + 1) t)
    let inner := String.join ", " tsStr
    s!"({inner})"
  | _, .TTypeVar n => n

abbrev prettyType := prettyTypeAux 0

partial def prettyExprAux : Nat → PSExpr → String
  | _, .Var n => n
  | _, .Constructor n => n
  | _, .Int i => toString i
  | _, .String s => s!"\"{s}\""
  | _, .Boolean b => if b then "true" else "false"
  | _, .Unit => "unit"
  | d, .Array elems =>
    let elemsStr := elems.map (fun e => prettyExprAux d e)
    let inner := String.join ", " elemsStr
    s!"[{inner}]"
  | d, .Record fields =>
    let fieldsStr := fields.map (fun (n, e) => s!"{n}: {prettyExprAux (d + 2) e}")
    let inner := String.join ",\n" fieldsStr
    s!"{{\n{indent (d + 2)}{inner}\n{indent d}}}"
  | d, .App f arg =>
    let fStr := prettyExprAux d f
    let argStr := prettyExprAux d arg
    s!"{fStr} ({argStr})"
  | d, .Lam arg t body =>
    let typeStr := match t with
      | .some t' => s!" : {prettyTypeAux 0 t'}"
      | .none => ""
    s!"\\{arg}{typeStr} -> {prettyExprAux (d + 2) body}"
  | d, .Let name t value body =>
    let typeStr := match t with
      | .some t' => s!" : {prettyTypeAux 0 t'}"
      | .none => ""
    s!"let {name}{typeStr} = {prettyExprAux (d + 2) value}\n{indent d}in {prettyExprAux (d + 2) body}"
  | d, .If cond then_ else_ =>
    let condStr := prettyExprAux d cond
    let thenStr := prettyExprAux d then_
    let elseStr := prettyExprAux d else_
    s!"if {condStr} then\n{indent (d + 2)}{thenStr}\n{indent d}else\n{indent (d + 2)}{elseStr}"
  | d, .Case scrutinee alts =>
    let altsStr := alts.map (fun (pat, body) =>
      s!"{prettyExprAux d pat} -> {prettyExprAux (d + 2) body}"
    )
    let inner := String.join ("\n" ++ indent (d + 2)) altsStr
    s!"case {prettyExprAux d scrutinee} of\n{indent (d + 2)}{inner}"
  | d, .Op op lhs rhs =>
    let lhsStr := prettyExprAux d lhs
    let rhsStr := prettyExprAux d rhs
    s!"({lhsStr} {op} {rhsStr})"
  | _, .Accessor obj field =>
    s!"{obj}.{field}"

abbrev prettyExpr := prettyExprAux 0

partial def prettyDeclAux : Nat → PSDecl → String
  | _, .Import names =>
    let namesStr := names.map (fun n => s!"\"{n}\"")
    let inner := String.join ", " namesStr
    s!"import {inner}"
  | d, .Module name decls =>
    let declsStr := decls.map (fun decl => prettyDeclAux (d + 2) decl)
    let inner := String.join "\n\n" declsStr
    s!"module {name} where\n\n{inner}"
  | _, .Data name constructors =>
    let consStr := constructors.map (fun (n, args) =>
      match args with
      | [] => n
      | as =>
        let argsStr := as.map (fun t => prettyTypeAux 0 t)
        s!"{n} {String.join " " argsStr}"
    )
    let inner := String.join ("\n  | ") consStr
    s!"data {name} =\n  {inner}"
  | _, .TypeSynonym name params body =>
    let paramsStr := match params with
      | [] => ""
      | ps => s!" ({String.join " " ps})"
    s!"type {name}{paramsStr} = {prettyTypeAux 0 body}"
  | d, .Value name t body =>
    let typeStr := match t with
      | .some t' => s!" : {prettyTypeAux 0 t'}"
      | .none => ""
    let bodyStr := prettyExprAux (d + 2) body
    s!"{name}{typeStr} =\n{indent (d + 2)}{bodyStr}"

abbrev prettyDecl := prettyDeclAux 0

-- ===== PROOFS =====

theorem var_preserves_id (x : String) :
  PSExpr.Var x = PSExpr.Var x := by
  rfl

theorem app_reflexive (e : PSExpr) :
  e = e := by
  rfl

theorem lam_preserves_structure (name : String) (t : Maybe PSType) (body : PSExpr) :
  PSExpr.Lam name t body = PSExpr.Lam name t body := by
  rfl

theorem pretty_preserves_var (name : String) :
  prettyExpr (PSExpr.Var name) = name := by
  rfl

-- Pretty printing is a homomorphism for simple cases
theorem pretty_homomorphism_int (n : Int) :
  prettyExpr (PSExpr.Int n) = toString n := by
  rfl

-- ===== EXAMPLES =====

-- Simple identity function
def identityFun : PSExpr :=
  PSExpr.Lam "x" .none (PSExpr.Var "x")

def identityDecl : PSDecl :=
  PSDecl.Value "identity" .none identityFun

#eval prettyDecl identityDecl

-- Function composition
def composeFun : PSExpr :=
  PSExpr.Lam "f" .none (
    PSExpr.Lam "g" .none (
      PSExpr.Lam "x" .none (
        PSExpr.App (PSExpr.Var "f") (
          PSExpr.App (PSExpr.Var "g") (PSExpr.Var "x")
        )
      )
    )
  )

def composeDecl : PSDecl :=
  PSDecl.Value "compose" .none composeFun

#eval prettyDecl composeDecl

-- Church encodings
def churchTrue : PSExpr :=
  PSExpr.Lam "t" .none (
    PSExpr.Lam "f" .none (PSExpr.Var "t")
  )

def churchFalse : PSExpr :=
  PSExpr.Lam "f" .none (
    PSExpr.Lam "t" .none (PSExpr.Var "t")
  )

def churchAnd : PSExpr :=
  PSExpr.Lam "p" .none (
    PSExpr.Lam "q" .none (
      PSExpr.App (PSExpr.Var "p") (
        PSExpr.App (PSExpr.Var "q") churchFalse
      )
    )
  )

def churchDecls : List PSDecl :=
  [ PSDecl.Value "true" .none churchTrue
  , PSDecl.Value "false" .none churchFalse
  , PSDecl.Value "and" .none churchAnd
  ]

#eval prettyDecl (PSDecl.Module "Church" churchDecls)

-- S, K, I combinators
def sCombinator : PSExpr :=
  PSExpr.Lam "f" .none (
    PSExpr.Lam "g" .none (
      PSExpr.Lam "x" .none (
        PSExpr.App (PSExpr.Var "f") (
          PSExpr.App (PSExpr.Var "g") (PSExpr.Var "x")
        )
      )
    )
  )

def kCombinator : PSExpr :=
  PSExpr.Lam "x" .none (
    PSExpr.Lam "y" .none (PSExpr.Var "x")
  )

def iCombinator : PSExpr :=
  PSExpr.Lam "x" .none (PSExpr.Var "x")

def combinatorsModule : List PSDecl :=
  [ PSDecl.Value "S" .none sCombinator
  , PSDecl.Value "K" .none kCombinator
  , PSDecl.Value "I" .none iCombinator
  ]

#eval prettyDecl (PSDecl.Module "Combinators" combinatorsModule)

-- Complete example with types
def listType : PSType :=
  PSType.TArray PSType.TInt

def mapDecl : PSDecl :=
  PSDecl.Value "map" (.some (
    PSType.TFunction (
      PSType.TFunction PSType.TInt PSType.TInt
    ) (PSType.TArray PSType.TInt)
  )) (
    PSExpr.Lam "f" .none (
      PSExpr.Lam "xs" .none (PSExpr.Var "xs")
    )
  )

def completeModule : List PSDecl :=
  [ PSDecl.Import ["Prelude", "Data.Array", "Data.Maybe"]
  , PSDecl.TypeSynonym "UserId" [] PSType.TInt
  , PSDecl.TypeSynonym "UserName" [] PSType.TString
  , mapDecl
  , identityDecl
  , composeDecl
  ]

#eval prettyDecl (PSDecl.Module "MyModule" completeModule)

-- Records
def personType : PSType :=
  PSType.TRecord [
    ("name", PSType.TString),
    ("age", PSType.TInt),
    ("active", PSType.TBoolean)
  ]

def personValue : PSExpr :=
  PSExpr.Record [
    ("name", PSExpr.String "Alice"),
    ("age", PSExpr.Int 30),
    ("active", PSExpr.Boolean true)
  ]

#eval prettyType personType
#eval prettyExpr personValue

-- Array operations
def arrayExample : PSExpr :=
  PSExpr.Array [
    PSExpr.Int 1,
    PSExpr.Int 2,
    PSExpr.Int 3
  ]

#eval prettyExpr arrayExample

-- If expression
def conditional : PSExpr :=
  PSExpr.If (PSExpr.Boolean true) (PSExpr.Int 1) (PSExpr.Int 0)

#eval prettyExpr conditional

-- Let binding
def letExample : PSExpr :=
  PSExpr.Let "x" .some PSType.TInt (PSExpr.Int 5) (
    PSExpr.Op "+" (PSExpr.Var "x") (PSExpr.Int 10)
  )

#eval prettyExpr letExample

-- Demonstrate proofs work
def proofExample : IO Unit := do
  IO.println "\n=== Proofs with rfl ==="
  IO.println s!"var_preserves_id \"x\": {id_preserves_type \"x\"}"
  IO.println s!"app_reflexive: {app_reflexive (PSExpr.Var \"x\")}"
  IO.println s!"pretty_homomorphism_int 42: {pretty_homomorphism_int 42}"

#eval proofExample
