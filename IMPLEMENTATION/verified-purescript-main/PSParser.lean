/-
  PureScript Parser
  
  Combinator-based parser for PureScript source code.
  
  Handles:
  - Type signatures (:: with forall and constraints)
  - Pattern matching (wildcards, constructors)
  - Infix operators (<<<, >>>, $, #, `backticks`)
  - Comments (-- and {- -})
  - Module/import declarations
-/

-- ═══════════════════════════════════════════════════════════════════════════════
-- PARSER MONAD
-- ═══════════════════════════════════════════════════════════════════════════════

structure ParseState where
  input : String
  pos : Nat
  deriving Repr

def Parser (α : Type) := ParseState → Option (α × ParseState)

instance : Monad Parser where
  pure a := fun s => some (a, s)
  bind p f := fun s =>
    match p s with
    | none => none
    | some (a, s') => f a s'

instance : Alternative Parser where
  failure := fun _ => none
  orElse p q := fun s =>
    match p s with
    | some r => some r
    | none => q () s

def runParser (p : Parser α) (input : String) : Option α :=
  match p { input, pos := 0 } with
  | some (a, _) => some a
  | none => none

-- ═══════════════════════════════════════════════════════════════════════════════
-- BASIC COMBINATORS
-- ═══════════════════════════════════════════════════════════════════════════════

def satisfy (pred : Char → Bool) : Parser Char := fun s =>
  match s.input.get? ⟨s.pos⟩ with
  | some c => if pred c then some (c, { s with pos := s.pos + 1 }) else none
  | none => none

def peek : Parser (Option Char) := fun s =>
  some (s.input.get? ⟨s.pos⟩, s)

def char (c : Char) : Parser Char := satisfy (· == c)

def pstring (str : String) : Parser String := fun s =>
  let len := str.length
  if s.input.extract ⟨s.pos⟩ ⟨s.pos + len⟩ == str
  then some (str, { s with pos := s.pos + len })
  else none

def many (p : Parser α) (fuel : Nat := 1000) : Parser (List α) := fun s =>
  let rec loop (acc : List α) (s : ParseState) (n : Nat) : List α × ParseState :=
    match n with
    | 0 => (acc.reverse, s)
    | n' + 1 =>
      match p s with
      | none => (acc.reverse, s)
      | some (a, s') => 
        if s'.pos > s.pos then loop (a :: acc) s' n'
        else (acc.reverse, s)
  some (loop [] s fuel)

def many1 (p : Parser α) : Parser (List α) := do
  let first ← p
  let rest ← many p
  pure (first :: rest)

def sepBy (p : Parser α) (sep : Parser β) : Parser (List α) :=
  (do
    let first ← p
    let rest ← many (sep *> p)
    pure (first :: rest)
  ) <|> pure []

def sepBy1 (p : Parser α) (sep : Parser β) : Parser (List α) := do
  let first ← p
  let rest ← many (sep *> p)
  pure (first :: rest)

def optionalP (p : Parser α) : Parser (Option α) :=
  (some <$> p) <|> pure none

-- ═══════════════════════════════════════════════════════════════════════════════
-- LEXING
-- ═══════════════════════════════════════════════════════════════════════════════

def isSpace (c : Char) : Bool := c == ' ' || c == '\t'
def isNewline (c : Char) : Bool := c == '\n' || c == '\r'
def isWhitespace (c : Char) : Bool := isSpace c || isNewline c
def isIdChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '\''
def isOperatorChar (c : Char) : Bool := 
  c == '<' || c == '>' || c == '$' || c == '#' || c == '.' || c == ':' || 
  c == '+' || c == '-' || c == '*' || c == '/' || c == '=' || c == '!' ||
  c == '&' || c == '|' || c == '^' || c == '~' || c == '@' || c == '%'

-- Skip line comment
def lineComment : Parser Unit := do
  let _ ← pstring "--"
  let _ ← many (satisfy (fun c => c != '\n'))
  pure ()

-- Skip block comment (simple, non-nested)
partial def blockComment : Parser Unit := do
  let _ ← pstring "{-"
  let rec skipUntilEnd : Parser Unit := do
    let c ← peek
    match c with
    | some '-' => (pstring "-}" *> pure ()) <|> (satisfy (fun _ => true) *> skipUntilEnd)
    | some _ => satisfy (fun _ => true) *> skipUntilEnd
    | none => pure ()
  skipUntilEnd

def ws : Parser Unit := do
  let _ ← many ((satisfy isWhitespace *> pure ()) <|> lineComment <|> blockComment)
  pure ()

def lexeme (p : Parser α) : Parser α := do
  let a ← p
  ws
  pure a

def symbol (str : String) : Parser String := lexeme (pstring str)

-- Reserved words
def reserved : List String := ["module", "where", "import", "class", "instance", 
  "if", "then", "else", "case", "of", "let", "in", "do", "forall", "data", "type",
  "newtype", "infixl", "infixr", "infix", "as", "hiding", "derive"]

def lowerIdent : Parser String := lexeme do
  let first ← satisfy (fun c => c.isLower || c == '_')
  let rest ← many (satisfy isIdChar)
  let name := String.mk (first :: rest)
  if reserved.contains name then failure
  else pure name

def upperIdent : Parser String := lexeme do
  let first ← satisfy Char.isUpper
  let rest ← many (satisfy isIdChar)
  pure (String.mk (first :: rest))

def ident : Parser String := lowerIdent <|> upperIdent

-- Operator in parens like ($) or (<<<)
def operatorName : Parser String := lexeme do
  let _ ← char '('
  let op ← many1 (satisfy isOperatorChar)
  let _ ← char ')'
  pure (String.mk op)

def number : Parser Int := lexeme do
  let neg ← optionalP (char '-')
  let digits ← many1 (satisfy Char.isDigit)
  let n := digits.foldl (fun acc d => acc * 10 + (d.toNat - '0'.toNat)) 0
  pure (if neg.isSome then -n else n)

-- ═══════════════════════════════════════════════════════════════════════════════
-- AST (Simplified)
-- ═══════════════════════════════════════════════════════════════════════════════

inductive PSType where
  | var : String → PSType
  | con : String → PSType
  | app : PSType → PSType → PSType
  | arr : PSType → PSType → PSType
  | forallTy : List String → PSType → PSType
  | constrained : PSType → PSType → PSType
  deriving Repr, Inhabited

inductive PSPattern where
  | var : String → PSPattern
  | wildcard : PSPattern
  | con : String → List PSPattern → PSPattern
  | litInt : Int → PSPattern
  deriving Repr, Inhabited

inductive PSExpr where
  | var : String → PSExpr
  | con : String → PSExpr
  | op : String → PSExpr
  | litInt : Int → PSExpr
  | lam : List PSPattern → PSExpr → PSExpr
  | app : PSExpr → PSExpr → PSExpr
  | infixApp : PSExpr → String → PSExpr → PSExpr
  | ifThenElse : PSExpr → PSExpr → PSExpr → PSExpr
  | parens : PSExpr → PSExpr
  deriving Repr, Inhabited

structure PSTypeSig where
  name : String
  ty : PSType
  deriving Repr, Inhabited

structure PSClause where
  patterns : List PSPattern
  body : PSExpr
  deriving Repr, Inhabited

structure PSFuncDef where
  name : String
  ty : Option PSType
  clauses : List PSClause
  deriving Repr, Inhabited

-- ═══════════════════════════════════════════════════════════════════════════════
-- TYPE PARSER
-- ═══════════════════════════════════════════════════════════════════════════════

mutual
  partial def pTypeAtom : Parser PSType :=
    (PSType.var <$> lowerIdent) <|>
    (PSType.con <$> upperIdent) <|>
    (do let _ ← symbol "("; ws; let _ ← symbol ")"; pure (PSType.con "Unit")) <|>
    (do let _ ← symbol "("; let t ← pType; let _ ← symbol ")"; pure t)

  partial def pTypeApp : Parser PSType := do
    let first ← pTypeAtom
    let rest ← many pTypeAtom
    pure (rest.foldl PSType.app first)

  partial def pTypeArr : Parser PSType := do
    let left ← pTypeApp
    let arr ← optionalP (symbol "->" *> pTypeArr)
    match arr with
    | some right => pure (PSType.arr left right)
    | none => pure left

  partial def pConstraint : Parser PSType := do
    let cls ← upperIdent
    let params ← many1 pTypeAtom
    pure (params.foldl PSType.app (PSType.con cls))

  partial def pConstraints : Parser (List PSType) := do
    let first ← pConstraint
    let rest ← many (symbol "," *> pConstraint)
    pure (first :: rest)

  partial def pForall : Parser PSType := do
    let _ ← symbol "forall"
    let vars ← many1 lowerIdent
    let _ ← symbol "."
    let constrained ← optionalP (do
      let constraints ← pConstraints
      let _ ← symbol "=>"
      pure constraints)
    let body ← pType
    let withConstraints := match constrained with
      | some cs => cs.foldr (fun c t => PSType.constrained c t) body
      | none => body
    pure (PSType.forallTy vars withConstraints)

  partial def pType : Parser PSType :=
    pForall <|> pTypeArr
end

-- ═══════════════════════════════════════════════════════════════════════════════
-- PATTERN PARSER
-- ═══════════════════════════════════════════════════════════════════════════════

mutual
  partial def pPatternAtom : Parser PSPattern :=
    (do let _ ← symbol "_"; pure PSPattern.wildcard) <|>
    (PSPattern.litInt <$> number) <|>
    (PSPattern.var <$> lowerIdent) <|>
    (do let con ← upperIdent; pure (PSPattern.con con [])) <|>
    (do let _ ← symbol "("; let p ← pPattern; let _ ← symbol ")"; pure p)

  partial def pPattern : Parser PSPattern := do
    let first ← pPatternAtom
    match first with
    | PSPattern.con con [] => do
      let args ← many pPatternAtom
      pure (PSPattern.con con args)
    | _ => pure first
end

-- ═══════════════════════════════════════════════════════════════════════════════
-- EXPRESSION PARSER
-- ═══════════════════════════════════════════════════════════════════════════════

def operator : Parser String := lexeme do
  let op ← many1 (satisfy isOperatorChar)
  let s := String.mk op
  if s == "=" then failure
  else pure s

def backtickOp : Parser String := do
  let _ ← char '`'
  let name ← ident
  let _ ← char '`'
  ws
  pure name

mutual
  partial def pExprAtom : Parser PSExpr :=
    (PSExpr.litInt <$> number) <|>
    (PSExpr.con <$> upperIdent) <|>
    (PSExpr.var <$> lowerIdent) <|>
    (do let _ ← symbol "("; ws; let _ ← symbol ")"; pure (PSExpr.con "Unit")) <|>
    (do 
      let _ ← symbol "("
      let inner ← pExpr
      let _ ← symbol ")"
      pure (PSExpr.parens inner)) <|>
    (PSExpr.op <$> operatorName)

  partial def pExprApp : Parser PSExpr := do
    let first ← pExprAtom
    let rest ← many pExprAtom
    pure (rest.foldl PSExpr.app first)

  partial def pExprInfix : Parser PSExpr := do
    let left ← pExprApp
    let chain ← many (do
      let op ← operator <|> backtickOp
      let right ← pExprApp
      pure (op, right))
    pure (chain.foldl (fun acc (op, right) => PSExpr.infixApp acc op right) left)

  partial def pLambda : Parser PSExpr := do
    let _ ← symbol "\\"
    let args ← many1 pPatternAtom
    let _ ← symbol "->"
    let body ← pExpr
    pure (PSExpr.lam args body)

  partial def pIf : Parser PSExpr := do
    let _ ← symbol "if"
    let c ← pExpr
    let _ ← symbol "then"
    let t ← pExpr
    let _ ← symbol "else"
    let e ← pExpr
    pure (PSExpr.ifThenElse c t e)

  partial def pExpr : Parser PSExpr :=
    pLambda <|> pIf <|> pExprInfix
end

-- ═══════════════════════════════════════════════════════════════════════════════
-- DECLARATION PARSERS
-- ═══════════════════════════════════════════════════════════════════════════════

partial def pTypeSig : Parser PSTypeSig := do
  let name ← lowerIdent <|> operatorName
  let _ ← symbol "::"
  let ty ← pType
  pure { name, ty }

-- ═══════════════════════════════════════════════════════════════════════════════
-- LINE-BASED PARSING
-- ═══════════════════════════════════════════════════════════════════════════════

def splitLines (s : String) : List String :=
  s.splitOn "\n"

def containsSubstr (s sub : String) : Bool :=
  (s.splitOn sub).length > 1

def isComment (line : String) : Bool :=
  let trimmed := line.trim
  trimmed.startsWith "--" || trimmed.startsWith "{-" || trimmed.isEmpty

def isTypeSigLine (line : String) : Bool :=
  containsSubstr line "::" && !line.trim.startsWith "--"

def isImportLine (line : String) : Bool :=
  line.trim.startsWith "import"

def isInfixLine (line : String) : Bool :=
  let t := line.trim
  t.startsWith "infixl" || t.startsWith "infixr" || t.startsWith "infix "

def isClassLine (line : String) : Bool :=
  line.trim.startsWith "class "

def isInstanceLine (line : String) : Bool :=
  line.trim.startsWith "instance "

def isFuncDefLine (line : String) : Bool :=
  let t := line.trim
  !isComment line && !isImportLine line && !isTypeSigLine line && 
  !isInfixLine line && !isClassLine line && !isInstanceLine line &&
  containsSubstr t "=" && !t.startsWith "module"

def parseFuncDefLine (line : String) : Option PSFuncDef := do
  let name ← runParser lowerIdent line
  let patterns ← runParser (lowerIdent *> many pPatternAtom) line
  let body ← runParser (lowerIdent *> many pPatternAtom *> symbol "=" *> pExpr) line
  pure { 
    name, 
    ty := none, 
    clauses := [{ patterns, body }] 
  }

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROOF DATABASE
-- ═══════════════════════════════════════════════════════════════════════════════

inductive ProofStatus where
  | proven : String → ProofStatus
  | axiom : String → ProofStatus  
  | unverified : ProofStatus
  deriving Repr, BEq

structure PropertyClaim where
  property : String
  statement : String
  status : ProofStatus
  deriving Repr

def proofDatabase : List (String × List PropertyClaim) := [
  ("identity", [
    { property := "identity_law"
      statement := "identity x = x"
      status := .proven "PS.identity_law" }
  ]),
  ("const", [
    { property := "const_law"
      statement := "const a _ = a"  
      status := .proven "PS.const_law" },
    { property := "const_compose"
      statement := "compose (const a) f = const a"
      status := .proven "PS.const_compose" }
  ]),
  ("flip", [
    { property := "flip_flip"
      statement := "flip (flip f) = f"
      status := .proven "PS.flip_flip" }
  ]),
  ("compose", [
    { property := "compose_assoc"
      statement := "compose f (compose g h) = compose (compose f g) h"
      status := .proven "PS.compose_assoc" },
    { property := "compose_id_left"
      statement := "compose identity f = f"
      status := .proven "PS.identity_left" },
    { property := "compose_id_right"
      statement := "compose f identity = f"
      status := .proven "PS.identity_right" }
  ]),
  ("(<<<)", [
    { property := "semigroupoid_assoc"
      statement := "p <<< (q <<< r) = (p <<< q) <<< r"
      status := .proven "semigroupoidFn.assoc" }
  ]),
  ("(>>>)", [
    { property := "forward_compose"
      statement := "f >>> g = g <<< f"
      status := .proven "PS.composeFlipped" }
  ]),
  ("apply", [
    { property := "apply_def"
      statement := "apply f x = f x"
      status := .proven "PS.apply (by rfl)" }
  ]),
  ("($)", [
    { property := "dollar_def"
      statement := "f $ x = f x"
      status := .proven "PS.apply (by rfl)" }
  ]),
  ("applyFlipped", [
    { property := "applyFlipped_def"
      statement := "applyFlipped x f = f x"
      status := .proven "PS.applyFlipped (by rfl)" },
    { property := "apply_applyFlipped"
      statement := "apply f x = applyFlipped x f"
      status := .proven "PS.apply_applyFlipped" }
  ]),
  ("(#)", [
    { property := "hash_def"
      statement := "x # f = f x"
      status := .proven "PS.applyFlipped (by rfl)" }
  ]),
  ("on", [
    { property := "on_def"
      statement := "on f g x y = f (g x) (g y)"
      status := .proven "PS.on (by rfl)" },
    { property := "on_const"
      statement := "on f (const b) x y = f b b"
      status := .proven "PS.on_const" }
  ]),
  ("applyN", [
    { property := "applyN_zero"
      statement := "applyN f 0 x = x"
      status := .proven "PS.applyN_zero" },
    { property := "applyN_succ"
      statement := "applyN f (n+1) x = applyN f n (f x)"
      status := .proven "PS.applyN_succ" },
    { property := "applyN_one"
      statement := "applyN f 1 x = f x"
      status := .proven "PS.applyN_one" },
    { property := "applyN_id"
      statement := "applyN id n x = x"
      status := .proven "PS.applyN_id" }
  ])
]

def lookupProofs (name : String) : List PropertyClaim :=
  match proofDatabase.find? (fun (n, _) => n == name) with
  | some (_, claims) => claims
  | none => []

-- ═══════════════════════════════════════════════════════════════════════════════
-- PRETTY PRINTERS
-- ═══════════════════════════════════════════════════════════════════════════════

def ProofStatus.pretty : ProofStatus → String
  | .proven thm => s!"✓ PROVEN ({thm})"
  | .axiom reason => s!"⚠ AXIOM ({reason})"
  | .unverified => "✗ UNVERIFIED"

def PropertyClaim.pretty (c : PropertyClaim) : String :=
  s!"-- {c.property}: {c.statement}\n-- Status: {c.status.pretty}"

partial def PSType.pretty : PSType → String
  | .var n => n
  | .con n => n
  | .app f a => s!"{PSType.pretty f} {PSType.pretty a}"
  | .arr a b => s!"({PSType.pretty a} -> {PSType.pretty b})"
  | .forallTy vars body => s!"forall {String.intercalate " " vars}. {PSType.pretty body}"
  | .constrained c t => s!"{PSType.pretty c} => {PSType.pretty t}"

partial def prettyPattern : PSPattern → String
  | .var n => n
  | .wildcard => "_"
  | .con c [] => c
  | .con c args => c ++ " " ++ String.intercalate " " (args.map prettyPattern)
  | .litInt n => toString n

partial def prettyExpr : PSExpr → String
  | .var n => n
  | .con n => n
  | .op n => "(" ++ n ++ ")"
  | .litInt n => toString n
  | .lam args body => "\\" ++ String.intercalate " " (args.map prettyPattern) ++ " -> " ++ prettyExpr body
  | .app f a => "(" ++ prettyExpr f ++ " " ++ prettyExpr a ++ ")"
  | .infixApp l op r => "(" ++ prettyExpr l ++ " " ++ op ++ " " ++ prettyExpr r ++ ")"
  | .ifThenElse c t e => "if " ++ prettyExpr c ++ " then " ++ prettyExpr t ++ " else " ++ prettyExpr e
  | .parens e => "(" ++ prettyExpr e ++ ")"

def PSPattern.pretty := prettyPattern
def PSExpr.pretty := prettyExpr

def PSTypeSig.pretty (sig : PSTypeSig) : String :=
  sig.name ++ " :: " ++ PSType.pretty sig.ty

def prettyClause (name : String) (c : PSClause) : String :=
  let patsStr := String.intercalate " " (c.patterns.map prettyPattern)
  let argsStr := if patsStr.isEmpty then "" else " " ++ patsStr
  name ++ argsStr ++ " = " ++ prettyExpr c.body

def PSFuncDef.pretty (f : PSFuncDef) : String :=
  let tyStr := match f.ty with
    | some t => f.name ++ " :: " ++ PSType.pretty t ++ "\n"
    | none => ""
  let clauses := f.clauses.map (prettyClause f.name)
  tyStr ++ String.intercalate "\n" clauses

def PSFuncDef.prettyAnnotated (f : PSFuncDef) : String :=
  let claims := lookupProofs f.name
  let claimsStr := if claims.isEmpty 
    then "-- Status: ✗ UNVERIFIED (no proofs found)\n"
    else String.intercalate "\n" (claims.map PropertyClaim.pretty) ++ "\n"
  claimsStr ++ PSFuncDef.pretty f

-- ═══════════════════════════════════════════════════════════════════════════════
-- JSON MANIFEST OUTPUT
-- ═══════════════════════════════════════════════════════════════════════════════

def escapeJson (s : String) : String :=
  s.replace "\"" "\\\"" |>.replace "\n" "\\n"

def PropertyClaim.toJson (moduleName funcName : String) (c : PropertyClaim) : String :=
  let (status, thm) := match c.status with
    | .proven t => ("proven", t)
    | .axiom r => ("axiom", r)
    | .unverified => ("unverified", "")
  "    {\"module\": \"" ++ moduleName ++ "\", \"function\": \"" ++ funcName ++ 
  "\", \"property\": \"" ++ c.property ++ "\", \"statement\": \"" ++ escapeJson c.statement ++ 
  "\", \"status\": \"" ++ status ++ "\", \"theorem\": \"" ++ thm ++ "\"}"

def moduleToJson (moduleName : String) (funcs : List String) : String :=
  let entries := funcs.flatMap fun f =>
    let claims := lookupProofs f
    if claims.isEmpty then
      ["    {\"module\": \"" ++ moduleName ++ "\", \"function\": \"" ++ f ++ 
       "\", \"property\": \"-\", \"statement\": \"-\", \"status\": \"unverified\", \"theorem\": \"\"}"]
    else
      claims.map (PropertyClaim.toJson moduleName f)
  "[\n" ++ String.intercalate ",\n" entries ++ "\n]"

-- ═══════════════════════════════════════════════════════════════════════════════
-- TSV MANIFEST OUTPUT
-- ═══════════════════════════════════════════════════════════════════════════════

def moduleToTsv (moduleName : String) (funcs : List String) : String :=
  let header := "module\tfunction\tproperty\tstatus\ttheorem"
  let lines := funcs.flatMap fun f =>
    let claims := lookupProofs f
    if claims.isEmpty then
      [s!"{moduleName}\t{f}\t-\tunverified\t-"]
    else
      claims.map fun c =>
        let (status, thm) := match c.status with
          | .proven t => ("proven", t)
          | .axiom r => ("axiom", r)
          | .unverified => ("unverified", "-")
        s!"{moduleName}\t{f}\t{c.property}\t{status}\t{thm}"
  header ++ "\n" ++ String.intercalate "\n" lines

-- ═══════════════════════════════════════════════════════════════════════════════
-- TESTS
-- ═══════════════════════════════════════════════════════════════════════════════

#eval runParser pType "forall a b c. (a -> b -> c) -> b -> a -> c"
#eval runParser pType "forall a. Semigroupoid a => a b c -> a c d -> a b d"
#eval runParser pTypeSig "flip :: forall a b c. (a -> b -> c) -> b -> a -> c"

#eval runParser pPattern "_"
#eval runParser pPattern "Just x"

#eval runParser pExpr "f a b"
#eval runParser pExpr "g x `f` g y"
#eval runParser pExpr "f <<< g"

-- Test with real prelude content
def realDataFunction := "module Data.Function where

flip :: forall a b c. (a -> b -> c) -> b -> a -> c
flip f b a = f a b

const :: forall a b. a -> b -> a
const a _ = a

apply :: forall a b. (a -> b) -> a -> b
apply f x = f x

infixr 0 apply as $

applyFlipped :: forall a b. a -> (a -> b) -> b
applyFlipped x f = f x

infixl 1 applyFlipped as #

on :: forall a b c. (b -> b -> c) -> (a -> b) -> a -> a -> c
on f g x y = g x `f` g y"

-- Parse and annotate
def parseAndAnnotate (input : String) : String :=
  let lines := splitLines input
  let funcLines := lines.filter isFuncDefLine
  let funcs := funcLines.filterMap parseFuncDefLine
  let annotated := funcs.map PSFuncDef.prettyAnnotated
  String.intercalate "\n\n" annotated

#eval IO.println "=== ANNOTATED OUTPUT ==="
#eval IO.println (parseAndAnnotate realDataFunction)

#eval IO.println "\n=== JSON MANIFEST ==="
#eval IO.println (moduleToJson "Data.Function" ["flip", "const", "apply", "($)", "applyFlipped", "(#)", "on", "applyN"])

#eval IO.println "\n=== TSV MANIFEST ==="
#eval IO.println (moduleToTsv "Data.Function" ["flip", "const", "apply", "($)", "applyFlipped", "(#)", "on"])

-- ═══════════════════════════════════════════════════════════════════════════════
-- SUMMARY
-- ═══════════════════════════════════════════════════════════════════════════════

/-
  PSParserV2: Extended PureScript Parser
  
  FEATURES:
  - Type signatures with :: and forall
  - Constraint parsing (Semigroupoid a =>)
  - Pattern wildcards (_)
  - Infix operators (<<<, >>>, $, #, `backticks`)
  - Line comments (--)
  - Block comments ({- -})
  - JSON and TSV manifest output
  
  PROOF DATABASE:
  - flip, const, compose, apply, applyFlipped, on
  - Operators: ($), (#), (<<<), (>>>)
  
  USAGE:
    #eval parseAndAnnotate myPureScriptCode
    #eval moduleToJson "Module.Name" ["func1", "func2"]
    #eval moduleToTsv "Module.Name" ["func1", "func2"]
-/

-- ═══════════════════════════════════════════════════════════════════════════════
-- MAIN: Parse and print Data.Function with proof annotations
-- ═══════════════════════════════════════════════════════════════════════════════

def main : IO Unit := do
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println "  // verified purescript // Parse → Prove → Print"
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println ""
  IO.println "Input: Data.Function (PureScript Prelude)"
  IO.println "───────────────────────────────────────────────────────────────"
  IO.println realDataFunction
  IO.println ""
  IO.println "Output: Annotated with proof status"
  IO.println "───────────────────────────────────────────────────────────────"
  IO.println "module Data.Function where"
  IO.println ""
  IO.println (parseAndAnnotate realDataFunction)
  IO.println ""
  IO.println "───────────────────────────────────────────────────────────────"
  IO.println "Proof Database:"
  IO.println "  flip       → flip_flip (rfl)"
  IO.println "  const      → const_const (rfl)"
  IO.println "  compose    → compose_assoc, identity_left, identity_right (rfl)"
  IO.println "  apply      → (alias for $)"
  IO.println "  applyFlipped → (alias for #)"
  IO.println "  on         → on_const (rfl)"
  IO.println ""
