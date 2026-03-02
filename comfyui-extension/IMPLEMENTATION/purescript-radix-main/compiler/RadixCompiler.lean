/-
  Radix Pure Compiler
  
  Generates PureScript/Halogen component skeletons from TypeScript .d.ts files.
  
  Usage: 
    nix run . -- <ComponentName>              # use builtin/cached spec
    nix run . -- --parse <file.d.ts>          # parse TypeScript definitions
-/

-- ═══════════════════════════════════════════════════════════════════════════════
-- PARSER COMBINATORS
-- ═══════════════════════════════════════════════════════════════════════════════

structure Pos where
  offset : Nat
  line : Nat
  col : Nat
  deriving Repr, Inhabited

structure ParseState where
  input : String
  pos : Pos
  deriving Repr

def ParseState.current (s : ParseState) : Option Char :=
  String.Pos.Raw.get? s.input ⟨s.pos.offset⟩

def ParseState.advance (s : ParseState) (c : Char) : ParseState :=
  let newLine := c == '\n'
  { s with pos := {
    offset := s.pos.offset + 1
    line := if newLine then s.pos.line + 1 else s.pos.line
    col := if newLine then 1 else s.pos.col + 1
  }}

def ParseState.atEnd (s : ParseState) : Bool :=
  s.pos.offset >= s.input.length

inductive ParseResult (α : Type) where
  | ok : α → ParseState → ParseResult α
  | err : String → Pos → ParseResult α
  deriving Repr

def Parser (α : Type) := ParseState → ParseResult α

instance : Monad Parser where
  pure a := fun s => .ok a s
  bind p f := fun s =>
    match p s with
    | .ok a s' => f a s'
    | .err msg pos => .err msg pos

instance : Alternative Parser where
  failure := fun s => .err "failure" s.pos
  orElse p q := fun s =>
    match p s with
    | .ok a s' => .ok a s'
    | .err _ _ => q () s

def Parser.run (p : Parser α) (input : String) : Except String α :=
  match p { input, pos := { offset := 0, line := 1, col := 1 } } with
  | .ok a _ => .ok a
  | .err msg pos => .error s!"{msg} at line {pos.line}, col {pos.col}"

def fail (msg : String) : Parser α := fun s => .err msg s.pos

def satisfy (pred : Char → Bool) (desc : String) : Parser Char := fun s =>
  match s.current with
  | some c => if pred c then .ok c (s.advance c) else .err s!"expected {desc}, got '{c}'" s.pos
  | none => .err s!"expected {desc}, got EOF" s.pos

def char (c : Char) : Parser Char := satisfy (· == c) s!"'{c}'"

def anyChar : Parser Char := fun s =>
  match s.current with
  | some c => .ok c (s.advance c)
  | none => .err "unexpected EOF" s.pos

def peek : Parser (Option Char) := fun s => .ok s.current s

def eof : Parser Unit := fun s =>
  if s.atEnd then .ok () s else .err "expected EOF" s.pos

def option (p : Parser α) : Parser (Option α) := fun s =>
  match p s with
  | .ok a s' => .ok (some a) s'
  | .err _ _ => .ok none s

def attempt (p : Parser α) : Parser α := fun s =>
  match p s with
  | .ok a s' => .ok a s'
  | .err msg _ => .err msg s.pos  -- Reset position on failure

partial def manyCore (p : Parser α) (acc : List α) : Parser (List α) := fun s =>
  match p s with
  | .ok a s' => manyCore p (acc ++ [a]) s'
  | .err _ _ => .ok acc s

def many (p : Parser α) : Parser (List α) := manyCore p []

def many1 (p : Parser α) : Parser (List α) := do
  let first ← p
  let rest ← many p
  pure (first :: rest)

def sepBy (p : Parser α) (sep : Parser β) : Parser (List α) := 
  (do let first ← p; let rest ← many (sep *> p); pure (first :: rest)) <|> pure []

def sepBy1 (p : Parser α) (sep : Parser β) : Parser (List α) := do
  let first ← p
  let rest ← many (sep *> p)
  pure (first :: rest)

def between (open_ : Parser α) (close : Parser β) (p : Parser γ) : Parser γ :=
  open_ *> p <* close

def notFollowedBy (p : Parser α) : Parser Unit := fun s =>
  match p s with
  | .ok _ _ => .err "unexpected" s.pos
  | .err _ _ => .ok () s

-- String utilities
def containsSubstr (s sub : String) : Bool :=
  (s.splitOn sub).length > 1

def strEndsWith (s suffix : String) : Bool :=
  s.length >= suffix.length && s.drop (s.length - suffix.length) == suffix

-- Character classes
def isSpace (c : Char) : Bool := c == ' ' || c == '\t'
def isNewline (c : Char) : Bool := c == '\n' || c == '\r'
def isWhitespace (c : Char) : Bool := isSpace c || isNewline c
def isDigit (c : Char) : Bool := c >= '0' && c <= '9'
def isAlpha (c : Char) : Bool := (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
def isAlphaNum (c : Char) : Bool := isAlpha c || isDigit c
def isIdentChar (c : Char) : Bool := isAlphaNum c || c == '_' || c == '$'
def isIdentStart (c : Char) : Bool := isAlpha c || c == '_' || c == '$'

def space : Parser Char := satisfy isSpace "space"
def newline : Parser Char := satisfy isNewline "newline"
def whitespace : Parser Char := satisfy isWhitespace "whitespace"
def digit : Parser Char := satisfy isDigit "digit"
def alpha : Parser Char := satisfy isAlpha "letter"
def alphaNum : Parser Char := satisfy isAlphaNum "alphanumeric"

def spaces : Parser Unit := many space *> pure ()
def whitespaces : Parser Unit := many whitespace *> pure ()

def string (str : String) : Parser String := fun st =>
  let chars := str.toList
  let rec go (cs : List Char) (state : ParseState) : ParseResult String :=
    match cs with
    | [] => .ok str state
    | c :: rest => 
      match state.current with
      | some c' =>
        if c == c' then go rest (state.advance c')
        else .err s!"expected \"{str}\"" st.pos
      | none => .err s!"expected \"{str}\", got EOF" st.pos
  go chars st

def identifier : Parser String := do
  let first ← satisfy isIdentStart "identifier"
  let rest ← many (satisfy isIdentChar "identifier char")
  pure (String.ofList (first :: rest))

def stringLiteral : Parser String := do
  let quote ← char '"' <|> char '\''
  let chars ← many (satisfy (· != quote) "string char")
  let _ ← char quote
  pure (String.ofList chars)

-- Skip line comment
def lineComment : Parser Unit := do
  let _ ← string "//"
  let _ ← many (satisfy (· != '\n') "")
  pure ()

-- Skip block comment  
partial def blockComment : Parser Unit := do
  let _ ← string "/*"
  let rec go : Parser Unit := do
    let c ← anyChar
    if c == '*' then do
      let next ← peek
      if next == some '/' then anyChar *> pure ()
      else go
    else go
  go

def comment : Parser Unit := lineComment <|> blockComment

def skipJunk : Parser Unit := many (whitespace <|> (comment *> pure ' ')) *> pure ()

def lexeme (p : Parser α) : Parser α := p <* skipJunk

def symbol (s : String) : Parser String := lexeme (string s)

def keyword (s : String) : Parser String := lexeme do
  let id ← string s
  notFollowedBy (satisfy isIdentChar "")
  pure id

def ident : Parser String := lexeme identifier

def semi : Parser Char := lexeme (char ';')
def comma : Parser Char := lexeme (char ',')
def colon : Parser Char := lexeme (char ':')
def question : Parser Char := lexeme (char '?')

def braces (p : Parser α) : Parser α := between (symbol "{") (symbol "}") p
def parens (p : Parser α) : Parser α := between (symbol "(") (symbol ")") p
def angles (p : Parser α) : Parser α := between (symbol "<") (symbol ">") p
def brackets (p : Parser α) : Parser α := between (symbol "[") (symbol "]") p

-- ═══════════════════════════════════════════════════════════════════════════════
-- TYPESCRIPT AST
-- ═══════════════════════════════════════════════════════════════════════════════

inductive TSType where
  | name : String → TSType
  | generic : String → List TSType → TSType
  | array : TSType → TSType
  | tuple : List TSType → TSType
  | union : List TSType → TSType
  | intersection : List TSType → TSType
  | func : List TSType → TSType → TSType
  | literal : String → TSType
  | typeof : String → TSType
  | keyof : TSType → TSType
  | indexed : TSType → TSType → TSType
  | conditional : TSType → TSType → TSType → TSType
  | infer : String → TSType
  deriving Repr, Inhabited

structure TSProp where
  name : String
  optional : Bool
  type : TSType
  doc : Option String := none
  deriving Repr

structure TSInterface where
  name : String
  typeParams : List String
  extends_ : List TSType
  props : List TSProp
  deriving Repr

structure TSTypeAlias where
  name : String
  typeParams : List String
  type : TSType
  deriving Repr

inductive TSDecl where
  | interface : TSInterface → TSDecl
  | typeAlias : TSTypeAlias → TSDecl
  | declare : String → TSDecl
  | import_ : TSDecl
  | export_ : TSDecl
  | other : TSDecl
  deriving Repr

-- ═══════════════════════════════════════════════════════════════════════════════
-- TYPESCRIPT PARSER
-- ═══════════════════════════════════════════════════════════════════════════════

mutual
  partial def tsType : Parser TSType := do
    let base ← tsUnionType
    -- Check for conditional type
    let ext ← option do
      let _ ← keyword "extends"
      let _cond ← tsType
      let _ ← symbol "?"
      let then_ ← tsType
      let _ ← symbol ":"
      let else_ ← tsType
      pure (then_, else_)
    match ext with
    | some (then_, else_) => pure (.conditional base then_ else_)
    | none => pure base

  partial def tsUnionType : Parser TSType := do
    let _ ← option (symbol "|")  -- Allow leading |
    let types ← sepBy1 tsIntersectionType (symbol "|")
    match types with
    | [t] => pure t
    | ts => pure (.union ts)

  partial def tsIntersectionType : Parser TSType := do
    let types ← sepBy1 tsPrimaryType (symbol "&")
    match types with
    | [t] => pure t
    | ts => pure (.intersection ts)

  partial def tsPrimaryType : Parser TSType := do
    let base ← tsAtomicType
    -- Check for array suffix []
    let hasBrackets ← option (brackets (pure ()))
    match hasBrackets with
    | some _ => pure (TSType.array base)
    | none => pure base

  partial def tsAtomicType : Parser TSType := 
    tsParenType <|> tsFuncType <|> tsTypeofType <|> tsKeyofType <|> 
    tsInferType <|> tsTupleType <|> tsLiteralType <|> tsNamedType

  partial def tsParenType : Parser TSType := parens tsType

  partial def tsFuncType : Parser TSType := do
    let params ← parens (sepBy tsFuncParam comma)
    let _ ← symbol "=>"
    let ret ← tsType
    pure (.func (params.map (·.2)) ret)

  partial def tsFuncParam : Parser (String × TSType) := do
    let name ← ident
    let _ ← option question
    let _ ← colon
    let ty ← tsType
    pure (name, ty)

  partial def tsTypeofType : Parser TSType := do
    let _ ← keyword "typeof"
    let name ← ident
    pure (.typeof name)

  partial def tsKeyofType : Parser TSType := do
    let _ ← keyword "keyof"
    let ty ← tsPrimaryType
    pure (.keyof ty)

  partial def tsInferType : Parser TSType := do
    let _ ← keyword "infer"
    let name ← ident
    pure (.infer name)

  partial def tsTupleType : Parser TSType := do
    let types ← brackets (sepBy tsType comma)
    pure (.tuple types)

  partial def tsLiteralType : Parser TSType := do
    let lit ← stringLiteral <|> (many1 digit >>= fun ds => pure (String.ofList ds))
    pure (.literal lit)

  partial def tsNamedType : Parser TSType := do
    let name ← ident
    -- Check for generic arguments
    let args ← option (angles (sepBy1 tsType comma))
    match args with
    | some ts => pure (.generic name ts)
    | none => pure (.name name)
end

def tsPropDef : Parser TSProp := do
  -- Optional readonly
  let _ ← option (keyword "readonly")
  let name ← ident <|> (brackets tsType >>= fun _ => pure "[index]")  -- Index signatures
  let opt ← option question
  let _ ← colon
  let ty ← tsType
  let _ ← option semi
  pure { name, optional := opt.isSome, type := ty }

def tsTypeParams : Parser (List String) :=
  (angles (sepBy1 ident comma)) <|> pure []

def tsExtends : Parser (List TSType) := do
  let ext ← option do
    let _ ← keyword "extends"
    sepBy1 tsType comma
  pure (ext.getD [])

def tsInterfaceDecl : Parser TSInterface := do
  let _ ← keyword "interface"
  let name ← ident
  let typeParams ← tsTypeParams
  let extends_ ← tsExtends
  let props ← braces (many tsPropDef)
  pure { name, typeParams, extends_, props }

def tsTypeAliasDecl : Parser TSTypeAlias := do
  let _ ← keyword "type"
  let name ← ident
  let typeParams ← tsTypeParams
  let _ ← symbol "="
  let ty ← tsType
  let _ ← option semi
  pure { name, typeParams, type := ty }

def tsDeclareDecl : Parser TSDecl := do
  let _ ← keyword "declare"
  let _ ← keyword "const" <|> keyword "function" <|> keyword "class" <|> keyword "var" <|> keyword "let"
  let name ← ident
  -- Skip rest of declaration
  let _ ← many (satisfy (fun c => c != ';' && c != '\n') "")
  let _ ← option semi
  pure (.declare name)

def tsImportDecl : Parser TSDecl := do
  let _ ← keyword "import"
  let _ ← many (satisfy (· != ';') "")
  let _ ← option semi
  pure .import_

def tsExportDecl : Parser TSDecl := do
  let _ ← keyword "export"
  let decl ← (tsInterfaceDecl >>= fun i => pure (.interface i)) <|>
             (tsTypeAliasDecl >>= fun t => pure (.typeAlias t)) <|>
             (tsDeclareDecl) <|>
             (braces (many ident) *> option semi *> pure .export_) <|>
             pure .export_
  pure decl

def tsDecl : Parser TSDecl :=
  tsExportDecl <|>
  tsImportDecl <|>
  (tsInterfaceDecl >>= fun i => pure (.interface i)) <|>
  (tsTypeAliasDecl >>= fun t => pure (.typeAlias t)) <|>
  tsDeclareDecl <|>
  (anyChar *> pure .other)  -- Skip unknown

def tsModule : Parser (List TSDecl) := do
  skipJunk
  let decls ← many tsDecl
  pure (decls.filter fun d => match d with | .other => false | .import_ => false | _ => true)

-- ═══════════════════════════════════════════════════════════════════════════════
-- COMPONENT SPECIFICATION
-- ═══════════════════════════════════════════════════════════════════════════════

inductive Behavior where
  | modal       -- focus trap, scroll lock, aria-hidden siblings
  | disclosure  -- open/close state machine
  | selection   -- value selection
  | navigation  -- keyboard nav
  deriving Repr, BEq

inductive PropType where
  | bool | string | int | handler | node
  deriving Repr

structure PropDef where
  name : String
  ty : PropType
  optional : Bool := true
  deriving Repr

structure PartDef where
  name : String
  element : String
  props : List PropDef := []
  deriving Repr

structure ComponentSpec where
  name : String
  behaviors : List Behavior
  parts : List PartDef
  doc : String := ""
  deriving Repr

-- Convert TS type to our PropType
def tsTypeToOurs : TSType → PropType
  | .name "boolean" => .bool
  | .name "number" => .int
  | .name "string" => .string
  | .literal "true" => .bool
  | .literal "false" => .bool
  | .generic "React.ReactNode" _ => .node
  | .name n => if strEndsWith n "Handler" || n.startsWith "on" then .handler else .string
  | .func _ _ => .handler
  | .union ts => 
    -- Check if it's a boolean-like union
    if ts.any (fun t => match t with | .literal "true" => true | .literal "false" => true | _ => false)
    then .bool else .string
  | _ => .string

-- Convert TSProp to our PropDef
def tsPropToOurs (p : TSProp) : Option PropDef :=
  -- Skip React internals, handlers (for now), and complex types
  if p.name.startsWith "on" || p.name == "children" || p.name == "ref" || 
     p.name == "key" || p.name == "as" || p.name == "asChild" ||
     p.name.startsWith "[" then none
  else some {
    name := p.name
    ty := tsTypeToOurs p.type
    optional := p.optional
  }

-- Infer element from part name
def inferElement (name : String) : String :=
  if containsSubstr name "Button" || containsSubstr name "Trigger" || containsSubstr name "Close" then "button"
  else if containsSubstr name "Input" then "input"
  else if containsSubstr name "Title" || containsSubstr name "Heading" then "h2"
  else if containsSubstr name "Description" || containsSubstr name "Label" then "p"
  else if containsSubstr name "Image" || containsSubstr name "Img" then "img"
  else "div"

-- Infer behaviors from interface props
def inferBehaviors (componentName : String) (props : List PropDef) : List Behavior :=
  let hasOpen := props.any (·.name == "open")
  let hasModal := props.any (·.name == "modal")
  let hasValue := props.any (·.name == "value")
  let isModal := componentName == "Dialog" || componentName == "AlertDialog" || hasModal
  let behaviors := (if hasOpen then [.disclosure] else []) ++
                   (if hasValue then [.selection, .navigation] else []) ++
                   (if isModal then [.modal] else [])
  if behaviors.isEmpty then [.disclosure] else behaviors

-- Extract component from parsed declarations
def extractComponent (decls : List TSDecl) (componentName : String) : ComponentSpec :=
  -- Find all interfaces for this component
  let interfaces := decls.filterMap fun d => match d with
    | .interface i => if i.name.startsWith componentName then some i else none
    | _ => none
  
  -- Build parts from interfaces
  let parts := interfaces.filterMap fun iface =>
    let partName := iface.name.replace componentName "" |>.replace "Props" "" |>.replace "Impl" ""
    let partName := if partName.isEmpty then "Root" else partName
    let props := iface.props.filterMap tsPropToOurs
    if props.isEmpty && partName != "Root" then none
    else some {
      name := partName
      element := inferElement partName
      props
    }
  
  -- Get root props for behavior inference
  let rootProps := parts.find? (·.name == "Root") |>.map (·.props) |>.getD []
  let behaviors := inferBehaviors componentName rootProps
  
  {
    name := componentName
    behaviors
    parts := if parts.isEmpty then [{name := "Root", element := "div", props := []}] else parts
    doc := s!"{componentName} (parsed from .d.ts)"
  }

-- ═══════════════════════════════════════════════════════════════════════════════
-- BUILTIN COMPONENT SPECS
-- ═══════════════════════════════════════════════════════════════════════════════

def dialogSpec : ComponentSpec := {
  name := "Dialog"
  behaviors := [.modal, .disclosure]
  doc := "Modal dialog with focus trap and scroll lock"
  parts := [
    { name := "Root", element := "div"
      props := [
        { name := "open", ty := .bool },
        { name := "defaultOpen", ty := .bool },
        { name := "modal", ty := .bool },
        { name := "closeOnEscape", ty := .bool },
        { name := "closeOnOutsideClick", ty := .bool }
      ] },
    { name := "Trigger", element := "button" },
    { name := "Overlay", element := "div" },
    { name := "Content", element := "div" },
    { name := "Title", element := "h2" },
    { name := "Description", element := "p" },
    { name := "Close", element := "button" }
  ]
}

def tabsSpec : ComponentSpec := {
  name := "Tabs"
  behaviors := [.selection, .navigation]
  doc := "Accessible tabs with keyboard navigation"
  parts := [
    { name := "Root", element := "div"
      props := [
        { name := "value", ty := .string },
        { name := "defaultValue", ty := .string },
        { name := "orientation", ty := .string },
        { name := "loop", ty := .bool }
      ] },
    { name := "List", element := "div" },
    { name := "Trigger", element := "button", props := [{ name := "value", ty := .string, optional := false }] },
    { name := "Content", element := "div", props := [{ name := "value", ty := .string, optional := false }] }
  ]
}

def popoverSpec : ComponentSpec := {
  name := "Popover"
  behaviors := [.disclosure]
  doc := "Floating content anchored to trigger"
  parts := [
    { name := "Root", element := "div"
      props := [
        { name := "open", ty := .bool },
        { name := "defaultOpen", ty := .bool }
      ] },
    { name := "Trigger", element := "button" },
    { name := "Content", element := "div", props := [
        { name := "side", ty := .string },
        { name := "sideOffset", ty := .int }
      ] },
    { name := "Close", element := "button" }
  ]
}

def allSpecs : List ComponentSpec := [dialogSpec, tabsSpec, popoverSpec]

-- ═══════════════════════════════════════════════════════════════════════════════
-- CODE GENERATION  
-- ═══════════════════════════════════════════════════════════════════════════════

-- PureScript syntax helpers (to avoid string escaping issues)
def lb : String := "{"  -- left brace
def rb : String := "}"  -- right brace
def bslash : String := "\\"  -- backslash

-- ═══════════════════════════════════════════════════════════════════════════════
-- STYLE PRESETS
-- ═══════════════════════════════════════════════════════════════════════════════

inductive StylePreset where
  | semantic   -- dialog-root, dialog-overlay, etc.
  | tailwind   -- raw tailwind utilities
  | shadcn     -- shadcn/ui classes
  | daisy      -- daisyUI classes
  deriving Repr, BEq

structure StyleClasses where
  root : String
  trigger : String
  overlay : String
  portal : String
  content : String
  close : String
  title : String
  description : String

def getStyles (preset : StylePreset) (component : String) : StyleClasses :=
  let c := component.toLower
  match preset with
  | .semantic => {
      root := s!"{c}-root"
      trigger := s!"{c}-trigger"
      overlay := s!"{c}-overlay"
      portal := s!"{c}-portal"
      content := s!"{c}-content"
      close := s!"{c}-close"
      title := s!"{c}-title"
      description := s!"{c}-description"
    }
  | .tailwind => {
      root := "relative"
      trigger := "inline-flex items-center justify-center rounded-md bg-primary px-4 py-2 text-sm font-medium text-white hover:bg-primary/90 focus:outline-none focus-visible:ring-2"
      overlay := "fixed inset-0 z-50 bg-black/80"
      portal := "fixed inset-0 z-50 flex items-center justify-center"
      content := "relative z-50 w-full max-w-lg rounded-lg bg-white p-6 shadow-lg focus:outline-none"
      close := "absolute right-4 top-4 rounded-sm opacity-70 hover:opacity-100 focus:outline-none focus:ring-2"
      title := "text-lg font-semibold"
      description := "text-sm text-gray-500"
    }
  | .shadcn => {
      root := "relative"
      trigger := "inline-flex items-center justify-center whitespace-nowrap rounded-md text-sm font-medium ring-offset-background transition-colors focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring focus-visible:ring-offset-2 disabled:pointer-events-none disabled:opacity-50 bg-primary text-primary-foreground hover:bg-primary/90 h-10 px-4 py-2"
      overlay := "fixed inset-0 z-50 bg-black/80 data-[state=open]:animate-in data-[state=closed]:animate-out data-[state=closed]:fade-out-0 data-[state=open]:fade-in-0"
      portal := "fixed inset-0 z-50 flex items-center justify-center"
      content := "fixed left-[50%] top-[50%] z-50 grid w-full max-w-lg translate-x-[-50%] translate-y-[-50%] gap-4 border bg-background p-6 shadow-lg duration-200 data-[state=open]:animate-in data-[state=closed]:animate-out data-[state=closed]:fade-out-0 data-[state=open]:fade-in-0 data-[state=closed]:zoom-out-95 data-[state=open]:zoom-in-95 data-[state=closed]:slide-out-to-left-1/2 data-[state=closed]:slide-out-to-top-[48%] data-[state=open]:slide-in-from-left-1/2 data-[state=open]:slide-in-from-top-[48%] sm:rounded-lg"
      close := "absolute right-4 top-4 rounded-sm opacity-70 ring-offset-background transition-opacity hover:opacity-100 focus:outline-none focus:ring-2 focus:ring-ring focus:ring-offset-2 disabled:pointer-events-none data-[state=open]:bg-accent data-[state=open]:text-muted-foreground"
      title := "text-lg font-semibold leading-none tracking-tight"
      description := "text-sm text-muted-foreground"
    }
  | .daisy => {
      root := ""
      trigger := "btn btn-primary"
      overlay := "modal-backdrop"
      portal := "modal modal-open"
      content := "modal-box"
      close := "btn btn-sm btn-circle btn-ghost absolute right-2 top-2"
      title := "font-bold text-lg"
      description := "py-4"
    }

def propToPSType : PropType → String
  | .bool => "Boolean"
  | .string => "String"
  | .int => "Int"
  | .handler => "Effect Unit"
  | .node => "Array (HH.HTML w i)"

def propField (p : PropDef) : String :=
  let ty := if p.optional then s!"Maybe {propToPSType p.ty}" else propToPSType p.ty
  s!"{p.name} :: {ty}"

def propDefault (p : PropDef) : String :=
  let v := if p.optional then "Nothing" else match p.ty with
    | .bool => "false" | .string => "\"\"" | .int => "0" | _ => "mempty"
  s!"{p.name}: {v}"

def genInputType (props : List PropDef) : String :=
  match props with
  | [] => "type Input = {}"
  | p :: ps => 
    let first := "  { " ++ propField p
    let rest := ps.map fun p => "  , " ++ propField p
    "type Input =\n" ++ first ++ "\n" ++ String.intercalate "\n" rest ++ "\n  }"

def genDefaultInput (props : List PropDef) : String :=
  match props with
  | [] => "defaultInput :: Input\ndefaultInput = {}"
  | p :: ps =>
    let first := "  { " ++ propDefault p
    let rest := ps.map fun p => "  , " ++ propDefault p
    "defaultInput :: Input\ndefaultInput =\n" ++ first ++ "\n" ++ String.intercalate "\n" rest ++ "\n  }"

def genPurs (spec : ComponentSpec) (preset : StylePreset := .semantic) : String :=
  let rootProps := spec.parts.find? (·.name == "Root") |>.map (·.props) |>.getD []
  let hasModal := spec.behaviors.contains .modal
  let styles := getStyles preset spec.name
  let modalImports := if hasModal then 
    "\nimport Radix.Pure.AriaHider as AH\nimport Radix.Pure.FocusTrap as FT\nimport Radix.Pure.Id as Id" 
    else ""
  
  "-- | " ++ spec.doc ++ "\n" ++
  "-- | Pure PureScript/Halogen. No React.\n" ++
  "module Radix.Pure." ++ spec.name ++ "\n" ++
  "  ( component\n" ++
  "  , Query(..)\n" ++
  "  , Input\n" ++
  "  , Output(..)\n" ++
  "  , Slot\n" ++
  "  , defaultInput\n" ++
  "  ) where\n\n" ++
  "import Prelude\n\n" ++
  "import Data.Foldable (for_)\n" ++
  "import Data.Maybe (Maybe(..), fromMaybe)\n" ++
  "import Effect (Effect)\n" ++
  "import Effect.Aff.Class (class MonadAff)\n" ++
  "import Effect.Class (liftEffect)\n" ++
  "import Halogen as H\n" ++
  "import Halogen.HTML as HH\n" ++
  "import Halogen.HTML.Events as HE\n" ++
  "import Halogen.HTML.Properties as HP\n" ++
  "import Halogen.HTML.Properties.ARIA as ARIA\n" ++
  "import Halogen.Query.Event as HQE\n" ++
  "import Web.Event.Event as Event\n" ++
  "import Web.HTML as HTML\n" ++
  "import Web.HTML.HTMLDocument as HTMLDocument\n" ++
  "import Web.HTML.HTMLElement as HTMLElement\n" ++
  "import Web.HTML.Window as Window\n" ++
  "import Web.UIEvent.KeyboardEvent as KE\n" ++
  "import Web.UIEvent.KeyboardEvent.EventTypes as KET" ++ modalImports ++ "\n\n" ++
  "-- TYPES\n\n" ++
  genInputType rootProps ++ "\n\n" ++
  genDefaultInput rootProps ++ "\n\n" ++
  "data Output\n  = Opened\n  | Closed\n  | OpenChanged Boolean\n\n" ++
  "data Query a\n  = Open a\n  | Close a\n  | Toggle a\n  | IsOpen (Boolean -> a)\n\n" ++
  "type State =\n  " ++ lb ++ " input :: Input\n  , isOpen :: Boolean\n  " ++ rb ++ "\n\n" ++
  "data Action\n  = Initialize\n  | Finalize\n  | Receive Input\n  | HandleTriggerClick\n  | HandleCloseClick\n  | HandleOverlayClick\n  | ContentClicked\n  | HandleKeyDown KE.KeyboardEvent\n\n" ++
  "type Slot id = H.Slot Query Output id\n\n" ++
  "-- COMPONENT\n\n" ++
  "component :: forall m. MonadAff m => H.Component Query Input Output m\n" ++
  "component = H.mkComponent\n" ++
  "  " ++ lb ++ " initialState\n" ++
  "  , render\n" ++
  "  , eval: H.mkEval $ H.defaultEval\n" ++
  "      " ++ lb ++ " handleAction = handleAction\n" ++
  "      , handleQuery = handleQuery\n" ++
  "      , initialize = Just Initialize\n" ++
  "      , finalize = Just Finalize\n" ++
  "      , receive = Just <<< Receive\n" ++
  "      " ++ rb ++ "\n" ++
  "  " ++ rb ++ "\n\n" ++
  "initialState :: Input -> State\n" ++
  "initialState input =\n" ++
  "  " ++ lb ++ " input\n" ++
  "  , isOpen: fromMaybe false input.defaultOpen\n" ++
  "  " ++ rb ++ "\n\n" ++
  "-- RENDER\n\n" ++
  "render :: forall m. State -> H.ComponentHTML Action () m\n" ++
  "render state =\n" ++
  "  HH.div\n" ++
  "    [ HP.class_ (HH.ClassName \"" ++ styles.root ++ "\") ]\n" ++
  "    [ HH.button\n" ++
  "        [ HP.class_ (HH.ClassName \"" ++ styles.trigger ++ "\")\n" ++
  "        , HP.type_ HP.ButtonButton\n" ++
  "        , HE.onClick \\\\_ -> HandleTriggerClick\n" ++
  "        , ARIA.hasPopup \"dialog\"\n" ++
  "        , ARIA.expanded (show state.isOpen)\n" ++
  "        ]\n" ++
  "        [ HH.text \"Open " ++ spec.name ++ "\" ]\n" ++
  "    , if state.isOpen then renderContent state else HH.text \"\"\n" ++
  "    ]\n\n" ++
  "renderContent :: forall m. State -> H.ComponentHTML Action () m\n" ++
  "renderContent state =\n" ++
  "  HH.div\n" ++
  "    [ HP.class_ (HH.ClassName \"" ++ styles.portal ++ "\") ]\n" ++
  "    [ HH.div\n" ++
  "        [ HP.class_ (HH.ClassName \"" ++ styles.overlay ++ "\")\n" ++
  "        , HE.onClick \\\\_ -> HandleOverlayClick\n" ++
  "        ]\n" ++
  "        []\n" ++
  "    , HH.div\n" ++
  "        [ HP.class_ (HH.ClassName \"" ++ styles.content ++ "\")\n" ++
  "        , HP.attr (HH.AttrName \"role\") \"dialog\"\n" ++
  "        , HP.tabIndex 0\n" ++
  "        , HE.onClick \\\\_ -> ContentClicked\n" ++
  "        ]\n" ++
  "        [ HH.text \"" ++ spec.name ++ " content\"\n" ++
  "        , HH.button\n" ++
  "            [ HP.class_ (HH.ClassName \"" ++ styles.close ++ "\")\n" ++
  "            , HP.type_ HP.ButtonButton\n" ++
  "            , HE.onClick \\\\_ -> HandleCloseClick\n" ++
  "            ]\n" ++
  "            [ HH.text \"Close\" ]\n" ++
  "        ]\n" ++
  "    ]\n\n" ++
  "-- ACTIONS\n\n" ++
  "handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit\n" ++
  "handleAction = case _ of\n" ++
  "  Initialize -> do\n" ++
  "    doc <- liftEffect $ HTML.window >>= Window.document\n" ++
  "    void $ H.subscribe $ HQE.eventListener\n" ++
  "      KET.keydown\n" ++
  "      (HTMLDocument.toEventTarget doc)\n" ++
  "      (KE.fromEvent >>> map HandleKeyDown)\n" ++
  "  Finalize -> pure unit\n" ++
  "  Receive input -> H.modify_ _ " ++ lb ++ " input = input " ++ rb ++ "\n" ++
  "  HandleTriggerClick -> do\n" ++
  "    state <- H.get\n" ++
  "    if state.isOpen then closeIt else openIt\n" ++
  "  HandleCloseClick -> closeIt\n" ++
  "  HandleOverlayClick -> closeIt\n" ++
  "  ContentClicked -> pure unit\n" ++
  "  HandleKeyDown ke -> do\n" ++
  "    state <- H.get\n" ++
  "    when (state.isOpen && KE.key ke == \"Escape\") do\n" ++
  "      liftEffect $ Event.preventDefault (KE.toEvent ke)\n" ++
  "      closeIt\n\n" ++
  "openIt :: forall m. MonadAff m => H.HalogenM State Action () Output m Unit\n" ++
  "openIt = do\n" ++
  "  H.modify_ _ " ++ lb ++ " isOpen = true " ++ rb ++ "\n" ++
  "  H.raise Opened\n" ++
  "  H.raise (OpenChanged true)\n\n" ++
  "closeIt :: forall m. MonadAff m => H.HalogenM State Action () Output m Unit\n" ++
  "closeIt = do\n" ++
  "  H.modify_ _ " ++ lb ++ " isOpen = false " ++ rb ++ "\n" ++
  "  H.raise Closed\n" ++
  "  H.raise (OpenChanged false)\n\n" ++
  "-- QUERIES\n\n" ++
  "handleQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Action () Output m (Maybe a)\n" ++
  "handleQuery = case _ of\n" ++
  "  Open a -> openIt *> pure (Just a)\n" ++
  "  Close a -> closeIt *> pure (Just a)\n" ++
  "  Toggle a -> do\n" ++
  "    state <- H.get\n" ++
  "    (if state.isOpen then closeIt else openIt) *> pure (Just a)\n" ++
  "  IsOpen reply -> do\n" ++
  "    state <- H.get\n" ++
  "    pure (Just (reply state.isOpen))\n"

def genJS (spec : ComponentSpec) : String :=
  if spec.behaviors.contains .modal then
    "// " ++ spec.name ++ ".js - Scroll lock FFI\n\n" ++
    "let originalOverflow = null;\n" ++
    "let lockCount = 0;\n\n" ++
    "export const lockBodyScroll = () => " ++ lb ++ "\n" ++
    "  if (++lockCount === 1) " ++ lb ++ "\n" ++
    "    originalOverflow = document.body.style.overflow;\n" ++
    "    document.body.style.overflow = 'hidden';\n" ++
    "  " ++ rb ++ "\n" ++
    rb ++ ";\n\n" ++
    "export const restoreBodyScroll = () => " ++ lb ++ "\n" ++
    "  if (--lockCount === 0 && originalOverflow !== null) " ++ lb ++ "\n" ++
    "    document.body.style.overflow = originalOverflow;\n" ++
    "    originalOverflow = null;\n" ++
    "  " ++ rb ++ "\n" ++
    "  lockCount = Math.max(0, lockCount);\n" ++
    rb ++ ";\n"
  else "// " ++ spec.name ++ ".js - No FFI required\n"

-- ═══════════════════════════════════════════════════════════════════════════════
-- MAIN
-- ═══════════════════════════════════════════════════════════════════════════════

def padRight (s : String) (n : Nat) : String :=
  s ++ "".pushn ' ' (n - s.length)

def genericSpec (name : String) : ComponentSpec := {
  name := name
  behaviors := [.disclosure]
  doc := s!"{name} component"
  parts := [
    { name := "Root", element := "div"
      props := [
        { name := "open", ty := .bool },
        { name := "defaultOpen", ty := .bool }
      ] },
    { name := "Trigger", element := "button" },
    { name := "Content", element := "div" },
    { name := "Close", element := "button" }
  ]
}

def showHelp : IO Unit := do
  IO.println "╔═══════════════════════════════════════╗"
  IO.println "║       Radix Pure Compiler             ║"
  IO.println "╚═══════════════════════════════════════╝"
  IO.println ""
  IO.println "Generates PureScript/Halogen skeletons from Radix TypeScript types."
  IO.println ""
  IO.println "Usage:"
  IO.println "  nix run . -- [OPTIONS] <ComponentName>"
  IO.println "  nix run . -- [OPTIONS] --parse <file.d.ts> <Name>"
  IO.println ""
  IO.println "Style options:"
  IO.println "  --semantic    Semantic classes: dialog-root, dialog-overlay (default)"
  IO.println "  --tailwind    Raw Tailwind utilities"
  IO.println "  --shadcn      shadcn/ui classes with animations"
  IO.println "  --daisy       DaisyUI component classes"
  IO.println ""
  IO.println "Examples:"
  IO.println "  nix run . -- Dialog"
  IO.println "  nix run . -- --shadcn Dialog"
  IO.println "  nix run . -- --daisy Accordion"
  IO.println "  nix run . -- --tailwind --parse ./index.d.ts Slider"
  IO.println ""
  IO.println "Builtin specs:"
  for spec in allSpecs do
    IO.println s!"  {padRight spec.name 12}{spec.doc}"

def capitalize (s : String) : String :=
  if s.isEmpty then "" else
    let first := s.front.toUpper
    let rest := s.drop 1
    first.toString ++ rest

def generateFromSpec (spec : ComponentSpec) (preset : StylePreset) : IO Unit := do
  let presetName := match preset with
    | .semantic => "semantic" | .tailwind => "tailwind" | .shadcn => "shadcn" | .daisy => "daisy"
  IO.println s!"-- Generated by Radix Pure Compiler"
  IO.println s!"-- Component: {spec.name}"
  IO.println s!"-- Style: {presetName}"
  if spec.parts.length > 1 then
    IO.println s!"-- Parts: {spec.parts.map (·.name) |> String.intercalate ", "}"
  IO.println ""
  IO.println (genPurs spec preset)
  IO.println "────────────────────────────────────────"
  IO.println (genJS spec)

def generateComponent (name : String) (preset : StylePreset) : IO Unit := do
  let name := capitalize name
  let spec := match allSpecs.find? (·.name.toLower == name.toLower) with
    | some s => s
    | none => genericSpec name
  generateFromSpec spec preset

def parseAndGenerate (dtsPath : String) (componentName : String) (preset : StylePreset) : IO Unit := do
  let contents ← IO.FS.readFile dtsPath
  match Parser.run tsModule contents with
  | .ok decls =>
    let spec := extractComponent decls (capitalize componentName)
    IO.eprintln s!"✓ Parsed {decls.length} declarations"
    IO.eprintln s!"✓ Found {spec.parts.length} parts: {spec.parts.map (·.name) |> String.intercalate ", "}"
    IO.eprintln s!"✓ Behaviors: {spec.behaviors.map (fun b => match b with | .modal => "modal" | .disclosure => "disclosure" | .selection => "selection" | .navigation => "navigation") |> String.intercalate ", "}"
    IO.eprintln ""
    generateFromSpec spec preset
  | .error msg =>
    IO.eprintln s!"Parse error: {msg}"

def parsePreset (args : List String) : StylePreset × List String :=
  match args with
  | [] => (.semantic, [])
  | "--shadcn" :: rest =>
    let (p, filtered) := parsePreset rest
    (.shadcn, filtered)
  | "--daisy" :: rest =>
    let (p, filtered) := parsePreset rest
    (.daisy, filtered)
  | "--tailwind" :: rest =>
    let (p, filtered) := parsePreset rest
    (.tailwind, filtered)
  | "--semantic" :: rest =>
    let (_, filtered) := parsePreset rest
    (.semantic, filtered)
  | x :: rest =>
    let (p, filtered) := parsePreset rest
    (p, x :: filtered)

 def main (args : List String) : IO Unit := do
  let (preset, args) := parsePreset args
  match args with
  | [] => showHelp
  | ["--parse", dtsPath, name] => parseAndGenerate dtsPath name preset
  | ["--parse", dtsPath] => 
    let name := dtsPath.splitOn "/" |>.getLast! |>.replace "react-" "" |>.replace ".d.ts" "" |>.replace "index" ""
    if name.isEmpty then
      IO.eprintln "Could not infer component name. Use: --parse <file> <ComponentName>"
    else
      parseAndGenerate dtsPath (capitalize name) preset
  | [name] => generateComponent name preset
  | _ => IO.eprintln "Usage: nix run . -- [--shadcn|--daisy|--tailwind] <ComponentName>"

