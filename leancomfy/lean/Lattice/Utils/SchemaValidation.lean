/-
  Lattice.Utils.SchemaValidation - JSON security validation

  SECURITY FEATURES:
  - Prototype pollution prevention (__proto__, constructor, prototype)
  - JSON depth limits (prevents stack overflow)
  - JSON size limits (prevents memory exhaustion)
  - String length limits (prevents payload attacks)
  - Path traversal prevention
  - Unicode normalization and sanitization

  Source: ui/src/utils/schemaValidation.ts
-/

namespace Lattice.Utils.SchemaValidation

/-! ## Configuration -/

/-- Options for safe JSON parsing -/
structure SafeParseOptions where
  maxDepth : Nat := 100                    -- Maximum nesting depth
  maxSize : Nat := 50 * 1024 * 1024        -- 50MB
  maxStringLength : Nat := 1024 * 1024     -- 1MB
  maxArrayLength : Nat := 100000
  context : String := "JSON"
  deriving Repr, BEq

/-- Default safe parse options -/
def defaultOptions : SafeParseOptions := {}

/-! ## Dangerous Keys -/

/-- Keys that can be used for prototype pollution attacks -/
def dangerousKeys : List String :=
  [ "__proto__"
  , "constructor"
  , "prototype"
  , "__defineGetter__"
  , "__defineSetter__"
  , "__lookupGetter__"
  , "__lookupSetter__"
  ]

/-- Check if a key is dangerous -/
def isDangerousKey (key : String) : Bool :=
  dangerousKeys.contains key

/-! ## Validation Errors -/

/-- Error codes for safe parse failures -/
inductive ParseErrorCode
  | parseError
  | sizeExceeded
  | depthExceeded
  | stringLengthExceeded
  | arrayLengthExceeded
  | prototypePollution
  | schemaValidation
  deriving Repr, BEq

/-- Parse error with details -/
structure ParseError where
  code : ParseErrorCode
  message : String
  context : String
  deriving Repr, BEq

/-- Create a parse error -/
def mkParseError (code : ParseErrorCode) (message : String) (context : String) : ParseError :=
  { code, message, context }

/-! ## JSON Validation -/

/-- Simple JSON value type -/
inductive JSONValue
  | null
  | bool (b : Bool)
  | number (n : Float)
  | string (s : String)
  | array (items : List JSONValue)
  | object (fields : List (String × JSONValue))
  deriving Repr, BEq

/-- Check a JSON value for prototype pollution (with fuel) -/
def hasPrototypePollutionAux (fuel : Nat) : JSONValue → Bool
  | .null => false
  | .bool _ => false
  | .number _ => false
  | .string _ => false
  | .array items =>
    if fuel == 0 then false
    else items.any (hasPrototypePollutionAux (fuel - 1))
  | .object fields =>
    if fuel == 0 then false
    else fields.any fun (key, value) =>
      isDangerousKey key || hasPrototypePollutionAux (fuel - 1) value

/-- Check a JSON value for prototype pollution -/
def hasPrototypePollution (value : JSONValue) : Bool :=
  -- Use large fuel for typical JSON structures
  hasPrototypePollutionAux 1000 value

/-- Calculate the depth of a JSON value (with fuel) -/
def jsonDepthAux (fuel : Nat) : JSONValue → Nat
  | .null => 0
  | .bool _ => 0
  | .number _ => 0
  | .string _ => 0
  | .array items =>
    if fuel == 0 then 1
    else match items.map (jsonDepthAux (fuel - 1)) |>.maximum? with
         | some max => max + 1
         | none => 1
  | .object fields =>
    if fuel == 0 then 1
    else match fields.map (fun (_, v) => jsonDepthAux (fuel - 1) v) |>.maximum? with
         | some max => max + 1
         | none => 1

/-- Calculate the depth of a JSON value -/
def jsonDepth (value : JSONValue) : Nat :=
  jsonDepthAux 1000 value

/-- Validate JSON depth against options -/
def validateDepth (value : JSONValue) (options : SafeParseOptions) : Except ParseError Unit :=
  let depth := jsonDepth value
  if depth > options.maxDepth then
    throw (mkParseError .depthExceeded
      s!"Depth {depth} exceeds maximum {options.maxDepth}"
      options.context)
  else
    pure ()

/-- Find maximum string length in JSON value (with fuel) -/
def maxStringLengthAux (fuel : Nat) : JSONValue → Nat
  | .null => 0
  | .bool _ => 0
  | .number _ => 0
  | .string s => s.length
  | .array items =>
    if fuel == 0 then 0
    else items.map (maxStringLengthAux (fuel - 1)) |>.foldl max 0
  | .object fields =>
    if fuel == 0 then 0
    else fields.map (fun (k, v) => max k.length (maxStringLengthAux (fuel - 1) v)) |>.foldl max 0

/-- Find maximum string length in JSON value -/
def maxStringLength (value : JSONValue) : Nat :=
  maxStringLengthAux 1000 value

/-- Validate string lengths against options -/
def validateStringLengths (value : JSONValue) (options : SafeParseOptions) : Except ParseError Unit :=
  let maxLen := maxStringLength value
  if maxLen > options.maxStringLength then
    throw (mkParseError .stringLengthExceeded
      s!"String length {maxLen} exceeds maximum {options.maxStringLength}"
      options.context)
  else
    pure ()

/-- Find maximum array length in JSON value (with fuel) -/
def maxArrayLenAux (fuel : Nat) : JSONValue → Nat
  | .null => 0
  | .bool _ => 0
  | .number _ => 0
  | .string _ => 0
  | .array items =>
    if fuel == 0 then items.length
    else max items.length (items.map (maxArrayLenAux (fuel - 1)) |>.foldl max 0)
  | .object fields =>
    if fuel == 0 then 0
    else fields.map (fun (_, v) => maxArrayLenAux (fuel - 1) v) |>.foldl max 0

/-- Find maximum array length in JSON value -/
def maxArrayLen (value : JSONValue) : Nat :=
  maxArrayLenAux 1000 value

/-- Validate array lengths against options -/
def validateArrayLengths (value : JSONValue) (options : SafeParseOptions) : Except ParseError Unit :=
  let maxLen := maxArrayLen value
  if maxLen > options.maxArrayLength then
    throw (mkParseError .arrayLengthExceeded
      s!"Array length {maxLen} exceeds maximum {options.maxArrayLength}"
      options.context)
  else
    pure ()

/-- Full validation of a JSON value -/
def validateJSON (value : JSONValue) (options : SafeParseOptions := {}) : Except ParseError Unit := do
  -- Check prototype pollution
  if hasPrototypePollution value then
    throw (mkParseError .prototypePollution "Dangerous key detected" options.context)

  -- Check depth
  validateDepth value options

  -- Check string lengths
  validateStringLengths value options

  -- Check array lengths
  validateArrayLengths value options

/-! ## Path Security -/

/-- Check if a path segment is dangerous -/
def isDangerousPathSegment (segment : String) : Bool :=
  segment == ".." ||
  segment == "." ||
  segment.startsWith "~" ||
  segment.toLower == ".git" ||
  segment.toLower == ".env" ||
  segment.toLower.containsSubstr "password" ||
  segment.toLower.containsSubstr "secret" ||
  segment.toLower.containsSubstr "credential"

/-- Dangerous path patterns -/
def dangerousPathPrefixes : List String :=
  [ "/etc/"
  , "/var/"
  , "/usr/"
  , "/bin/"
  , "/sbin/"
  , "/root/"
  , "/home/"
  , "/tmp/"
  ]

/-- Check if a path is safe -/
def isPathSafe (path : String) : Bool :=
  -- Check for null bytes
  !path.any (· == '\x00') &&
  -- Check for traversal
  !path.containsSubstr ".." &&
  -- Check for dangerous prefixes
  !dangerousPathPrefixes.any (fun prefix => path.toLower.startsWith prefix)

/-- Normalize path separators -/
def normalizePath (path : String) : String :=
  path.replace "\\" "/"

/-- Sanitize a user path relative to a base -/
def sanitizePath (basePath userPath : String) : Except String String :=
  let normalizedBase := normalizePath basePath |>.dropRightWhile (· == '/')
  let normalizedUser := normalizePath userPath |>.dropWhile (· == '/')

  -- Check for null bytes
  if normalizedUser.any (· == '\x00') then
    throw "Null byte detected in path"
  -- Check for traversal
  else if normalizedUser.containsSubstr ".." then
    throw "Path traversal pattern detected"
  else
    pure s!"{normalizedBase}/{normalizedUser}"

/-! ## String Sanitization -/

/-- Control characters to remove -/
def controlChars : List Char :=
  (List.range 32).map Char.ofNat |>.filter (· != '\n' && · != '\t' && · != '\r')

/-- Unicode direction override characters to remove -/
def unicodeOverrides : List Char :=
  ['\u202A', '\u202B', '\u202C', '\u202D', '\u202E',
   '\u2066', '\u2067', '\u2068', '\u2069']

/-- Options for string sanitization -/
structure SanitizeStringOptions where
  maxLength : Nat := 10000
  allowNewlines : Bool := true
  deriving Repr, BEq

/-- Sanitize a string for safe processing -/
def sanitizeString (input : String) (options : SanitizeStringOptions := {}) : String :=
  input.toList
    -- Remove null bytes
    |>.filter (· != '\x00')
    -- Remove Unicode direction overrides
    |>.filter (· ∉ unicodeOverrides)
    -- Remove control characters (keep newlines/tabs if allowed)
    |>.filter (fun c =>
      if options.allowNewlines
      then c ∉ controlChars
      else c ∉ (controlChars ++ ['\n', '\r']))
    |> String.mk
    -- Trim
    |>.trim
    -- Enforce max length
    |> fun s => s.take options.maxLength

/-- Invalid filename characters -/
def invalidFilenameChars : List Char :=
  ['/', '\\', '\x00', '<', '>', ':', '"', '|', '?', '*', ';', '&', '`', '$',
   '(', ')', '{', '}', '[', ']', '!', '#', '\'']

/-- Sanitize a filename -/
def sanitizeFilename (filename : String) : String :=
  filename
    -- Replace path separators and invalid chars with underscore
    |> fun s => s.toList.map (fun c =>
        if c ∈ invalidFilenameChars then '_' else c) |> String.mk
    -- Remove traversal attempts
    |>.replace ".." "_"
    -- Remove leading dots (hidden files)
    |> fun s => if s.startsWith "." then "_" ++ s.drop 1 else s
    -- Limit length to 200
    |> fun s => s.take 200
    -- Ensure non-empty
    |> fun s => if s.isEmpty || s == "_" then "unnamed" else s

/-! ## Malicious Payload Detection -/

/-- Check if a string looks like a potential injection payload -/
def looksLikeMaliciousPayload (value : String) : Bool :=
  let lowerValue := value.toLower
  -- Script injection
  lowerValue.containsSubstr "<script" ||
  lowerValue.containsSubstr "javascript:" ||
  -- SQL injection patterns
  lowerValue.containsSubstr "' or '" ||
  lowerValue.containsSubstr "; drop table" ||
  lowerValue.containsSubstr "; delete from" ||
  -- Command injection
  lowerValue.containsSubstr "; rm -rf" ||
  lowerValue.containsSubstr "| cat " ||
  -- Path traversal
  value.containsSubstr "../" ||
  value.containsSubstr "..\\"

end Lattice.Utils.SchemaValidation
