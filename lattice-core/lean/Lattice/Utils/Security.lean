/-
  Lattice.Utils.Security - Security utilities

  Provides secure alternatives for common operations:
  - URL validation (SSRF prevention)
  - Input sanitization
  - Runtime type validation

  Note: Crypto random is platform-specific and not included.
  Use platform-native secure random APIs.

  Source: ui/src/utils/security.ts
-/

namespace Lattice.Utils.Security

/-! ## URL Validation -/

/-- Allowed URL protocols -/
def allowedProtocols : List String :=
  ["https:", "http:", "data:", "blob:"]

/-- Blocked hostnames (localhost, private IPs) -/
def blockedHostnames : List String :=
  ["localhost", "127.0.0.1", "0.0.0.0", "::1"]

/-- Check if a hostname is a private IPv4 address -/
def isPrivateIP (hostname : String) : Bool :=
  -- 10.0.0.0/8
  hostname.startsWith "10." ||
  -- 172.16.0.0/12
  (hostname.startsWith "172." &&
    match hostname.splitOn "." with
    | _ :: second :: _ =>
      match second.toNat? with
      | some n => n >= 16 && n <= 31
      | none => false
    | _ => false) ||
  -- 192.168.0.0/16
  hostname.startsWith "192.168." ||
  -- 169.254.0.0/16 (link-local)
  hostname.startsWith "169.254." ||
  -- 127.0.0.0/8 (loopback)
  hostname.startsWith "127."

/-- URL validation options -/
structure URLValidationOptions where
  allowData : Bool := true
  allowBlob : Bool := true
  allowHttp : Bool := false  -- Default to HTTPS only
  deriving Repr, BEq

/-- URL validation result -/
inductive URLValidationResult
  | valid
  | invalidProtocol (protocol : String)
  | blockedHostname (hostname : String)
  | privateIP (hostname : String)
  | parseError (error : String)
  deriving Repr, BEq

/-- Parsed URL components (simplified) -/
structure ParsedURL where
  protocol : String
  hostname : String
  port : Option Nat
  path : String
  deriving Repr, BEq

/-- Simple URL parser (extract protocol and hostname) -/
def parseURL (url : String) : Option ParsedURL :=
  -- Find protocol (ends with ://)
  match url.splitOn "://" with
  | [protocol, rest] =>
    let protocolWithColon := protocol ++ ":"
    -- For data: and blob: URLs, no hostname
    if protocolWithColon == "data:" || protocolWithColon == "blob:" then
      some { protocol := protocolWithColon, hostname := "", port := none, path := rest }
    else
      -- Extract hostname (before first /)
      match rest.splitOn "/" with
      | [] => none
      | hostPart :: pathParts =>
        -- Handle port (hostname:port)
        let (hostname, port) := match hostPart.splitOn ":" with
          | [h] => (h, none)
          | [h, p] => (h, p.toNat?)
          | _ => (hostPart, none)
        some {
          protocol := protocolWithColon
          hostname := hostname.toLower
          port := port
          path := "/" ++ String.intercalate "/" pathParts
        }
  | _ => none

/-- Validate a URL for safe external resource loading -/
def validateURL (url : String) (options : URLValidationOptions := {}) : URLValidationResult :=
  match parseURL url with
  | none => .parseError "Invalid URL format"
  | some parsed =>
    -- Build allowed protocols list
    let allowed := ["https:"] ++
      (if options.allowHttp then ["http:"] else []) ++
      (if options.allowData then ["data:"] else []) ++
      (if options.allowBlob then ["blob:"] else [])

    -- Check protocol
    if !allowed.contains parsed.protocol then
      .invalidProtocol parsed.protocol
    -- For data: and blob:, skip hostname checks
    else if parsed.protocol == "data:" || parsed.protocol == "blob:" then
      .valid
    -- Check blocked hostnames
    else if blockedHostnames.contains parsed.hostname then
      .blockedHostname parsed.hostname
    -- Check private IPs
    else if isPrivateIP parsed.hostname then
      .privateIP parsed.hostname
    else
      .valid

/-- Check if URL validation succeeded -/
def isValidURL (url : String) (options : URLValidationOptions := {}) : Bool :=
  match validateURL url options with
  | .valid => true
  | _ => false

/-! ## Input Sanitization -/

/-- Characters invalid in filenames (cross-platform) -/
def invalidFilenameChars : List Char :=
  ['<', '>', ':', '"', '/', '\\', '|', '?', '*']

/-- Sanitize a filename to prevent directory traversal -/
def sanitizeFilename (filename : String) : String :=
  filename
    -- Remove directory traversal
    |>.replace ".." ""
    -- Remove invalid characters
    |> (fun s => s.toList.filter (· ∉ invalidFilenameChars) |> String.mk)
    -- Remove leading dots (hidden files)
    |>.dropWhile (· == '.')
    -- Trim whitespace
    |>.trim
    -- Ensure non-empty
    |> fun s => if s.isEmpty then "unnamed" else s

/-- HTML-unsafe characters and their entities -/
def htmlEntities : List (Char × String) :=
  [('&', "&amp;"), ('<', "&lt;"), ('>', "&gt;"), ('"', "&quot;"), ('\'', "&#39;")]

/-- Escape a string for safe HTML display -/
def escapeHTML (input : String) : String :=
  input.toList.map (fun c =>
    match htmlEntities.find? (·.1 == c) with
    | some (_, entity) => entity.toList
    | none => [c]
  ) |>.join |> String.mk

/-! ## Runtime Type Validation -/

/-- Validation error with context -/
structure ValidationError where
  message : String
  path : List String := []
  deriving Repr, BEq

/-- Create a validation error -/
def mkValidationError (message : String) (path : List String := []) : ValidationError :=
  { message, path }

/-- Format validation error path -/
def formatPath (path : List String) : String :=
  if path.isEmpty then "root"
  else String.intercalate "." path

/-! ## JSON Value Type (for validation) -/

/-- Simple JSON value representation -/
inductive JSONValue
  | null
  | bool (b : Bool)
  | number (n : Float)
  | string (s : String)
  | array (items : List JSONValue)
  | object (fields : List (String × JSONValue))
  deriving Repr, BEq

/-- Check if a JSONValue is an object -/
def JSONValue.isObject : JSONValue → Bool
  | .object _ => true
  | _ => false

/-- Check if a JSONValue is an array -/
def JSONValue.isArray : JSONValue → Bool
  | .array _ => true
  | _ => false

/-- Get object fields if value is an object -/
def JSONValue.getFields : JSONValue → Option (List (String × JSONValue))
  | .object fields => some fields
  | _ => none

/-- Get array items if value is an array -/
def JSONValue.getItems : JSONValue → Option (List JSONValue)
  | .array items => some items
  | _ => none

/-- Lookup a field in a JSON object -/
def JSONValue.field (v : JSONValue) (key : String) : Option JSONValue :=
  match v with
  | .object fields => fields.find? (·.1 == key) |>.map (·.2)
  | _ => none

/-! ## Project Structure Validation -/

/-- Required fields for project validation -/
def requiredProjectFields : List String := ["version"]

/-- Validate basic project structure -/
def validateProjectStructure (data : JSONValue) : Except ValidationError Unit := do
  -- Must be an object
  let fields ← match data.getFields with
    | some f => pure f
    | none => throw (mkValidationError "Expected object")

  -- Must have version field
  if !fields.any (·.1 == "version") then
    throw (mkValidationError "Missing required field 'version'")

  -- Must have compositions or layers
  let hasCompositions := fields.any (·.1 == "compositions")
  let hasLayers := fields.any (·.1 == "layers")
  if !hasCompositions && !hasLayers then
    throw (mkValidationError "Missing required field 'compositions' or 'layers'")

  pure ()

end Lattice.Utils.Security
