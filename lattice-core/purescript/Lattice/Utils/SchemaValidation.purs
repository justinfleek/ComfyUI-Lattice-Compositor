-- | Lattice.Utils.SchemaValidation - JSON security validation
-- |
-- | SECURITY FEATURES:
-- | - Prototype pollution prevention (__proto__, constructor, prototype)
-- | - JSON depth limits (prevents stack overflow)
-- | - JSON size limits (prevents memory exhaustion)
-- | - String length limits (prevents payload attacks)
-- | - Path traversal prevention
-- | - Unicode normalization and sanitization
-- |
-- | Source: lattice-core/lean/Lattice/Utils/SchemaValidation.lean

module Lattice.Utils.SchemaValidation
  ( -- Configuration
    SafeParseOptions
  , defaultSafeParseOptions
    -- Dangerous Keys
  , dangerousKeys
  , isDangerousKey
    -- Validation Errors
  , ParseErrorCode(..)
  , ParseError
  , mkParseError
    --                                                                 // json // v
  , JSONValue(..)
  , hasPrototypePollution
  , jsonDepth
  , maxStringLength
  , maxArrayLength
    -- Validation
  , validateDepth
  , validateStringLengths
  , validateArrayLengths
  , validateJSON
    -- Path Security
  , isPathSafe
  , sanitizePath
  , dangerousPathPrefixes
    -- String Sanitization
  , SanitizeStringOptions
  , defaultSanitizeStringOptions
  , sanitizeString
  , sanitizeFilename
    -- Malicious Payload Detection
  , looksLikeMaliciousPayload
  ) where

import Prelude
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (any, foldl)
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Set as Set
import Data.String as String
import Data.String.CodePoints (codePointFromChar)
import Data.String.CodePoints as SCP
import Data.String.Pattern (Pattern(..))
import Data.Tuple (Tuple(..), snd)
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

-- ────────────────────────────────────────────────────────────────────────────
-- Configuration
-- ────────────────────────────────────────────────────────────────────────────

-- | Options for safe JSON parsing
type SafeParseOptions =
  { maxDepth :: Int        -- ^ Maximum nesting depth (default: 100)
  , maxSize :: Int         -- ^ Maximum size in bytes (default: 50MB)
  , maxStringLength :: Int -- ^ Maximum string length (default: 1MB)
  , maxArrayLength :: Int  -- ^ Maximum array length (default: 100000)
  , context :: String      -- ^ Context name for errors
  }

-- | Default safe parse options
defaultSafeParseOptions :: SafeParseOptions
defaultSafeParseOptions =
  { maxDepth: 100
  , maxSize: 50 * 1024 * 1024
  , maxStringLength: 1024 * 1024
  , maxArrayLength: 100000
  , context: "JSON"
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Dangerous Keys
-- ────────────────────────────────────────────────────────────────────────────

-- | Keys that can be used for prototype pollution attacks
dangerousKeys :: Set String
dangerousKeys = Set.fromFoldable
  [ "__proto__"
  , "constructor"
  , "prototype"
  , "__defineGetter__"
  , "__defineSetter__"
  , "__lookupGetter__"
  , "__lookupSetter__"
  ]

-- | Check if a key is dangerous
isDangerousKey :: String -> Boolean
isDangerousKey = flip Set.member dangerousKeys

-- ────────────────────────────────────────────────────────────────────────────
-- Validation Errors
-- ────────────────────────────────────────────────────────────────────────────

-- | Error codes for safe parse failures
data ParseErrorCode
  = ParseError
  | SizeExceeded
  | DepthExceeded
  | StringLengthExceeded
  | ArrayLengthExceeded
  | PrototypePollution
  | SchemaValidation

derive instance Generic ParseErrorCode _
derive instance Eq ParseErrorCode

instance Show ParseErrorCode where
  show = genericShow

-- | Parse error with details
type ParseError =
  { code :: ParseErrorCode
  , message :: String
  , context :: String
  }

-- | Create a parse error
mkParseError :: ParseErrorCode -> String -> String -> ParseError
mkParseError code message context = { code, message, context }

-- ────────────────────────────────────────────────────────────────────────────
--                                                                 // json // v
-- ────────────────────────────────────────────────────────────────────────────

-- | Simple JSON value type
data JSONValue
  = JSONNull
  | JSONBool Boolean
  | JSONNumber Number
  | JSONString String
  | JSONArray (Array JSONValue)
  | JSONObject (Array (Tuple String JSONValue))

derive instance Eq JSONValue

instance Show JSONValue where
  show JSONNull = "JSONNull"
  show (JSONBool b) = "(JSONBool " <> show b <> ")"
  show (JSONNumber n) = "(JSONNumber " <> show n <> ")"
  show (JSONString s) = "(JSONString " <> show s <> ")"
  show (JSONArray items) = "(JSONArray [" <> showItems items <> "])"
    where
      showItems [] = ""
      showItems arr = case Array.uncons arr of
        Nothing -> ""
        Just { head: x, tail: [] } -> show x
        Just { head: x, tail: xs } -> show x <> ", " <> showItems xs
  show (JSONObject fields) = "(JSONObject [" <> showFields fields <> "])"
    where
      showFields [] = ""
      showFields arr = case Array.uncons arr of
        Nothing -> ""
        Just { head: (Tuple k v), tail: [] } -> "(Tuple " <> show k <> " " <> show v <> ")"
        Just { head: (Tuple k v), tail: xs } -> "(Tuple " <> show k <> " " <> show v <> "), " <> showFields xs

-- | Check a JSON value for prototype pollution
hasPrototypePollution :: JSONValue -> Boolean
hasPrototypePollution = case _ of
  JSONNull -> false
  JSONBool _ -> false
  JSONNumber _ -> false
  JSONString _ -> false
  JSONArray items -> any hasPrototypePollution items
  JSONObject fields ->
    any (\(Tuple k v) -> isDangerousKey k || hasPrototypePollution v) fields

-- | Calculate the depth of a JSON value
jsonDepth :: JSONValue -> Int
jsonDepth = case _ of
  JSONNull -> 0
  JSONBool _ -> 0
  JSONNumber _ -> 0
  JSONString _ -> 0
  JSONArray items ->
    if Array.null items then 1
    else 1 + foldl max 0 (map jsonDepth items)
  JSONObject fields ->
    if Array.null fields then 1
    else 1 + foldl max 0 (map (jsonDepth <<< snd) fields)

-- | Find maximum string length in JSON value
maxStringLength :: JSONValue -> Int
maxStringLength = case _ of
  JSONNull -> 0
  JSONBool _ -> 0
  JSONNumber _ -> 0
  JSONString s -> String.length s
  JSONArray items ->
    if Array.null items then 0
    else foldl max 0 (map maxStringLength items)
  JSONObject fields ->
    if Array.null fields then 0
    else foldl max 0 (map (\(Tuple k v) -> max (String.length k) (maxStringLength v)) fields)

-- | Find maximum array length in JSON value
maxArrayLength :: JSONValue -> Int
maxArrayLength = case _ of
  JSONNull -> 0
  JSONBool _ -> 0
  JSONNumber _ -> 0
  JSONString _ -> 0
  JSONArray items ->
    let nested = if Array.null items then 0 else foldl max 0 (map maxArrayLength items)
    in max (Array.length items) nested
  JSONObject fields ->
    if Array.null fields then 0
    else foldl max 0 (map (maxArrayLength <<< snd) fields)

-- ────────────────────────────────────────────────────────────────────────────
-- Validation
-- ────────────────────────────────────────────────────────────────────────────

-- | Validate JSON depth
validateDepth :: JSONValue -> SafeParseOptions -> Either ParseError Unit
validateDepth val opts =
  let depth = jsonDepth val
  in if depth > opts.maxDepth
     then Left $ mkParseError DepthExceeded
       ("Depth " <> show depth <> " exceeds maximum " <> show opts.maxDepth)
       opts.context
     else Right unit

-- | Validate string lengths
validateStringLengths :: JSONValue -> SafeParseOptions -> Either ParseError Unit
validateStringLengths val opts =
  let maxLen = maxStringLength val
  in if maxLen > opts.maxStringLength
     then Left $ mkParseError StringLengthExceeded
       ("String length " <> show maxLen <> " exceeds maximum " <> show opts.maxStringLength)
       opts.context
     else Right unit

-- | Validate array lengths
validateArrayLengths :: JSONValue -> SafeParseOptions -> Either ParseError Unit
validateArrayLengths val opts =
  let maxLen = maxArrayLength val
  in if maxLen > opts.maxArrayLength
     then Left $ mkParseError ArrayLengthExceeded
       ("Array length " <> show maxLen <> " exceeds maximum " <> show opts.maxArrayLength)
       opts.context
     else Right unit

-- | Full validation of a JSON value
validateJSON :: JSONValue -> SafeParseOptions -> Either ParseError Unit
validateJSON val opts = do
  -- Check prototype pollution
  if hasPrototypePollution val
    then Left $ mkParseError PrototypePollution "Dangerous key detected" opts.context
    else pure unit
  -- Check depth
  validateDepth val opts
  -- Check string lengths
  validateStringLengths val opts
  -- Check array lengths
  validateArrayLengths val opts

-- ────────────────────────────────────────────────────────────────────────────
-- Path Security
-- ────────────────────────────────────────────────────────────────────────────

-- | Dangerous path prefixes
dangerousPathPrefixes :: Array String
dangerousPathPrefixes =
  [ "/etc/"
  , "/var/"
  , "/usr/"
  , "/bin/"
  , "/sbin/"
  , "/root/"
  , "/home/"
  , "/tmp/"
  ]

-- | Check if a path is safe
isPathSafe :: String -> Boolean
isPathSafe path =
  not (String.contains (Pattern "\x00") path) &&  -- No null bytes
  not (String.contains (Pattern "..") path) &&    -- No traversal
  not (any (\prefix -> String.contains (Pattern prefix) (String.toLower path)) dangerousPathPrefixes)

-- | Normalize path separators
normalizePath :: String -> String
normalizePath = String.replaceAll (Pattern "\\") (String.Replacement "/")

-- | Sanitize a user path relative to a base
sanitizePath :: String -> String -> Either String String
sanitizePath basePath userPath =
  let normalizedBase = SCP.dropWhile (_ == codePointFromChar '/') $ normalizePath basePath
      normalizedUser = SCP.dropWhile (_ == codePointFromChar '/') $ normalizePath userPath
  in if String.contains (Pattern "\x00") normalizedUser
     then Left "Null byte detected in path"
     else if String.contains (Pattern "..") normalizedUser
     then Left "Path traversal pattern detected"
     else Right $ normalizedBase <> "/" <> normalizedUser

-- ────────────────────────────────────────────────────────────────────────────
-- String Sanitization
-- ────────────────────────────────────────────────────────────────────────────

-- | Options for string sanitization
type SanitizeStringOptions =
  { maxLength :: Int       -- ^ Maximum length (default: 10000)
  , allowNewlines :: Boolean -- ^ Allow newlines (default: true)
  }

-- | Default sanitize string options
defaultSanitizeStringOptions :: SanitizeStringOptions
defaultSanitizeStringOptions =
  { maxLength: 10000
  , allowNewlines: true
  }

-- | Unicode direction override characters to remove
unicodeOverrides :: Array String
unicodeOverrides =
  [ "\x202A", "\x202B", "\x202C", "\x202D", "\x202E"
  , "\x2066", "\x2067", "\x2068", "\x2069"
  ]

-- | Sanitize a string for safe processing
sanitizeString :: String -> SanitizeStringOptions -> String
sanitizeString input opts =
  let -- Remove null bytes
      s1 = String.replaceAll (Pattern "\x00") (String.Replacement "") input
      -- Remove unicode overrides
      s2 = foldl (\acc c -> String.replaceAll (Pattern c) (String.Replacement "") acc) s1 unicodeOverrides
      -- Trim
      s3 = String.trim s2
      -- Enforce max length
      s4 = String.take opts.maxLength s3
  in s4

-- | Invalid filename characters
invalidFilenameChars :: Array String
invalidFilenameChars =
  ["/", "\\", "\x00", "<", ">", ":", "\"", "|", "?", "*", ";", "&", "`", "$",
   "(", ")", "{", "}", "[", "]", "!", "#", "'"]

-- | Sanitize a filename
sanitizeFilename :: String -> String
sanitizeFilename filename =
  let -- Replace invalid chars with underscore
      s1 = foldl (\acc c -> String.replaceAll (Pattern c) (String.Replacement "_") acc) filename invalidFilenameChars
      -- Remove traversal
      s2 = String.replaceAll (Pattern "..") (String.Replacement "_") s1
      -- Remove leading dots
      s3 = if String.take 1 s2 == "." then "_" <> String.drop 1 s2 else s2
      -- Limit length
      s4 = String.take 200 s3
  in if String.null s4 || s4 == "_" then "unnamed" else s4

-- ────────────────────────────────────────────────────────────────────────────
-- Malicious Payload Detection
-- ────────────────────────────────────────────────────────────────────────────

-- | Check if a string looks like a potential injection payload
looksLikeMaliciousPayload :: String -> Boolean
looksLikeMaliciousPayload value =
  let lower = String.toLower value
  in -- Script injection
     String.contains (Pattern "<script") lower ||
     String.contains (Pattern "javascript:") lower ||
     --                                                                       // sql
     String.contains (Pattern "' or '") lower ||
     String.contains (Pattern "; drop table") lower ||
     String.contains (Pattern "; delete from") lower ||
     -- Command injection
     String.contains (Pattern "; rm -rf") lower ||
     String.contains (Pattern "| cat ") lower ||
     -- Path traversal
     String.contains (Pattern "../") value ||
     String.contains (Pattern "..\\") value
