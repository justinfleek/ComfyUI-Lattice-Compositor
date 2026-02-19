{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Lattice.Utils.SchemaValidation
Description : JSON security validation
Copyright   : (c) Lattice, 2026
License     : MIT

SECURITY FEATURES:
- Prototype pollution prevention (__proto__, constructor, prototype)
- JSON depth limits (prevents stack overflow)
- JSON size limits (prevents memory exhaustion)
- String length limits (prevents payload attacks)
- Path traversal prevention
- Unicode normalization and sanitization

Source: lattice-core/lean/Lattice/Utils/SchemaValidation.lean
-}

module Lattice.Utils.SchemaValidation
  ( -- * Configuration
    SafeParseOptions(..)
  , defaultSafeParseOptions
    -- * Dangerous Keys
  , dangerousKeys
  , isDangerousKey
    -- * Validation Errors
  , ParseErrorCode(..)
  , ParseError(..)
  , mkParseError
    -- * JSON Value
  , JSONValue(..)
  , hasPrototypePollution
  , jsonDepth
  , maxStringLength
  , maxArrayLength
    -- * Validation
  , validateDepth
  , validateStringLengths
  , validateArrayLengths
  , validateJSON
    -- * Path Security
  , isPathSafe
  , sanitizePath
  , dangerousPathPrefixes
    -- * String Sanitization
  , SanitizeStringOptions(..)
  , defaultSanitizeStringOptions
  , sanitizeString
  , sanitizeFilename
    -- * Malicious Payload Detection
  , looksLikeMaliciousPayload
  ) where

import GHC.Generics (Generic)
import Data.Text (Text)
import qualified Data.Text as T
import Data.Char (ord, isControl)
import Data.List (isPrefixOf)
import Data.Set (Set)
import qualified Data.Set as Set

--------------------------------------------------------------------------------
-- Configuration
--------------------------------------------------------------------------------

-- | Options for safe JSON parsing
data SafeParseOptions = SafeParseOptions
  { optMaxDepth        :: !Int     -- ^ Maximum nesting depth (default: 100)
  , optMaxSize         :: !Int     -- ^ Maximum size in bytes (default: 50MB)
  , optMaxStringLength :: !Int     -- ^ Maximum string length (default: 1MB)
  , optMaxArrayLength  :: !Int     -- ^ Maximum array length (default: 100000)
  , optContext         :: !Text    -- ^ Context name for errors
  }
  deriving stock (Eq, Show, Generic)

-- | Default safe parse options
defaultSafeParseOptions :: SafeParseOptions
defaultSafeParseOptions = SafeParseOptions
  { optMaxDepth = 100
  , optMaxSize = 50 * 1024 * 1024
  , optMaxStringLength = 1024 * 1024
  , optMaxArrayLength = 100000
  , optContext = "JSON"
  }

--------------------------------------------------------------------------------
-- Dangerous Keys
--------------------------------------------------------------------------------

-- | Keys that can be used for prototype pollution attacks
dangerousKeys :: Set Text
dangerousKeys = Set.fromList
  [ "__proto__"
  , "constructor"
  , "prototype"
  , "__defineGetter__"
  , "__defineSetter__"
  , "__lookupGetter__"
  , "__lookupSetter__"
  ]

-- | Check if a key is dangerous
isDangerousKey :: Text -> Bool
isDangerousKey = (`Set.member` dangerousKeys)

--------------------------------------------------------------------------------
-- Validation Errors
--------------------------------------------------------------------------------

-- | Error codes for safe parse failures
data ParseErrorCode
  = ParseError
  | SizeExceeded
  | DepthExceeded
  | StringLengthExceeded
  | ArrayLengthExceeded
  | PrototypePollution
  | SchemaValidation
  deriving stock (Eq, Show, Generic)

-- | Parse error with details
data ParseError = ParseErr
  { parseErrorCode    :: !ParseErrorCode
  , parseErrorMessage :: !Text
  , parseErrorContext :: !Text
  }
  deriving stock (Eq, Show, Generic)

-- | Create a parse error
mkParseError :: ParseErrorCode -> Text -> Text -> ParseError
mkParseError code msg ctx = ParseErr
  { parseErrorCode = code
  , parseErrorMessage = msg
  , parseErrorContext = ctx
  }

--------------------------------------------------------------------------------
-- JSON Value
--------------------------------------------------------------------------------

-- | Simple JSON value type
data JSONValue
  = JSONNull
  | JSONBool !Bool
  | JSONNumber !Double
  | JSONString !Text
  | JSONArray ![JSONValue]
  | JSONObject ![(Text, JSONValue)]
  deriving stock (Eq, Show, Generic)

-- | Check a JSON value for prototype pollution
hasPrototypePollution :: JSONValue -> Bool
hasPrototypePollution JSONNull = False
hasPrototypePollution (JSONBool _) = False
hasPrototypePollution (JSONNumber _) = False
hasPrototypePollution (JSONString _) = False
hasPrototypePollution (JSONArray items) = any hasPrototypePollution items
hasPrototypePollution (JSONObject fields) =
  any (\(k, v) -> isDangerousKey k || hasPrototypePollution v) fields

-- | Calculate the depth of a JSON value
jsonDepth :: JSONValue -> Int
jsonDepth JSONNull = 0
jsonDepth (JSONBool _) = 0
jsonDepth (JSONNumber _) = 0
jsonDepth (JSONString _) = 0
jsonDepth (JSONArray []) = 1
jsonDepth (JSONArray items) = 1 + maximum (map jsonDepth items)
jsonDepth (JSONObject []) = 1
jsonDepth (JSONObject fields) = 1 + maximum (map (jsonDepth . snd) fields)

-- | Find maximum string length in JSON value
maxStringLength :: JSONValue -> Int
maxStringLength JSONNull = 0
maxStringLength (JSONBool _) = 0
maxStringLength (JSONNumber _) = 0
maxStringLength (JSONString s) = T.length s
maxStringLength (JSONArray items) =
  if null items then 0 else maximum (map maxStringLength items)
maxStringLength (JSONObject fields) =
  if null fields then 0
  else maximum (map (\(k, v) -> max (T.length k) (maxStringLength v)) fields)

-- | Find maximum array length in JSON value
maxArrayLength :: JSONValue -> Int
maxArrayLength JSONNull = 0
maxArrayLength (JSONBool _) = 0
maxArrayLength (JSONNumber _) = 0
maxArrayLength (JSONString _) = 0
maxArrayLength (JSONArray items) =
  max (length items) (if null items then 0 else maximum (map maxArrayLength items))
maxArrayLength (JSONObject fields) =
  if null fields then 0 else maximum (map (maxArrayLength . snd) fields)

--------------------------------------------------------------------------------
-- Validation
--------------------------------------------------------------------------------

-- | Validate JSON depth
validateDepth :: JSONValue -> SafeParseOptions -> Either ParseError ()
validateDepth val opts =
  let depth = jsonDepth val
  in if depth > optMaxDepth opts
     then Left $ mkParseError DepthExceeded
       (T.pack $ "Depth " <> show depth <> " exceeds maximum " <> show (optMaxDepth opts))
       (optContext opts)
     else Right ()

-- | Validate string lengths
validateStringLengths :: JSONValue -> SafeParseOptions -> Either ParseError ()
validateStringLengths val opts =
  let maxLen = maxStringLength val
  in if maxLen > optMaxStringLength opts
     then Left $ mkParseError StringLengthExceeded
       (T.pack $ "String length " <> show maxLen <> " exceeds maximum " <> show (optMaxStringLength opts))
       (optContext opts)
     else Right ()

-- | Validate array lengths
validateArrayLengths :: JSONValue -> SafeParseOptions -> Either ParseError ()
validateArrayLengths val opts =
  let maxLen = maxArrayLength val
  in if maxLen > optMaxArrayLength opts
     then Left $ mkParseError ArrayLengthExceeded
       (T.pack $ "Array length " <> show maxLen <> " exceeds maximum " <> show (optMaxArrayLength opts))
       (optContext opts)
     else Right ()

-- | Full validation of a JSON value
validateJSON :: JSONValue -> SafeParseOptions -> Either ParseError ()
validateJSON val opts = do
  -- Check prototype pollution
  if hasPrototypePollution val
    then Left $ mkParseError PrototypePollution "Dangerous key detected" (optContext opts)
    else Right ()
  -- Check depth
  validateDepth val opts
  -- Check string lengths
  validateStringLengths val opts
  -- Check array lengths
  validateArrayLengths val opts

--------------------------------------------------------------------------------
-- Path Security
--------------------------------------------------------------------------------

-- | Dangerous path prefixes
dangerousPathPrefixes :: [Text]
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
isPathSafe :: Text -> Bool
isPathSafe path =
  not (T.any (== '\0') path) &&           -- No null bytes
  not (T.isInfixOf ".." path) &&          -- No traversal
  not (any (`T.isPrefixOf` T.toLower path) dangerousPathPrefixes)

-- | Normalize path separators
normalizePath :: Text -> Text
normalizePath = T.replace "\\" "/"

-- | Sanitize a user path relative to a base
sanitizePath :: Text -> Text -> Either Text Text
sanitizePath basePath userPath =
  let normalizedBase = T.dropWhileEnd (== '/') (normalizePath basePath)
      normalizedUser = T.dropWhile (== '/') (normalizePath userPath)
  in if T.any (== '\0') normalizedUser
     then Left "Null byte detected in path"
     else if T.isInfixOf ".." normalizedUser
     then Left "Path traversal pattern detected"
     else Right $ normalizedBase <> "/" <> normalizedUser

--------------------------------------------------------------------------------
-- String Sanitization
--------------------------------------------------------------------------------

-- | Options for string sanitization
data SanitizeStringOptions = SanitizeStringOptions
  { sanitizeMaxLength    :: !Int   -- ^ Maximum length (default: 10000)
  , sanitizeAllowNewlines :: !Bool -- ^ Allow newlines (default: True)
  }
  deriving stock (Eq, Show, Generic)

-- | Default sanitize string options
defaultSanitizeStringOptions :: SanitizeStringOptions
defaultSanitizeStringOptions = SanitizeStringOptions
  { sanitizeMaxLength = 10000
  , sanitizeAllowNewlines = True
  }

-- | Unicode direction override characters
unicodeOverrides :: Set Char
unicodeOverrides = Set.fromList
  [ '\x202A', '\x202B', '\x202C', '\x202D', '\x202E'
  , '\x2066', '\x2067', '\x2068', '\x2069'
  ]

-- | Control characters to filter
isControlToFilter :: Bool -> Char -> Bool
isControlToFilter allowNewlines c
  | c == '\n' || c == '\r' || c == '\t' = not allowNewlines
  | otherwise = isControl c

-- | Sanitize a string for safe processing
sanitizeString :: Text -> SanitizeStringOptions -> Text
sanitizeString input opts =
  T.take (sanitizeMaxLength opts) $
  T.strip $
  T.filter (\c ->
    c /= '\0' &&                              -- No null bytes
    not (Set.member c unicodeOverrides) &&    -- No direction overrides
    not (isControlToFilter (sanitizeAllowNewlines opts) c)
  ) input

-- | Invalid filename characters
invalidFilenameChars :: Set Char
invalidFilenameChars = Set.fromList
  ['/', '\\', '\0', '<', '>', ':', '"', '|', '?', '*', ';', '&', '`', '$',
   '(', ')', '{', '}', '[', ']', '!', '#', '\'']

-- | Sanitize a filename
sanitizeFilename :: Text -> Text
sanitizeFilename filename =
  let -- Replace invalid chars
      s1 = T.map (\c -> if Set.member c invalidFilenameChars then '_' else c) filename
      -- Remove traversal
      s2 = T.replace ".." "_" s1
      -- Remove leading dots
      s3 = if T.isPrefixOf "." s2 then "_" <> T.drop 1 s2 else s2
      -- Limit length
      s4 = T.take 200 s3
  in if T.null s4 || s4 == "_" then "unnamed" else s4

--------------------------------------------------------------------------------
-- Malicious Payload Detection
--------------------------------------------------------------------------------

-- | Check if a string looks like a potential injection payload
looksLikeMaliciousPayload :: Text -> Bool
looksLikeMaliciousPayload value =
  let lower = T.toLower value
  in -- Script injection
     T.isInfixOf "<script" lower ||
     T.isInfixOf "javascript:" lower ||
     -- SQL injection
     T.isInfixOf "' or '" lower ||
     T.isInfixOf "; drop table" lower ||
     T.isInfixOf "; delete from" lower ||
     -- Command injection
     T.isInfixOf "; rm -rf" lower ||
     T.isInfixOf "| cat " lower ||
     -- Path traversal
     T.isInfixOf "../" value ||
     T.isInfixOf "..\\" value
