-- | Lattice.Services.Security.JsonSanitizer - JSON validation and sanitization
-- |
-- | Security module for validating and sanitizing JSON data before processing.
-- | Prevents JSON bombs, prototype pollution, and resource exhaustion attacks.
-- |
-- | ENTERPRISE SECURITY: Critical security control for Enterprise readiness.
-- |
-- | Source: ui/src/services/security/jsonSanitizer.ts

module Lattice.Services.Security.JsonSanitizer
  ( -- * Types
    JSONSanitizeOptions
  , JSONSanitizeResult
  , SanitizeStats
  , defaultOptions
    -- * Parsing & Sanitization
  , parseAndSanitize
  , sanitize
  , sanitizeValue
    -- * Quick Validation
  , quickValidate
  , safeParse
    -- * Utilities
  , deepFreeze
    -- * Constants
  , prototypeKeys
  ) where

import Prelude
import Data.Argonaut.Core (Json, isNull, isBoolean, isNumber, isString, isArray, isObject)
import Data.Argonaut.Core as Json
import Data.Argonaut.Parser (jsonParser)
import Data.Array (length, elem, mapWithIndex, filter)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldl)
import Data.Int (toNumber)
import Data.Maybe (Maybe(..))
import Data.String (Pattern(..), contains, length, toLower) as Str
import Data.String.CodeUnits (toCharArray)
import Data.String.CodeUnits as SCU
import Data.String.Regex (Regex, regex, test)
import Data.String.Regex.Flags (ignoreCase)
import Data.Tuple (Tuple(..))
import Foreign.Object (Object)
import Foreign.Object as Obj

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Sanitization options
type JSONSanitizeOptions =
  { maxDepth :: Int          -- Maximum nesting depth (default: 50)
  , maxArrayLength :: Int    -- Maximum array length (default: 100,000)
  , maxStringLength :: Int   -- Maximum string length in bytes (default: 10MB)
  , maxTotalKeys :: Int      -- Maximum total keys across all objects (default: 1,000,000)
  , maxKeyLength :: Int      -- Maximum object key length (default: 1000)
  , removePrototypeKeys :: Boolean  -- Remove __proto__ and constructor keys
  , removeNullBytes :: Boolean      -- Remove null byte characters from strings
  }

-- | Statistics collected during sanitization
type SanitizeStats =
  { depth :: Int
  , totalKeys :: Int
  , totalArrayElements :: Int
  , maxStringLength :: Int
  , prototypeKeysRemoved :: Int
  }

-- | Sanitization result
type JSONSanitizeResult =
  { valid :: Boolean
  , dat :: Maybe Json        -- "data" is reserved in some contexts
  , err :: Maybe String      -- "error" abbreviated
  , warnings :: Array String
  , stats :: SanitizeStats
  }

-- | Internal state for recursive sanitization
type SanitizeState =
  { stats :: SanitizeStats
  , warnings :: Array String
  }

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

-- | Default sanitization options
defaultOptions :: JSONSanitizeOptions
defaultOptions =
  { maxDepth: 50
  , maxArrayLength: 100000
  , maxStringLength: 10 * 1024 * 1024  -- 10MB
  , maxTotalKeys: 1000000
  , maxKeyLength: 1000
  , removePrototypeKeys: true
  , removeNullBytes: true
  }

-- | Dangerous keys that could enable prototype pollution
prototypeKeys :: Array String
prototypeKeys =
  [ "__proto__"
  , "constructor"
  , "prototype"
  , "__defineGetter__"
  , "__defineSetter__"
  , "__lookupGetter__"
  , "__lookupSetter__"
  ]

-- | Initial stats
emptyStats :: SanitizeStats
emptyStats =
  { depth: 0
  , totalKeys: 0
  , totalArrayElements: 0
  , maxStringLength: 0
  , prototypeKeysRemoved: 0
  }

-- | Initial state
emptyState :: SanitizeState
emptyState = { stats: emptyStats, warnings: [] }

--------------------------------------------------------------------------------
-- Parsing & Sanitization
--------------------------------------------------------------------------------

-- | Parse and sanitize JSON string
parseAndSanitize :: String -> JSONSanitizeOptions -> JSONSanitizeResult
parseAndSanitize jsonString opts =
  -- Input validation: empty check
  if Str.length jsonString == 0
    then mkError "Input string is empty" emptyStats []
  -- Length check before parsing (prevent DoS)
  else if Str.length jsonString > opts.maxStringLength * 2
    then mkError
      ("JSON string too large: " <> show (Str.length jsonString) <> " bytes (max: " <> show (opts.maxStringLength * 2) <> ")")
      emptyStats []
  -- Parse JSON
  else case jsonParser jsonString of
    Left parseErr -> mkError ("Invalid JSON: " <> parseErr) emptyStats []
    Right parsed ->
      -- Sanitize the parsed data
      case sanitizeValue parsed opts emptyState 0 of
        Left err -> mkError err emptyState.stats emptyState.warnings
        Right (Tuple sanitized state) ->
          { valid: true
          , dat: Just sanitized
          , err: Nothing
          , warnings: state.warnings
          , stats: state.stats
          }

-- | Sanitize already-parsed JSON data
sanitize :: Json -> JSONSanitizeOptions -> JSONSanitizeResult
sanitize json opts =
  case sanitizeValue json opts emptyState 0 of
    Left err -> mkError err emptyState.stats emptyState.warnings
    Right (Tuple sanitized state) ->
      { valid: true
      , dat: Just sanitized
      , err: Nothing
      , warnings: state.warnings
      , stats: state.stats
      }

-- | Recursively sanitize a JSON value
sanitizeValue :: Json -> JSONSanitizeOptions -> SanitizeState -> Int -> Either String (Tuple Json SanitizeState)
sanitizeValue json opts state depth =
  -- Track max depth
  let state1 = state { stats = state.stats { depth = max state.stats.depth depth } }
  in
  -- Depth limit check
  if depth > opts.maxDepth
    then Left ("Maximum nesting depth exceeded: " <> show opts.maxDepth <> " levels")
  -- Null is valid JSON
  else if isNull json
    then Right (Tuple json state1)
  -- Boolean is valid JSON
  else if isBoolean json
    then Right (Tuple json state1)
  -- Number is valid JSON (Argonaut handles NaN/Infinity during parsing)
  else if isNumber json
    then case Json.toNumber json of
      Just n ->
        if isFinite n
          then Right (Tuple json state1)
          else Left ("Non-finite number is not valid JSON: " <> show n)
      Nothing -> Left "Failed to extract number from JSON"
  -- String
  else if isString json
    then case Json.toString json of
      Just s -> sanitizeString s opts state1
      Nothing -> Left "Failed to extract string from JSON"
  -- Array
  else if isArray json
    then case Json.toArray json of
      Just arr -> sanitizeArray arr opts state1 depth
      Nothing -> Left "Failed to extract array from JSON"
  -- Object
  else if isObject json
    then case Json.toObject json of
      Just obj -> sanitizeObject obj opts state1 depth
      Nothing -> Left "Failed to extract object from JSON"
  -- Unknown type (should not happen with valid JSON)
  else Left "Unknown JSON value type"

--------------------------------------------------------------------------------
-- String Sanitization
--------------------------------------------------------------------------------

-- | Sanitize a string value
sanitizeString :: String -> JSONSanitizeOptions -> SanitizeState -> Either String (Tuple Json SanitizeState)
sanitizeString str opts state =
  -- Length check
  if Str.length str > opts.maxStringLength
    then Left ("String exceeds maximum length: " <> show (Str.length str) <> " bytes (max: " <> show opts.maxStringLength <> ")")
  else
    -- Track max string length
    let state1 = state { stats = state.stats { maxStringLength = max state.stats.maxStringLength (Str.length str) } }
        -- Remove null bytes if configured
        (finalStr /\ state2) =
          if opts.removeNullBytes && Str.contains (Str.Pattern "\x00") str
            then (removeNullBytes str) /\ (state1 { warnings = state1.warnings <> ["Null bytes removed from string"] })
            else str /\ state1
    in Right (Tuple (Json.fromString finalStr) state2)

-- | Remove null bytes from string
removeNullBytes :: String -> String
removeNullBytes str =
  let chars = toCharArray str
      filtered = filter (\c -> c /= '\x00') chars
  in foldl (\acc c -> acc <> SCU.singleton c) "" filtered

--------------------------------------------------------------------------------
-- Array Sanitization
--------------------------------------------------------------------------------

-- | Sanitize an array
sanitizeArray :: Array Json -> JSONSanitizeOptions -> SanitizeState -> Int -> Either String (Tuple Json SanitizeState)
sanitizeArray arr opts state depth =
  -- Length check
  if length arr > opts.maxArrayLength
    then Left ("Array exceeds maximum length: " <> show (length arr) <> " elements (max: " <> show opts.maxArrayLength <> ")")
  else
    let state1 = state { stats = state.stats { totalArrayElements = state.stats.totalArrayElements + length arr } }
    in
    -- Check cumulative elements
    if state1.stats.totalArrayElements > opts.maxArrayLength * 10
      then Left ("Total array elements exceed limit: " <> show state1.stats.totalArrayElements)
      else sanitizeArrayElements arr opts state1 depth []

-- | Sanitize array elements recursively
sanitizeArrayElements :: Array Json -> JSONSanitizeOptions -> SanitizeState -> Int -> Array Json -> Either String (Tuple Json SanitizeState)
sanitizeArrayElements arr opts state depth acc =
  case Array.uncons arr of
    Nothing -> Right (Tuple (Json.fromArray acc) state)
    Just { head, tail } ->
      case sanitizeValue head opts state (depth + 1) of
        Left err -> Left err
        Right (Tuple sanitized newState) ->
          sanitizeArrayElements tail opts newState depth (acc <> [sanitized])

--------------------------------------------------------------------------------
-- Object Sanitization
--------------------------------------------------------------------------------

-- | Sanitize an object
sanitizeObject :: Object Json -> JSONSanitizeOptions -> SanitizeState -> Int -> Either String (Tuple Json SanitizeState)
sanitizeObject obj opts state depth =
  let keys = Obj.keys obj
      state1 = state { stats = state.stats { totalKeys = state.stats.totalKeys + length keys } }
  in
  -- Key count check
  if state1.stats.totalKeys > opts.maxTotalKeys
    then Left ("Total object keys exceed limit: " <> show state1.stats.totalKeys <> " (max: " <> show opts.maxTotalKeys <> ")")
    else sanitizeObjectKeys (Obj.toUnfoldable obj) opts state1 depth Obj.empty

-- | Sanitize object keys recursively
sanitizeObjectKeys :: Array (Tuple String Json) -> JSONSanitizeOptions -> SanitizeState -> Int -> Object Json -> Either String (Tuple Json SanitizeState)
sanitizeObjectKeys pairs opts state depth acc =
  case Array.uncons pairs of
    Nothing -> Right (Tuple (Json.fromObject acc) state)
    Just { head: (Tuple key val), tail } ->
      -- Key length check
      if Str.length key > opts.maxKeyLength
        then
          let state1 = state { warnings = state.warnings <> ["Key truncated: " <> take 50 key <> "... (exceeded " <> show opts.maxKeyLength <> " chars)"] }
          in sanitizeObjectKeys tail opts state1 depth acc
      -- Prototype pollution check
      else if opts.removePrototypeKeys && (key `elem` prototypeKeys)
        then
          let state1 = state
                { stats = state.stats { prototypeKeysRemoved = state.stats.prototypeKeysRemoved + 1 }
                , warnings = state.warnings <> ["Prototype pollution key removed: " <> key]
                }
          in sanitizeObjectKeys tail opts state1 depth acc
      -- Also check lowercase variant
      else if opts.removePrototypeKeys && (toLower key `elem` map toLower prototypeKeys)
        then
          let state1 = state
                { stats = state.stats { prototypeKeysRemoved = state.stats.prototypeKeysRemoved + 1 }
                , warnings = state.warnings <> ["Prototype pollution key removed (case variant): " <> key]
                }
          in sanitizeObjectKeys tail opts state1 depth acc
      -- Sanitize the value
      else case sanitizeValue val opts state (depth + 1) of
        Left err -> Left err
        Right (Tuple sanitized newState) ->
          sanitizeObjectKeys tail opts newState depth (Obj.insert key sanitized acc)

--------------------------------------------------------------------------------
-- Quick Validation
--------------------------------------------------------------------------------

-- | Quick validation without full sanitization
-- | Use for fast rejection of obviously malicious input
quickValidate :: String -> JSONSanitizeOptions -> Boolean
quickValidate jsonString opts =
  -- Length check
  if Str.length jsonString > opts.maxStringLength * 2
    then false
  -- Quick depth check via bracket counting
  else if maxBracketDepth jsonString > opts.maxDepth
    then false
  -- Quick prototype pollution check
  else if opts.removePrototypeKeys && hasPrototypeKey jsonString
    then false
  else true

-- | Count maximum bracket depth
maxBracketDepth :: String -> Int
maxBracketDepth str =
  let chars = toCharArray str
  in foldl countBrackets { max: 0, current: 0 } chars # _.max
  where
    countBrackets acc c
      | c == '{' || c == '[' =
          let newCurrent = acc.current + 1
          in { max: max acc.max newCurrent, current: newCurrent }
      | c == '}' || c == ']' =
          { max: acc.max, current: acc.current - 1 }
      | otherwise = acc

-- | Check for prototype pollution patterns
hasPrototypeKey :: String -> Boolean
hasPrototypeKey str =
  case protoRegex of
    Just r -> test r str
    Nothing -> false
  where
    protoRegex :: Maybe Regex
    protoRegex = case regex "\"(__proto__|constructor|prototype)\"\\s*:" ignoreCase of
      Right r -> Just r
      Left _ -> Nothing

-- | Safe JSON.parse with size limits
safeParse :: String -> JSONSanitizeOptions -> Either String Json
safeParse jsonString opts =
  let result = parseAndSanitize jsonString opts
  in
  if result.valid
    then case result.dat of
      Just d -> Right d
      Nothing -> Left "JSON validation passed but no data returned"
    else Left (case result.err of
      Just e -> e
      Nothing -> "JSON validation failed")

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

-- | Deep freeze (no-op in PureScript since data is immutable)
-- | Included for API compatibility
deepFreeze :: Json -> Json
deepFreeze = identity

--------------------------------------------------------------------------------
-- Internal Helpers
--------------------------------------------------------------------------------

-- | Create error result
mkError :: String -> SanitizeStats -> Array String -> JSONSanitizeResult
mkError err stats warnings =
  { valid: false
  , dat: Nothing
  , err: Just err
  , warnings
  , stats
  }

-- | Check if number is finite
isFinite :: Number -> Boolean
isFinite n = n == n && n /= infinity && n /= (-infinity)
  where infinity = 1.0 / 0.0

-- | Take first n characters
take :: Int -> String -> String
take n str = SCU.take n str

-- | Convert to lowercase
toLower :: String -> String
toLower = Str.toLower

-- | Map over array (uses Prelude's Functor map)
map :: forall a b. (a -> b) -> Array a -> Array b
map f arr = f <$> arr

-- | Tuple operator
infixr 6 Tuple as /\
