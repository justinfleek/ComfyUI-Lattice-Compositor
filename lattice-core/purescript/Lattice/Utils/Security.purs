-- | Lattice.Utils.Security - Security utilities
-- |
-- | Provides secure alternatives for common operations:
-- | - URL validation (SSRF prevention)
-- | - Input sanitization
-- | - Runtime type validation
-- |
-- | Note: Crypto random is platform-specific. Use Effect.Random
-- | or a crypto library for secure random in PureScript.
-- |
-- | Source: lattice-core/lean/Lattice/Utils/Security.lean

module Lattice.Utils.Security
  ( -- URL Validation
    URLValidationOptions
  , defaultURLOptions
  , URLValidationResult(..)
  , ParsedURL
  , parseURL
  , validateURL
  , isValidURL
  , isPrivateIP
  , blockedHostnames
    -- Input Sanitization
  , sanitizeFilename
  , escapeHTML
    -- Runtime Type Validation
  , ValidationError
  , mkValidationError
  , formatPath
    -- JSON Value
  , JSONValue(..)
  , jsonIsObject
  , jsonIsArray
  , jsonGetFields
  , jsonGetItems
  , jsonField
    -- Project Validation
  , validateProjectStructure
  ) where

import Prelude
import Data.Array as Array
import Data.Either (Either(..))
import Data.Int as Int
import Data.Maybe (Maybe(..))
import Data.String as String
import Data.String.CodePoints (codePointFromChar)
import Data.String.Pattern (Pattern(..))
import Data.Tuple (Tuple(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

--------------------------------------------------------------------------------
-- URL Validation
--------------------------------------------------------------------------------

-- | Blocked hostnames (localhost, private IPs)
blockedHostnames :: Array String
blockedHostnames = ["localhost", "127.0.0.1", "0.0.0.0", "::1"]

-- | Check if a hostname is a private IPv4 address
isPrivateIP :: String -> Boolean
isPrivateIP hostname =
  String.take 3 hostname == "10." ||
  is172Private hostname ||
  String.take 8 hostname == "192.168." ||
  String.take 8 hostname == "169.254." ||
  String.take 4 hostname == "127."
  where
    is172Private h =
      case String.split (Pattern ".") h of
        ["172", second, _, _] ->
          case Int.fromString second of
            Just n -> n >= 16 && n <= 31
            Nothing -> false
        _ -> false

-- | URL validation options
type URLValidationOptions =
  { allowData :: Boolean  -- ^ Allow data: URLs (default: true)
  , allowBlob :: Boolean  -- ^ Allow blob: URLs (default: true)
  , allowHttp :: Boolean  -- ^ Allow http: URLs (default: false, HTTPS only)
  }

-- | Default URL validation options
defaultURLOptions :: URLValidationOptions
defaultURLOptions =
  { allowData: true
  , allowBlob: true
  , allowHttp: false
  }

-- | URL validation result
data URLValidationResult
  = URLValid
  | URLInvalidProtocol String
  | URLBlockedHostname String
  | URLPrivateIP String
  | URLParseError String

derive instance Generic URLValidationResult _

instance Show URLValidationResult where
  show = genericShow

derive instance Eq URLValidationResult

-- | Parsed URL components
type ParsedURL =
  { protocol :: String
  , hostname :: String
  , port :: Maybe Int
  , path :: String
  }

-- | Simple URL parser
parseURL :: String -> Maybe ParsedURL
parseURL url =
  case String.split (Pattern "://") url of
    [protocol, rest] ->
      let protocolWithColon = protocol <> ":"
      in if protocolWithColon == "data:" || protocolWithColon == "blob:"
         then Just
           { protocol: protocolWithColon
           , hostname: ""
           , port: Nothing
           , path: rest
           }
         else case String.split (Pattern "/") rest of
           [] -> Nothing
           parts ->
             let hostPart = case Array.head parts of
                   Just h -> h
                   Nothing -> ""
                 pathParts = Array.drop 1 parts
                 hostPort = case String.split (Pattern ":") hostPart of
                   [h] -> { host: h, port: Nothing }
                   [h, p] -> { host: h, port: Int.fromString p }
                   _ -> { host: hostPart, port: Nothing }
             in Just
               { protocol: protocolWithColon
               , hostname: String.toLower hostPort.host
               , port: hostPort.port
               , path: "/" <> String.joinWith "/" pathParts
               }
    _ -> Nothing

-- | Validate a URL for safe external resource loading
validateURL :: String -> URLValidationOptions -> URLValidationResult
validateURL url options =
  case parseURL url of
    Nothing -> URLParseError "Invalid URL format"
    Just parsed ->
      let allowed = ["https:"] <>
            (if options.allowHttp then ["http:"] else []) <>
            (if options.allowData then ["data:"] else []) <>
            (if options.allowBlob then ["blob:"] else [])
      in if not (Array.elem parsed.protocol allowed)
         then URLInvalidProtocol parsed.protocol
         else if parsed.protocol == "data:" || parsed.protocol == "blob:"
         then URLValid
         else if Array.elem parsed.hostname blockedHostnames
         then URLBlockedHostname parsed.hostname
         else if isPrivateIP parsed.hostname
         then URLPrivateIP parsed.hostname
         else URLValid

-- | Check if URL validation succeeded
isValidURL :: String -> URLValidationOptions -> Boolean
isValidURL url options =
  case validateURL url options of
    URLValid -> true
    _ -> false

--------------------------------------------------------------------------------
-- Input Sanitization
--------------------------------------------------------------------------------

-- | Characters invalid in filenames
invalidFilenameChars :: Array String
invalidFilenameChars = ["<", ">", ":", "\"", "/", "\\", "|", "?", "*"]

-- | Sanitize a filename to prevent directory traversal
sanitizeFilename :: String -> String
sanitizeFilename filename =
  let -- Remove directory traversal
      s1 = String.replaceAll (Pattern "..") (String.Replacement "") filename
      -- Remove invalid characters (simplified - filter by char)
      s2 = String.joinWith "" $ Array.filter
        (\c -> not (Array.elem c invalidFilenameChars))
        (String.split (Pattern "") s1)
      -- Remove leading dots
      s3 = String.dropWhile (_ == codePointFromChar '.') s2
      -- Trim whitespace
      s4 = String.trim s3
  in if String.null s4 then "unnamed" else s4

-- | HTML entities for escaping
htmlEntities :: Array { char :: String, entity :: String }
htmlEntities =
  [ { char: "&", entity: "&amp;" }
  , { char: "<", entity: "&lt;" }
  , { char: ">", entity: "&gt;" }
  , { char: "\"", entity: "&quot;" }
  , { char: "'", entity: "&#39;" }
  ]

-- | Escape a string for safe HTML display
escapeHTML :: String -> String
escapeHTML input =
  Array.foldl
    (\acc ent -> String.replaceAll (Pattern ent.char) (String.Replacement ent.entity) acc)
    input
    htmlEntities

--------------------------------------------------------------------------------
-- Runtime Type Validation
--------------------------------------------------------------------------------

-- | Validation error with context
type ValidationError =
  { message :: String
  , path :: Array String
  }

-- | Create a validation error
mkValidationError :: String -> Array String -> ValidationError
mkValidationError message path = { message, path }

-- | Format validation error path
formatPath :: Array String -> String
formatPath path =
  if Array.null path then "root"
  else String.joinWith "." path

--------------------------------------------------------------------------------
-- JSON Value
--------------------------------------------------------------------------------

-- | Simple JSON value representation
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
  show (JSONArray items) = "(JSONArray [" <> String.joinWith ", " (map show items) <> "])"
  show (JSONObject fields) = "(JSONObject [" <> String.joinWith ", " (map showField fields) <> "])"
    where
      showField (Tuple k v) = "(Tuple " <> show k <> " " <> show v <> ")"

-- | Check if a JSONValue is an object
jsonIsObject :: JSONValue -> Boolean
jsonIsObject (JSONObject _) = true
jsonIsObject _ = false

-- | Check if a JSONValue is an array
jsonIsArray :: JSONValue -> Boolean
jsonIsArray (JSONArray _) = true
jsonIsArray _ = false

-- | Get object fields
jsonGetFields :: JSONValue -> Maybe (Array (Tuple String JSONValue))
jsonGetFields (JSONObject fields) = Just fields
jsonGetFields _ = Nothing

-- | Get array items
jsonGetItems :: JSONValue -> Maybe (Array JSONValue)
jsonGetItems (JSONArray items) = Just items
jsonGetItems _ = Nothing

-- | Lookup a field in a JSON object
jsonField :: JSONValue -> String -> Maybe JSONValue
jsonField (JSONObject fields) key =
  map (\(Tuple _ v) -> v) $ Array.find (\(Tuple k _) -> k == key) fields
jsonField _ _ = Nothing

--------------------------------------------------------------------------------
-- Project Validation
--------------------------------------------------------------------------------

-- | Validate basic project structure
validateProjectStructure :: JSONValue -> Either ValidationError Unit
validateProjectStructure val = do
  -- Must be an object
  fields <- case jsonGetFields val of
    Just f -> Right f
    Nothing -> Left (mkValidationError "Expected object" [])

  -- Must have version field
  let hasVersion = Array.any (\(Tuple k _) -> k == "version") fields
  if not hasVersion
    then Left (mkValidationError "Missing required field 'version'" [])
    else pure unit

  -- Must have compositions or layers
  let hasComps = Array.any (\(Tuple k _) -> k == "compositions") fields
      hasLayers = Array.any (\(Tuple k _) -> k == "layers") fields
  if not hasComps && not hasLayers
    then Left (mkValidationError "Missing required field 'compositions' or 'layers'" [])
    else pure unit
