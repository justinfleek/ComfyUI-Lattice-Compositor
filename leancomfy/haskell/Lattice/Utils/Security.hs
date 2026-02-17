{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Lattice.Utils.Security
Description : Security utilities
Copyright   : (c) Lattice, 2026
License     : MIT

Provides secure alternatives for common operations:
- URL validation (SSRF prevention)
- Input sanitization
- Runtime type validation

Note: Crypto random is platform-specific. Use System.Random.Stateful
or cryptonite for secure random in Haskell.

Source: leancomfy/lean/Lattice/Utils/Security.lean
-}

module Lattice.Utils.Security
  ( -- * URL Validation
    URLValidationOptions(..)
  , defaultURLOptions
  , URLValidationResult(..)
  , ParsedURL(..)
  , parseURL
  , validateURL
  , isValidURL
  , isPrivateIP
  , blockedHostnames
    -- * Input Sanitization
  , sanitizeFilename
  , escapeHTML
    -- * Runtime Type Validation
  , ValidationError(..)
  , mkValidationError
  , formatPath
    -- * JSON Value
  , JSONValue(..)
  , jsonIsObject
  , jsonIsArray
  , jsonGetFields
  , jsonGetItems
  , jsonField
    -- * Project Validation
  , validateProjectStructure
  ) where

import GHC.Generics (Generic)
import Data.Text (Text)
import qualified Data.Text as T
import Data.Char (toLower, isAlphaNum)
import Data.List (find, isPrefixOf)
import Data.Maybe (isJust)

--------------------------------------------------------------------------------
-- URL Validation
--------------------------------------------------------------------------------

-- | Blocked hostnames (localhost, private IPs)
blockedHostnames :: [Text]
blockedHostnames = ["localhost", "127.0.0.1", "0.0.0.0", "::1"]

-- | Check if a hostname is a private IPv4 address
isPrivateIP :: Text -> Bool
isPrivateIP hostname =
  let h = T.unpack hostname
  in "10." `isPrefixOf` h ||
     is172Private h ||
     "192.168." `isPrefixOf` h ||
     "169.254." `isPrefixOf` h ||
     "127." `isPrefixOf` h
  where
    is172Private h =
      case splitOn '.' h of
        "172" : second : _ ->
          case reads second :: [(Int, String)] of
            [(n, "")] -> n >= 16 && n <= 31
            _ -> False
        _ -> False

    splitOn :: Char -> String -> [String]
    splitOn _ [] = [""]
    splitOn c (x:xs)
      | c == x    = "" : splitOn c xs
      | otherwise = let (h:t) = splitOn c xs in (x:h) : t

-- | URL validation options
data URLValidationOptions = URLValidationOptions
  { urlAllowData :: !Bool  -- ^ Allow data: URLs (default: True)
  , urlAllowBlob :: !Bool  -- ^ Allow blob: URLs (default: True)
  , urlAllowHttp :: !Bool  -- ^ Allow http: URLs (default: False, HTTPS only)
  }
  deriving stock (Eq, Show, Generic)

-- | Default URL validation options
defaultURLOptions :: URLValidationOptions
defaultURLOptions = URLValidationOptions
  { urlAllowData = True
  , urlAllowBlob = True
  , urlAllowHttp = False
  }

-- | URL validation result
data URLValidationResult
  = URLValid
  | URLInvalidProtocol Text
  | URLBlockedHostname Text
  | URLPrivateIP Text
  | URLParseError Text
  deriving stock (Eq, Show, Generic)

-- | Parsed URL components
data ParsedURL = ParsedURL
  { parsedProtocol :: Text
  , parsedHostname :: Text
  , parsedPort     :: Maybe Int
  , parsedPath     :: Text
  }
  deriving stock (Eq, Show, Generic)

-- | Simple URL parser
parseURL :: Text -> Maybe ParsedURL
parseURL url =
  case T.splitOn "://" url of
    [protocol, rest] ->
      let protocolWithColon = protocol <> ":"
      in if protocolWithColon == "data:" || protocolWithColon == "blob:"
         then Just ParsedURL
           { parsedProtocol = protocolWithColon
           , parsedHostname = ""
           , parsedPort = Nothing
           , parsedPath = rest
           }
         else case T.splitOn "/" rest of
           [] -> Nothing
           (hostPart : pathParts) ->
             let (hostname, port) = case T.splitOn ":" hostPart of
                   [h] -> (h, Nothing)
                   [h, p] -> (h, readMaybe (T.unpack p))
                   _ -> (hostPart, Nothing)
             in Just ParsedURL
               { parsedProtocol = protocolWithColon
               , parsedHostname = T.toLower hostname
               , parsedPort = port
               , parsedPath = "/" <> T.intercalate "/" pathParts
               }
    _ -> Nothing
  where
    readMaybe :: Read a => String -> Maybe a
    readMaybe s = case reads s of
      [(x, "")] -> Just x
      _ -> Nothing

-- | Validate a URL for safe external resource loading
validateURL :: Text -> URLValidationOptions -> URLValidationResult
validateURL url options =
  case parseURL url of
    Nothing -> URLParseError "Invalid URL format"
    Just parsed ->
      let allowed = ["https:"] ++
            (if urlAllowHttp options then ["http:"] else []) ++
            (if urlAllowData options then ["data:"] else []) ++
            (if urlAllowBlob options then ["blob:"] else [])
          proto = parsedProtocol parsed
          host = parsedHostname parsed
      in if proto `notElem` allowed
         then URLInvalidProtocol proto
         else if proto == "data:" || proto == "blob:"
         then URLValid
         else if host `elem` blockedHostnames
         then URLBlockedHostname host
         else if isPrivateIP host
         then URLPrivateIP host
         else URLValid

-- | Check if URL validation succeeded
isValidURL :: Text -> URLValidationOptions -> Bool
isValidURL url options =
  case validateURL url options of
    URLValid -> True
    _ -> False

--------------------------------------------------------------------------------
-- Input Sanitization
--------------------------------------------------------------------------------

-- | Characters invalid in filenames
invalidFilenameChars :: [Char]
invalidFilenameChars = ['<', '>', ':', '"', '/', '\\', '|', '?', '*']

-- | Sanitize a filename to prevent directory traversal
sanitizeFilename :: Text -> Text
sanitizeFilename filename =
  let -- Remove directory traversal
      s1 = T.replace ".." "" filename
      -- Remove invalid characters
      s2 = T.filter (`notElem` invalidFilenameChars) s1
      -- Remove leading dots
      s3 = T.dropWhile (== '.') s2
      -- Trim whitespace
      s4 = T.strip s3
  in if T.null s4 then "unnamed" else s4

-- | HTML entities for escaping
htmlEntities :: [(Char, Text)]
htmlEntities =
  [ ('&', "&amp;")
  , ('<', "&lt;")
  , ('>', "&gt;")
  , ('"', "&quot;")
  , ('\'', "&#39;")
  ]

-- | Escape a string for safe HTML display
escapeHTML :: Text -> Text
escapeHTML input = T.concatMap escape input
  where
    escape c = case lookup c htmlEntities of
      Just entity -> entity
      Nothing -> T.singleton c

--------------------------------------------------------------------------------
-- Runtime Type Validation
--------------------------------------------------------------------------------

-- | Validation error with context
data ValidationError = ValidationError
  { validationMessage :: Text
  , validationPath    :: [Text]
  }
  deriving stock (Eq, Show, Generic)

-- | Create a validation error
mkValidationError :: Text -> [Text] -> ValidationError
mkValidationError msg path = ValidationError
  { validationMessage = msg
  , validationPath = path
  }

-- | Format validation error path
formatPath :: [Text] -> Text
formatPath [] = "root"
formatPath path = T.intercalate "." path

--------------------------------------------------------------------------------
-- JSON Value
--------------------------------------------------------------------------------

-- | Simple JSON value representation
data JSONValue
  = JSONNull
  | JSONBool !Bool
  | JSONNumber !Double
  | JSONString !Text
  | JSONArray ![JSONValue]
  | JSONObject ![(Text, JSONValue)]
  deriving stock (Eq, Show, Generic)

-- | Check if a JSONValue is an object
jsonIsObject :: JSONValue -> Bool
jsonIsObject (JSONObject _) = True
jsonIsObject _ = False

-- | Check if a JSONValue is an array
jsonIsArray :: JSONValue -> Bool
jsonIsArray (JSONArray _) = True
jsonIsArray _ = False

-- | Get object fields
jsonGetFields :: JSONValue -> Maybe [(Text, JSONValue)]
jsonGetFields (JSONObject fields) = Just fields
jsonGetFields _ = Nothing

-- | Get array items
jsonGetItems :: JSONValue -> Maybe [JSONValue]
jsonGetItems (JSONArray items) = Just items
jsonGetItems _ = Nothing

-- | Lookup a field in a JSON object
jsonField :: JSONValue -> Text -> Maybe JSONValue
jsonField (JSONObject fields) key = snd <$> find ((== key) . fst) fields
jsonField _ _ = Nothing

--------------------------------------------------------------------------------
-- Project Validation
--------------------------------------------------------------------------------

-- | Validate basic project structure
validateProjectStructure :: JSONValue -> Either ValidationError ()
validateProjectStructure val = do
  -- Must be an object
  fields <- case jsonGetFields val of
    Just f -> Right f
    Nothing -> Left (mkValidationError "Expected object" [])

  -- Must have version field
  if not (any ((== "version") . fst) fields)
    then Left (mkValidationError "Missing required field 'version'" [])
    else Right ()

  -- Must have compositions or layers
  let hasComps = any ((== "compositions") . fst) fields
      hasLayers = any ((== "layers") . fst) fields
  if not hasComps && not hasLayers
    then Left (mkValidationError "Missing required field 'compositions' or 'layers'" [])
    else Right ()
