-- | Lattice.Services.Security.UrlValidator - URL validation for security
-- |
-- | Security module for validating URLs before loading external resources.
-- | Blocks dangerous protocols that could lead to XSS, code execution, or data exfiltration.
-- |
-- | ENTERPRISE SECURITY: Critical security control for Enterprise Grade security.
-- |
-- | Source: ui/src/services/security/urlValidator.ts

module Lattice.Services.Security.UrlValidator
  ( -- * Types
    URLValidationResult
  , URLContext(..)
  , URLRiskLevel(..)
    -- * Validation
  , validateURL
  , validateDataURL
  , validateURLs
    -- * Sanitization
  , sanitizeURLForHTML
    -- * Trust Checking
  , isTrustedDomain
  , extractAndValidateURLs
    -- * Constants
  , blockedProtocols
  , maxURLLength
  ) where

import Prelude
import Data.Array (any, elem, filter, mapMaybe)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldl)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.String (Pattern(..), toLower, trim, length)
import Data.String as Str
import Data.String.CodeUnits (indexOf)
import Data.String.Regex (Regex, regex, test)
import Data.String.Regex.Flags (ignoreCase)
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | URL validation context
data URLContext = CtxAsset | CtxFetch | CtxEmbed

derive instance Eq URLContext
derive instance Generic URLContext _
instance Show URLContext where show = genericShow

-- | Risk level assessment
data URLRiskLevel = RiskSafe | RiskWarning | RiskBlocked

derive instance Eq URLRiskLevel
derive instance Generic URLRiskLevel _
instance Show URLRiskLevel where show = genericShow

-- | Validation result
type URLValidationResult =
  { valid :: Boolean
  , sanitized :: Maybe String
  , error :: Maybe String
  , warning :: Maybe String
  , protocol :: String
  , riskLevel :: URLRiskLevel
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Constants
-- ────────────────────────────────────────────────────────────────────────────

-- | Maximum URL length (2MB for data URLs)
maxURLLength :: Int
maxURLLength = 2000000

-- | Dangerous protocols that MUST be blocked
-- | These can execute code or access local resources
blockedProtocols :: Array String
blockedProtocols =
  [ "javascript:"  -- XSS - code execution
  , "vbscript:"    -- Legacy IE code execution
  , "file:"        -- Local file system access
  , "ftp:"         -- Unencrypted file transfer
  , "gopher:"      -- Legacy protocol, security issues
  , "ws:"          -- Unencrypted WebSocket (block for assets)
  , "wss:"         -- WebSocket (block for assets)
  , "chrome:"      -- Browser internals
  , "chrome-extension:"
  , "moz-extension:"
  , "about:"       -- Browser internals
  , "view-source:" -- Source viewing
  ]

-- ────────────────────────────────────────────────────────────────────────────
-- Regex Patterns (compiled once)
-- ────────────────────────────────────────────────────────────────────────────

-- | Protocol extraction regex
protocolRegex :: Maybe Regex
protocolRegex = case regex "^([a-zA-Z][a-zA-Z0-9+.-]*):" ignoreCase of
  Right r -> Just r
  Left _ -> Nothing

-- | URL extraction regex for text scanning
urlExtractRegex :: Maybe Regex
urlExtractRegex = case regex "https?://[^\\s<>\"{}|\\\\^`\\[\\]]+|data:[^\\s<>\"{}|\\\\^`\\[\\]]+|" ignoreCase of
  Right r -> Just r
  Left _ -> Nothing

-- | Blocked data URL patterns (HTML, JavaScript, etc.)
blockedDataPatterns :: Array Regex
blockedDataPatterns = mapMaybe mkRegex
  [ "^data:text/html"
  , "^data:application/javascript"
  , "^data:application/x-javascript"
  , "^data:text/javascript"
  , "^data:application/ecmascript"
  , "^data:text/ecmascript"
  , "^data:application/xhtml\\+xml"
  , "^data:image/svg\\+xml.*<script"
  ]
  where
    mkRegex :: String -> Maybe Regex
    mkRegex pat = case regex pat ignoreCase of
      Right r -> Just r
      Left _ -> Nothing

-- | Safe data URL patterns (images, audio, video, fonts)
safeDataPatterns :: Array Regex
safeDataPatterns = mapMaybe mkRegex
  [ "^data:image/(png|jpeg|jpg|gif|webp|bmp|ico|avif)"
  , "^data:image/svg\\+xml(?!.*<script)"
  , "^data:audio/(mp3|wav|ogg|webm|aac|flac)"
  , "^data:video/(mp4|webm|ogg)"
  , "^data:font/(woff|woff2|ttf|otf)"
  , "^data:application/octet-stream"
  , "^data:application/json"
  , "^data:text/plain"
  , "^data:text/csv"
  ]
  where
    mkRegex :: String -> Maybe Regex
    mkRegex pat = case regex pat ignoreCase of
      Right r -> Just r
      Left _ -> Nothing

-- ────────────────────────────────────────────────────────────────────────────
-- Validation Functions
-- ────────────────────────────────────────────────────────────────────────────

-- | Validate a URL for safe loading
validateURL :: String -> URLContext -> URLValidationResult
validateURL url _context =
  -- Trim whitespace
  let trimmedUrl = trim url
  in
  -- Empty string check
  if length trimmedUrl == 0
    then mkBlocked "URL is empty" "none"
  -- Length limit (prevent DoS)
  else if length trimmedUrl > maxURLLength
    then mkBlocked "URL exceeds maximum length (2MB)" "unknown"
  -- Check blocked protocols
  else case findBlockedProtocol trimmedUrl of
    Just blocked -> mkBlocked ("Blocked protocol: " <> blocked <> " - security risk") blocked
    Nothing ->
      let protocol = extractProtocol trimmedUrl
      in
      -- Handle data: URLs
      if protocol == "data:"
        then validateDataURL trimmedUrl
      -- Handle blob: URLs (created by browser, generally safe)
      else if protocol == "blob:"
        then mkSafe trimmedUrl "blob:"
      --                                                                     // https
      else if protocol == "https:"
        then mkSafe trimmedUrl "https:"
      --                                                                      // http
      else if protocol == "http:"
        then mkWarning trimmedUrl "http:" "Unencrypted HTTP connection - data may be intercepted"
      -- Relative URLs are safe
      else if isRelativeURL trimmedUrl protocol
        then mkSafe trimmedUrl "relative"
      -- Unknown protocol - block by default (fail closed)
      else mkBlocked ("Unknown protocol: " <> protocol <> " - blocked for security") protocol

-- | Validate data: URLs - only allows safe MIME types
validateDataURL :: String -> URLValidationResult
validateDataURL url =
  -- Check for blocked patterns first
  if any (\pat -> test pat url) blockedDataPatterns
    then mkBlocked "Data URL contains blocked content type (possible script injection)" "data:"
  -- Check for safe patterns
  else if any (\pat -> test pat url) safeDataPatterns
    then mkSafe url "data:"
  -- Unknown data URL type - block by default
  else
    let mime = extractMimeFromDataURL url
    in mkBlocked ("Data URL with unrecognized MIME type: " <> mime) "data:"

-- | Batch validate multiple URLs
validateURLs :: Array String -> Map String URLValidationResult
validateURLs urls =
  foldl (\m url -> Map.insert url (validateURL url CtxAsset) m) Map.empty urls

-- ────────────────────────────────────────────────────────────────────────────
-- Sanitization
-- ────────────────────────────────────────────────────────────────────────────

-- | Sanitize a URL for safe use in HTML attributes
-- | Returns Either with error on invalid URL (no exceptions)
sanitizeURLForHTML :: String -> Either String String
sanitizeURLForHTML url =
  let result = validateURL url CtxAsset
  in
  if result.valid
    then case result.sanitized of
      Just s -> Right (escapeHTML s)
      Nothing -> Left "URL validation passed but no sanitized URL returned"
    else Left (case result.error of
      Just e -> e
      Nothing -> "URL validation failed")

-- | Escape HTML special characters
escapeHTML :: String -> String
escapeHTML s = s
  # Str.replaceAll (Pattern "&") (Str.Replacement "&amp;")
  # Str.replaceAll (Pattern "<") (Str.Replacement "&lt;")
  # Str.replaceAll (Pattern ">") (Str.Replacement "&gt;")
  # Str.replaceAll (Pattern "\"") (Str.Replacement "&quot;")
  # Str.replaceAll (Pattern "'") (Str.Replacement "&#x27;")

-- ────────────────────────────────────────────────────────────────────────────
-- Trust Checking
-- ────────────────────────────────────────────────────────────────────────────

-- | Check if URL is from a trusted domain
isTrustedDomain :: String -> Array String -> Boolean
isTrustedDomain url trustedDomains =
  case parseHostname url of
    Nothing -> false
    Just hostname ->
      let normalizedHost = toLower hostname
      in any (\domain ->
        let normalizedDomain = toLower domain
        in normalizedHost == normalizedDomain
           || Str.contains (Pattern ("." <> normalizedDomain)) normalizedHost
      ) trustedDomains

-- | Extract and validate URLs from text content
extractAndValidateURLs :: String -> Array URLValidationResult
extractAndValidateURLs text =
  -- Simple URL extraction (https://, http://, data:)
  let urls = extractURLsFromText text
  in map (\u -> validateURL u CtxAsset) urls

-- ────────────────────────────────────────────────────────────────────────────
-- Internal Helpers
-- ────────────────────────────────────────────────────────────────────────────

-- | Create a blocked result
mkBlocked :: String -> String -> URLValidationResult
mkBlocked err proto =
  { valid: false
  , sanitized: Nothing
  , error: Just err
  , warning: Nothing
  , protocol: proto
  , riskLevel: RiskBlocked
  }

-- | Create a safe result
mkSafe :: String -> String -> URLValidationResult
mkSafe url proto =
  { valid: true
  , sanitized: Just url
  , error: Nothing
  , warning: Nothing
  , protocol: proto
  , riskLevel: RiskSafe
  }

-- | Create a warning result
mkWarning :: String -> String -> String -> URLValidationResult
mkWarning url proto warn =
  { valid: true
  , sanitized: Just url
  , error: Nothing
  , warning: Just warn
  , protocol: proto
  , riskLevel: RiskWarning
  }

-- | Find blocked protocol in URL
findBlockedProtocol :: String -> Maybe String
findBlockedProtocol url =
  let lowUrl = toLower url
      matched = filter (\p -> startsWith p lowUrl) blockedProtocols
  in Array.head matched

-- | Extract protocol from URL
extractProtocol :: String -> String
extractProtocol url =
  case indexOf (Pattern ":") url of
    Just idx ->
      let proto = Str.take (idx + 1) url
      in toLower proto
    Nothing -> "relative"

-- | Check if URL is relative
isRelativeURL :: String -> String -> Boolean
isRelativeURL url protocol =
  protocol == "relative"
  || startsWith "/" url
  || startsWith "./" url
  || startsWith "../" url

-- | Extract MIME type from data URL
extractMimeFromDataURL :: String -> String
extractMimeFromDataURL url =
  -- data:mime/type;base64,content or data:mime/type,content
  let afterData = Str.drop 5 url  -- Remove "data:"
  in case indexOf (Pattern ";") afterData of
    Just idx -> Str.take idx afterData
    Nothing -> case indexOf (Pattern ",") afterData of
      Just idx -> Str.take idx afterData
      Nothing -> "unknown"

-- | Parse hostname from URL
parseHostname :: String -> Maybe String
parseHostname url =
  -- Simple hostname extraction: protocol://hostname/path
  case indexOf (Pattern "://") url of
    Nothing -> Nothing
    Just protoEnd ->
      let afterProto = Str.drop (protoEnd + 3) url
          -- Find end of hostname (/, :, or end of string)
          endIdx = case indexOf (Pattern "/") afterProto of
            Just i -> i
            Nothing -> case indexOf (Pattern ":") afterProto of
              Just i -> i
              Nothing -> length afterProto
      in Just (Str.take endIdx afterProto)

-- | Extract URLs from text (simple implementation)
extractURLsFromText :: String -> Array String
extractURLsFromText text =
  -- Split by whitespace and filter for URL-like strings
  let words = Str.split (Pattern " ") text
      isURLLike w = startsWith "http://" (toLower w)
                 || startsWith "https://" (toLower w)
                 || startsWith "data:" (toLower w)
  in filter isURLLike words

-- | Check if string starts with prefix
startsWith :: String -> String -> Boolean
startsWith prefix str =
  Str.take (length prefix) str == prefix
