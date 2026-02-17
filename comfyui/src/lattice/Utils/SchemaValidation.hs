-- |
-- Module      : Lattice.Utils.SchemaValidation
-- Description : Schema validation security utilities
--
-- Migrated from ui/src/utils/schemaValidation.ts (pure parts)
-- SECURITY: Prototype pollution prevention, path/string sanitization
-- No forbidden patterns; errors as Either Text a.
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.Utils.SchemaValidation
  ( -- Options
    SafeParseOptions(..)
  , defaultSafeParseOptions
  -- Dangerous keys
  , dangerousKeys
  , isDangerousKey
  -- Error codes
  , SafeParseErrorCode(..)
  -- String sanitization
  , sanitizeString
  , SanitizeStringOptions(..)
  , defaultSanitizeStringOptions
  , sanitizeFilename
  , looksLikeMaliciousPayload
  ) where

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import Text.Regex.TDFA ((=~))

-- ============================================================================
-- OPTIONS
-- ============================================================================

data SafeParseOptions = SafeParseOptions
  { safeParseMaxDepth        :: Int
  , safeParseMaxSize         :: Int
  , safeParseMaxStringLength :: Int
  , safeParseMaxArrayLength  :: Int
  , safeParseContext         :: Text
  }
  deriving (Eq, Show)

-- | Default: depth 100, 50MB, 1MB string, 100k array, context "JSON"
defaultSafeParseOptions :: SafeParseOptions
defaultSafeParseOptions = SafeParseOptions
  { safeParseMaxDepth        = 100
  , safeParseMaxSize         = 50 * 1024 * 1024
  , safeParseMaxStringLength = 1024 * 1024
  , safeParseMaxArrayLength  = 100000
  , safeParseContext         = "JSON"
  }

-- ============================================================================
-- DANGEROUS KEYS (prototype pollution)
-- ============================================================================

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

isDangerousKey :: Text -> Bool
isDangerousKey k = Set.member k dangerousKeys

-- ============================================================================
-- ERROR CODES
-- ============================================================================

data SafeParseErrorCode
  = ParseError
  | SizeExceeded
  | DepthExceeded
  | StringLengthExceeded
  | ArrayLengthExceeded
  | PrototypePollution
  | SchemaValidation
  | Unknown
  deriving (Eq, Show, Enum, Bounded)

-- ============================================================================
-- STRING SANITIZATION OPTIONS
-- ============================================================================

data SanitizeStringOptions = SanitizeStringOptions
  { sanitizeMaxLength      :: Int
  , sanitizeAllowNewlines  :: Bool
  , sanitizeNormalizeUnicode :: Bool
  }
  deriving (Eq, Show)

defaultSanitizeStringOptions :: SanitizeStringOptions
defaultSanitizeStringOptions = SanitizeStringOptions
  { sanitizeMaxLength        = 10000
  , sanitizeAllowNewlines   = True
  , sanitizeNormalizeUnicode = True
  }

-- | Remove null bytes from Text
stripNulls :: Text -> Text
stripNulls = T.filter (/= '\0')

-- | Remove Unicode direction overrides (U+202A–202E, U+2066–2069)
stripDirectionOverrides :: Text -> Text
stripDirectionOverrides = T.filter (\c ->
  let n = fromEnum c
  in not (n >= 0x202A && n <= 0x202E || n >= 0x2066 && n <= 0x2069))

-- | Keep printable chars; if allowNewlines, keep tab and newline
stripControlChars' :: Bool -> Text -> Text
stripControlChars' allowNewlines =
  T.filter (\c ->
    let n = fromEnum c
    in (n >= 0x20 && n /= 0x7F) || (allowNewlines && (n == 9 || n == 10)))

-- | Normalize runs of spaces/tabs to single space
normalizeSpaces :: Text -> Text
normalizeSpaces = T.unwords . T.words

-- | Trim and take at most n characters
trimAndTake :: Int -> Text -> Text
trimAndTake n = T.take n . T.strip

sanitizeString :: SanitizeStringOptions -> Text -> Text
sanitizeString opts input =
  let step1 = stripNulls input
      step2 = stripDirectionOverrides step1
      step3 = stripControlChars' (sanitizeAllowNewlines opts) step2
      step4 = if sanitizeAllowNewlines opts then step3 else normalizeSpaces step3
      step5 = T.strip step4
      step6 = trimAndTake (sanitizeMaxLength opts) step5
      -- Unicode NFC: use Data.Text.Encoding or text-icu; avoid for portability
  in step6

-- | Sanitize filename: no path sep, no control chars, no "..", no leading dot, max 200 (+ ext)
sanitizeFilename :: Text -> Text
sanitizeFilename filename =
  let step1 = T.map (\c -> if c == '/' || c == '\\' then '_' else c) filename
      step2 = stripNulls step1
      shellMeta = ";&|`$(){}[]<>!#*?\"'"
      step3 = T.map (\c -> if T.any (== c) (T.pack shellMeta) then '_' else c) step2
      step4 = T.filter (\c -> let n = fromEnum c in n >= 0x20 && n /= 0x7F) step3
      step5 = T.replace ".." "_" step4
      step6 = if T.isPrefixOf "." step5 then "_" <> T.drop 1 step5 else step5
      (base, ext) = case T.breakOnEnd "." step6 of
        (b, e) | T.null e -> (step6, "")
               | otherwise -> (T.dropEnd (T.length e) step6, e)
      limited = if T.length step6 > 200
                then T.take (200 - T.length ext) base <> ext
                else step6
      final = if T.null limited || limited == "_" then "unnamed" else limited
  in final

-- | Heuristic: does value look like an injection payload?
looksLikeMaliciousPayload :: Text -> Bool
looksLikeMaliciousPayload value =
  let s = T.unpack value
  in  s =~ ("<script" :: String)
  ||  s =~ ("javascript:" :: String)
  ||  s =~ ("on[a-zA-Z0-9_]+\\s*=" :: String)
  ||  s =~ ("'\\s*or\\s+'1'\\s*=\\s*'1" :: String)
  ||  s =~ (";\\s*drop\\s+table" :: String)
  ||  s =~ (";\\s*delete\\s+from" :: String)
  ||  s =~ (";\\s*rm\\s+-rf" :: String)
  ||  s =~ ("\\|\\s*cat\\s+" :: String)
  ||  s =~ ("`[^`]*`" :: String)
  ||  s =~ ("\\.\\./" :: String)
  ||  s =~ ("\\.\\\\.*" :: String)
  ||  s =~ ("\\$\\{[^}]+\\}" :: String)
  ||  s =~ ("%[A-Za-z_]+%" :: String)
  ||  s =~ ("^[A-Za-z0-9+/]{50,}={0,2}$" :: String)
