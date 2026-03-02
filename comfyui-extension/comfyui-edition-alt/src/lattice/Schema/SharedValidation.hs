-- |
-- Module      : Lattice.Schema.SharedValidation
-- Description : Shared validation functions for schema validation
-- 
-- Migrated from ui/src/schemas/shared-validation.ts
-- Provides validation functions matching Zod schema patterns
-- Used for validating data at runtime boundaries (FFI, JSON parsing)
--
-- All validation functions return Either Text a (success or error message)

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}

module Lattice.Schema.SharedValidation
  ( -- Validation constants
    maxNameLength
  , maxDescriptionLength
  , maxCommentLength
  , maxTagLength
  , maxTagsCount
  , maxPathLength
  , maxIdLength
  , maxMimeTypeLength
  , maxFontFamilyLength
  , maxFontStyleLength
  , maxUrlLength
  , maxBase64Length
  , maxShaderLength
  , maxFilenameLength
  , maxAnimationNameLength
  , maxWarningLength
    -- Configurable limits (with defaults)
  , ValidationLimits(..)
  , defaultValidationLimits
  , initValidationLimits
  , updateLimits
  , getLimits
  , getMaxDimension
  , getMaxDimensionPure
  , getMaxFrameCount
  , getMaxFrameCountPure
  , getMaxArrayLength
  , getMaxArrayLengthPure
  , getMaxParticles
  , getMaxParticlesPure
  , getMaxLayers
  , getMaxLayersPure
  , getMaxKeyframesPerProperty
  , getMaxKeyframesPerPropertyPure
  , getMaxStringLength
  , getMaxStringLengthPure
  , getMaxFPS
  , getMaxFPSPure
    -- Validation functions
  , validateNonEmptyString
  , validateIso8601DateTime
  , validateBase64OrDataUrl
  , validateMimeType
  , validateHexColor
  , validateEntityId
  , validatePropertyPath
  , validateFilename
  , validateUrl
  , validateShaderCode
  , validateBoundedArray
  , validateNonEmptyArray
  , validateJsonSerializable
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import Data.Aeson (Value(..), encode, eitherDecode)
import qualified Data.ByteString.Lazy as BL
import Text.Regex.TDFA ((=~))
import Control.Monad (void)
import Control.Concurrent.MVar (MVar, newMVar, readMVar, swapMVar)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                   // validation // constants
-- ════════════════════════════════════════════════════════════════════════════

maxNameLength :: Int
maxNameLength = 200

maxDescriptionLength :: Int
maxDescriptionLength = 2000

maxCommentLength :: Int
maxCommentLength = 5000

maxTagLength :: Int
maxTagLength = 50

maxTagsCount :: Int
maxTagsCount = 50

maxPathLength :: Int
maxPathLength = 500

maxIdLength :: Int
maxIdLength = 200

maxMimeTypeLength :: Int
maxMimeTypeLength = 100

maxFontFamilyLength :: Int
maxFontFamilyLength = 200

maxFontStyleLength :: Int
maxFontStyleLength = 100

maxUrlLength :: Int
maxUrlLength = 2048

maxBase64Length :: Int
maxBase64Length = 50 * 1024 * 1024  -- 50MB

maxShaderLength :: Int
maxShaderLength = 100000

maxFilenameLength :: Int
maxFilenameLength = 255

maxAnimationNameLength :: Int
maxAnimationNameLength = 100

maxWarningLength :: Int
maxWarningLength = 500

-- ════════════════════════════════════════════════════════════════════════════
--                                                    // configurable // limits
-- ════════════════════════════════════════════════════════════════════════════

data ValidationLimits = ValidationLimits
  { limitsMaxDimension :: Int
  , limitsMaxFrameCount :: Int
  , limitsMaxArrayLength :: Int
  , limitsMaxParticles :: Int
  , limitsMaxLayers :: Int
  , limitsMaxKeyframesPerProperty :: Int
  , limitsMaxStringLength :: Int
  , limitsMaxFPS :: Int
  }
  deriving (Eq, Show)

defaultValidationLimits :: ValidationLimits
defaultValidationLimits = ValidationLimits
  { limitsMaxDimension = 8192
  , limitsMaxFrameCount = 10000
  , limitsMaxArrayLength = 100000
  , limitsMaxParticles = 1000000
  , limitsMaxLayers = 1000
  , limitsMaxKeyframesPerProperty = 10000
  , limitsMaxStringLength = 100000
  , limitsMaxFPS = 120
  }

-- | Initialize validation limits MVar (call once at startup)
-- Must be called before any validation functions that use limits
initValidationLimits :: IO (MVar ValidationLimits)
initValidationLimits = newMVar defaultValidationLimits

-- | Update validation limits (called from TypeScript store)
updateLimits :: MVar ValidationLimits -> ValidationLimits -> IO ()
updateLimits limits newVal = void (swapMVar limits newVal)

-- | Get current validation limits
getLimits :: MVar ValidationLimits -> IO ValidationLimits
getLimits = readMVar

-- | Get max dimension (pure version - accepts limits as parameter)
getMaxDimensionPure :: ValidationLimits -> Int
getMaxDimensionPure = limitsMaxDimension

-- | Get max dimension (IO version - reads from MVar)
getMaxDimension :: MVar ValidationLimits -> IO Int
getMaxDimension limits = limitsMaxDimension <$> readMVar limits

-- | Get max frame count (pure version)
getMaxFrameCountPure :: ValidationLimits -> Int
getMaxFrameCountPure = limitsMaxFrameCount

-- | Get max frame count (IO version)
getMaxFrameCount :: MVar ValidationLimits -> IO Int
getMaxFrameCount limits = limitsMaxFrameCount <$> readMVar limits

-- | Get max array length (pure version)
getMaxArrayLengthPure :: ValidationLimits -> Int
getMaxArrayLengthPure = limitsMaxArrayLength

-- | Get max array length (IO version)
getMaxArrayLength :: MVar ValidationLimits -> IO Int
getMaxArrayLength limits = limitsMaxArrayLength <$> readMVar limits

-- | Get max particles (pure version)
getMaxParticlesPure :: ValidationLimits -> Int
getMaxParticlesPure = limitsMaxParticles

-- | Get max particles (IO version)
getMaxParticles :: MVar ValidationLimits -> IO Int
getMaxParticles limits = limitsMaxParticles <$> readMVar limits

-- | Get max layers (pure version)
getMaxLayersPure :: ValidationLimits -> Int
getMaxLayersPure = limitsMaxLayers

-- | Get max layers (IO version)
getMaxLayers :: MVar ValidationLimits -> IO Int
getMaxLayers limits = limitsMaxLayers <$> readMVar limits

-- | Get max keyframes per property (pure version)
getMaxKeyframesPerPropertyPure :: ValidationLimits -> Int
getMaxKeyframesPerPropertyPure = limitsMaxKeyframesPerProperty

-- | Get max keyframes per property (IO version)
getMaxKeyframesPerProperty :: MVar ValidationLimits -> IO Int
getMaxKeyframesPerProperty limits = limitsMaxKeyframesPerProperty <$> readMVar limits

-- | Get max string length (pure version)
getMaxStringLengthPure :: ValidationLimits -> Int
getMaxStringLengthPure = limitsMaxStringLength

-- | Get max string length (IO version)
getMaxStringLength :: MVar ValidationLimits -> IO Int
getMaxStringLength limits = limitsMaxStringLength <$> readMVar limits

-- | Get max FPS (pure version)
getMaxFPSPure :: ValidationLimits -> Int
getMaxFPSPure = limitsMaxFPS

-- | Get max FPS (IO version)
getMaxFPS :: MVar ValidationLimits -> IO Int
getMaxFPS limits = limitsMaxFPS <$> readMVar limits

-- ════════════════════════════════════════════════════════════════════════════
--                                                   // validation // functions
-- ════════════════════════════════════════════════════════════════════════════

-- | Validate non-empty string with max length and trimming
validateNonEmptyString :: Int -> Text -> Either Text Text
validateNonEmptyString maxLen str =
  let trimmed = T.strip str
  in if T.null trimmed
    then Left "String cannot be empty"
    else if T.length trimmed > maxLen
      then Left ("String must be at most " <> T.pack (show maxLen) <> " characters")
      else Right trimmed

-- | Validate ISO 8601 datetime string
validateIso8601DateTime :: Text -> Either Text Text
validateIso8601DateTime str =
  -- Basic ISO 8601 pattern: YYYY-MM-DDTHH:mm:ss.sssZ or YYYY-MM-DDTHH:mm:ssZ
  if str =~ ("^[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}(\\.[0-9]{1,3})?Z?$" :: String)
    then Right str
    else Left "Must be valid ISO 8601 datetime string"

-- | Validate base64 or data URL string
validateBase64OrDataUrl :: Text -> Either Text Text
validateBase64OrDataUrl str =
  if T.length str > maxBase64Length
    then Left "Base64/data URL exceeds maximum length"
    else if T.isPrefixOf "data:" str
      then validateDataUrl str
      else validateBase64 str
  where
    validateDataUrl :: Text -> Either Text Text
    validateDataUrl urlStr =
      case T.findIndex (== ',') urlStr of
        Nothing -> Left "Data URL must contain comma separator"
        Just idx ->
          let header = T.take idx urlStr
              dataPart = T.drop (idx + 1) urlStr
          in if T.isInfixOf "base64" header || not (T.null dataPart)
            then Right urlStr
            else Left "Data URL must have base64 encoding or non-empty data"
    
    validateBase64 :: Text -> Either Text Text
    validateBase64 str' =
      if str' =~ ("^[A-Za-z0-9+/=]+$" :: String)
        then Right str'
        else Left "Must be valid base64 or data URL"

-- | Validate MIME type
validateMimeType :: Text -> Either Text Text
validateMimeType str =
  if T.length str > maxMimeTypeLength
    then Left ("MIME type must be at most " <> T.pack (show maxMimeTypeLength) <> " characters")
    else if str =~ ("^[a-z][a-z0-9]*/[a-z0-9][a-z0-9._-]*$" :: String)
      then Right str
      else Left "Must be valid MIME type (e.g., 'image/png', 'video/mp4')"

-- | Validate hex color string (#RRGGBB or #RRGGBBAA)
validateHexColor :: Text -> Either Text Text
validateHexColor str =
  if str =~ ("^#([0-9A-Fa-f]{6}|[0-9A-Fa-f]{8})$" :: String)
    then Right str
    else Left "Must be valid hex color (#RRGGBB or #RRGGBBAA)"

-- | Validate entity ID format (alphanumeric with underscores/hyphens)
validateEntityId :: Text -> Either Text Text
validateEntityId str =
  if T.null str
    then Left "Entity ID cannot be empty"
    else if T.length str > maxIdLength
      then Left ("Entity ID must be at most " <> T.pack (show maxIdLength) <> " characters")
      else if str =~ ("^[a-zA-Z0-9_-]+$" :: String)
        then Right str
        else Left "Must be valid ID format (alphanumeric, underscores, hyphens only)"

-- | Validate property path (e.g., "data.text", "transform.position.x")
validatePropertyPath :: Text -> Either Text Text
validatePropertyPath str =
  if T.length str > maxPathLength
    then Left ("Property path must be at most " <> T.pack (show maxPathLength) <> " characters")
    else if str =~ ("^[a-zA-Z_$][a-zA-Z0-9_$.]*(\\.[a-zA-Z_$][a-zA-Z0-9_$.]*)*$" :: String)
      then Right str
      else Left "Must be valid property path (e.g., 'data.text', 'transform.position.x')"

-- | Validate filename
validateFilename :: Text -> Either Text Text
validateFilename str =
  if T.length str > maxFilenameLength
    then Left ("Filename must be at most " <> T.pack (show maxFilenameLength) <> " characters")
    else if str =~ ("[<>:\"|?*\\x00-\\x1F]" :: String)
      then Left "Filename contains invalid characters"
    else if T.isSuffixOf "." str || T.isSuffixOf " " str
      then Left "Filename cannot end with dot or space"
      else Right str

-- | Validate URL
validateUrl :: Text -> Either Text Text
validateUrl str =
  if T.length str > maxUrlLength
    then Left ("URL must be at most " <> T.pack (show maxUrlLength) <> " characters")
    else if T.isPrefixOf "http://" str || T.isPrefixOf "https://" str
      then Right str
      else Left "Must be valid URL"

-- | Validate shader code (check for dangerous patterns)
validateShaderCode :: Text -> Either Text Text
validateShaderCode str =
  if T.length str > maxShaderLength
    then Left ("Shader code must be at most " <> T.pack (show maxShaderLength) <> " characters")
    else checkDangerousPatterns str
  where
    dangerousPatterns :: [String]
    dangerousPatterns =
      [ "eval\\s*\\("
      , "Function\\s*\\("
      , "require\\s*\\("
      , "import\\s*\\("
      , "process\\."
      , "fetch\\s*\\("
      , "XMLHttpRequest"
      , "WebSocket"
      , "document\\."
      , "window\\."
      ]
    
    checkDangerousPatterns :: Text -> Either Text Text
    checkDangerousPatterns code =
      if any (\pattern -> code =~ pattern) dangerousPatterns
        then Left "Shader code contains potentially dangerous patterns"
        else Right code

-- | Validate bounded array (with max length)
validateBoundedArray :: Int -> [a] -> Either Text [a]
validateBoundedArray maxLen arr =
  if length arr > maxLen
    then Left ("Array must have at most " <> T.pack (show maxLen) <> " items")
    else Right arr

-- | Validate non-empty array
validateNonEmptyArray :: [a] -> Either Text [a]
validateNonEmptyArray arr =
  if null arr
    then Left "Array cannot be empty"
    else Right arr

-- | Validate JSON-serializable value
validateJsonSerializable :: Value -> Either Text Value
validateJsonSerializable val =
  case eitherDecode (encode val) :: Either String Value of
    Left err -> Left ("Value must be JSON-serializable: " <> T.pack err)
    Right _ -> Right val
