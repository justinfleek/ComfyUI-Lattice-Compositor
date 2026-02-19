{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Lattice.Schemas.Settings.ExportTemplateSchema
Description : Export template validation
Copyright   : (c) Lattice, 2026
License     : MIT

Validates export templates stored in localStorage.

Source: ui/src/schemas/settings/export-template-schema.ts
-}

module Lattice.Schemas.Settings.ExportTemplateSchema
  ( -- * Constants
    maxDimension
  , maxFrames
  , maxFPS
  , maxTimestamp
  , maxTemplates
  , maxPathLength
  , maxFilenameLength
  , maxPromptLength
  , maxSeed
  , maxSteps
  , maxCfgScale
  , maxUrlLength
    -- * Export Template Config
  , ExportTemplateConfig(..)
  , defaultExportTemplateConfig
    -- * Export Template
  , ExportTemplate(..)
  , validateExportTemplate
  , safeValidateExportTemplate
    -- * Export Template Store
  , ExportTemplateStore(..)
  , validateExportTemplateStore
  , safeValidateExportTemplateStore
  ) where

import GHC.Generics (Generic)
import Data.Text (Text, pack)
import qualified Data.Text as T
import Data.Maybe (isJust)

import Lattice.Schemas.SharedValidation
  ( ValidationError, mkError
  , maxNameLength, maxDescriptionLength
  , validateEntityId, validateNonEmptyString
  )
import Lattice.Schemas.ComfyUI.Targets
  ( ExportTarget, DepthMapFormat, ControlType )

-- ────────────────────────────────────────────────────────────────────────────
-- Constants
-- ────────────────────────────────────────────────────────────────────────────

maxDimension :: Int
maxDimension = 16384

maxFrames :: Int
maxFrames = 100000

maxFPS :: Double
maxFPS = 120.0

maxTimestamp :: Int
maxTimestamp = 2147483647000

maxTemplates :: Int
maxTemplates = 1000

maxPathLength :: Int
maxPathLength = 500

maxFilenameLength :: Int
maxFilenameLength = 255

maxPromptLength :: Int
maxPromptLength = 10000

maxSeed :: Int
maxSeed = 2147483647

maxSteps :: Int
maxSteps = 1000

maxCfgScale :: Double
maxCfgScale = 30.0

maxUrlLength :: Int
maxUrlLength = 2048

-- ────────────────────────────────────────────────────────────────────────────
-- Export Template Config
-- ────────────────────────────────────────────────────────────────────────────

-- | Partial export config for templates
data ExportTemplateConfig = ExportTemplateConfig
  { etcTarget :: !(Maybe ExportTarget)
  , etcWidth :: !(Maybe Int)
  , etcHeight :: !(Maybe Int)
  , etcFrameCount :: !(Maybe Int)
  , etcFps :: !(Maybe Double)
  , etcStartFrame :: !(Maybe Int)
  , etcEndFrame :: !(Maybe Int)
  , etcOutputDir :: !(Maybe Text)
  , etcFilenamePrefix :: !(Maybe Text)
  , etcExportDepthMap :: !(Maybe Bool)
  , etcExportControlImages :: !(Maybe Bool)
  , etcExportCameraData :: !(Maybe Bool)
  , etcExportReferenceFrame :: !(Maybe Bool)
  , etcExportLastFrame :: !(Maybe Bool)
  , etcDepthFormat :: !(Maybe DepthMapFormat)
  , etcControlType :: !(Maybe ControlType)
  , etcPrompt :: !(Maybe Text)
  , etcNegativePrompt :: !(Maybe Text)
  , etcSeed :: !(Maybe Int)
  , etcSteps :: !(Maybe Int)
  , etcCfgScale :: !(Maybe Double)
  , etcComfyuiServer :: !(Maybe Text)
  , etcAutoQueueWorkflow :: !(Maybe Bool)
  , etcWorkflowTemplate :: !(Maybe Text)
  }
  deriving stock (Eq, Show, Generic)

-- | Default export template config
defaultExportTemplateConfig :: ExportTemplateConfig
defaultExportTemplateConfig = ExportTemplateConfig
  { etcTarget = Nothing
  , etcWidth = Nothing
  , etcHeight = Nothing
  , etcFrameCount = Nothing
  , etcFps = Nothing
  , etcStartFrame = Nothing
  , etcEndFrame = Nothing
  , etcOutputDir = Nothing
  , etcFilenamePrefix = Nothing
  , etcExportDepthMap = Nothing
  , etcExportControlImages = Nothing
  , etcExportCameraData = Nothing
  , etcExportReferenceFrame = Nothing
  , etcExportLastFrame = Nothing
  , etcDepthFormat = Nothing
  , etcControlType = Nothing
  , etcPrompt = Nothing
  , etcNegativePrompt = Nothing
  , etcSeed = Nothing
  , etcSteps = Nothing
  , etcCfgScale = Nothing
  , etcComfyuiServer = Nothing
  , etcAutoQueueWorkflow = Nothing
  , etcWorkflowTemplate = Nothing
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Export Template
-- ────────────────────────────────────────────────────────────────────────────

-- | Export template structure
data ExportTemplate = ExportTemplate
  { etId :: !Text
  , etName :: !Text
  , etDescription :: !(Maybe Text)
  , etCreatedAt :: !Int
  , etModifiedAt :: !Int
  , etConfig :: !ExportTemplateConfig
  }
  deriving stock (Eq, Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Export Template Store
-- ────────────────────────────────────────────────────────────────────────────

-- | Export template store
data ExportTemplateStore = ExportTemplateStore
  { etsTemplates :: ![ExportTemplate]
  , etsLastUsedTemplateId :: !(Maybe Text)
  }
  deriving stock (Eq, Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Validation
-- ────────────────────────────────────────────────────────────────────────────

-- | Validate ExportTemplateConfig
validateExportTemplateConfig :: ExportTemplateConfig -> Either ValidationError ExportTemplateConfig
validateExportTemplateConfig config = do
  -- Validate dimensions
  case etcWidth config of
    Just w | w > maxDimension -> Left $ mkError "config.width" $
             "must be at most " <> pack (show maxDimension)
    _ -> Right ()

  case etcHeight config of
    Just h | h > maxDimension -> Left $ mkError "config.height" $
             "must be at most " <> pack (show maxDimension)
    _ -> Right ()

  -- Validate frameCount
  case etcFrameCount config of
    Just fc | fc > maxFrames -> Left $ mkError "config.frameCount" $
              "must be at most " <> pack (show maxFrames)
    _ -> Right ()

  -- Validate startFrame/endFrame relationship
  case (etcStartFrame config, etcEndFrame config) of
    (Just sf, Just ef) | ef < sf -> Left $ mkError "config.endFrame" "must be >= startFrame"
    _ -> Right ()

  -- Validate string lengths
  case etcOutputDir config of
    Just od | T.length od > maxPathLength -> Left $ mkError "config.outputDir" $
              "must be at most " <> pack (show maxPathLength) <> " characters"
    _ -> Right ()

  case etcFilenamePrefix config of
    Just fp | T.length fp > maxFilenameLength -> Left $ mkError "config.filenamePrefix" $
              "must be at most " <> pack (show maxFilenameLength) <> " characters"
    _ -> Right ()

  case etcPrompt config of
    Just p | T.length p > maxPromptLength -> Left $ mkError "config.prompt" $
             "must be at most " <> pack (show maxPromptLength) <> " characters"
    _ -> Right ()

  case etcNegativePrompt config of
    Just np | T.length np > maxPromptLength -> Left $ mkError "config.negativePrompt" $
              "must be at most " <> pack (show maxPromptLength) <> " characters"
    _ -> Right ()

  -- Validate numeric limits
  case etcSeed config of
    Just s | s > maxSeed -> Left $ mkError "config.seed" $
             "must be at most " <> pack (show maxSeed)
    _ -> Right ()

  case etcSteps config of
    Just st | st > maxSteps -> Left $ mkError "config.steps" $
              "must be at most " <> pack (show maxSteps)
    _ -> Right ()

  Right config

-- | Validate ExportTemplate
validateExportTemplate :: ExportTemplate -> Either ValidationError ExportTemplate
validateExportTemplate template = do
  _ <- validateEntityId "id" (etId template)
  _ <- validateNonEmptyString "name" maxNameLength (etName template)

  -- Validate description
  case etDescription template of
    Just d | T.length d > maxDescriptionLength -> Left $ mkError "description" $
             "must be at most " <> pack (show maxDescriptionLength) <> " characters"
    _ -> Right ()

  -- Validate timestamps
  if etCreatedAt template > maxTimestamp
    then Left $ mkError "createdAt" $ "must be at most " <> pack (show maxTimestamp)
    else Right ()

  if etModifiedAt template > maxTimestamp
    then Left $ mkError "modifiedAt" $ "must be at most " <> pack (show maxTimestamp)
    else Right ()

  if etModifiedAt template < etCreatedAt template
    then Left $ mkError "modifiedAt" "must be >= createdAt"
    else Right ()

  _ <- validateExportTemplateConfig (etConfig template)
  Right template

-- | Safe validation
safeValidateExportTemplate :: ExportTemplate -> Maybe ExportTemplate
safeValidateExportTemplate template =
  case validateExportTemplate template of
    Right t -> Just t
    Left _ -> Nothing

-- | Validate ExportTemplateStore
validateExportTemplateStore :: ExportTemplateStore -> Either ValidationError ExportTemplateStore
validateExportTemplateStore store = do
  if length (etsTemplates store) > maxTemplates
    then Left $ mkError "templates" $ "must have at most " <> pack (show maxTemplates) <> " templates"
    else Right ()

  -- Validate all templates
  mapM_ validateExportTemplate (etsTemplates store)

  -- Validate lastUsedTemplateId exists
  case etsLastUsedTemplateId store of
    Just lastId ->
      if any (\t -> etId t == lastId) (etsTemplates store)
        then Right ()
        else Left $ mkError "lastUsedTemplateId" "must exist in templates array"
    Nothing -> Right ()

  Right store

-- | Safe validation
safeValidateExportTemplateStore :: ExportTemplateStore -> Maybe ExportTemplateStore
safeValidateExportTemplateStore store =
  case validateExportTemplateStore store of
    Right s -> Just s
    Left _ -> Nothing
