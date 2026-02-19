-- | Lattice.Schemas.Settings.ExportTemplateSchema - Export template validation
-- |
-- | Validates export templates stored in localStorage.
-- |
-- | Source: ui/src/schemas/settings/export-template-schema.ts

module Lattice.Schemas.Settings.ExportTemplateSchema
  ( -- Constants
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
    -- Export Template Config
  , ExportTemplateConfig
  , defaultExportTemplateConfig
    -- Export Template
  , ExportTemplate
  , validateExportTemplate
  , safeValidateExportTemplate
    -- Export Template Store
  , ExportTemplateStore
  , validateExportTemplateStore
  , safeValidateExportTemplateStore
  ) where

import Prelude
import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.String as String
import Data.Traversable (traverse_)

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

maxFPS :: Number
maxFPS = 120.0

maxTimestamp :: Int
maxTimestamp = 2147483647

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

maxCfgScale :: Number
maxCfgScale = 30.0

maxUrlLength :: Int
maxUrlLength = 2048

-- ────────────────────────────────────────────────────────────────────────────
-- Export Template Config
-- ────────────────────────────────────────────────────────────────────────────

-- | Partial export config for templates
type ExportTemplateConfig =
  { target :: Maybe ExportTarget
  , width :: Maybe Int
  , height :: Maybe Int
  , frameCount :: Maybe Int
  , fps :: Maybe Number
  , startFrame :: Maybe Int
  , endFrame :: Maybe Int
  , outputDir :: Maybe String
  , filenamePrefix :: Maybe String
  , exportDepthMap :: Maybe Boolean
  , exportControlImages :: Maybe Boolean
  , exportCameraData :: Maybe Boolean
  , exportReferenceFrame :: Maybe Boolean
  , exportLastFrame :: Maybe Boolean
  , depthFormat :: Maybe DepthMapFormat
  , controlType :: Maybe ControlType
  , prompt :: Maybe String
  , negativePrompt :: Maybe String
  , seed :: Maybe Int
  , steps :: Maybe Int
  , cfgScale :: Maybe Number
  , comfyuiServer :: Maybe String
  , autoQueueWorkflow :: Maybe Boolean
  , workflowTemplate :: Maybe String
  }

-- | Default export template config
defaultExportTemplateConfig :: ExportTemplateConfig
defaultExportTemplateConfig =
  { target: Nothing
  , width: Nothing
  , height: Nothing
  , frameCount: Nothing
  , fps: Nothing
  , startFrame: Nothing
  , endFrame: Nothing
  , outputDir: Nothing
  , filenamePrefix: Nothing
  , exportDepthMap: Nothing
  , exportControlImages: Nothing
  , exportCameraData: Nothing
  , exportReferenceFrame: Nothing
  , exportLastFrame: Nothing
  , depthFormat: Nothing
  , controlType: Nothing
  , prompt: Nothing
  , negativePrompt: Nothing
  , seed: Nothing
  , steps: Nothing
  , cfgScale: Nothing
  , comfyuiServer: Nothing
  , autoQueueWorkflow: Nothing
  , workflowTemplate: Nothing
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Export Template
-- ────────────────────────────────────────────────────────────────────────────

-- | Export template structure
type ExportTemplate =
  { id :: String
  , name :: String
  , description :: Maybe String
  , createdAt :: Int
  , modifiedAt :: Int
  , config :: ExportTemplateConfig
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Export Template Store
-- ────────────────────────────────────────────────────────────────────────────

-- | Export template store
type ExportTemplateStore =
  { templates :: Array ExportTemplate
  , lastUsedTemplateId :: Maybe String
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Validation
-- ────────────────────────────────────────────────────────────────────────────

-- | Validate ExportTemplateConfig
validateExportTemplateConfig :: ExportTemplateConfig -> Either ValidationError ExportTemplateConfig
validateExportTemplateConfig config = do
  -- Validate dimensions
  case config.width of
    Just w | w > maxDimension -> Left $ mkError "config.width" $
             "must be at most " <> show maxDimension
    _ -> pure unit

  case config.height of
    Just h | h > maxDimension -> Left $ mkError "config.height" $
             "must be at most " <> show maxDimension
    _ -> pure unit

  -- Validate frameCount
  case config.frameCount of
    Just fc | fc > maxFrames -> Left $ mkError "config.frameCount" $
              "must be at most " <> show maxFrames
    _ -> pure unit

  -- Validate startFrame/endFrame relationship
  case config.startFrame, config.endFrame of
    Just sf, Just ef | ef < sf -> Left $ mkError "config.endFrame" "must be >= startFrame"
    _, _ -> pure unit

  -- Validate string lengths
  case config.outputDir of
    Just od | String.length od > maxPathLength -> Left $ mkError "config.outputDir" $
              "must be at most " <> show maxPathLength <> " characters"
    _ -> pure unit

  case config.filenamePrefix of
    Just fp | String.length fp > maxFilenameLength -> Left $ mkError "config.filenamePrefix" $
              "must be at most " <> show maxFilenameLength <> " characters"
    _ -> pure unit

  case config.prompt of
    Just p | String.length p > maxPromptLength -> Left $ mkError "config.prompt" $
             "must be at most " <> show maxPromptLength <> " characters"
    _ -> pure unit

  case config.negativePrompt of
    Just np | String.length np > maxPromptLength -> Left $ mkError "config.negativePrompt" $
              "must be at most " <> show maxPromptLength <> " characters"
    _ -> pure unit

  -- Validate numeric limits
  case config.seed of
    Just s | s > maxSeed -> Left $ mkError "config.seed" $
             "must be at most " <> show maxSeed
    _ -> pure unit

  case config.steps of
    Just st | st > maxSteps -> Left $ mkError "config.steps" $
              "must be at most " <> show maxSteps
    _ -> pure unit

  pure config

-- | Validate ExportTemplate
validateExportTemplate :: ExportTemplate -> Either ValidationError ExportTemplate
validateExportTemplate template = do
  _ <- validateEntityId "id" template.id
  _ <- validateNonEmptyString "name" maxNameLength template.name

  -- Validate description
  case template.description of
    Just d | String.length d > maxDescriptionLength -> Left $ mkError "description" $
             "must be at most " <> show maxDescriptionLength <> " characters"
    _ -> pure unit

  -- Validate timestamps
  if template.createdAt > maxTimestamp
    then Left $ mkError "createdAt" $ "must be at most " <> show maxTimestamp
    else pure unit

  if template.modifiedAt > maxTimestamp
    then Left $ mkError "modifiedAt" $ "must be at most " <> show maxTimestamp
    else pure unit

  if template.modifiedAt < template.createdAt
    then Left $ mkError "modifiedAt" "must be >= createdAt"
    else pure unit

  _ <- validateExportTemplateConfig template.config
  pure template

-- | Safe validation
safeValidateExportTemplate :: ExportTemplate -> Maybe ExportTemplate
safeValidateExportTemplate template =
  case validateExportTemplate template of
    Right t -> Just t
    Left _ -> Nothing

-- | Validate ExportTemplateStore
validateExportTemplateStore :: ExportTemplateStore -> Either ValidationError ExportTemplateStore
validateExportTemplateStore store = do
  if Array.length store.templates > maxTemplates
    then Left $ mkError "templates" $ "must have at most " <> show maxTemplates <> " templates"
    else pure unit

  -- Validate all templates
  traverse_ validateExportTemplate store.templates

  -- Validate lastUsedTemplateId exists
  case store.lastUsedTemplateId of
    Just lastId ->
      if Array.any (\t -> t.id == lastId) store.templates
        then pure unit
        else Left $ mkError "lastUsedTemplateId" "must exist in templates array"
    Nothing -> pure unit

  pure store

-- | Safe validation
safeValidateExportTemplateStore :: ExportTemplateStore -> Maybe ExportTemplateStore
safeValidateExportTemplateStore store =
  case validateExportTemplateStore store of
    Right s -> Just s
    Left _ -> Nothing
