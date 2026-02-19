-- | Lattice.Schemas.Settings.ExportTemplateSchema - Project template validation
-- |
-- | Validates project templates stored in localStorage for the standalone compositor.
-- | Templates allow users to save and share preset configurations including:
-- | - Composition settings (dimensions, fps, duration)
-- | - Render settings (quality, format, codec)
-- | - Generation parameters (prompts, models for AI generation)
-- | - Layer presets and effect chains
-- |
-- | Note: This is for the STANDALONE compositor. ComfyUI integration uses
-- | separate schemas in the comfyui-integration package.

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
    -- Export Target
  , ExportTarget(..)
  , exportTargetFromString
  , exportTargetToString
    -- Output Format
  , OutputFormat(..)
  , outputFormatFromString
  , outputFormatToString
    -- Codec
  , VideoCodec(..)
  , videoCodecFromString
  , videoCodecToString
    -- Quality Level
  , QualityLevel(..)
  , qualityLevelFromString
  , qualityLevelToString
    -- Export Template Config
  , ExportTemplateConfig
  , defaultExportTemplateConfig
    -- Render Settings
  , RenderSettings
  , defaultRenderSettings
    -- Generation Settings
  , GenerationSettings
  , defaultGenerationSettings
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
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..))
import Data.Show.Generic (genericShow)
import Data.String as String
import Data.Traversable (traverse_)

import Lattice.Schemas.SharedValidation
  ( ValidationError, mkError
  , maxNameLength, maxDescriptionLength
  , validateEntityId, validateNonEmptyString
  )

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
-- Export Target
-- ────────────────────────────────────────────────────────────────────────────

-- | Export target for rendered output
data ExportTarget
  = TargetLocal        -- Export to local filesystem
  | TargetBridge       -- Send to Haskell bridge for processing
  | TargetClipboard    -- Copy to clipboard (single frame)
  | TargetPreview      -- Preview only (no file output)

derive instance Eq ExportTarget
derive instance Generic ExportTarget _

instance Show ExportTarget where
  show = genericShow

exportTargetFromString :: String -> Maybe ExportTarget
exportTargetFromString = case _ of
  "local" -> Just TargetLocal
  "bridge" -> Just TargetBridge
  "clipboard" -> Just TargetClipboard
  "preview" -> Just TargetPreview
  _ -> Nothing

exportTargetToString :: ExportTarget -> String
exportTargetToString = case _ of
  TargetLocal -> "local"
  TargetBridge -> "bridge"
  TargetClipboard -> "clipboard"
  TargetPreview -> "preview"

-- ────────────────────────────────────────────────────────────────────────────
-- Output Format
-- ────────────────────────────────────────────────────────────────────────────

-- | Output format for export
data OutputFormat
  = FormatPNG          -- PNG sequence
  | FormatJPEG         -- JPEG sequence
  | FormatWebP         -- WebP sequence
  | FormatMP4          -- MP4 video
  | FormatWebM         -- WebM video
  | FormatGIF          -- Animated GIF
  | FormatAPNG         -- Animated PNG

derive instance Eq OutputFormat
derive instance Generic OutputFormat _

instance Show OutputFormat where
  show = genericShow

outputFormatFromString :: String -> Maybe OutputFormat
outputFormatFromString = case _ of
  "png" -> Just FormatPNG
  "jpeg" -> Just FormatJPEG
  "jpg" -> Just FormatJPEG
  "webp" -> Just FormatWebP
  "mp4" -> Just FormatMP4
  "webm" -> Just FormatWebM
  "gif" -> Just FormatGIF
  "apng" -> Just FormatAPNG
  _ -> Nothing

outputFormatToString :: OutputFormat -> String
outputFormatToString = case _ of
  FormatPNG -> "png"
  FormatJPEG -> "jpeg"
  FormatWebP -> "webp"
  FormatMP4 -> "mp4"
  FormatWebM -> "webm"
  FormatGIF -> "gif"
  FormatAPNG -> "apng"

-- ────────────────────────────────────────────────────────────────────────────
-- Video Codec
-- ────────────────────────────────────────────────────────────────────────────

-- | Video codec for video exports
data VideoCodec
  = CodecH264          -- H.264 / AVC
  | CodecH265          -- H.265 / HEVC
  | CodecVP9           -- VP9 (WebM)
  | CodecAV1           -- AV1
  | CodecProRes        -- Apple ProRes

derive instance Eq VideoCodec
derive instance Generic VideoCodec _

instance Show VideoCodec where
  show = genericShow

videoCodecFromString :: String -> Maybe VideoCodec
videoCodecFromString = case _ of
  "h264" -> Just CodecH264
  "h265" -> Just CodecH265
  "hevc" -> Just CodecH265
  "vp9" -> Just CodecVP9
  "av1" -> Just CodecAV1
  "prores" -> Just CodecProRes
  _ -> Nothing

videoCodecToString :: VideoCodec -> String
videoCodecToString = case _ of
  CodecH264 -> "h264"
  CodecH265 -> "h265"
  CodecVP9 -> "vp9"
  CodecAV1 -> "av1"
  CodecProRes -> "prores"

-- ────────────────────────────────────────────────────────────────────────────
-- Quality Level
-- ────────────────────────────────────────────────────────────────────────────

-- | Quality level for rendering
data QualityLevel
  = QualityDraft       -- Fast preview, lower quality
  | QualityNormal      -- Balanced quality/speed
  | QualityHigh        -- High quality, slower
  | QualityFinal       -- Maximum quality for final export

derive instance Eq QualityLevel
derive instance Generic QualityLevel _

instance Show QualityLevel where
  show = genericShow

qualityLevelFromString :: String -> Maybe QualityLevel
qualityLevelFromString = case _ of
  "draft" -> Just QualityDraft
  "normal" -> Just QualityNormal
  "high" -> Just QualityHigh
  "final" -> Just QualityFinal
  _ -> Nothing

qualityLevelToString :: QualityLevel -> String
qualityLevelToString = case _ of
  QualityDraft -> "draft"
  QualityNormal -> "normal"
  QualityHigh -> "high"
  QualityFinal -> "final"

-- ────────────────────────────────────────────────────────────────────────────
-- Render Settings
-- ────────────────────────────────────────────────────────────────────────────

-- | Render output settings
type RenderSettings =
  { format :: Maybe OutputFormat
  , codec :: Maybe VideoCodec
  , quality :: Maybe QualityLevel
  , bitrate :: Maybe Int           -- kbps for video
  , crf :: Maybe Int               -- Constant rate factor (0-51)
  , pixelFormat :: Maybe String    -- yuv420p, yuv444p, etc.
  , includeAudio :: Maybe Boolean
  , loopCount :: Maybe Int         -- For GIF/APNG (0 = infinite)
  }

-- | Default render settings
defaultRenderSettings :: RenderSettings
defaultRenderSettings =
  { format: Nothing
  , codec: Nothing
  , quality: Nothing
  , bitrate: Nothing
  , crf: Nothing
  , pixelFormat: Nothing
  , includeAudio: Nothing
  , loopCount: Nothing
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Generation Settings (for AI/Bridge calls)
-- ────────────────────────────────────────────────────────────────────────────

-- | AI generation settings for Bridge API
type GenerationSettings =
  { prompt :: Maybe String
  , negativePrompt :: Maybe String
  , seed :: Maybe Int
  , steps :: Maybe Int
  , cfgScale :: Maybe Number
  , model :: Maybe String          -- Model identifier
  , scheduler :: Maybe String      -- Scheduler type
  , denoisingStrength :: Maybe Number  -- 0.0-1.0
  , controlStrength :: Maybe Number    -- 0.0-1.0 for control inputs
  }

-- | Default generation settings
defaultGenerationSettings :: GenerationSettings
defaultGenerationSettings =
  { prompt: Nothing
  , negativePrompt: Nothing
  , seed: Nothing
  , steps: Nothing
  , cfgScale: Nothing
  , model: Nothing
  , scheduler: Nothing
  , denoisingStrength: Nothing
  , controlStrength: Nothing
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Export Template Config
-- ────────────────────────────────────────────────────────────────────────────

-- | Partial export config for templates (all fields optional for flexibility)
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
  , render :: RenderSettings
  , generation :: GenerationSettings
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
  , render: defaultRenderSettings
  , generation: defaultGenerationSettings
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
  , tags :: Array String           -- For categorization
  , isDefault :: Boolean           -- System default template
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

-- | Validate RenderSettings
validateRenderSettings :: RenderSettings -> Either ValidationError RenderSettings
validateRenderSettings settings = do
  -- Validate bitrate if present
  case settings.bitrate of
    Just br | br <= 0 -> Left $ mkError "render.bitrate" "must be positive"
    Just br | br > 500000 -> Left $ mkError "render.bitrate" "must be at most 500000 kbps"
    _ -> pure unit

  -- Validate CRF if present
  case settings.crf of
    Just c | c < 0 -> Left $ mkError "render.crf" "must be non-negative"
    Just c | c > 51 -> Left $ mkError "render.crf" "must be at most 51"
    _ -> pure unit

  -- Validate loopCount if present
  case settings.loopCount of
    Just lc | lc < 0 -> Left $ mkError "render.loopCount" "must be non-negative"
    _ -> pure unit

  pure settings

-- | Validate GenerationSettings
validateGenerationSettings :: GenerationSettings -> Either ValidationError GenerationSettings
validateGenerationSettings settings = do
  -- Validate prompt length
  case settings.prompt of
    Just p | String.length p > maxPromptLength -> Left $ mkError "generation.prompt" $
             "must be at most " <> show maxPromptLength <> " characters"
    _ -> pure unit

  -- Validate negativePrompt length
  case settings.negativePrompt of
    Just np | String.length np > maxPromptLength -> Left $ mkError "generation.negativePrompt" $
              "must be at most " <> show maxPromptLength <> " characters"
    _ -> pure unit

  -- Validate seed
  case settings.seed of
    Just s | s < 0 -> Left $ mkError "generation.seed" "must be non-negative"
    Just s | s > maxSeed -> Left $ mkError "generation.seed" $
             "must be at most " <> show maxSeed
    _ -> pure unit

  -- Validate steps
  case settings.steps of
    Just st | st <= 0 -> Left $ mkError "generation.steps" "must be positive"
    Just st | st > maxSteps -> Left $ mkError "generation.steps" $
              "must be at most " <> show maxSteps
    _ -> pure unit

  -- Validate cfgScale
  case settings.cfgScale of
    Just cfg | cfg < 0.0 -> Left $ mkError "generation.cfgScale" "must be non-negative"
    Just cfg | cfg > maxCfgScale -> Left $ mkError "generation.cfgScale" $
               "must be at most " <> show maxCfgScale
    _ -> pure unit

  -- Validate denoisingStrength (0-1)
  case settings.denoisingStrength of
    Just ds | ds < 0.0 || ds > 1.0 -> Left $ mkError "generation.denoisingStrength"
              "must be between 0.0 and 1.0"
    _ -> pure unit

  -- Validate controlStrength (0-1)
  case settings.controlStrength of
    Just cs | cs < 0.0 || cs > 1.0 -> Left $ mkError "generation.controlStrength"
              "must be between 0.0 and 1.0"
    _ -> pure unit

  pure settings

-- | Validate ExportTemplateConfig
validateExportTemplateConfig :: ExportTemplateConfig -> Either ValidationError ExportTemplateConfig
validateExportTemplateConfig config = do
  -- Validate dimensions
  case config.width of
    Just w | w <= 0 -> Left $ mkError "config.width" "must be positive"
    Just w | w > maxDimension -> Left $ mkError "config.width" $
             "must be at most " <> show maxDimension
    _ -> pure unit

  case config.height of
    Just h | h <= 0 -> Left $ mkError "config.height" "must be positive"
    Just h | h > maxDimension -> Left $ mkError "config.height" $
             "must be at most " <> show maxDimension
    _ -> pure unit

  -- Validate frameCount
  case config.frameCount of
    Just fc | fc <= 0 -> Left $ mkError "config.frameCount" "must be positive"
    Just fc | fc > maxFrames -> Left $ mkError "config.frameCount" $
              "must be at most " <> show maxFrames
    _ -> pure unit

  -- Validate fps
  case config.fps of
    Just f | f <= 0.0 -> Left $ mkError "config.fps" "must be positive"
    Just f | f > maxFPS -> Left $ mkError "config.fps" $
             "must be at most " <> show maxFPS
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

  -- Validate nested settings
  _ <- validateRenderSettings config.render
  _ <- validateGenerationSettings config.generation

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
  if template.createdAt < 0
    then Left $ mkError "createdAt" "must be non-negative"
    else pure unit

  if template.createdAt > maxTimestamp
    then Left $ mkError "createdAt" $ "must be at most " <> show maxTimestamp
    else pure unit

  if template.modifiedAt < 0
    then Left $ mkError "modifiedAt" "must be non-negative"
    else pure unit

  if template.modifiedAt > maxTimestamp
    then Left $ mkError "modifiedAt" $ "must be at most " <> show maxTimestamp
    else pure unit

  if template.modifiedAt < template.createdAt
    then Left $ mkError "modifiedAt" "must be >= createdAt"
    else pure unit

  -- Validate tags count
  if Array.length template.tags > 50
    then Left $ mkError "tags" "must have at most 50 tags"
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
