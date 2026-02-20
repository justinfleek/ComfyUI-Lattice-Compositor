-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // lattice-server // Api/Generate
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- API types for AI image/video generation using local diffusion models.
-- Supports ComfyUI-compatible model directories and extra_model_paths.yaml.
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

module Api.Generate
    ( -- * Request/Response Types
      GenerateConfig(..)
    , GenerateResult(..)
    , GenerateProgress(..)
    , ModelInfo(..)
    , ModelCategory(..)
    , ModelPaths(..)
    ) where

import Data.Aeson
import Data.Text (Text)
import GHC.Generics (Generic)


-- ═══════════════════════════════════════════════════════════════════════════
-- // request/response types //
-- ═══════════════════════════════════════════════════════════════════════════

-- | Configuration for image/video generation
data GenerateConfig = GenerateConfig
    { gcPrompt :: Text
    , gcNegativePrompt :: Maybe Text
    , gcWidth :: Int
    , gcHeight :: Int
    , gcNumFrames :: Maybe Int          -- For video generation
    , gcFps :: Maybe Double             -- For video generation
    , gcModel :: Text                   -- Model identifier (path or name)
    , gcSeed :: Maybe Int
    , gcSteps :: Maybe Int
    , gcCfgScale :: Maybe Double
    , gcControlnetImage :: Maybe Text   -- Base64 encoded control image
    , gcControlnetType :: Maybe Text    -- "depth", "canny", "pose", etc.
    , gcControlnetStrength :: Maybe Double
    , gcVae :: Maybe Text               -- Optional VAE override
    , gcClip :: Maybe Text              -- Optional CLIP model
    , gcSampler :: Maybe Text           -- Sampler name
    , gcScheduler :: Maybe Text         -- Scheduler name
    } deriving (Eq, Show, Generic)

instance FromJSON GenerateConfig where
    parseJSON = withObject "GenerateConfig" $ \v -> GenerateConfig
        <$> v .: "prompt"
        <*> v .:? "negativePrompt"
        <*> v .:? "width" .!= 1024
        <*> v .:? "height" .!= 1024
        <*> v .:? "numFrames"
        <*> v .:? "fps"
        <*> v .: "model"
        <*> v .:? "seed"
        <*> v .:? "steps" .!= Just 20
        <*> v .:? "cfgScale" .!= Just 7.0
        <*> v .:? "controlnetImage"
        <*> v .:? "controlnetType"
        <*> v .:? "controlnetStrength"
        <*> v .:? "vae"
        <*> v .:? "clip"
        <*> v .:? "sampler"
        <*> v .:? "scheduler"

instance ToJSON GenerateConfig where
    toJSON gc = object
        [ "prompt" .= gcPrompt gc
        , "negativePrompt" .= gcNegativePrompt gc
        , "width" .= gcWidth gc
        , "height" .= gcHeight gc
        , "numFrames" .= gcNumFrames gc
        , "fps" .= gcFps gc
        , "model" .= gcModel gc
        , "seed" .= gcSeed gc
        , "steps" .= gcSteps gc
        , "cfgScale" .= gcCfgScale gc
        , "controlnetImage" .= gcControlnetImage gc
        , "controlnetType" .= gcControlnetType gc
        , "controlnetStrength" .= gcControlnetStrength gc
        , "vae" .= gcVae gc
        , "clip" .= gcClip gc
        , "sampler" .= gcSampler gc
        , "scheduler" .= gcScheduler gc
        ]


-- | Result from generation
data GenerateResult = GenerateResult
    { grSuccess :: Bool
    , grFrames :: [Text]                -- Base64 encoded frames
    , grError :: Maybe Text
    , grSeed :: Int                     -- Actual seed used
    , grTimeTaken :: Double             -- Milliseconds
    , grModel :: Text                   -- Model used
    } deriving (Eq, Show, Generic)

instance ToJSON GenerateResult where
    toJSON gr = object
        [ "success" .= grSuccess gr
        , "frames" .= grFrames gr
        , "error" .= grError gr
        , "seed" .= grSeed gr
        , "timeTaken" .= grTimeTaken gr
        , "model" .= grModel gr
        ]

instance FromJSON GenerateResult where
    parseJSON = withObject "GenerateResult" $ \v -> GenerateResult
        <$> v .: "success"
        <*> v .:? "frames" .!= []
        <*> v .:? "error"
        <*> v .:? "seed" .!= 0
        <*> v .:? "timeTaken" .!= 0
        <*> v .:? "model" .!= ""


-- | Progress update during generation
data GenerateProgress = GenerateProgress
    { gpStep :: Int                     -- Current step (0-indexed)
    , gpTotalSteps :: Int               -- Total steps
    , gpStage :: Text                   -- "encoding" | "sampling" | "decoding"
    , gpPercentage :: Double            -- 0.0 to 100.0
    , gpEta :: Maybe Double             -- Estimated seconds remaining
    , gpPreviewFrame :: Maybe Text      -- Optional preview (base64)
    } deriving (Eq, Show, Generic)

instance ToJSON GenerateProgress where
    toJSON gp = object
        [ "step" .= gpStep gp
        , "totalSteps" .= gpTotalSteps gp
        , "stage" .= gpStage gp
        , "percentage" .= gpPercentage gp
        , "eta" .= gpEta gp
        , "previewFrame" .= gpPreviewFrame gp
        ]


-- | Information about an available model
data ModelInfo = ModelInfo
    { miName :: Text                    -- Display name
    , miPath :: Text                    -- Full path to model file
    , miCategory :: Text                -- Category (checkpoints, loras, vae, etc.)
    , miFormat :: Text                  -- File format (safetensors, ckpt, etc.)
    , miSize :: Maybe Integer           -- File size in bytes
    , miHash :: Maybe Text              -- SHA256 hash (if available)
    , miMetadata :: Maybe Value         -- Parsed .metadata.json if exists
    } deriving (Eq, Show, Generic)

instance ToJSON ModelInfo where
    toJSON mi = object
        [ "name" .= miName mi
        , "path" .= miPath mi
        , "category" .= miCategory mi
        , "format" .= miFormat mi
        , "size" .= miSize mi
        , "hash" .= miHash mi
        , "metadata" .= miMetadata mi
        ]


-- | Model category with available models
data ModelCategory = ModelCategory
    { mcName :: Text                    -- Category name
    , mcPath :: Text                    -- Directory path
    , mcModels :: [ModelInfo]           -- Available models
    , mcCount :: Int                    -- Total count
    } deriving (Eq, Show, Generic)

instance ToJSON ModelCategory where
    toJSON mc = object
        [ "name" .= mcName mc
        , "path" .= mcPath mc
        , "models" .= mcModels mc
        , "count" .= mcCount mc
        ]


-- | Model paths configuration (ComfyUI extra_model_paths.yaml compatible)
data ModelPaths = ModelPaths
    { mpBasePath :: Text
    , mpCheckpoints :: Maybe Text
    , mpVae :: Maybe Text
    , mpClip :: Maybe Text
    , mpControlnet :: Maybe Text
    , mpLoras :: Maybe Text
    , mpEmbeddings :: Maybe Text
    , mpDiffusionModels :: Maybe Text
    , mpTextEncoders :: Maybe Text
    , mpUpscaleModels :: Maybe Text
    , mpCustomPaths :: [(Text, Text)]   -- Additional category -> path mappings
    } deriving (Eq, Show, Generic)

instance ToJSON ModelPaths where
    toJSON mp = object
        [ "basePath" .= mpBasePath mp
        , "checkpoints" .= mpCheckpoints mp
        , "vae" .= mpVae mp
        , "clip" .= mpClip mp
        , "controlnet" .= mpControlnet mp
        , "loras" .= mpLoras mp
        , "embeddings" .= mpEmbeddings mp
        , "diffusionModels" .= mpDiffusionModels mp
        , "textEncoders" .= mpTextEncoders mp
        , "upscaleModels" .= mpUpscaleModels mp
        , "customPaths" .= mpCustomPaths mp
        ]

instance FromJSON ModelPaths where
    parseJSON = withObject "ModelPaths" $ \v -> ModelPaths
        <$> v .: "basePath"
        <*> v .:? "checkpoints"
        <*> v .:? "vae"
        <*> v .:? "clip"
        <*> v .:? "controlnet"
        <*> v .:? "loras"
        <*> v .:? "embeddings"
        <*> v .:? "diffusionModels"
        <*> v .:? "textEncoders"
        <*> v .:? "upscaleModels"
        <*> v .:? "customPaths" .!= []
