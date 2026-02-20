-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // lattice-server // Generate/Models
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- Model discovery and management for local diffusion models.
-- Supports ComfyUI-compatible extra_model_paths.yaml configuration.
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Generate.Models
    ( -- * Model Discovery
      discoverModels
    , discoverCategories
    , listModelsInCategory
    , findModel

      -- * Configuration
    , loadModelPaths
    , saveModelPaths
    , defaultModelPaths
    ) where

import Api.Generate (ModelInfo(..), ModelCategory(..), ModelPaths(..))
import Control.Exception (catch, SomeException)
import Control.Monad (forM)
import Data.Aeson (encode)
import qualified Data.Aeson as Aeson
import qualified Data.ByteString.Lazy as BSL
import Data.List (isSuffixOf)
import Data.Maybe (catMaybes)
import Data.Text (Text)
import qualified Data.Text as T
import System.Directory
import System.FilePath


-- ═══════════════════════════════════════════════════════════════════════════
-- // model discovery //
-- ═══════════════════════════════════════════════════════════════════════════

-- | Valid model file extensions
modelExtensions :: [String]
modelExtensions = [".safetensors", ".ckpt", ".pt", ".pth", ".bin", ".gguf"]

-- | Discover all models from configured paths
discoverModels :: ModelPaths -> IO [ModelInfo]
discoverModels paths = do
    let basePath = T.unpack (mpBasePath paths)

    -- Collect all category paths
    let categoryPaths =
            catMaybes
                [ ("checkpoints",) . T.unpack <$> mpCheckpoints paths
                , ("vae",) . T.unpack <$> mpVae paths
                , ("clip",) . T.unpack <$> mpClip paths
                , ("controlnet",) . T.unpack <$> mpControlnet paths
                , ("loras",) . T.unpack <$> mpLoras paths
                , ("embeddings",) . T.unpack <$> mpEmbeddings paths
                , ("diffusion_models",) . T.unpack <$> mpDiffusionModels paths
                , ("text_encoders",) . T.unpack <$> mpTextEncoders paths
                , ("upscale_models",) . T.unpack <$> mpUpscaleModels paths
                ]
            ++ [(T.unpack cat, T.unpack p) | (cat, p) <- mpCustomPaths paths]

    -- Discover models in each category
    models <- forM categoryPaths $ \(category, relPath) -> do
        let fullPath = basePath </> relPath
        exists <- doesDirectoryExist fullPath
        if exists
            then discoverModelsInDir (T.pack category) fullPath
            else pure []

    pure $ concat models


-- | Discover models in a specific directory (non-recursive for now)
discoverModelsInDir :: Text -> FilePath -> IO [ModelInfo]
discoverModelsInDir category dir = do
    entries <- listDirectory dir `catch` \(_ :: SomeException) -> pure []
    models <- forM entries $ \entry -> do
        let fullPath = dir </> entry
        isFile <- doesFileExist fullPath
        if isFile && isModelFile entry
            then Just <$> buildModelInfo category fullPath entry
            else pure Nothing
    pure $ catMaybes models
  where
    isModelFile name = any (`isSuffixOf` name) modelExtensions

-- | Build ModelInfo from file path
buildModelInfo :: Text -> FilePath -> String -> IO ModelInfo
buildModelInfo category fullPath name = do
    size <- getFileSizeSafe fullPath
    pure $ ModelInfo
        { miName = T.pack $ modelBaseName name
        , miPath = T.pack fullPath
        , miCategory = category
        , miFormat = T.pack $ modelExtension name
        , miSize = size
        , miHash = Nothing
        , miMetadata = Nothing
        }
  where
    modelBaseName n = takeBaseName n
    modelExtension n = drop 1 $ takeExtension n

-- | Get file size safely
getFileSizeSafe :: FilePath -> IO (Maybe Integer)
getFileSizeSafe path =
    (Just <$> System.Directory.getFileSize path)
        `catch` \(_ :: SomeException) -> pure Nothing


-- | Discover categories with model counts
discoverCategories :: ModelPaths -> IO [ModelCategory]
discoverCategories paths = do
    let basePath = T.unpack (mpBasePath paths)

    let categoryDefs =
            catMaybes
                [ mkCat "checkpoints" <$> mpCheckpoints paths
                , mkCat "vae" <$> mpVae paths
                , mkCat "clip" <$> mpClip paths
                , mkCat "controlnet" <$> mpControlnet paths
                , mkCat "loras" <$> mpLoras paths
                , mkCat "embeddings" <$> mpEmbeddings paths
                , mkCat "diffusion_models" <$> mpDiffusionModels paths
                , mkCat "text_encoders" <$> mpTextEncoders paths
                , mkCat "upscale_models" <$> mpUpscaleModels paths
                ]
            ++ [mkCat cat p | (cat, p) <- mpCustomPaths paths]

    forM categoryDefs $ \(catName, relPath) -> do
        let fullPath = basePath </> T.unpack relPath
        models <- discoverModelsInDir catName fullPath
        pure $ ModelCategory
            { mcName = catName
            , mcPath = T.pack fullPath
            , mcModels = take 10 models  -- Limit for category listing
            , mcCount = length models
            }
  where
    mkCat name path = (name, path)


-- | List models in a specific category
listModelsInCategory :: ModelPaths -> Text -> IO [ModelInfo]
listModelsInCategory paths category = do
    models <- discoverModels paths
    pure $ filter (\m -> miCategory m == category) models


-- | Find a model by name or path
findModel :: ModelPaths -> Text -> IO (Maybe ModelInfo)
findModel paths nameOrPath = do
    -- First try exact path
    let exactPath = T.unpack nameOrPath
    exists <- doesFileExist exactPath
    if exists
        then Just <$> buildModelInfo "unknown" exactPath (takeFileName exactPath)
        else do
            -- Search all models
            models <- discoverModels paths
            pure $ findByName models
  where
    findByName models =
        let nameMatch = filter (\m -> miName m == nameOrPath) models
            pathMatch = filter (\m -> miPath m == nameOrPath) models
         in case nameMatch of
                (m:_) -> Just m
                [] -> case pathMatch of
                    (m:_) -> Just m
                    [] -> Nothing


-- ═══════════════════════════════════════════════════════════════════════════
-- // configuration persistence //
-- ═══════════════════════════════════════════════════════════════════════════

-- | Default model paths (for development/testing)
defaultModelPaths :: ModelPaths
defaultModelPaths = ModelPaths
    { mpBasePath = "/mnt/d"  -- WSL path to Windows D: drive
    , mpCheckpoints = Just "models/checkpoints"
    , mpVae = Just "models/vae"
    , mpClip = Just "models/clip"
    , mpControlnet = Just "models/controlnet"
    , mpLoras = Just "models/loras"
    , mpEmbeddings = Just "models/embeddings"
    , mpDiffusionModels = Just "models/diffusion_models"
    , mpTextEncoders = Just "models/text_encoders"
    , mpUpscaleModels = Just "models/upscale_models"
    , mpCustomPaths = []
    }


-- | Load model paths from config file
loadModelPaths :: FilePath -> IO ModelPaths
loadModelPaths configDir = do
    let configPath = configDir </> "model_paths.json"
    exists <- doesFileExist configPath
    if exists
        then do
            result <- Aeson.eitherDecodeFileStrict configPath
            case result of
                Right paths -> pure paths
                Left _ -> pure defaultModelPaths
        else pure defaultModelPaths


-- | Save model paths to config file
saveModelPaths :: FilePath -> ModelPaths -> IO ()
saveModelPaths configDir paths = do
    createDirectoryIfMissing True configDir
    let configPath = configDir </> "model_paths.json"
    BSL.writeFile configPath (encode paths)
