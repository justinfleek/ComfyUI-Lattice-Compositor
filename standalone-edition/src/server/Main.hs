{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}

{-|
Module      : Main
Description : Lattice HTTP REST API Server
Copyright   : (c) Lattice, 2026
License     : MIT

HTTP server implementing the Lattice Render API with AI generation endpoints.
Conforms to specs/render.openapi.yaml.

Run: cabal run lattice-server -- --port 8080
-}

module Main where

import Data.Aeson (ToJSON(..), FromJSON(..), (.=), (.:), (.:?), object, encode, decode, withObject)
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Base64 as B64
import qualified Data.ByteString.Lazy as BSL
import Data.IORef
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Data.Word (Word8, Word32)
import Network.HTTP.Types
import Network.Wai
import Network.Wai.Handler.Warp
import System.Environment (getArgs)
import System.Random (randomRIO)

-- Import Lattice services for actual rendering
import Lattice.Services.Noise.SimplexNoise (simplexNoise2D, fbm)

-- Import generation modules
import Api.Generate
import Generate.Models

-- ────────────────────────────────────────────────────────────────────────────
-- Configuration
-- ────────────────────────────────────────────────────────────────────────────

data ServerConfig = ServerConfig
  { scPort :: Int
  , scHost :: String
  } deriving (Eq, Show)

defaultConfig :: ServerConfig
defaultConfig = ServerConfig
  { scPort = 8080
  , scHost = "127.0.0.1"
  }

parseArgs :: [String] -> ServerConfig
parseArgs = go defaultConfig
  where
    go cfg [] = cfg
    go cfg ("--port":p:rest) = go cfg { scPort = read p } rest
    go cfg ("--host":h:rest) = go cfg { scHost = h } rest
    go cfg (_:rest) = go cfg rest

-- ────────────────────────────────────────────────────────────────────────────
-- Request/Response Types (matching OpenAPI spec)
-- ────────────────────────────────────────────────────────────────────────────

data RenderFrameRequest = RenderFrameRequest
  { rfrWidth :: Int
  , rfrHeight :: Int
  , rfrFrame :: Maybe Int
  , rfrShader :: Maybe Text
  } deriving (Eq, Show)

instance FromJSON RenderFrameRequest where
  parseJSON = withObject "RenderFrameRequest" $ \v ->
    RenderFrameRequest
      <$> v .: "width"
      <*> v .: "height"
      <*> v .:? "frame"
      <*> v .:? "shader"

data RenderFrameResponse = RenderFrameResponse
  { rfrRespWidth :: Int
  , rfrRespHeight :: Int
  , rfrRespFormat :: Text
  , rfrRespData :: Text  -- Base64 encoded
  } deriving (Eq, Show)

instance ToJSON RenderFrameResponse where
  toJSON r = object
    [ "width" .= rfrRespWidth r
    , "height" .= rfrRespHeight r
    , "format" .= rfrRespFormat r
    , "data" .= rfrRespData r
    ]

data RenderPreviewRequest = RenderPreviewRequest
  { rpWidth :: Int
  , rpHeight :: Int
  , rpQuality :: Maybe Double
  } deriving (Eq, Show)

instance FromJSON RenderPreviewRequest where
  parseJSON = withObject "RenderPreviewRequest" $ \v ->
    RenderPreviewRequest
      <$> v .: "width"
      <*> v .: "height"
      <*> v .:? "quality"

data RenderPreviewResponse = RenderPreviewResponse
  { rpRespThumbnail :: Text
  , rpRespWidth :: Int
  , rpRespHeight :: Int
  } deriving (Eq, Show)

instance ToJSON RenderPreviewResponse where
  toJSON r = object
    [ "thumbnail" .= rpRespThumbnail r
    , "width" .= rpRespWidth r
    , "height" .= rpRespHeight r
    ]

data RenderDepthRequest = RenderDepthRequest
  { rdWidth :: Int
  , rdHeight :: Int
  , rdNear :: Maybe Double
  , rdFar :: Maybe Double
  } deriving (Eq, Show)

instance FromJSON RenderDepthRequest where
  parseJSON = withObject "RenderDepthRequest" $ \v ->
    RenderDepthRequest
      <$> v .: "width"
      <*> v .: "height"
      <*> v .:? "near"
      <*> v .:? "far"

data DepthBuffer = DepthBuffer
  { dbWidth :: Int
  , dbHeight :: Int
  , dbData :: [Double]
  , dbMin :: Double
  , dbMax :: Double
  } deriving (Eq, Show)

instance ToJSON DepthBuffer where
  toJSON d = object
    [ "width" .= dbWidth d
    , "height" .= dbHeight d
    , "data" .= dbData d
    , "min" .= dbMin d
    , "max" .= dbMax d
    ]

data Codec = Codec
  { codecId :: Text
  , codecName :: Text
  , codecContainer :: Text
  , codecHardware :: Bool
  } deriving (Eq, Show)

instance ToJSON Codec where
  toJSON c = object
    [ "id" .= codecId c
    , "name" .= codecName c
    , "container" .= codecContainer c
    , "hardware" .= codecHardware c
    ]

data HealthResponse = HealthResponse
  { hrStatus :: Text
  , hrVersion :: Text
  } deriving (Eq, Show)

instance ToJSON HealthResponse where
  toJSON h = object
    [ "status" .= hrStatus h
    , "version" .= hrVersion h
    ]

data ErrorResponse = ErrorResponse
  { errError :: Text
  , errCode :: Maybe Text
  } deriving (Eq, Show)

instance ToJSON ErrorResponse where
  toJSON e = object $
    [ "error" .= errError e ] <>
    maybe [] (\c -> ["code" .= c]) (errCode e)

-- ────────────────────────────────────────────────────────────────────────────
-- Application
-- ────────────────────────────────────────────────────────────────────────────

-- | Create the application with model path configuration
mkApp :: IORef ModelPaths -> Application
mkApp modelPathsRef req respond = do
  let path = pathInfo req
      method = requestMethod req
  
  case (method, path) of
    -- Health check
    ("GET", ["health"]) ->
      respond $ jsonResponse status200 $ HealthResponse "healthy" "1.0.0"
    
    -- ────────────────────────────────────────────────────────────────────────
    -- Generation endpoints
    -- ────────────────────────────────────────────────────────────────────────
    
    -- List all available models
    ("GET", ["generate", "models"]) -> do
      modelPaths <- readIORef modelPathsRef
      let categoryFilter = lookup "category" (queryString req) >>= id >>= (pure . TE.decodeUtf8)
      let searchFilter = lookup "search" (queryString req) >>= id >>= (pure . TE.decodeUtf8)
      models <- case categoryFilter of
        Just cat -> listModelsInCategory modelPaths cat
        Nothing -> discoverModels modelPaths
      let filteredModels = case searchFilter of
            Just search -> filter (\m -> T.toLower search `T.isInfixOf` T.toLower (miName m)) models
            Nothing -> models
      respond $ jsonResponse status200 filteredModels
    
    -- List model categories with counts
    ("GET", ["generate", "models", "categories"]) -> do
      modelPaths <- readIORef modelPathsRef
      categories <- discoverCategories modelPaths
      respond $ jsonResponse status200 categories
    
    -- Get model paths configuration
    ("GET", ["generate", "config"]) -> do
      modelPaths <- readIORef modelPathsRef
      respond $ jsonResponse status200 modelPaths
    
    -- Update model paths configuration
    ("PATCH", ["generate", "config"]) -> do
      body <- strictRequestBody req
      case decode body of
        Nothing -> respond $ jsonResponse status400 $
          ErrorResponse "Invalid request body" (Just "PARSE_ERROR")
        Just newPaths -> do
          writeIORef modelPathsRef newPaths
          respond $ jsonResponse status200 newPaths
    
    -- Generate image (placeholder - needs inference backend)
    ("POST", ["generate", "image"]) -> do
      body <- strictRequestBody req
      case decode body of
        Nothing -> respond $ jsonResponse status400 $
          ErrorResponse "Invalid request body" (Just "PARSE_ERROR")
        Just (cfg :: GenerateConfig) -> do
          -- For now, return a placeholder response
          -- The actual implementation requires a TensorRT inference backend
          respond $ jsonResponse status200 $ GenerateResult
            { grSuccess = False
            , grFrames = []
            , grError = Just "Inference backend not yet implemented. Model loaded from: N/A"
            , grSeed = maybe 0 id (gcSeed cfg)
            , grTimeTaken = 0
            , grModel = gcModel cfg
            }
    
    -- Generate video (placeholder - needs inference backend)
    ("POST", ["generate", "video"]) -> do
      body <- strictRequestBody req
      case decode body of
        Nothing -> respond $ jsonResponse status400 $
          ErrorResponse "Invalid request body" (Just "PARSE_ERROR")
        Just (cfg :: GenerateConfig) -> do
          respond $ jsonResponse status200 $ GenerateResult
            { grSuccess = False
            , grFrames = []
            , grError = Just "Video inference backend not yet implemented"
            , grSeed = maybe 0 id (gcSeed cfg)
            , grTimeTaken = 0
            , grModel = gcModel cfg
            }
    
    -- ────────────────────────────────────────────────────────────────────────
    -- Render endpoints
    -- ────────────────────────────────────────────────────────────────────────
    
    -- Render frame
    ("POST", ["render", "frame"]) -> do
      body <- strictRequestBody req
      case decode body of
        Nothing -> respond $ jsonResponse status400 $
          ErrorResponse "Invalid request body" (Just "PARSE_ERROR")
        Just reqBody -> do
          frameData <- generateFrame (rfrWidth reqBody) (rfrHeight reqBody)
          respond $ jsonResponse status200 $ RenderFrameResponse
            { rfrRespWidth = rfrWidth reqBody
            , rfrRespHeight = rfrHeight reqBody
            , rfrRespFormat = "rgba8"
            , rfrRespData = TE.decodeUtf8 $ B64.encode frameData
            }
    
    -- Render preview
    ("POST", ["render", "preview"]) -> do
      body <- strictRequestBody req
      case decode body of
        Nothing -> respond $ jsonResponse status400 $
          ErrorResponse "Invalid request body" (Just "PARSE_ERROR")
        Just reqBody -> do
          thumbData <- generatePreview (rpWidth reqBody) (rpHeight reqBody)
          respond $ jsonResponse status200 $ RenderPreviewResponse
            { rpRespThumbnail = TE.decodeUtf8 $ B64.encode thumbData
            , rpRespWidth = rpWidth reqBody
            , rpRespHeight = rpHeight reqBody
            }
    
    -- Render depth
    ("POST", ["render", "depth"]) -> do
      body <- strictRequestBody req
      case decode body of
        Nothing -> respond $ jsonResponse status400 $
          ErrorResponse "Invalid request body" (Just "PARSE_ERROR")
        Just reqBody -> do
          depthBuf <- generateDepth (rdWidth reqBody) (rdHeight reqBody)
          respond $ jsonResponse status200 depthBuf
    
    -- ────────────────────────────────────────────────────────────────────────
    -- Export endpoints
    -- ────────────────────────────────────────────────────────────────────────
    
    -- Export codecs
    ("GET", ["export", "codecs"]) ->
      respond $ jsonResponse status200 $ object
        [ "codecs" .= supportedCodecs ]
    
    -- Export encode (stub - returns success)
    ("POST", ["export", "encode"]) ->
      respond $ jsonResponse status200 $ object
        [ "success" .= True
        , "frameIndex" .= (0 :: Int)
        ]
    
    -- Export finalize (stub)
    ("POST", ["export", "finalize"]) ->
      respond $ jsonResponse status200 $ object
        [ "downloadUrl" .= ("http://localhost:8080/download/export.mp4" :: Text)
        , "size" .= (1024 :: Int)
        ]
    
    -- 404 for unknown routes
    _ -> respond $ jsonResponse status404 $
      ErrorResponse "Not found" (Just "NOT_FOUND")

-- | Legacy app without model path ref (for backward compatibility)
app :: Application
app = mkApp (error "Model paths not initialized")

jsonResponse :: ToJSON a => Status -> a -> Response
jsonResponse status body =
  responseLBS status
    [ (hContentType, "application/json")
    , ("Access-Control-Allow-Origin", "*")
    ]
    (encode body)

-- ────────────────────────────────────────────────────────────────────────────
-- Rendering Functions (using actual Lattice services)
-- ────────────────────────────────────────────────────────────────────────────

-- | Generate a frame using simplex noise
generateFrame :: Int -> Int -> IO ByteString
generateFrame width height = do
  seed <- randomRIO (0, maxBound :: Word32)
  let pixels = [generatePixel seed x y | y <- [0..height-1], x <- [0..width-1]]
  pure $ BS.pack $ concatMap pixelToRGBA pixels
  where
    generatePixel :: Word32 -> Int -> Int -> (Word8, Word8, Word8, Word8)
    generatePixel seed x y =
      let fx = fromIntegral x / fromIntegral width
          fy = fromIntegral y / fromIntegral height
          -- Use simplex noise for color
          r = simplexNoise2D (fx * 4) (fy * 4) seed
          g = simplexNoise2D (fx * 4 + 100) (fy * 4) seed
          b = simplexNoise2D (fx * 4) (fy * 4 + 100) seed
      in ( toWord8 r
         , toWord8 g
         , toWord8 b
         , 255  -- Alpha
         )
    
    toWord8 :: Double -> Word8
    toWord8 d = floor (d * 255)
    
    pixelToRGBA (r, g, b, a) = [r, g, b, a]

-- | Generate a preview thumbnail
generatePreview :: Int -> Int -> IO ByteString
generatePreview = generateFrame  -- Same as frame for now

-- | Generate a depth buffer using noise
generateDepth :: Int -> Int -> IO DepthBuffer
generateDepth width height = do
  seed <- randomRIO (0, maxBound :: Word32)
  let depths = [fbm (fromIntegral x / fromIntegral width * 2)
                    (fromIntegral y / fromIntegral height * 2)
                    seed 4 0.5 2.0
               | y <- [0..height-1], x <- [0..width-1]]
      minD = minimum depths
      maxD = maximum depths
  pure $ DepthBuffer width height depths minD maxD

-- | Supported video codecs
supportedCodecs :: [Codec]
supportedCodecs =
  [ Codec "avc1.42001f" "H.264 Baseline" "mp4" False
  , Codec "avc1.4d001f" "H.264 Main" "mp4" False
  , Codec "avc1.64001f" "H.264 High" "mp4" True
  , Codec "vp09.00.10.08" "VP9" "webm" False
  ]

-- ────────────────────────────────────────────────────────────────────────────
-- Main
-- ────────────────────────────────────────────────────────────────────────────

main :: IO ()
main = do
  args <- getArgs
  let cfg = parseArgs args
  
  -- Initialize model paths
  modelPathsRef <- newIORef defaultModelPaths
  
  putStrLn $ "Starting Lattice Server on " <> scHost cfg <> ":" <> show (scPort cfg)
  putStrLn ""
  putStrLn "Model Directory: /mnt/d/models"
  putStrLn ""
  putStrLn "Endpoints:"
  putStrLn "  GET  /health                    - Health check"
  putStrLn ""
  putStrLn "  Generation:"
  putStrLn "  GET  /generate/models           - List available models"
  putStrLn "  GET  /generate/models/categories- List model categories"
  putStrLn "  GET  /generate/config           - Get model paths config"
  putStrLn "  PATCH /generate/config          - Update model paths config"
  putStrLn "  POST /generate/image            - Generate image (WIP)"
  putStrLn "  POST /generate/video            - Generate video (WIP)"
  putStrLn ""
  putStrLn "  Render:"
  putStrLn "  POST /render/frame              - Render frame"
  putStrLn "  POST /render/preview            - Render preview"
  putStrLn "  POST /render/depth              - Render depth map"
  putStrLn ""
  putStrLn "  Export:"
  putStrLn "  GET  /export/codecs             - List supported codecs"
  putStrLn "  POST /export/encode             - Encode frame"
  putStrLn "  POST /export/finalize           - Finalize export"
  putStrLn ""
  run (scPort cfg) (mkApp modelPathsRef)
