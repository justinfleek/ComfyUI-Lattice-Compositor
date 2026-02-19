{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-|
Module      : Lattice.Services.Bridge.Handlers.Export
Description : Video export handler using FFmpeg
Copyright   : (c) Lattice, 2026
License     : MIT

Replaces browser WebCodecs with server-side video encoding via FFmpeg.
Uses ffmpeg-light for Haskell bindings.

Key operations:
- Video encoding (H.264, H.265, VP9, AV1)
- Frame sequence to video
- ZIP archive creation
- Blob download
-}

module Lattice.Services.Bridge.Handlers.Export
  ( handleExportOp
  , exportHandler
  , ExportContext(..)
  , initExport
  , disposeExport
  ) where

import Codec.FFmpeg
import Codec.FFmpeg.Encode
import Codec.FFmpeg.Types
import Codec.Picture (Image, PixelRGBA8(..), generateImage)
import Codec.Archive.Zip
import Control.Concurrent.MVar
import Control.Exception (try, SomeException, bracket)
import Control.Monad (forM_, when)
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as LBS
import Data.IORef
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Data.Word (Word8)
import System.Directory (createDirectoryIfMissing, removeFile)
import System.FilePath ((</>))
import System.IO.Temp (withSystemTempDirectory)

import Lattice.Services.Bridge.Protocol

-- ────────────────────────────────────────────────────────────────────────────
-- Export Context
-- ────────────────────────────────────────────────────────────────────────────

data ExportContext = ExportContext
  { ecTempDir :: !FilePath
  , ecActiveEncoders :: !(MVar (Map Text EncoderState))
  , ecNextEncoderId :: !(IORef Int)
  }

data EncoderState = EncoderState
  { esId :: !Text
  , esCodec :: !Text
  , esWidth :: !Int
  , esHeight :: !Int
  , esFps :: !Int
  , esBitrate :: !Int
  , esFrames :: !(IORef [ByteString])  -- Accumulated frames
  , esOutputPath :: !FilePath
  , esCancelled :: !(IORef Bool)
  }

-- | Initialize export context
initExport :: FilePath -> IO ExportContext
initExport tempDir = do
  createDirectoryIfMissing True tempDir
  encoders <- newMVar Map.empty
  nextId <- newIORef 0
  
  -- Initialize FFmpeg
  initFFmpeg
  
  pure ExportContext
    { ecTempDir = tempDir
    , ecActiveEncoders = encoders
    , ecNextEncoderId = nextId
    }

-- | Dispose export context
disposeExport :: ExportContext -> IO ()
disposeExport ctx = do
  encoders <- takeMVar (ecActiveEncoders ctx)
  -- Cancel all active encoders
  forM_ (Map.elems encoders) $ \enc -> do
    writeIORef (esCancelled enc) True
  putMVar (ecActiveEncoders ctx) Map.empty

-- ────────────────────────────────────────────────────────────────────────────
-- Handler
-- ────────────────────────────────────────────────────────────────────────────

exportHandler :: ExportContext -> Handler ExportOp
exportHandler ctx = handleExportOp ctx

handleExportOp :: ExportContext -> ExportOp -> IO Response
handleExportOp ctx = \case
  ExportCreateEncoder codec width height fps bitrate -> do
    -- Generate encoder ID
    encoderId <- atomicModifyIORef (ecNextEncoderId ctx) $ \n -> (n + 1, n)
    let encId = T.pack $ "encoder_" <> show encoderId
    
    -- Create output path
    let outputPath = ecTempDir ctx </> T.unpack encId <> ".mp4"
    
    -- Initialize encoder state
    frames <- newIORef []
    cancelled <- newIORef False
    
    let encoder = EncoderState
          { esId = encId
          , esCodec = codec
          , esWidth = width
          , esHeight = height
          , esFps = fps
          , esBitrate = bitrate
          , esFrames = frames
          , esOutputPath = outputPath
          , esCancelled = cancelled
          }
    
    modifyMVar_ (ecActiveEncoders ctx) $ \m -> pure $ Map.insert encId encoder m
    
    pure $ RespText 0 encId
  
  ExportEncodeFrame frameData timestamp isKeyframe -> do
    -- For now, find the most recent encoder
    encoders <- readMVar (ecActiveEncoders ctx)
    case Map.toList encoders of
      [] -> pure $ RespError 0 "No active encoder"
      ((encId, enc):_) -> do
        cancelled <- readIORef (esCancelled enc)
        if cancelled
          then pure $ RespError 0 "Encoder cancelled"
          else do
            -- Accumulate frame
            modifyIORef (esFrames enc) (frameData :)
            pure $ RespOk 0
  
  ExportFinalize -> do
    encoders <- readMVar (ecActiveEncoders ctx)
    case Map.toList encoders of
      [] -> pure $ RespError 0 "No active encoder"
      ((encId, enc):_) -> do
        result <- try $ finalizeEncoder enc
        case result of
          Left (e :: SomeException) -> pure $ RespError 0 (T.pack $ show e)
          Right videoBytes -> do
            -- Remove encoder from active list
            modifyMVar_ (ecActiveEncoders ctx) $ \m -> pure $ Map.delete encId m
            pure $ RespData 0 videoBytes
  
  ExportCancel -> do
    encoders <- readMVar (ecActiveEncoders ctx)
    case Map.toList encoders of
      [] -> pure $ RespOk 0
      ((encId, enc):_) -> do
        writeIORef (esCancelled enc) True
        modifyMVar_ (ecActiveEncoders ctx) $ \m -> pure $ Map.delete encId m
        pure $ RespOk 0
  
  ExportGetSupportedCodecs -> do
    let codecs = ["h264", "h265", "vp9", "av1"]
    pure $ RespText 0 (T.intercalate "," codecs)
  
  ExportCreateZip files -> do
    let archive = foldr addFileToArchive emptyArchive files
        zipBytes = fromArchive archive
    pure $ RespData 0 (LBS.toStrict zipBytes)
  
  ExportDownload filename content -> do
    -- Write to temp directory for download
    let path = ecTempDir ctx </> T.unpack filename
    BS.writeFile path content
    pure $ RespText 0 (T.pack path)

-- ────────────────────────────────────────────────────────────────────────────
-- Encoder Implementation
-- ────────────────────────────────────────────────────────────────────────────

-- | Finalize encoder and produce video bytes
finalizeEncoder :: EncoderState -> IO ByteString
finalizeEncoder enc = do
  frames <- reverse <$> readIORef (esFrames enc)
  
  when (null frames) $
    error "No frames to encode"
  
  -- Create encoding parameters
  let params = defaultParams (esWidth enc) (esHeight enc)
        & setFps (esFps enc)
        & setBitrate (esBitrate enc)
        & setCodec (selectCodec (esCodec enc))
  
  -- Encode frames
  withSystemTempDirectory "lattice-export" $ \tmpDir -> do
    let outputPath = tmpDir </> "output.mp4"
    
    -- Create frame writer
    frameWriter <- imageWriter params outputPath
    
    -- Write each frame
    forM_ frames $ \frameBytes -> do
      let img = bytesToImage (esWidth enc) (esHeight enc) frameBytes
      frameWriter (Just img)
    
    -- Finalize
    frameWriter Nothing
    
    -- Read output file
    BS.readFile outputPath

-- | Convert RGBA bytes to JuicyPixels Image
bytesToImage :: Int -> Int -> ByteString -> Image PixelRGBA8
bytesToImage width height bytes =
  generateImage pixelAt width height
  where
    pixelAt x y =
      let offset = (y * width + x) * 4
          r = BS.index bytes offset
          g = BS.index bytes (offset + 1)
          b = BS.index bytes (offset + 2)
          a = BS.index bytes (offset + 3)
      in PixelRGBA8 r g b a

-- | Select FFmpeg codec based on name
selectCodec :: Text -> AVCodecID
selectCodec codec = case T.toLower codec of
  "h264" -> avCodecIdH264
  "h265" -> avCodecIdH265
  "hevc" -> avCodecIdH265
  "vp9"  -> avCodecIdVp9
  "av1"  -> avCodecIdAv1
  _      -> avCodecIdH264  -- Default to H.264

-- | Add file to ZIP archive
addFileToArchive :: (Text, ByteString) -> Archive -> Archive
addFileToArchive (filename, content) archive =
  addEntryToArchive entry archive
  where
    entry = toEntry (T.unpack filename) 0 (LBS.fromStrict content)

-- ────────────────────────────────────────────────────────────────────────────
-- FFmpeg Parameter Helpers
-- ────────────────────────────────────────────────────────────────────────────

setFps :: Int -> EncodingParams -> EncodingParams
setFps fps params = params { epFps = fps }

setBitrate :: Int -> EncodingParams -> EncodingParams  
setBitrate br params = params { epTargetBitrate = Just (fromIntegral br) }

setCodec :: AVCodecID -> EncodingParams -> EncodingParams
setCodec codec params = params { epCodec = Just codec }
