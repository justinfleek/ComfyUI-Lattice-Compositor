-- |
-- Module      : Lattice.Services.ExportPipeline
-- Description : Pure export validation and image processing functions
-- 
-- Migrated from ui/src/services/export/exportPipeline.ts
-- Pure validation and image processing functions for export pipeline
-- Note: IO functions (rendering, file operations) deferred
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.Services.ExportPipeline
  ( -- Types
    ExportTarget(..)
  , ExportConfigValidation(..)
  -- Validation functions
  , validateConfig
  , needsPrompt
  -- Image processing functions
  , applyEdgeDetection
  , applyLineart
  , applySoftEdge
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import Data.Maybe (Maybe(..))
import Data.Word (Word8)
import Data.List (replicate)
import Lattice.Utils.ArrayUtils (safeArrayGet)
import Lattice.Utils.NumericSafety (safeSqrt)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                     // types
-- ════════════════════════════════════════════════════════════════════════════

-- | Export target type
data ExportTarget
  = TargetControlNetDepth
  | TargetControlNetCanny
  | TargetControlNetLineart
  | TargetControlNetSoftEdge
  | TargetControlNetNormal
  | TargetControlNetPose
  | TargetMotionCtrl
  | TargetMotionCtrlSVD
  | TargetUni3C
  | TargetWan22I2V
  | TargetWan22Fun
  | TargetCustom
  deriving (Eq, Show, Ord)

-- | Export configuration validation (subset of full config)
data ExportConfigValidation = ExportConfigValidation
  { configWidth :: Int
  , configHeight :: Int
  , configFrameCount :: Int
  , configFps :: Double
  , configStartFrame :: Int
  , configEndFrame :: Int
  , configPrompt :: Maybe Text
  , configTarget :: ExportTarget
  }
  deriving (Eq, Show)

-- ════════════════════════════════════════════════════════════════════════════
--                                                   // validation // functions
-- ════════════════════════════════════════════════════════════════════════════

-- | Validate export configuration
-- Pure function: same inputs → same outputs
-- Returns list of error messages (empty if valid)
validateConfig :: ExportConfigValidation -> [Text]
validateConfig config = concat
  [ validateWidth (configWidth config)
  , validateHeight (configHeight config)
  , validateFrameCount (configFrameCount config)
  , validateFps (configFps config)
  , validateStartFrame (configStartFrame config) (configFrameCount config)
  , validateEndFrame (configEndFrame config) (configStartFrame config) (configFrameCount config)
  , validatePrompt config
  ]

validateWidth :: Int -> [Text]
validateWidth width =
  if width < 64 || width > 4096
  then ["Width must be between 64 and 4096"]
  else []

validateHeight :: Int -> [Text]
validateHeight height =
  if height < 64 || height > 4096
  then ["Height must be between 64 and 4096"]
  else []

validateFrameCount :: Int -> [Text]
validateFrameCount frameCount =
  if frameCount < 1 || frameCount > 1000
  then ["Frame count must be between 1 and 1000"]
  else []

validateFps :: Double -> [Text]
validateFps fps =
  if fps < 1.0 || fps > 120.0
  then ["FPS must be between 1 and 120"]
  else []

validateStartFrame :: Int -> Int -> [Text]
validateStartFrame startFrame frameCount =
  if startFrame < 0 || startFrame >= frameCount
  then ["Invalid start frame"]
  else []

validateEndFrame :: Int -> Int -> Int -> [Text]
validateEndFrame endFrame startFrame frameCount =
  if endFrame <= startFrame || endFrame > frameCount
  then ["Invalid end frame"]
  else []

validatePrompt :: ExportConfigValidation -> [Text]
validatePrompt config =
  if needsPrompt (configTarget config) && configPrompt config == Nothing
  then ["Prompt is required for this export target"]
  else []

-- | Check if export target requires a prompt
-- Pure function: same inputs → same outputs
needsPrompt :: ExportTarget -> Bool
needsPrompt target = case target of
  TargetControlNetDepth -> False
  TargetControlNetCanny -> False
  TargetControlNetLineart -> False
  _ -> True

-- ════════════════════════════════════════════════════════════════════════════
--                                          // image // processing // functions
-- ════════════════════════════════════════════════════════════════════════════

-- | Apply Sobel-like edge detection to image data
-- Pure function: same inputs → same outputs
-- Input: RGBA image data (4 bytes per pixel), width, height
-- Output: New RGBA image data with edges (grayscale edges)
-- Note: Returns new array (immutable pattern)
applyEdgeDetection ::
  [Word8] ->  -- RGBA image data (4 bytes per pixel)
  Int ->      -- Width
  Int ->      -- Height
  [Word8]     -- Output RGBA image data
applyEdgeDetection imageData width height =
  let pixelCount = width * height
      -- Convert to grayscale
      grayscale = convertToGrayscale imageData width height pixelCount
      -- Apply Sobel edge detection
      edges = applySobelEdges grayscale width height
      -- Convert edges back to RGBA
  in edgesToRGBA edges width height pixelCount

-- | Convert RGBA to grayscale
convertToGrayscale :: [Word8] -> Int -> Int -> Int -> [Double]
convertToGrayscale pixels width height pixelCount =
  [ let idx = i * 4
        r = fromIntegral (safeGet pixels idx 0)
        g = fromIntegral (safeGet pixels (idx + 1) 0)
        b = fromIntegral (safeGet pixels (idx + 2) 0)
    in (r * 0.299 + g * 0.587 + b * 0.114) / 255.0
  | i <- [0 .. pixelCount - 1]
  ]

-- | Apply Sobel edge detection operators
applySobelEdges :: [Double] -> Int -> Int -> [Double]
applySobelEdges grayscale width height =
  let pixelCount = width * height
      getGray idx = safeArrayGet grayscale idx 0.0
      -- Process inner pixels (skip border)
      processPixel y x =
        let idx = y * width + x
            -- Sobel Gx operator
            gx = -getGray (idx - width - 1)
                + getGray (idx - width + 1)
                - 2 * getGray (idx - 1)
                + 2 * getGray (idx + 1)
                - getGray (idx + width - 1)
                + getGray (idx + width + 1)
            -- Sobel Gy operator
            gy = -getGray (idx - width - 1)
                - 2 * getGray (idx - width)
                - getGray (idx - width + 1)
                + getGray (idx + width - 1)
                + 2 * getGray (idx + width)
                + getGray (idx + width + 1)
            magnitude = min 1.0 (safeSqrt (gx * gx + gy * gy) * 2.0)
        in magnitude
  in [ if y >= 1 && y < height - 1 && x >= 1 && x < width - 1
       then processPixel y x
       else 0.0
     | y <- [0 .. height - 1]
     , x <- [0 .. width - 1]
     ]

-- | Convert edge values to RGBA format
edgesToRGBA :: [Double] -> Int -> Int -> Int -> [Word8]
edgesToRGBA edges width height pixelCount =
  concat [ let val = floor (edge * 255.0) `min` 255 `max` 0
           in [fromIntegral val, fromIntegral val, fromIntegral val, 255]
         | edge <- edges
         ]

-- | Safe array accessor (returns default if out of bounds)
safeGet :: [Word8] -> Int -> Word8 -> Word8
safeGet arr idx defaultVal = safeArrayGet arr idx defaultVal

-- | Apply high-contrast lineart conversion to image data
-- Pure function: same inputs → same outputs
-- Input: RGBA image data (4 bytes per pixel)
-- Output: New RGBA image data with binary lineart
applyLineart :: [Word8] -> [Word8]
applyLineart pixels =
  let getByte idx = safeArrayGet pixels idx 0
      processPixel i =
        if i `mod` 4 < 3  -- R, G, B channels
        then let r = fromIntegral (getByte i)
                 g = fromIntegral (getByte (i + 1))
                 b = fromIntegral (getByte (i + 2))
                 gray = r * 0.299 + g * 0.587 + b * 0.114
                 val = if gray > 128 then 255 else 0
             in fromIntegral val
        else getByte i  -- Alpha channel unchanged
  in [ processPixel i | i <- [0 .. length pixels - 1] ]

-- | Apply soft edge detection with Gaussian blur
-- Pure function: same inputs → same outputs
-- Input: RGBA image data (4 bytes per pixel), width, height
-- Output: New RGBA image data with soft edges
applySoftEdge :: [Word8] -> Int -> Int -> [Word8]
applySoftEdge pixels width height =
  let -- First apply edge detection
      edges = applyEdgeDetection pixels width height
      -- Then apply box blur
  in applyBoxBlur edges width height

-- | Apply simple box blur
applyBoxBlur :: [Word8] -> Int -> Int -> [Word8]
applyBoxBlur pixels width height =
  let kernel = 2
      pixelCount = width * height
      getByte idx = safeArrayGet pixels idx 0
      -- Process inner pixels
      processPixel y x =
        let kernelSum = sum [ getByte (((y + ky) * width + (x + kx)) * 4)
                            | ky <- [-kernel .. kernel]
                            , kx <- [-kernel .. kernel]
                            ]
            count = (2 * kernel + 1) * (2 * kernel + 1)
            val = floor (fromIntegral kernelSum / fromIntegral count) `min` 255 `max` 0
        in [fromIntegral val, fromIntegral val, fromIntegral val, 255]
      getPixelBytes y x = [ getByte ((y * width + x) * 4 + i) | i <- [0 .. 3] ]
  in concat [ if y >= kernel && y < height - kernel && x >= kernel && x < width - kernel
              then processPixel y x
              else getPixelBytes y x
            | y <- [0 .. height - 1]
            , x <- [0 .. width - 1]
            ]
