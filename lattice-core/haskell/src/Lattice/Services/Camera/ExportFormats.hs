{-|
Module      : Lattice.Services.Camera.ExportFormats
Description : Camera export format conversions
Copyright   : (c) Lattice Compositor, 2026
License     : MIT

Pure functions for exporting camera data to various AI video formats:
- MotionCtrl format (4x4 RT matrices)
- CameraCtrl poses format
- Focal length to pixel conversion
- Speed calculation from motion magnitude

Source: ui/src/services/export/cameraExportFormats.ts (lines 294-1054)
-}

{-# LANGUAGE StrictData #-}

module Lattice.Services.Camera.ExportFormats
  ( -- * Types
    MotionCtrlPose(..)
  , CameraCtrlPoseEntry
  , CameraCtrlPoses(..)
  , FullCameraFrame(..)
  , CameraExportMetadata(..)
  , ExportTarget(..)
    -- * Constants
  , defaultFilmSize
  , minTanHalfFov
    -- * Focal Length Conversions
  , focalLengthToPixels
  , applyZoom
    -- * Speed Calculation
  , calculateSpeed
    -- * Pose Entry Construction
  , buildCameraCtrlPoseEntry
  , defaultPrincipalPoint
    -- * Aspect Ratio
  , calculateAspectRatio
    -- * Validation
  , validateDimensions
  , validateFps
  , validateFrameCount
  , frameToTimestamp
    -- * Export Target
  , parseExportTarget
    -- * String Utilities
  , capitalize
    -- * Frame Sequence
  , generateFrameIndices
  , isValidFrameIndex
  ) where

import Data.Vector (Vector)
import qualified Data.Vector as V
import Data.Char (toUpper)

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | MotionCtrl pose entry (4x4 RT matrix).
newtype MotionCtrlPose = MotionCtrlPose
  { mpRT :: Vector (Vector Double)
  } deriving (Show, Eq)

-- | CameraCtrl pose entry array.
type CameraCtrlPoseEntry = Vector Double

-- | CameraCtrl poses result.
data CameraCtrlPoses = CameraCtrlPoses
  { ccpMotionType  :: String
  , ccpSpeed       :: Int
  , ccpFrameLength :: Int
  } deriving (Show, Eq)

-- | Full camera frame export.
data FullCameraFrame = FullCameraFrame
  { fcfFrame            :: Int
  , fcfTimestamp        :: Double
  , fcfViewMatrix       :: Vector (Vector Double)
  , fcfProjectionMatrix :: Vector (Vector Double)
  , fcfPosition         :: Vector Double
  , fcfRotation         :: Vector Double
  , fcfFov              :: Double
  , fcfFocalLength      :: Double
  , fcfFocusDistance    :: Double
  } deriving (Show, Eq)

-- | Full camera export metadata.
data CameraExportMetadata = CameraExportMetadata
  { cemWidth       :: Int
  , cemHeight      :: Int
  , cemFps         :: Int
  , cemTotalFrames :: Int
  , cemCameraType  :: String
  , cemFilmSize    :: Double
  } deriving (Show, Eq)

-- | Supported export targets.
data ExportTarget
  = TargetMotionCtrl
  | TargetMotionCtrlSVD
  | TargetWan22FunCamera
  | TargetUni3CCamera
  | TargetUni3CMotion
  | TargetAnimateDiffCameraCtrl
  | TargetFullMatrices
  deriving (Show, Eq)

-- ────────────────────────────────────────────────────────────────────────────
-- Constants
-- ────────────────────────────────────────────────────────────────────────────

-- | Default film size (36mm full frame).
defaultFilmSize :: Double
defaultFilmSize = 36.0

-- | Minimum tan(halfFov) threshold.
minTanHalfFov :: Double
minTanHalfFov = 0.001

-- ────────────────────────────────────────────────────────────────────────────
-- Focal Length Conversions
-- ────────────────────────────────────────────────────────────────────────────

-- | Convert focal length (mm) to pixels.
focalLengthToPixels :: Double -> Int -> Double -> Double
focalLengthToPixels focalLengthMM imageWidth sensorWidth =
  let safeSensor = if sensorWidth > 0 then sensorWidth else defaultFilmSize
  in (focalLengthMM * fromIntegral imageWidth) / safeSensor

-- | Apply zoom to focal length.
applyZoom :: Double -> Double -> Double
applyZoom focalLength zoom =
  focalLength * (if zoom > 0 then zoom else 1.0)

-- ────────────────────────────────────────────────────────────────────────────
-- Speed Calculation
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate CameraCtrl speed from motion magnitude.
calculateSpeed :: Bool -> Bool -> Bool -> Double -> Double -> Double -> Int
calculateSpeed hasZoom hasPan hasRotation zoomMag panMag rotMag =
  let speed
        | hasZoom = min 100 (zoomMag / 5)
        | hasPan = min 100 (panMag / 3)
        | hasRotation = min 100 (rotMag * 2)
        | otherwise = 0
  in round speed

-- ────────────────────────────────────────────────────────────────────────────
-- Pose Entry Construction
-- ────────────────────────────────────────────────────────────────────────────

-- | Build CameraCtrl pose entry array.
buildCameraCtrlPoseEntry :: Int -> Double -> Double -> Double -> Double -> Double
                         -> Vector Double -> CameraCtrlPoseEntry
buildCameraCtrlPoseEntry frame fx fy cx cy aspect w2cFlat =
  V.fromList [fromIntegral frame, fx, fy, cx, cy, aspect, 0, 0] V.++ w2cFlat

-- | Default principal point (image center, normalized).
defaultPrincipalPoint :: (Double, Double)
defaultPrincipalPoint = (0.5, 0.5)

-- ────────────────────────────────────────────────────────────────────────────
-- Aspect Ratio
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate aspect ratio from dimensions.
calculateAspectRatio :: Int -> Int -> Double
calculateAspectRatio width height
  | height > 0 = fromIntegral width / fromIntegral height
  | otherwise = 1.0

-- ────────────────────────────────────────────────────────────────────────────
-- Validation
-- ────────────────────────────────────────────────────────────────────────────

-- | Validate export dimensions.
validateDimensions :: Int -> Int -> Bool
validateDimensions width height = width > 0 && height > 0

-- | Validate FPS.
validateFps :: Int -> Bool
validateFps fps = fps > 0

-- | Validate frame count.
validateFrameCount :: Int -> Bool
validateFrameCount frameCount = frameCount >= 1

-- | Calculate frame timestamp from frame number and FPS.
frameToTimestamp :: Int -> Int -> Double
frameToTimestamp frame fps
  | fps > 0 = fromIntegral frame / fromIntegral fps
  | otherwise = 0

-- ────────────────────────────────────────────────────────────────────────────
-- Export Target
-- ────────────────────────────────────────────────────────────────────────────

-- | Parse export target from string.
parseExportTarget :: String -> ExportTarget
parseExportTarget s = case s of
  "motionctrl" -> TargetMotionCtrl
  "motionctrl-svd" -> TargetMotionCtrlSVD
  "wan22-fun-camera" -> TargetWan22FunCamera
  "uni3c-camera" -> TargetUni3CCamera
  "uni3c-motion" -> TargetUni3CMotion
  "animatediff-cameractrl" -> TargetAnimateDiffCameraCtrl
  _ -> TargetFullMatrices

-- ────────────────────────────────────────────────────────────────────────────
-- String Utilities
-- ────────────────────────────────────────────────────────────────────────────

-- | Capitalize first letter of string.
capitalize :: String -> String
capitalize [] = []
capitalize (c:cs) = toUpper c : cs

-- ────────────────────────────────────────────────────────────────────────────
-- Frame Sequence
-- ────────────────────────────────────────────────────────────────────────────

-- | Generate frame indices for export.
generateFrameIndices :: Int -> [Int]
generateFrameIndices frameCount = [0 .. frameCount - 1]

-- | Check if frame index is valid.
isValidFrameIndex :: Int -> Int -> Bool
isValidFrameIndex frame frameCount = frame >= 0 && frame < frameCount
