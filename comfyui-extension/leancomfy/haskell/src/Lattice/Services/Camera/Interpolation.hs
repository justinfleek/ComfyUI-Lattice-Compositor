{-|
Module      : Lattice.Services.Camera.Interpolation
Description : Camera keyframe interpolation
Copyright   : (c) Lattice Compositor, 2026
License     : MIT

Pure functions for camera keyframe interpolation:
- Linear interpolation
- Angle interpolation with wrapping
- Keyframe search and blending
- Camera state interpolation

Source: ui/src/services/export/cameraExportFormats.ts (lines 28-165)
-}

{-# LANGUAGE StrictData #-}

module Lattice.Services.Camera.Interpolation
  ( -- * Types
    Vec3(..)
  , InterpolatedCamera(..)
  , CameraKeyframe(..)
  , BaseCamera(..)
    -- * Default Values
  , defaultPosition
  , defaultOrientation
  , defaultFocalLength
  , defaultZoom
  , defaultFocusDistance
  , defaultBaseCamera
    -- * Linear Interpolation
  , lerp
  , lerpVec3
    -- * Angle Interpolation
  , normalizeAngle
  , angleDiff
  , lerpAngle
  , lerpRotation
    -- * Keyframe Search
  , findSurroundingKeyframes
  , calculateT
    -- * Value Extraction
  , getPosition
  , getOrientation
  , getFocalLength
  , getZoom
  , getFocusDistance
    -- * Camera Interpolation
  , interpolateCameraAtFrame
  ) where

import Data.List (sortBy)
import Data.Ord (comparing)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | 3D vector for position or rotation.
data Vec3 = Vec3
  { vec3X :: Double
  , vec3Y :: Double
  , vec3Z :: Double
  } deriving (Show, Eq)

-- | Interpolated camera state.
data InterpolatedCamera = InterpolatedCamera
  { icPosition      :: Vec3
  , icRotation      :: Vec3
  , icFocalLength   :: Double
  , icZoom          :: Double
  , icFocusDistance :: Double
  } deriving (Show, Eq)

-- | Camera keyframe.
data CameraKeyframe = CameraKeyframe
  { ckFrame         :: Int
  , ckPosition      :: Maybe Vec3
  , ckOrientation   :: Maybe Vec3
  , ckFocalLength   :: Maybe Double
  , ckZoom          :: Maybe Double
  , ckFocusDistance :: Maybe Double
  } deriving (Show, Eq)

-- | Base camera with default values.
data BaseCamera = BaseCamera
  { bcPosition      :: Vec3
  , bcOrientation   :: Vec3
  , bcFocalLength   :: Double
  , bcZoom          :: Double
  , bcFocusDistance :: Double
  } deriving (Show, Eq)

--------------------------------------------------------------------------------
-- Default Values
--------------------------------------------------------------------------------

-- | Default position at origin.
defaultPosition :: Vec3
defaultPosition = Vec3 0 0 0

-- | Default orientation (no rotation).
defaultOrientation :: Vec3
defaultOrientation = Vec3 0 0 0

-- | Default focal length (50mm standard lens).
defaultFocalLength :: Double
defaultFocalLength = 50.0

-- | Default zoom (1x).
defaultZoom :: Double
defaultZoom = 1.0

-- | Default focus distance (meters).
defaultFocusDistance :: Double
defaultFocusDistance = 10.0

-- | Default base camera.
defaultBaseCamera :: BaseCamera
defaultBaseCamera = BaseCamera
  { bcPosition      = defaultPosition
  , bcOrientation   = defaultOrientation
  , bcFocalLength   = defaultFocalLength
  , bcZoom          = defaultZoom
  , bcFocusDistance = defaultFocusDistance
  }

--------------------------------------------------------------------------------
-- Linear Interpolation
--------------------------------------------------------------------------------

-- | Linear interpolation between two values.
lerp :: Double -> Double -> Double -> Double
lerp a b t = a + (b - a) * t

-- | Interpolate Vec3 components.
lerpVec3 :: Vec3 -> Vec3 -> Double -> Vec3
lerpVec3 a b t = Vec3
  { vec3X = lerp (vec3X a) (vec3X b) t
  , vec3Y = lerp (vec3Y a) (vec3Y b) t
  , vec3Z = lerp (vec3Z a) (vec3Z b) t
  }

--------------------------------------------------------------------------------
-- Angle Interpolation
--------------------------------------------------------------------------------

-- | Normalize angle to [0, 360) range.
normalizeAngle :: Double -> Double
normalizeAngle angle =
  let a = angle `mod'` 360.0
  in if a < 0 then a + 360 else a
  where
    mod' x y = x - y * fromIntegral (floor (x / y) :: Int)

-- | Calculate shortest angle difference.
angleDiff :: Double -> Double -> Double
angleDiff a b =
  let diff = b - a
      adjusted
        | diff > 180  = diff - 360
        | diff < -180 = diff + 360
        | otherwise   = diff
  in adjusted

-- | Interpolate between two angles, taking shortest path.
lerpAngle :: Double -> Double -> Double -> Double
lerpAngle a b t =
  let diff = angleDiff a b
      result = a + diff * t
      normalized
        | result > 360 = result - 360
        | result < 0   = result + 360
        | otherwise    = result
  in normalized

-- | Interpolate rotation vector with angle wrapping.
lerpRotation :: Vec3 -> Vec3 -> Double -> Vec3
lerpRotation a b t = Vec3
  { vec3X = lerpAngle (vec3X a) (vec3X b) t
  , vec3Y = lerpAngle (vec3Y a) (vec3Y b) t
  , vec3Z = lerpAngle (vec3Z a) (vec3Z b) t
  }

--------------------------------------------------------------------------------
-- Keyframe Search
--------------------------------------------------------------------------------

-- | Find surrounding keyframes for a given frame.
findSurroundingKeyframes :: [CameraKeyframe] -> Int -> Maybe (CameraKeyframe, CameraKeyframe)
findSurroundingKeyframes [] _ = Nothing
findSurroundingKeyframes keyframes frame =
  let sorted = sortBy (comparing ckFrame) keyframes
      first = head sorted
      lastKf = last sorted
      findPrev [] acc = acc
      findPrev (kf:rest) acc
        | ckFrame kf <= frame = findPrev rest kf
        | otherwise = acc
      findNext [] acc = acc
      findNext (kf:rest) acc
        | ckFrame kf >= frame && ckFrame acc < frame = kf
        | otherwise = findNext rest acc
      prev = findPrev sorted first
      next = findNext sorted lastKf
  in Just (prev, next)

-- | Calculate interpolation factor between two frames.
calculateT :: Int -> Int -> Int -> Double
calculateT prevFrame nextFrame currentFrame
  | prevFrame == nextFrame = 0.0
  | otherwise = fromIntegral (currentFrame - prevFrame) /
                fromIntegral (nextFrame - prevFrame)

--------------------------------------------------------------------------------
-- Value Extraction
--------------------------------------------------------------------------------

-- | Get position from keyframe with default fallback.
getPosition :: CameraKeyframe -> Vec3 -> Vec3
getPosition kf def = maybe def id (ckPosition kf)

-- | Get orientation from keyframe with default fallback.
getOrientation :: CameraKeyframe -> Vec3 -> Vec3
getOrientation kf def = maybe def id (ckOrientation kf)

-- | Get focal length from keyframe with default fallback.
getFocalLength :: CameraKeyframe -> Double -> Double
getFocalLength kf def = case ckFocalLength kf of
  Just fl | fl > 0 -> fl
  _ -> def

-- | Get zoom from keyframe with default fallback.
getZoom :: CameraKeyframe -> Double -> Double
getZoom kf def = case ckZoom kf of
  Just z | z > 0 -> z
  _ -> def

-- | Get focus distance from keyframe with default fallback.
getFocusDistance :: CameraKeyframe -> Double -> Double
getFocusDistance kf def = case ckFocusDistance kf of
  Just fd | fd > 0 -> fd
  _ -> def

--------------------------------------------------------------------------------
-- Camera Interpolation
--------------------------------------------------------------------------------

-- | Interpolate camera properties at a specific frame.
interpolateCameraAtFrame :: BaseCamera -> [CameraKeyframe] -> Int -> InterpolatedCamera
interpolateCameraAtFrame base keyframes frame =
  case findSurroundingKeyframes keyframes frame of
    Nothing -> InterpolatedCamera
      { icPosition      = bcPosition base
      , icRotation      = bcOrientation base
      , icFocalLength   = bcFocalLength base
      , icZoom          = bcZoom base
      , icFocusDistance = bcFocusDistance base
      }
    Just (prev, next)
      | ckFrame prev == ckFrame next -> InterpolatedCamera
          { icPosition      = getPosition prev (bcPosition base)
          , icRotation      = getOrientation prev (bcOrientation base)
          , icFocalLength   = getFocalLength prev (bcFocalLength base)
          , icZoom          = getZoom prev (bcZoom base)
          , icFocusDistance = getFocusDistance prev (bcFocusDistance base)
          }
      | otherwise ->
          let t = calculateT (ckFrame prev) (ckFrame next) frame
              prevPos = getPosition prev (bcPosition base)
              nextPos = getPosition next (bcPosition base)
              prevOri = getOrientation prev (bcOrientation base)
              nextOri = getOrientation next (bcOrientation base)
          in InterpolatedCamera
              { icPosition      = lerpVec3 prevPos nextPos t
              , icRotation      = lerpRotation prevOri nextOri t
              , icFocalLength   = lerp (getFocalLength prev (bcFocalLength base))
                                       (getFocalLength next (bcFocalLength base)) t
              , icZoom          = lerp (getZoom prev (bcZoom base))
                                       (getZoom next (bcZoom base)) t
              , icFocusDistance = lerp (getFocusDistance prev (bcFocusDistance base))
                                       (getFocusDistance next (bcFocusDistance base)) t
              }
