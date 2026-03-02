-- | Lattice.Services.Export.CameraExport.MotionAnalysis - Motion detection
-- |
-- | Analyzes camera keyframes to detect motion patterns (pan, zoom, orbit, rotation).
-- | Used by export format mappers to select appropriate presets.
-- |
-- | Source: ui/src/services/export/cameraExportFormats.ts

module Lattice.Services.Export.CameraExport.MotionAnalysis
  ( -- * Motion Analysis
    analyzeCameraMotion
  , detectDominantMotion
    -- * Thresholds
  , panThreshold
  , zoomThreshold
  , orbitThreshold
  , rotationThreshold
  ) where

import Prelude
import Data.Array (length, (!!))
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Number (abs)

import Lattice.Services.Export.CameraExport.Types
  ( CameraMotionAnalysis
  , PanDirection(..)
  , ZoomDirection(..)
  , OrbitDirection(..)
  , Vec3
  , defaultMotionAnalysis
  )

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Camera keyframe (simplified)
type CameraKeyframe =
  { frame :: Int
  , position :: Maybe Vec3
  , orientation :: Maybe Vec3
  }

--------------------------------------------------------------------------------
-- Thresholds
--------------------------------------------------------------------------------

-- | Pan detection threshold (position units)
panThreshold :: Number
panThreshold = 30.0

-- | Zoom detection threshold (position units)
zoomThreshold :: Number
zoomThreshold = 50.0

-- | Orbit detection threshold (degrees)
orbitThreshold :: Number
orbitThreshold = 20.0

-- | Rotation detection threshold (degrees)
rotationThreshold :: Number
rotationThreshold = 5.0

--------------------------------------------------------------------------------
-- Motion Analysis
--------------------------------------------------------------------------------

-- | Analyze camera motion pattern from keyframes
analyzeCameraMotion :: Array CameraKeyframe -> CameraMotionAnalysis
analyzeCameraMotion keyframes =
  if length keyframes < 2 then
    defaultMotionAnalysis
  else
    case { first: keyframes !! 0, last: keyframes !! (length keyframes - 1) } of
      { first: Just f, last: Just l } ->
        analyzeKeyframePair f l
      _ ->
        defaultMotionAnalysis

-- | Analyze motion between first and last keyframe
analyzeKeyframePair :: CameraKeyframe -> CameraKeyframe -> CameraMotionAnalysis
analyzeKeyframePair first last =
  let
    defaultVec = { x: 0.0, y: 0.0, z: 0.0 }

    firstPos = fromMaybe defaultVec first.position
    lastPos = fromMaybe defaultVec last.position
    firstOri = fromMaybe defaultVec first.orientation
    lastOri = fromMaybe defaultVec last.orientation

    deltaX = lastPos.x - firstPos.x
    deltaY = lastPos.y - firstPos.y
    deltaZ = lastPos.z - firstPos.z
    deltaRy = lastOri.y - firstOri.y

    -- Pan detection
    panX = abs deltaX
    panY = abs deltaY
    hasPanX = panX > panThreshold
    hasPanY = panY > panThreshold
    hasPan = hasPanX || hasPanY

    panDirection =
      if not hasPan then Nothing
      else if panX > panY then
        if deltaX > 0.0 then Just PanRight else Just PanLeft
      else
        if deltaY > 0.0 then Just PanDown else Just PanUp

    panMagnitude = max panX panY

    -- Zoom detection
    hasZoom = abs deltaZ > zoomThreshold
    zoomDirection =
      if not hasZoom then Nothing
      else if deltaZ < 0.0 then Just ZoomIn else Just ZoomOut
    zoomMagnitude = abs deltaZ

    -- Orbit detection (rotation + position change)
    hasOrbit = abs deltaRy > orbitThreshold && abs deltaX > panThreshold
    orbitDirection =
      if not hasOrbit then Nothing
      else if deltaRy > 0.0 then Just OrbitRight else Just OrbitLeft
    orbitMagnitude = abs deltaRy

    -- Rotation detection
    hasRotation = abs deltaRy > rotationThreshold
    rotationMagnitude = abs deltaRy
  in
    { hasPan
    , panDirection
    , panMagnitude
    , hasZoom
    , zoomDirection
    , zoomMagnitude
    , hasOrbit
    , orbitDirection
    , orbitMagnitude
    , hasRotation
    , rotationMagnitude
    }

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

-- | Detect dominant motion type
detectDominantMotion :: CameraMotionAnalysis -> String
detectDominantMotion motion
  | motion.hasOrbit = "orbit"
  | motion.hasZoom && motion.hasPan = "zoom_pan"
  | motion.hasZoom = "zoom"
  | motion.hasPan = "pan"
  | motion.hasRotation = "rotation"
  | otherwise = "static"

-- | Max of two numbers
max :: Number -> Number -> Number
max a b = if a > b then a else b
