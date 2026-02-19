-- | Lattice.Services.Math3D.Lens - Camera lens mathematics
-- |
-- | Pure math functions for camera lens calculations.
-- | Converts between focal length, field of view, and zoom values.
-- |
-- | Source: ui/src/services/math3d.ts (lines 731-825)

module Lattice.Services.Math3D.Lens
  ( -- * Constants
    fullFrameSensorWidth
  , fullFrameSensorHeight
  , super35SensorWidth
  , apscSensorWidth
  , standardFocalLength
    -- * Angle Conversion
  , degToRad, radToDeg
    -- * Focal Length / FOV Conversion
  , focalLengthToFOV, fovToFocalLength
    -- * Zoom / Focal Length Conversion
  , zoomToFocalLength, focalLengthToZoom
    -- * Convenience Functions
  , horizontalFOV, verticalFOV, diagonalFOV
  , fovDegreesToFocalLength
  , cropFactor, fullFrameEquivalent
  ) where

import Prelude
import Math (pi, atan, tan, sqrt) as Math

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

-- | Full frame sensor width in mm (35mm film equivalent)
fullFrameSensorWidth :: Number
fullFrameSensorWidth = 36.0

-- | Full frame sensor height in mm
fullFrameSensorHeight :: Number
fullFrameSensorHeight = 24.0

-- | Super 35 sensor width in mm
super35SensorWidth :: Number
super35SensorWidth = 24.89

-- | APS-C sensor width in mm (Canon)
apscSensorWidth :: Number
apscSensorWidth = 22.3

-- | Standard 50mm focal length
standardFocalLength :: Number
standardFocalLength = 50.0

--------------------------------------------------------------------------------
-- Angle Conversion
--------------------------------------------------------------------------------

-- | Convert degrees to radians
degToRad :: Number -> Number
degToRad degrees = degrees * (Math.pi / 180.0)

-- | Convert radians to degrees
radToDeg :: Number -> Number
radToDeg radians = radians * (180.0 / Math.pi)

--------------------------------------------------------------------------------
-- Focal Length / FOV Conversion
--------------------------------------------------------------------------------

-- | Convert focal length to field of view
-- |
-- | @param focalLength Focal length in mm
-- | @param sensorSize Sensor size in mm (36mm for full frame)
-- | @returns FOV in radians
focalLengthToFOV :: Number -> Number -> Number
focalLengthToFOV focalLength sensorSize
  | focalLength <= 0.0 = Math.pi / 2.0  -- Return wide FOV for invalid input
  | otherwise = 2.0 * Math.atan (sensorSize / (2.0 * focalLength))

-- | Convert field of view to focal length
-- |
-- | @param fov Field of view in radians (must be in (0, π))
-- | @param sensorSize Sensor size in mm
-- | @returns Focal length in mm
fovToFocalLength :: Number -> Number -> Number
fovToFocalLength fov sensorSize
  | fov <= 0.0 || fov >= Math.pi = sensorSize  -- Return standard equivalent
  | otherwise = sensorSize / (2.0 * Math.tan (fov / 2.0))

--------------------------------------------------------------------------------
-- Zoom / Focal Length Conversion
--------------------------------------------------------------------------------

-- | Convert AE zoom value to focal length
-- |
-- | @param zoom Zoom value in pixels
-- | @param compWidth Composition width in pixels
-- | @param filmSize Film size in mm
-- | @returns Focal length in mm
zoomToFocalLength :: Number -> Number -> Number -> Number
zoomToFocalLength zoom compWidth filmSize
  | compWidth <= 0.0 = filmSize  -- Default to 1:1 zoom ratio
  | otherwise = (zoom * filmSize) / compWidth

-- | Convert focal length to AE zoom value
-- |
-- | @param focalLength Focal length in mm
-- | @param compWidth Composition width in pixels
-- | @param filmSize Film size in mm
-- | @returns Zoom value in pixels
focalLengthToZoom :: Number -> Number -> Number -> Number
focalLengthToZoom focalLength compWidth filmSize
  | filmSize <= 0.0 = compWidth  -- Default to 1:1 zoom ratio
  | otherwise = (focalLength * compWidth) / filmSize

--------------------------------------------------------------------------------
-- Convenience Functions
--------------------------------------------------------------------------------

-- | Calculate horizontal FOV for a given focal length using full frame sensor
horizontalFOV :: Number -> Number
horizontalFOV focalLength = focalLengthToFOV focalLength fullFrameSensorWidth

-- | Calculate vertical FOV for a given focal length using full frame sensor
verticalFOV :: Number -> Number
verticalFOV focalLength = focalLengthToFOV focalLength fullFrameSensorHeight

-- | Calculate diagonal FOV for a given focal length using full frame sensor
diagonalFOV :: Number -> Number
diagonalFOV focalLength =
  let diagonalSize = Math.sqrt (fullFrameSensorWidth * fullFrameSensorWidth +
                                 fullFrameSensorHeight * fullFrameSensorHeight)
  in focalLengthToFOV focalLength diagonalSize

-- | Convert horizontal FOV in degrees to focal length (full frame)
fovDegreesToFocalLength :: Number -> Number
fovDegreesToFocalLength fovDegrees =
  fovToFocalLength (degToRad fovDegrees) fullFrameSensorWidth

-- | Calculate crop factor relative to full frame
cropFactor :: Number -> Number
cropFactor sensorWidth
  | sensorWidth <= 0.0 = 1.0
  | otherwise = fullFrameSensorWidth / sensorWidth

-- | Calculate equivalent focal length on full frame
-- |
-- | @param focalLength Actual focal length in mm
-- | @param sensorWidth Sensor width in mm
-- | @returns Full frame equivalent focal length in mm
fullFrameEquivalent :: Number -> Number -> Number
fullFrameEquivalent focalLength sensorWidth =
  focalLength * cropFactor sensorWidth
