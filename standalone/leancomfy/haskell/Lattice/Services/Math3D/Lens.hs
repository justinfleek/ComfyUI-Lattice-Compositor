{-# LANGUAGE StrictData #-}

{-|
Module      : Lattice.Services.Math3D.Lens
Description : Camera lens mathematics
Copyright   : (c) Lattice, 2026
License     : MIT

Pure math functions for camera lens calculations.
Converts between focal length, field of view, and zoom values.

Source: ui/src/services/math3d.ts (lines 731-825)
-}

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

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

-- | Full frame sensor width in mm (35mm film equivalent)
fullFrameSensorWidth :: Double
fullFrameSensorWidth = 36.0

-- | Full frame sensor height in mm
fullFrameSensorHeight :: Double
fullFrameSensorHeight = 24.0

-- | Super 35 sensor width in mm
super35SensorWidth :: Double
super35SensorWidth = 24.89

-- | APS-C sensor width in mm (Canon)
apscSensorWidth :: Double
apscSensorWidth = 22.3

-- | Standard 50mm focal length
standardFocalLength :: Double
standardFocalLength = 50.0

--------------------------------------------------------------------------------
-- Angle Conversion
--------------------------------------------------------------------------------

-- | Convert degrees to radians
degToRad :: Double -> Double
degToRad degrees = degrees * (pi / 180.0)

-- | Convert radians to degrees
radToDeg :: Double -> Double
radToDeg radians = radians * (180.0 / pi)

--------------------------------------------------------------------------------
-- Focal Length / FOV Conversion
--------------------------------------------------------------------------------

-- | Convert focal length to field of view
--
-- @param focalLength Focal length in mm
-- @param sensorSize Sensor size in mm (36mm for full frame)
-- @returns FOV in radians
focalLengthToFOV :: Double -> Double -> Double
focalLengthToFOV focalLength sensorSize
  | focalLength <= 0.0 = pi / 2.0  -- Return wide FOV for invalid input
  | otherwise = 2.0 * atan (sensorSize / (2.0 * focalLength))

-- | Convert field of view to focal length
--
-- @param fov Field of view in radians (must be in (0, π))
-- @param sensorSize Sensor size in mm
-- @returns Focal length in mm
fovToFocalLength :: Double -> Double -> Double
fovToFocalLength fov sensorSize
  | fov <= 0.0 || fov >= pi = sensorSize  -- Return standard equivalent
  | otherwise = sensorSize / (2.0 * tan (fov / 2.0))

--------------------------------------------------------------------------------
-- Zoom / Focal Length Conversion
--------------------------------------------------------------------------------

-- | Convert AE zoom value to focal length
--
-- @param zoom Zoom value in pixels
-- @param compWidth Composition width in pixels
-- @param filmSize Film size in mm
-- @returns Focal length in mm
zoomToFocalLength :: Double -> Double -> Double -> Double
zoomToFocalLength zoom compWidth filmSize
  | compWidth <= 0.0 = filmSize  -- Default to 1:1 zoom ratio
  | otherwise = (zoom * filmSize) / compWidth

-- | Convert focal length to AE zoom value
--
-- @param focalLength Focal length in mm
-- @param compWidth Composition width in pixels
-- @param filmSize Film size in mm
-- @returns Zoom value in pixels
focalLengthToZoom :: Double -> Double -> Double -> Double
focalLengthToZoom focalLength compWidth filmSize
  | filmSize <= 0.0 = compWidth  -- Default to 1:1 zoom ratio
  | otherwise = (focalLength * compWidth) / filmSize

--------------------------------------------------------------------------------
-- Convenience Functions
--------------------------------------------------------------------------------

-- | Calculate horizontal FOV for a given focal length using full frame sensor
horizontalFOV :: Double -> Double
horizontalFOV focalLength = focalLengthToFOV focalLength fullFrameSensorWidth

-- | Calculate vertical FOV for a given focal length using full frame sensor
verticalFOV :: Double -> Double
verticalFOV focalLength = focalLengthToFOV focalLength fullFrameSensorHeight

-- | Calculate diagonal FOV for a given focal length using full frame sensor
diagonalFOV :: Double -> Double
diagonalFOV focalLength =
  let diagonalSize = sqrt (fullFrameSensorWidth * fullFrameSensorWidth +
                           fullFrameSensorHeight * fullFrameSensorHeight)
  in focalLengthToFOV focalLength diagonalSize

-- | Convert horizontal FOV in degrees to focal length (full frame)
fovDegreesToFocalLength :: Double -> Double
fovDegreesToFocalLength fovDegrees =
  fovToFocalLength (degToRad fovDegrees) fullFrameSensorWidth

-- | Calculate crop factor relative to full frame
cropFactor :: Double -> Double
cropFactor sensorWidth
  | sensorWidth <= 0.0 = 1.0
  | otherwise = fullFrameSensorWidth / sensorWidth

-- | Calculate equivalent focal length on full frame
--
-- @param focalLength Actual focal length in mm
-- @param sensorWidth Sensor width in mm
-- @returns Full frame equivalent focal length in mm
fullFrameEquivalent :: Double -> Double -> Double
fullFrameEquivalent focalLength sensorWidth =
  focalLength * cropFactor sensorWidth
