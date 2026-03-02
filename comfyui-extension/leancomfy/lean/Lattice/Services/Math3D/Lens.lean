/-
  Lattice.Services.Math3D.Lens - Camera lens mathematics

  Pure math functions for camera lens calculations.
  Converts between focal length, field of view, and zoom values.

  Source: ui/src/services/math3d.ts (lines 731-825)
-/

namespace Lattice.Services.Math3D.Lens

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

/-- Pi constant -/
def pi : Float := 3.14159265358979323846

/-- Full frame sensor width in mm (35mm film equivalent) -/
def fullFrameSensorWidth : Float := 36.0

/-- Full frame sensor height in mm -/
def fullFrameSensorHeight : Float := 24.0

/-- Super 35 sensor width in mm -/
def super35SensorWidth : Float := 24.89

/-- APS-C sensor width in mm (Canon) -/
def apscSensorWidth : Float := 22.3

/-- Standard 50mm focal length -/
def standardFocalLength : Float := 50.0

--------------------------------------------------------------------------------
-- Angle Conversion
--------------------------------------------------------------------------------

/-- Convert degrees to radians -/
def degToRad (degrees : Float) : Float :=
  degrees * (pi / 180.0)

/-- Convert radians to degrees -/
def radToDeg (radians : Float) : Float :=
  radians * (180.0 / pi)

--------------------------------------------------------------------------------
-- Focal Length / FOV Conversion
--------------------------------------------------------------------------------

/-- Convert focal length to field of view
    @param focalLength Focal length in mm
    @param sensorSize Sensor size in mm (36mm for full frame)
    @returns FOV in radians -/
def focalLengthToFOV (focalLength sensorSize : Float) : Float :=
  if focalLength <= 0.0 then
    -- Return wide FOV for invalid input
    pi / 2.0
  else
    2.0 * Float.atan (sensorSize / (2.0 * focalLength))

/-- Convert field of view to focal length
    @param fov Field of view in radians (must be in (0, π))
    @param sensorSize Sensor size in mm
    @returns Focal length in mm -/
def fovToFocalLength (fov sensorSize : Float) : Float :=
  -- FOV must be in (0, π) to avoid division by zero
  if fov <= 0.0 || fov >= pi then
    -- Return standard 50mm equivalent
    sensorSize
  else
    sensorSize / (2.0 * Float.tan (fov / 2.0))

--------------------------------------------------------------------------------
-- Zoom / Focal Length Conversion
--------------------------------------------------------------------------------

/-- Convert AE zoom value to focal length
    @param zoom Zoom value in pixels
    @param compWidth Composition width in pixels
    @param filmSize Film size in mm
    @returns Focal length in mm -/
def zoomToFocalLength (zoom compWidth filmSize : Float) : Float :=
  if compWidth <= 0.0 then
    -- Default to 1:1 zoom ratio
    filmSize
  else
    (zoom * filmSize) / compWidth

/-- Convert focal length to AE zoom value
    @param focalLength Focal length in mm
    @param compWidth Composition width in pixels
    @param filmSize Film size in mm
    @returns Zoom value in pixels -/
def focalLengthToZoom (focalLength compWidth filmSize : Float) : Float :=
  if filmSize <= 0.0 then
    -- Default to 1:1 zoom ratio
    compWidth
  else
    (focalLength * compWidth) / filmSize

--------------------------------------------------------------------------------
-- Convenience Functions
--------------------------------------------------------------------------------

/-- Calculate horizontal FOV for a given focal length using full frame sensor -/
def horizontalFOV (focalLength : Float) : Float :=
  focalLengthToFOV focalLength fullFrameSensorWidth

/-- Calculate vertical FOV for a given focal length using full frame sensor -/
def verticalFOV (focalLength : Float) : Float :=
  focalLengthToFOV focalLength fullFrameSensorHeight

/-- Calculate diagonal FOV for a given focal length using full frame sensor -/
def diagonalFOV (focalLength : Float) : Float :=
  let diagonalSize := Float.sqrt (fullFrameSensorWidth * fullFrameSensorWidth +
                                   fullFrameSensorHeight * fullFrameSensorHeight)
  focalLengthToFOV focalLength diagonalSize

/-- Convert horizontal FOV in degrees to focal length (full frame) -/
def fovDegreesToFocalLength (fovDegrees : Float) : Float :=
  fovToFocalLength (degToRad fovDegrees) fullFrameSensorWidth

/-- Calculate crop factor relative to full frame -/
def cropFactor (sensorWidth : Float) : Float :=
  if sensorWidth <= 0.0 then 1.0
  else fullFrameSensorWidth / sensorWidth

/-- Calculate equivalent focal length on full frame
    @param focalLength Actual focal length in mm
    @param sensorWidth Sensor width in mm
    @returns Full frame equivalent focal length in mm -/
def fullFrameEquivalent (focalLength sensorWidth : Float) : Float :=
  focalLength * cropFactor sensorWidth

end Lattice.Services.Math3D.Lens
