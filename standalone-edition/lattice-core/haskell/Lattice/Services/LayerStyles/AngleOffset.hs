{-|
  Lattice.Services.LayerStyles.AngleOffset - Angle to Offset Conversion

  Pure mathematical functions for layer style positioning:
  - Angle to X/Y offset (for shadows, bevels)
  - Photoshop-style angle convention (0° = right, 90° = up)

  Source: ui/src/services/effects/layerStyleRenderer.ts (lines 119-129)
-}

module Lattice.Services.LayerStyles.AngleOffset
  ( degreesToRadians
  , photoshopAngleToRad
  , offsetX
  , offsetY
  , angleToOffset
  , offsetToAngle
  , offsetToDistance
  , resolveAngle
  ) where

-- ────────────────────────────────────────────────────────────────────────────
-- Angle Conventions
-- ────────────────────────────────────────────────────────────────────────────

-- | Convert degrees to radians.
--
--   @param degrees Angle in degrees
--   @return Angle in radians
degreesToRadians :: Double -> Double
degreesToRadians degrees = degrees * pi / 180.0

-- | Photoshop angle offset: 0° = right, 90° = up (counter-clockwise).
--
--   The Photoshop convention uses 0° = right (east), with angles
--   increasing counter-clockwise. We subtract 90° to align
--   with the standard mathematical convention where 0° = right.
--
--   @param angleDeg Angle in degrees (Photoshop convention)
--   @return Adjusted angle in radians
photoshopAngleToRad :: Double -> Double
photoshopAngleToRad angleDeg = degreesToRadians (angleDeg - 90.0)

-- ────────────────────────────────────────────────────────────────────────────
-- Offset Calculation
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate X offset from angle and distance.
--
--   Uses Photoshop convention: 0° = right, 90° = up.
--
--   @param angleDeg Angle in degrees
--   @param distance Distance in pixels
--   @return X offset (positive = right)
offsetX :: Double -> Double -> Double
offsetX angleDeg distance =
  let angleRad = photoshopAngleToRad angleDeg
  in cos angleRad * distance

-- | Calculate Y offset from angle and distance.
--
--   Uses Photoshop convention: 0° = right, 90° = up.
--   Y is negated because screen Y increases downward.
--
--   @param angleDeg Angle in degrees
--   @param distance Distance in pixels
--   @return Y offset (positive = down in screen coordinates)
offsetY :: Double -> Double -> Double
offsetY angleDeg distance =
  let angleRad = photoshopAngleToRad angleDeg
  in -(sin angleRad * distance)

-- | Calculate both X and Y offsets from angle and distance.
--
--   @param angleDeg Angle in degrees (Photoshop convention)
--   @param distance Distance in pixels
--   @return (offsetX, offsetY) tuple
angleToOffset :: Double -> Double -> (Double, Double)
angleToOffset angleDeg distance =
  (offsetX angleDeg distance, offsetY angleDeg distance)

-- ────────────────────────────────────────────────────────────────────────────
-- Inverse Operations
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate angle from X/Y offsets.
--
--   @param x X offset
--   @param y Y offset (screen coordinates, positive = down)
--   @return Angle in degrees (Photoshop convention)
offsetToAngle :: Double -> Double -> Double
offsetToAngle x y =
  let angleRad = atan2 (-y) x
      angleDeg = angleRad * 180.0 / pi
  in angleDeg + 90.0

-- | Calculate distance from X/Y offsets.
--
--   @param x X offset
--   @param y Y offset
--   @return Distance in pixels
offsetToDistance :: Double -> Double -> Double
offsetToDistance x y = sqrt (x * x + y * y)

-- ────────────────────────────────────────────────────────────────────────────
-- Global Light
-- ────────────────────────────────────────────────────────────────────────────

-- | Apply global light angle if enabled.
--
--   @param localAngle Local angle setting
--   @param globalAngle Global light angle
--   @param useGlobal Whether to use global light
--   @return Resolved angle in degrees
resolveAngle :: Double -> Double -> Bool -> Double
resolveAngle localAngle globalAngle useGlobal =
  if useGlobal then globalAngle else localAngle
