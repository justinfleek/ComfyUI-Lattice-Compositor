{-
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

import Prelude

import Data.Tuple (Tuple(..))
import Math (atan2, cos, pi, sin, sqrt)

--------------------------------------------------------------------------------
-- Angle Conventions
--------------------------------------------------------------------------------

-- | Convert degrees to radians.
degreesToRadians :: Number -> Number
degreesToRadians degrees = degrees * pi / 180.0

-- | Photoshop angle offset: 0° = right, 90° = up (counter-clockwise).
photoshopAngleToRad :: Number -> Number
photoshopAngleToRad angleDeg = degreesToRadians (angleDeg - 90.0)

--------------------------------------------------------------------------------
-- Offset Calculation
--------------------------------------------------------------------------------

-- | Calculate X offset from angle and distance.
offsetX :: Number -> Number -> Number
offsetX angleDeg distance =
  let angleRad = photoshopAngleToRad angleDeg
  in cos angleRad * distance

-- | Calculate Y offset from angle and distance.
offsetY :: Number -> Number -> Number
offsetY angleDeg distance =
  let angleRad = photoshopAngleToRad angleDeg
  in -(sin angleRad * distance)

-- | Calculate both X and Y offsets from angle and distance.
angleToOffset :: Number -> Number -> Tuple Number Number
angleToOffset angleDeg distance =
  Tuple (offsetX angleDeg distance) (offsetY angleDeg distance)

--------------------------------------------------------------------------------
-- Inverse Operations
--------------------------------------------------------------------------------

-- | Calculate angle from X/Y offsets.
offsetToAngle :: Number -> Number -> Number
offsetToAngle x y =
  let angleRad = atan2 (-y) x
      angleDeg = angleRad * 180.0 / pi
  in angleDeg + 90.0

-- | Calculate distance from X/Y offsets.
offsetToDistance :: Number -> Number -> Number
offsetToDistance x y = sqrt (x * x + y * y)

--------------------------------------------------------------------------------
-- Global Light
--------------------------------------------------------------------------------

-- | Apply global light angle if enabled.
resolveAngle :: Number -> Number -> Boolean -> Number
resolveAngle localAngle globalAngle useGlobal =
  if useGlobal then globalAngle else localAngle
