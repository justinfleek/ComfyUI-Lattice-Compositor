-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // schema // spatial // sensor width
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | SensorWidth Atom — Camera sensor width in millimeters.
-- |
-- | Used with FocalLength to calculate FOV.
-- |
-- | ## Common Values
-- | - 36mm: Full Frame (35mm film)
-- | - 24mm: APS-C
-- | - 17.3mm: Micro Four Thirds
-- | - 6.17mm: 1/2.3" (Phone)

module Hydrogen.Schema.Spatial.SensorWidth
  ( SensorWidth
  , sensorWidth
  , unsafeSensorWidth
  , unwrapSensorWidth
  , fullFrame
  , apsC
  , microFourThirds
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , (<>)
  , (<)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // sensor width
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sensor width in millimeters (> 0)
newtype SensorWidth = SensorWidth Number

derive instance eqSensorWidth :: Eq SensorWidth
derive instance ordSensorWidth :: Ord SensorWidth

instance showSensorWidth :: Show SensorWidth where
  show (SensorWidth w) = "(SensorWidth " <> show w <> "mm)"

-- | Create SensorWidth, clamping to minimum 1mm
sensorWidth :: Number -> SensorWidth
sensorWidth w
  | w < 1.0 = SensorWidth 1.0
  | otherwise = SensorWidth w

-- | Create SensorWidth without bounds checking
unsafeSensorWidth :: Number -> SensorWidth
unsafeSensorWidth = SensorWidth

-- | Extract raw Number
unwrapSensorWidth :: SensorWidth -> Number
unwrapSensorWidth (SensorWidth w) = w

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Full Frame (36mm)
fullFrame :: SensorWidth
fullFrame = SensorWidth 36.0

-- | APS-C (24mm)
apsC :: SensorWidth
apsC = SensorWidth 24.0

-- | Micro Four Thirds (17.3mm)
microFourThirds :: SensorWidth
microFourThirds = SensorWidth 17.3
