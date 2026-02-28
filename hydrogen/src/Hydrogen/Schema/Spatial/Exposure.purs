-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // spatial // exposure
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Exposure Atom — Camera exposure value (EV).
-- |
-- | Adjusts the brightness of the rendered image.
-- | 0.0 = No adjustment
-- | +1.0 = Double brightness (1 stop up)
-- | -1.0 = Half brightness (1 stop down)

module Hydrogen.Schema.Spatial.Exposure
  ( Exposure
  , exposure
  , unsafeExposure
  , unwrapExposure
  , exposureBounds
  ) where

import Prelude
import Hydrogen.Schema.Bounded as Bounded

-- | Exposure compensation (EV)
newtype Exposure = Exposure Number

derive instance eqExposure :: Eq Exposure
derive instance ordExposure :: Ord Exposure

instance showExposure :: Show Exposure where
  show (Exposure e) = "(Exposure " <> show e <> ")"

-- | Create Exposure, clamped to practical range [-10, 10]
exposure :: Number -> Exposure
exposure n
  | n < -10.0 = Exposure (-10.0)
  | n > 10.0 = Exposure 10.0
  | otherwise = Exposure n

unsafeExposure :: Number -> Exposure
unsafeExposure = Exposure

unwrapExposure :: Exposure -> Number
unwrapExposure (Exposure n) = n

exposureBounds :: Bounded.NumberBounds
exposureBounds = Bounded.numberBounds (-10.0) 10.0 "Exposure"
  "Exposure compensation in EV stops (-10 to +10)"
