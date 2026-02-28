-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // schema // spatial // spot angle
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | SpotAngle Atom — Cone angle of a spotlight.
-- |
-- | Maximum angle of light dispersion from the direction axis.
-- | Usually defined as the full cone angle or half-angle.
-- | Here we use **Full Angle** in radians for math, but atoms usually store degrees.
-- | Let's stick to Radians for internal consistency with Three.js?
-- | SCHEMA.md says `SpotAngle | Number | 0 | 180 | clamps`. This implies Degrees.

module Hydrogen.Schema.Spatial.SpotAngle
  ( SpotAngle
  , spotAngle
  , unsafeSpotAngle
  , unwrapSpotAngle
  , spotAngleBounds
  ) where

import Prelude
import Hydrogen.Schema.Bounded as Bounded

-- | Spot angle in degrees (0 to 180)
newtype SpotAngle = SpotAngle Number

derive instance eqSpotAngle :: Eq SpotAngle
derive instance ordSpotAngle :: Ord SpotAngle

instance showSpotAngle :: Show SpotAngle where
  show (SpotAngle a) = "(SpotAngle " <> show a <> "°)"

-- | Create SpotAngle, clamped to [0, 180]
spotAngle :: Number -> SpotAngle
spotAngle n
  | n < 0.0 = SpotAngle 0.0
  | n > 180.0 = SpotAngle 180.0
  | otherwise = SpotAngle n

unsafeSpotAngle :: Number -> SpotAngle
unsafeSpotAngle = SpotAngle

unwrapSpotAngle :: SpotAngle -> Number
unwrapSpotAngle (SpotAngle n) = n

spotAngleBounds :: Bounded.NumberBounds
spotAngleBounds = Bounded.numberBounds 0.0 180.0 "SpotAngle"
  "Spotlight cone angle in degrees (0-180)"
