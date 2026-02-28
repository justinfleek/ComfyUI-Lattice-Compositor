-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // schema // spatial // fov
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | FOV Atom — Camera Field of View.
-- |
-- | Vertical field of view in degrees.
-- |
-- | Bounds: 1.0° to 179.0°
-- | - < 1.0: Telephoto/orthographic-like
-- | - > 179.0: Extreme fisheye/impossible
-- | - Typical human vision: ~135° (binocular), ~180° (peripheral)
-- | - Typical games/apps: 45° - 90°

module Hydrogen.Schema.Spatial.FOV
  ( FOV
  , fov
  , unsafeFOV
  , unwrapFOV
  , fovBounds
  , standard
  , wide
  , telephoto
  ) where

import Prelude
import Hydrogen.Schema.Bounded as Bounded

-- | Field of View in degrees
newtype FOV = FOV Number

derive instance eqFOV :: Eq FOV
derive instance ordFOV :: Ord FOV

instance showFOV :: Show FOV where
  show (FOV f) = "(FOV " <> show f <> "°)"

-- | Create FOV, clamped to [1.0, 179.0]
fov :: Number -> FOV
fov n
  | n < 1.0 = FOV 1.0
  | n > 179.0 = FOV 179.0
  | otherwise = FOV n

-- | Unsafe constructor
unsafeFOV :: Number -> FOV
unsafeFOV = FOV

-- | Unwrap
unwrapFOV :: FOV -> Number
unwrapFOV (FOV f) = f

-- | Bounds
fovBounds :: Bounded.NumberBounds
fovBounds = Bounded.numberBounds 1.0 179.0 "FOV"
  "Vertical field of view in degrees (1.0 to 179.0)"

-- | Standard FOV (60 degrees)
standard :: FOV
standard = FOV 60.0

-- | Wide angle (90 degrees)
wide :: FOV
wide = FOV 90.0

-- | Telephoto (30 degrees)
telephoto :: FOV
telephoto = FOV 30.0
