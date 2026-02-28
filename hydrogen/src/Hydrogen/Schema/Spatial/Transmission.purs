-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // schema // spatial // transmission
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Transmission - light transmission through material for PBR (glass, water, thin materials).
-- |
-- | Range: 0.0 to 1.0 (clamps)
-- | - **0.0**: Opaque (no light transmission)
-- | - **0.5**: Translucent (frosted glass, thin fabric)
-- | - **1.0**: Fully transmissive (clear glass, water, diamond)
-- |
-- | Controls how much light passes THROUGH the material rather than being reflected or absorbed.
-- | Works with IOR (index of refraction) to create realistic glass/water/transparent materials.
-- | Requires raytracing or screen-space refraction to render correctly.

module Hydrogen.Schema.Spatial.Transmission
  ( Transmission
  , transmission
  , unwrap
  , toNumber
  , bounds
  , opaque
  , translucent
  , transparent
  ) where

import Prelude

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // transmission
-- ═════════════════════════════════════════════════════════════════════════════

-- | Light transmission factor for PBR (0.0 to 1.0)
-- |
-- | 0 = opaque, 1 = fully transmissive (glass, water).
newtype Transmission = Transmission Number

derive instance eqTransmission :: Eq Transmission
derive instance ordTransmission :: Ord Transmission

instance showTransmission :: Show Transmission where
  show (Transmission t) = show t

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a transmission value, clamping to 0.0-1.0
transmission :: Number -> Transmission
transmission n = Transmission (Bounded.clampNumber 0.0 1.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Opaque (no transmission)
opaque :: Transmission
opaque = Transmission 0.0

-- | Translucent (frosted glass, thin fabric)
translucent :: Transmission
translucent = Transmission 0.5

-- | Fully transparent (clear glass, water)
transparent :: Transmission
transparent = Transmission 1.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Number value
unwrap :: Transmission -> Number
unwrap (Transmission t) = t

-- | Convert to Number (passthrough for this type)
toNumber :: Transmission -> Number
toNumber (Transmission t) = t

-- | Bounds documentation for this type
bounds :: Bounded.NumberBounds
bounds = Bounded.numberBounds 0.0 1.0 "transmission" "PBR light transmission (glass, water transparency)"
