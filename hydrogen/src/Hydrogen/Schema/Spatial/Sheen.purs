-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // schema // spatial // sheen
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Sheen - fabric sheen intensity for PBR materials.
-- |
-- | Range: 0.0 to 1.0 (clamps)
-- | - **0.0**: No sheen (standard material)
-- | - **0.5**: Moderate sheen (velvet, soft fabrics)
-- | - **1.0**: Strong sheen (silk, satin)
-- |
-- | Creates the soft, colored highlight seen on fabric edges at grazing angles.
-- | Specific to cloth rendering - simulates microfiber reflection.
-- | Common materials: velvet, satin, silk, plush fabrics, carpets.

module Hydrogen.Schema.Spatial.Sheen
  ( Sheen
  , sheen
  , unwrap
  , toNumber
  , bounds
  , none
  , velvet
  , silk
  ) where

import Prelude

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // sheen
-- ═════════════════════════════════════════════════════════════════════════════

-- | Fabric sheen intensity for PBR (0.0 to 1.0)
-- |
-- | 0 = no sheen, 1 = strong sheen (silk, satin, velvet).
newtype Sheen = Sheen Number

derive instance eqSheen :: Eq Sheen
derive instance ordSheen :: Ord Sheen

instance showSheen :: Show Sheen where
  show (Sheen s) = show s

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a sheen value, clamping to 0.0-1.0
sheen :: Number -> Sheen
sheen n = Sheen (Bounded.clampNumber 0.0 1.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | No sheen (standard material)
none :: Sheen
none = Sheen 0.0

-- | Velvet sheen (moderate)
velvet :: Sheen
velvet = Sheen 0.5

-- | Silk/satin sheen (strong)
silk :: Sheen
silk = Sheen 1.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Number value
unwrap :: Sheen -> Number
unwrap (Sheen s) = s

-- | Convert to Number (passthrough for this type)
toNumber :: Sheen -> Number
toNumber (Sheen s) = s

-- | Bounds documentation for this type
bounds :: Bounded.NumberBounds
bounds = Bounded.numberBounds 0.0 1.0 "sheen" "PBR fabric sheen (velvet, silk, satin)"
