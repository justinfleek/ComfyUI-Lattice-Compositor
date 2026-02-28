-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // spatial // clearcoat
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ClearCoat - intensity of clear coat layer for PBR materials.
-- |
-- | Range: 0.0 to 1.0 (clamps)
-- | - **0.0**: No clear coat (standard material)
-- | - **0.5**: Partial clear coat effect
-- | - **1.0**: Full clear coat layer (car paint, lacquered wood)
-- |
-- | Clear coat adds a secondary specular layer on top of the base material,
-- | simulating glossy protective coatings like automotive paint, varnish, or lacquer.
-- | Has its own roughness parameter (ClearCoatRoughness) independent of base roughness.

module Hydrogen.Schema.Spatial.ClearCoat
  ( ClearCoat
  , clearCoat
  , unwrap
  , toNumber
  , bounds
  , none
  , partial
  , full
  ) where

import Prelude

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // clearcoat
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clear coat layer intensity for PBR (0.0 to 1.0)
-- |
-- | 0 = no clear coat, 1 = full clear coat layer (car paint effect).
newtype ClearCoat = ClearCoat Number

derive instance eqClearCoat :: Eq ClearCoat
derive instance ordClearCoat :: Ord ClearCoat

instance showClearCoat :: Show ClearCoat where
  show (ClearCoat c) = show c

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a clear coat value, clamping to 0.0-1.0
clearCoat :: Number -> ClearCoat
clearCoat n = ClearCoat (Bounded.clampNumber 0.0 1.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | No clear coat (standard material)
none :: ClearCoat
none = ClearCoat 0.0

-- | Partial clear coat
partial :: ClearCoat
partial = ClearCoat 0.5

-- | Full clear coat (automotive paint, varnish)
full :: ClearCoat
full = ClearCoat 1.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Number value
unwrap :: ClearCoat -> Number
unwrap (ClearCoat c) = c

-- | Convert to Number (passthrough for this type)
toNumber :: ClearCoat -> Number
toNumber (ClearCoat c) = c

-- | Bounds documentation for this type
bounds :: Bounded.NumberBounds
bounds = Bounded.numberBounds 0.0 1.0 "clearCoat" "PBR clear coat layer intensity (automotive paint effect)"
