-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // schema // spatial // subsurface
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Subsurface - subsurface scattering intensity for PBR materials.
-- |
-- | Range: 0.0 to 1.0 (clamps)
-- | - **0.0**: No subsurface scattering (opaque surface)
-- | - **0.5**: Moderate subsurface (wax, jade)
-- | - **1.0**: Strong subsurface (skin, milk, marble)
-- |
-- | Simulates light penetrating the surface, scattering internally, and exiting
-- | at a different location. Critical for realistic skin, wax, marble, jade, milk.
-- | Produces the soft "glow" seen in translucent organic materials.

module Hydrogen.Schema.Spatial.Subsurface
  ( Subsurface
  , subsurface
  , unwrap
  , toNumber
  , bounds
  , none
  , weak
  , moderate
  , strong
  ) where

import Prelude

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // subsurface
-- ═════════════════════════════════════════════════════════════════════════════

-- | Subsurface scattering intensity for PBR (0.0 to 1.0)
-- |
-- | 0 = no SSS, 1 = strong SSS (skin, marble, wax).
newtype Subsurface = Subsurface Number

derive instance eqSubsurface :: Eq Subsurface
derive instance ordSubsurface :: Ord Subsurface

instance showSubsurface :: Show Subsurface where
  show (Subsurface s) = show s

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a subsurface value, clamping to 0.0-1.0
subsurface :: Number -> Subsurface
subsurface n = Subsurface (Bounded.clampNumber 0.0 1.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | No subsurface scattering
none :: Subsurface
none = Subsurface 0.0

-- | Weak subsurface (thin wax, jade)
weak :: Subsurface
weak = Subsurface 0.3

-- | Moderate subsurface (thicker wax, thin skin)
moderate :: Subsurface
moderate = Subsurface 0.6

-- | Strong subsurface (skin, marble, milk)
strong :: Subsurface
strong = Subsurface 1.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Number value
unwrap :: Subsurface -> Number
unwrap (Subsurface s) = s

-- | Convert to Number (passthrough for this type)
toNumber :: Subsurface -> Number
toNumber (Subsurface s) = s

-- | Bounds documentation for this type
bounds :: Bounded.NumberBounds
bounds = Bounded.numberBounds 0.0 1.0 "subsurface" "PBR subsurface scattering (skin, wax, marble)"
