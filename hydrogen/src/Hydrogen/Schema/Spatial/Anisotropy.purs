-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // schema // spatial // anisotropy
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Anisotropy - directional stretching of reflections for PBR materials.
-- |
-- | Range: -1.0 to +1.0 (clamps)
-- | - **-1.0**: Maximum anisotropy perpendicular to tangent direction
-- | - **0.0**: Isotropic (standard round highlights)
-- | - **+1.0**: Maximum anisotropy along tangent direction
-- |
-- | Creates elongated highlights seen on brushed metal, hair, satin fabrics.
-- | Requires tangent/bitangent vectors to define stretch direction.
-- | Common materials: brushed aluminum, CDs, hair, silk, carbon fiber.

module Hydrogen.Schema.Spatial.Anisotropy
  ( Anisotropy
  , anisotropy
  , unwrap
  , toNumber
  , bounds
  , isotropic
  , weak
  , moderate
  , strong
  ) where

import Prelude

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // anisotropy
-- ═════════════════════════════════════════════════════════════════════════════

-- | Anisotropic reflection factor for PBR (-1.0 to +1.0)
-- |
-- | 0 = isotropic (normal), ±1 = maximum anisotropy (brushed metal, hair).
newtype Anisotropy = Anisotropy Number

derive instance eqAnisotropy :: Eq Anisotropy
derive instance ordAnisotropy :: Ord Anisotropy

instance showAnisotropy :: Show Anisotropy where
  show (Anisotropy a) = show a

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create an anisotropy value, clamping to -1.0 to +1.0
anisotropy :: Number -> Anisotropy
anisotropy n = Anisotropy (Bounded.clampNumber (-1.0) 1.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | No anisotropy (isotropic, standard round highlights)
isotropic :: Anisotropy
isotropic = Anisotropy 0.0

-- | Weak anisotropy (subtle brushed effect)
weak :: Anisotropy
weak = Anisotropy 0.3

-- | Moderate anisotropy (visible brushed metal)
moderate :: Anisotropy
moderate = Anisotropy 0.6

-- | Strong anisotropy (pronounced hair/silk effect)
strong :: Anisotropy
strong = Anisotropy 1.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Number value
unwrap :: Anisotropy -> Number
unwrap (Anisotropy a) = a

-- | Convert to Number (passthrough for this type)
toNumber :: Anisotropy -> Number
toNumber (Anisotropy a) = a

-- | Bounds documentation for this type
bounds :: Bounded.NumberBounds
bounds = Bounded.numberBounds (-1.0) 1.0 "anisotropy" "PBR directional reflection (brushed metal, hair, silk)"
