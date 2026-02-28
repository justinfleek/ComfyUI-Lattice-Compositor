-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                               // hydrogen // schema // spatial // reflectance
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Reflectance - dielectric reflectance at normal incidence (F0) for PBR materials.
-- |
-- | Range: 0.0 to 1.0 (clamps)
-- | - **0.0**: No reflection (unphysical, but allowed)
-- | - **0.04**: Common dielectrics (plastic, wood, ~1.5 IOR)
-- | - **0.08**: Higher IOR dielectrics (glass, water, ~2.0 IOR)
-- | - **1.0**: Perfect mirror (theoretical maximum)
-- |
-- | This controls the base reflectivity of NON-METALLIC materials.
-- | For metals, reflectance comes from the albedo color instead.
-- | Common range: 0.02 to 0.16 for real-world dielectrics.

module Hydrogen.Schema.Spatial.Reflectance
  ( Reflectance
  , reflectance
  , unwrap
  , toNumber
  , bounds
  , none
  , standard
  , glass
  , diamond
  ) where

import Prelude

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // reflectance
-- ═════════════════════════════════════════════════════════════════════════════

-- | Dielectric reflectance factor for PBR (0.0 to 1.0)
-- |
-- | F0 value for non-metals. Controls base reflectivity before Fresnel effect.
newtype Reflectance = Reflectance Number

derive instance eqReflectance :: Eq Reflectance
derive instance ordReflectance :: Ord Reflectance

instance showReflectance :: Show Reflectance where
  show (Reflectance r) = show r

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a reflectance value, clamping to 0.0-1.0
reflectance :: Number -> Reflectance
reflectance n = Reflectance (Bounded.clampNumber 0.0 1.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | No reflectance (unphysical black hole)
none :: Reflectance
none = Reflectance 0.0

-- | Standard dielectric (~1.5 IOR: plastic, wood, concrete)
standard :: Reflectance
standard = Reflectance 0.04

-- | Glass (~1.5-1.6 IOR)
glass :: Reflectance
glass = Reflectance 0.08

-- | Diamond (~2.4 IOR, high reflectance)
diamond :: Reflectance
diamond = Reflectance 0.17

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Number value
unwrap :: Reflectance -> Number
unwrap (Reflectance r) = r

-- | Convert to Number (passthrough for this type)
toNumber :: Reflectance -> Number
toNumber (Reflectance r) = r

-- | Bounds documentation for this type
bounds :: Bounded.NumberBounds
bounds = Bounded.numberBounds 0.0 1.0 "reflectance" "PBR dielectric reflectance (F0 for non-metals)"
