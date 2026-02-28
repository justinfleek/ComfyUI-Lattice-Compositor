-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                      // hydrogen // schema // spatial // clear-coat-roughness
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ClearCoatRoughness - surface roughness of clear coat layer for PBR materials.
-- |
-- | Range: 0.0 to 1.0 (clamps)
-- | - **0.0**: Mirror-smooth clear coat (perfect gloss, show car finish)
-- | - **0.2**: Slight texture (most automotive clear coats)
-- | - **0.5**: Semi-rough clear coat (aged varnish)
-- | - **1.0**: Completely rough clear coat (satin/matte finish)
-- |
-- | Controls the roughness of the CLEAR COAT LAYER specifically, independent
-- | of the base material's roughness. Only applies when ClearCoat > 0.

module Hydrogen.Schema.Spatial.ClearCoatRoughness
  ( ClearCoatRoughness
  , clearCoatRoughness
  , unwrap
  , toNumber
  , bounds
  , smooth
  , glossy
  , semiRough
  , matte
  ) where

import Prelude

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // clear-coat-roughness
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clear coat surface roughness for PBR (0.0 to 1.0)
-- |
-- | 0 = mirror smooth, 1 = fully rough. Independent of base material roughness.
newtype ClearCoatRoughness = ClearCoatRoughness Number

derive instance eqClearCoatRoughness :: Eq ClearCoatRoughness
derive instance ordClearCoatRoughness :: Ord ClearCoatRoughness

instance showClearCoatRoughness :: Show ClearCoatRoughness where
  show (ClearCoatRoughness r) = show r

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a clear coat roughness value, clamping to 0.0-1.0
clearCoatRoughness :: Number -> ClearCoatRoughness
clearCoatRoughness n = ClearCoatRoughness (Bounded.clampNumber 0.0 1.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Mirror-smooth clear coat (show car finish)
smooth :: ClearCoatRoughness
smooth = ClearCoatRoughness 0.0

-- | Glossy clear coat (typical automotive)
glossy :: ClearCoatRoughness
glossy = ClearCoatRoughness 0.2

-- | Semi-rough clear coat (aged varnish)
semiRough :: ClearCoatRoughness
semiRough = ClearCoatRoughness 0.5

-- | Matte clear coat (satin finish)
matte :: ClearCoatRoughness
matte = ClearCoatRoughness 1.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Number value
unwrap :: ClearCoatRoughness -> Number
unwrap (ClearCoatRoughness r) = r

-- | Convert to Number (passthrough for this type)
toNumber :: ClearCoatRoughness -> Number
toNumber (ClearCoatRoughness r) = r

-- | Bounds documentation for this type
bounds :: Bounded.NumberBounds
bounds = Bounded.numberBounds 0.0 1.0 "clearCoatRoughness" "PBR clear coat surface roughness (independent of base)"
