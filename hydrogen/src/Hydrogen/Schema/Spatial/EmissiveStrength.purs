-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // schema // spatial // emissive-strength
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | EmissiveStrength - emissive light intensity for self-illuminated materials.
-- |
-- | Range: 0.0 to finite (clamps at 0, no upper bound but must remain finite)
-- | - **0.0**: No emission (surface does not glow)
-- | - **1.0**: Standard emission
-- | - **10.0**: Bright glow
-- | - **100.0+**: Very bright (light source)
-- |
-- | Multiplier for emissive color. Used for LEDs, neon, screens, magic effects.
-- | HDR values (>1.0) can affect bloom and exposure.

module Hydrogen.Schema.Spatial.EmissiveStrength
  ( EmissiveStrength
  , emissiveStrength
  , unwrap
  , toNumber
  , bounds
  , off
  , subtle
  , bright
  , veryBright
  ) where

import Prelude

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // emissive-strength
-- ═════════════════════════════════════════════════════════════════════════════

-- | Emissive strength (0.0 to finite)
-- |
-- | Intensity multiplier for self-illuminated surfaces.
newtype EmissiveStrength = EmissiveStrength Number

derive instance eqEmissiveStrength :: Eq EmissiveStrength
derive instance ordEmissiveStrength :: Ord EmissiveStrength

instance showEmissiveStrength :: Show EmissiveStrength where
  show (EmissiveStrength e) = show e <> "x"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create an emissive strength, clamping to 0.0 minimum and ensuring finite
emissiveStrength :: Number -> EmissiveStrength
emissiveStrength n = EmissiveStrength (Bounded.clampNumberMin 0.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | No emission
off :: EmissiveStrength
off = EmissiveStrength 0.0

-- | Subtle glow
subtle :: EmissiveStrength
subtle = EmissiveStrength 1.0

-- | Bright emission
bright :: EmissiveStrength
bright = EmissiveStrength 10.0

-- | Very bright (light source)
veryBright :: EmissiveStrength
veryBright = EmissiveStrength 100.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Number value
unwrap :: EmissiveStrength -> Number
unwrap (EmissiveStrength e) = e

-- | Convert to Number (passthrough for this type)
toNumber :: EmissiveStrength -> Number
toNumber (EmissiveStrength e) = e

-- | Bounds documentation for this type
-- |
-- | Note: No practical upper bound, but we specify 1000.0 as a reasonable maximum
-- | for documentation and UI purposes. HDR values commonly go up to 100 or so.
bounds :: Bounded.NumberBounds
bounds = Bounded.numberBounds 0.0 1000.0 "emissiveStrength" "Self-illumination intensity"
