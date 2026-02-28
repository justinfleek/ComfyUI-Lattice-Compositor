-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // schema // material // noise-lacunarity
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | NoiseLacunarity - frequency multiplier between octaves in FBM.
-- |
-- | Range: 1.0 to finite (clamps at 1.0, no upper bound but must remain finite)
-- | - **1.0**: No frequency change (all octaves same frequency - not useful)
-- | - **2.0**: Each octave doubles frequency (standard, natural)
-- | - **3.0**: Each octave triples frequency (sharper features)
-- | - **4.0+**: Very rapid frequency increase
-- |
-- | Controls the "gap" between octave frequencies. Standard value is 2.0.
-- | Higher values create more distinct octave layers.

module Hydrogen.Schema.Material.NoiseLacunarity
  ( NoiseLacunarity
  , noiseLacunarity
  , unwrap
  , toNumber
  , bounds
  , standard
  , moderate
  , sharp
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  )

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // noise-lacunarity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Noise lacunarity (1.0 to finite)
-- |
-- | Frequency multiplier between FBM octaves. Standard is 2.0 (doubling).
newtype NoiseLacunarity = NoiseLacunarity Number

derive instance eqNoiseLacunarity :: Eq NoiseLacunarity
derive instance ordNoiseLacunarity :: Ord NoiseLacunarity

instance showNoiseLacunarity :: Show NoiseLacunarity where
  show (NoiseLacunarity l) = show l <> "x"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a noise lacunarity, clamping to 1.0 minimum and ensuring finite
noiseLacunarity :: Number -> NoiseLacunarity
noiseLacunarity n = NoiseLacunarity (Bounded.clampNumberMin 1.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Standard lacunarity (doubling)
standard :: NoiseLacunarity
standard = NoiseLacunarity 2.0

-- | Moderate lacunarity (2.5x)
moderate :: NoiseLacunarity
moderate = NoiseLacunarity 2.5

-- | Sharp lacunarity (3.0x)
sharp :: NoiseLacunarity
sharp = NoiseLacunarity 3.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Number value
unwrap :: NoiseLacunarity -> Number
unwrap (NoiseLacunarity l) = l

-- | Convert to Number (passthrough for this type)
toNumber :: NoiseLacunarity -> Number
toNumber (NoiseLacunarity l) = l

-- | Bounds documentation for this type
-- |
-- | Note: No practical upper bound, but we specify 10.0 as a reasonable maximum
-- | for documentation and UI purposes. Values beyond this rarely make visual sense.
bounds :: Bounded.NumberBounds
bounds = Bounded.numberBounds 1.0 10.0 "noiseLacunarity" "FBM frequency multiplier per octave"
