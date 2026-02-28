-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // schema // spatial // ior
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | IOR - Index of Refraction for transparent materials.
-- |
-- | Range: 1.0 to 3.0 (clamps)
-- | - **1.0**: No refraction (vacuum, air ≈ 1.0003)
-- | - **1.33**: Water
-- | - **1.5**: Glass (common soda-lime)
-- | - **1.52**: Acrylic
-- | - **2.4**: Diamond
-- | - **3.0**: High-index materials
-- |
-- | Controls how much light bends when entering/exiting a transparent surface.
-- | Used for glass, water, crystals, lenses. Critical for ray tracing.

module Hydrogen.Schema.Spatial.IOR
  ( IOR
  , ior
  , unwrap
  , toNumber
  , bounds
  -- Constants
  , air
  , water
  , glass
  , acrylic
  , crystal
  , diamond
  -- Operations
  , blend
  , lerp
  , fresnelF0
  , reflectivity
  , criticalAngle
  -- Predicates
  , isAir
  , isWater
  , isGlass
  , isDiamond
  , isLowIOR
  , isHighIOR
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  , (+)
  , (-)
  , (*)
  , (/)
  , (==)
  , (>)
  , (<)
  , (<=)
  , (>=)
  , (&&)
  )

import Data.Number (asin) as Number
import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                        // ior
-- ═════════════════════════════════════════════════════════════════════════════

-- | Index of Refraction (1.0 to 3.0)
-- |
-- | Physical property determining light refraction through transparent materials.
newtype IOR = IOR Number

derive instance eqIOR :: Eq IOR
derive instance ordIOR :: Ord IOR

instance showIOR :: Show IOR where
  show (IOR i) = "IOR=" <> show i

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create an IOR value, clamping to 1.0-3.0
ior :: Number -> IOR
ior n = IOR (Bounded.clampNumber 1.0 3.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Air (no refraction)
air :: IOR
air = IOR 1.0

-- | Water
water :: IOR
water = IOR 1.33

-- | Glass (soda-lime)
glass :: IOR
glass = IOR 1.5

-- | Acrylic/PMMA
acrylic :: IOR
acrylic = IOR 1.49

-- | Crystal (quartz)
crystal :: IOR
crystal = IOR 1.54

-- | Diamond
diamond :: IOR
diamond = IOR 2.42

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Number value
unwrap :: IOR -> Number
unwrap (IOR i) = i

-- | Convert to Number (passthrough for this type)
toNumber :: IOR -> Number
toNumber (IOR i) = i

-- | Bounds documentation for this type
bounds :: Bounded.NumberBounds
bounds = Bounded.numberBounds 1.0 3.0 "ior" "Index of refraction for transparent materials"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Blend two IOR values with weight (0.0 = all first, 1.0 = all second)
-- |
-- | Linear interpolation between two IOR values. Useful for procedural material
-- | generation or transition effects:
-- | ```purescript
-- | blend 0.0 water glass  -- IOR 1.33
-- | blend 0.5 water glass  -- IOR 1.415
-- | blend 1.0 water glass  -- IOR 1.5
-- | ```
blend :: Number -> IOR -> IOR -> IOR
blend weight (IOR a) (IOR b) =
  let w = Bounded.clampNumber 0.0 1.0 weight
  in ior (a * (1.0 - w) + b * w)

-- | Linear interpolation (alias for blend with reversed argument order)
-- |
-- | Standard lerp signature matching shader conventions:
-- | ```purescript
-- | lerp water glass 0.5  -- IOR 1.415 (halfway)
-- | ```
lerp :: IOR -> IOR -> Number -> IOR
lerp from to t = blend t from to

-- | Calculate Fresnel F0 reflectivity at normal incidence
-- |
-- | The Schlick approximation uses this as the base reflectivity. This is THE
-- | critical calculation for physically-based rendering of dielectrics:
-- |
-- | F0 = ((n1 - n2) / (n1 + n2))^2
-- |
-- | Assuming light travels from air (n=1.0) into the material:
-- | ```purescript
-- | fresnelF0 water    -- ~0.02 (2% reflected at normal)
-- | fresnelF0 glass    -- ~0.04 (4% reflected at normal)
-- | fresnelF0 diamond  -- ~0.17 (17% reflected at normal)
-- | ```
fresnelF0 :: IOR -> Number
fresnelF0 (IOR n) =
  let ratio = (n - 1.0) / (n + 1.0)
  in ratio * ratio

-- | Reflectivity percentage at normal incidence (F0 as percentage)
-- |
-- | Human-readable version of fresnelF0:
-- | ```purescript
-- | reflectivity water    -- ~2.0 (2%)
-- | reflectivity glass    -- ~4.0 (4%)
-- | reflectivity diamond  -- ~17.0 (17%)
-- | ```
reflectivity :: IOR -> Number
reflectivity i = fresnelF0 i * 100.0

-- | Calculate the critical angle for total internal reflection (in radians)
-- |
-- | Light traveling from a denser medium to a less dense medium (e.g., glass to air)
-- | will undergo total internal reflection beyond this angle. Returns Nothing for
-- | IOR <= 1.0 (no total internal reflection possible):
-- | ```purescript
-- | criticalAngle glass    -- ~0.7297 rad (41.8 degrees from air)
-- | criticalAngle water    -- ~0.8481 rad (48.6 degrees from air)
-- | criticalAngle diamond  -- ~0.4287 rad (24.6 degrees from air)
-- | ```
criticalAngle :: IOR -> Number
criticalAngle (IOR n) = Number.asin (1.0 / n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if approximately air (IOR = 1.0)
-- |
-- | Vacuum and air both have IOR ~1.0. No refraction occurs:
-- | ```purescript
-- | isAir air        -- true
-- | isAir (ior 1.0)  -- true
-- | isAir water      -- false
-- | ```
isAir :: IOR -> Boolean
isAir (IOR n) = n == 1.0

-- | Check if approximately water (IOR near 1.33)
-- |
-- | Water has a distinctive IOR of 1.33. Allows small tolerance:
-- | ```purescript
-- | isWater water       -- true
-- | isWater (ior 1.32)  -- true (within tolerance)
-- | isWater glass       -- false
-- | ```
isWater :: IOR -> Boolean
isWater (IOR n) = n >= 1.31 && n <= 1.35

-- | Check if approximately glass (IOR near 1.5)
-- |
-- | Common glass has IOR between 1.45-1.55:
-- | ```purescript
-- | isGlass glass       -- true
-- | isGlass (ior 1.52)  -- true
-- | isGlass diamond     -- false
-- | ```
isGlass :: IOR -> Boolean
isGlass (IOR n) = n >= 1.45 && n <= 1.55

-- | Check if approximately diamond (IOR near 2.42)
-- |
-- | Diamond has a very high IOR giving it extreme brilliance:
-- | ```purescript
-- | isDiamond diamond     -- true
-- | isDiamond (ior 2.4)   -- true (within tolerance)
-- | isDiamond glass       -- false
-- | ```
isDiamond :: IOR -> Boolean
isDiamond (IOR n) = n >= 2.35 && n <= 2.5

-- | Check if low IOR (less than 1.4)
-- |
-- | Low IOR materials have minimal refraction. Includes air, gases,
-- | and some thin films:
-- | ```purescript
-- | isLowIOR air    -- true
-- | isLowIOR water  -- true
-- | isLowIOR glass  -- false
-- | ```
isLowIOR :: IOR -> Boolean
isLowIOR (IOR n) = n < 1.4

-- | Check if high IOR (greater than 2.0)
-- |
-- | High IOR materials have strong refraction and brilliance. Includes
-- | diamond, cubic zirconia, and some crystals:
-- | ```purescript
-- | isHighIOR diamond     -- true
-- | isHighIOR (ior 2.2)   -- true
-- | isHighIOR glass       -- false
-- | ```
isHighIOR :: IOR -> Boolean
isHighIOR (IOR n) = n > 2.0
