-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // spatial // metallic
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Metallic - metallic factor for PBR materials.
-- |
-- | Range: 0.0 to 1.0 (clamps)
-- | - **0.0**: Dielectric (non-metal: plastic, wood, fabric, skin)
-- | - **0.5**: Partial (oxidized metal, hybrid materials)
-- | - **1.0**: Pure metal (gold, steel, aluminum)
-- |
-- | Controls whether a surface follows metal or dielectric BRDF in PBR shading.
-- | Metals have no diffuse reflection and colored specular (Fresnel F0 from albedo).
-- | Dielectrics have diffuse+specular with achromatic reflections (F0 ≈ 0.04).

module Hydrogen.Schema.Spatial.Metallic
  ( Metallic
  , metallic
  , unwrap
  , toNumber
  , bounds
  -- Constants
  , dielectric
  , partial
  , metal
  -- Operations
  , blend
  , lerp
  , scale
  , add
  , subtract
  -- Predicates
  , isDielectric
  , isMetal
  , isHybrid
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (+)
  , (-)
  , (*)
  , (==)
  , (>)
  , (<)
  , (&&)
  )

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // metallic
-- ═════════════════════════════════════════════════════════════════════════════

-- | Metallic factor for PBR (0.0 to 1.0)
-- |
-- | 0 = dielectric (non-metal), 1 = pure metal. Affects Fresnel and energy conservation.
newtype Metallic = Metallic Number

derive instance eqMetallic :: Eq Metallic
derive instance ordMetallic :: Ord Metallic

instance showMetallic :: Show Metallic where
  show (Metallic m) = show m

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a metallic value, clamping to 0.0-1.0
metallic :: Number -> Metallic
metallic n = Metallic (Bounded.clampNumber 0.0 1.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Dielectric (non-metal)
dielectric :: Metallic
dielectric = Metallic 0.0

-- | Partial metallic (oxidized, hybrid)
partial :: Metallic
partial = Metallic 0.5

-- | Pure metal
metal :: Metallic
metal = Metallic 1.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Number value
unwrap :: Metallic -> Number
unwrap (Metallic m) = m

-- | Convert to Number (passthrough for this type)
toNumber :: Metallic -> Number
toNumber (Metallic m) = m

-- | Bounds documentation for this type
bounds :: Bounded.NumberBounds
bounds = Bounded.numberBounds 0.0 1.0 "metallic" "PBR metallic factor (dielectric to metal)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Blend two metallic values with weight (0.0 = all first, 1.0 = all second)
-- |
-- | Linear interpolation between two metallic factors. Critical for PBR material
-- | transitions and procedural material generation:
-- | ```purescript
-- | blend 0.0 dielectric metal  -- Metallic 0.0
-- | blend 0.5 dielectric metal  -- Metallic 0.5
-- | blend 1.0 dielectric metal  -- Metallic 1.0
-- | ```
blend :: Number -> Metallic -> Metallic -> Metallic
blend weight (Metallic a) (Metallic b) =
  let w = Bounded.clampNumber 0.0 1.0 weight
  in metallic (a * (1.0 - w) + b * w)

-- | Linear interpolation (alias for blend with reversed argument order)
-- |
-- | Standard lerp signature matching shader conventions:
-- | ```purescript
-- | lerp dielectric metal 0.5  -- Metallic 0.5 (halfway)
-- | ```
lerp :: Metallic -> Metallic -> Number -> Metallic
lerp from to t = blend t from to

-- | Scale metallic value by a factor
-- |
-- | Useful for procedural material variations:
-- | ```purescript
-- | scale 0.5 metal      -- Metallic 0.5
-- | scale 2.0 (metallic 0.3)  -- Metallic 0.6
-- | ```
scale :: Number -> Metallic -> Metallic
scale factor (Metallic m) = metallic (m * factor)

-- | Add to metallic value (clamped)
-- |
-- | Increases metallic factor:
-- | ```purescript
-- | add 0.2 (metallic 0.3)  -- Metallic 0.5
-- | add 0.5 (metallic 0.8)  -- Metallic 1.0 (clamped)
-- | ```
add :: Number -> Metallic -> Metallic
add amount (Metallic m) = metallic (m + amount)

-- | Subtract from metallic value (clamped)
-- |
-- | Decreases metallic factor:
-- | ```purescript
-- | subtract 0.2 (metallic 0.5)  -- Metallic 0.3
-- | subtract 0.5 (metallic 0.3)  -- Metallic 0.0 (clamped)
-- | ```
subtract :: Number -> Metallic -> Metallic
subtract amount (Metallic m) = metallic (m - amount)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if fully dielectric (non-metal)
-- |
-- | Dielectric materials (metallic = 0.0) have achromatic specular reflections
-- | with Fresnel F0 ≈ 0.04 and full diffuse reflection:
-- | ```purescript
-- | isDielectric dielectric  -- true
-- | isDielectric metal       -- false
-- | ```
isDielectric :: Metallic -> Boolean
isDielectric (Metallic m) = m == 0.0

-- | Check if fully metallic
-- |
-- | Pure metals (metallic = 1.0) have no diffuse reflection and use albedo color
-- | as their Fresnel F0 for colored specular reflections:
-- | ```purescript
-- | isMetal metal       -- true
-- | isMetal dielectric  -- false
-- | ```
isMetal :: Metallic -> Boolean
isMetal (Metallic m) = m == 1.0

-- | Check if hybrid/partial metallic (between dielectric and metal)
-- |
-- | Hybrid values (0.0 < metallic < 1.0) represent oxidized metals, coated
-- | surfaces, or procedural transitions. These are common in real-world materials:
-- | ```purescript
-- | isHybrid partial     -- true
-- | isHybrid dielectric  -- false
-- | isHybrid metal       -- false
-- | ```
isHybrid :: Metallic -> Boolean
isHybrid (Metallic m) = m > 0.0 && m < 1.0
