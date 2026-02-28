-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // spatial // roughness
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Roughness - surface roughness for PBR materials.
-- |
-- | Range: 0.0 to 1.0 (clamps)
-- | - **0.0**: Perfectly smooth (mirror-like reflections)
-- | - **0.3**: Glossy (polished metal, wet surfaces)
-- | - **0.7**: Rough (concrete, fabric)
-- | - **1.0**: Completely diffuse (matte, no specular)
-- |
-- | Controls microfacet distribution in PBR shading models (GGX, Beckmann).
-- | Used in Unreal, Unity, Cinema4D, Blender, Arnold, etc.

module Hydrogen.Schema.Spatial.Roughness
  ( Roughness
  , roughness
  , unwrap
  , toNumber
  , bounds
  -- Constants
  , mirror
  , glossy
  , semiRough
  , matte
  -- Operations
  , blend
  , lerp
  , scale
  , add
  , subtract
  , invert
  , toSmoothness
  , fromSmoothness
  -- Predicates
  , isMirror
  , isGlossy
  , isSemiRough
  , isMatte
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
  , (<=)
  , (>=)
  , (&&)
  )

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // roughness
-- ═════════════════════════════════════════════════════════════════════════════

-- | Surface roughness for PBR (0.0 to 1.0)
-- |
-- | Controls how rough a surface appears. Smooth surfaces have sharp reflections,
-- | rough surfaces have diffuse, blurred reflections.
newtype Roughness = Roughness Number

derive instance eqRoughness :: Eq Roughness
derive instance ordRoughness :: Ord Roughness

instance showRoughness :: Show Roughness where
  show (Roughness r) = show r

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a roughness value, clamping to 0.0-1.0
roughness :: Number -> Roughness
roughness n = Roughness (Bounded.clampNumber 0.0 1.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Mirror smooth (perfect reflections)
mirror :: Roughness
mirror = Roughness 0.0

-- | Glossy (polished metal, wet surfaces)
glossy :: Roughness
glossy = Roughness 0.2

-- | Semi-rough (plastic, wood)
semiRough :: Roughness
semiRough = Roughness 0.6

-- | Matte (fabric, paper, diffuse)
matte :: Roughness
matte = Roughness 1.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Number value
unwrap :: Roughness -> Number
unwrap (Roughness r) = r

-- | Convert to Number (passthrough for this type)
toNumber :: Roughness -> Number
toNumber (Roughness r) = r

-- | Bounds documentation for this type
bounds :: Bounded.NumberBounds
bounds = Bounded.numberBounds 0.0 1.0 "roughness" "PBR surface roughness (smooth to diffuse)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Blend two roughness values with weight (0.0 = all first, 1.0 = all second)
-- |
-- | Linear interpolation between two roughness values. Critical for PBR material
-- | transitions and procedural weathering effects:
-- | ```purescript
-- | blend 0.0 mirror matte  -- Roughness 0.0
-- | blend 0.5 mirror matte  -- Roughness 0.5
-- | blend 1.0 mirror matte  -- Roughness 1.0
-- | ```
blend :: Number -> Roughness -> Roughness -> Roughness
blend weight (Roughness a) (Roughness b) =
  let w = Bounded.clampNumber 0.0 1.0 weight
  in roughness (a * (1.0 - w) + b * w)

-- | Linear interpolation (alias for blend with reversed argument order)
-- |
-- | Standard lerp signature matching shader conventions:
-- | ```purescript
-- | lerp mirror matte 0.5  -- Roughness 0.5 (halfway)
-- | ```
lerp :: Roughness -> Roughness -> Number -> Roughness
lerp from to t = blend t from to

-- | Scale roughness value by a factor
-- |
-- | Useful for procedural material variations:
-- | ```purescript
-- | scale 0.5 matte         -- Roughness 0.5
-- | scale 2.0 (roughness 0.3)  -- Roughness 0.6
-- | ```
scale :: Number -> Roughness -> Roughness
scale factor (Roughness r) = roughness (r * factor)

-- | Add to roughness value (clamped)
-- |
-- | Increases roughness (makes more matte):
-- | ```purescript
-- | add 0.2 (roughness 0.3)  -- Roughness 0.5
-- | add 0.5 (roughness 0.8)  -- Roughness 1.0 (clamped)
-- | ```
add :: Number -> Roughness -> Roughness
add amount (Roughness r) = roughness (r + amount)

-- | Subtract from roughness value (clamped)
-- |
-- | Decreases roughness (makes more glossy):
-- | ```purescript
-- | subtract 0.2 (roughness 0.5)  -- Roughness 0.3
-- | subtract 0.5 (roughness 0.3)  -- Roughness 0.0 (clamped)
-- | ```
subtract :: Number -> Roughness -> Roughness
subtract amount (Roughness r) = roughness (r - amount)

-- | Invert roughness (1.0 - value)
-- |
-- | Converts roughness to smoothness and vice versa. Some engines use smoothness
-- | (Unity Standard) while others use roughness (Unreal, Blender):
-- | ```purescript
-- | invert (roughness 0.3)  -- Roughness 0.7
-- | invert mirror           -- Roughness 1.0 (matte)
-- | invert matte            -- Roughness 0.0 (mirror)
-- | ```
invert :: Roughness -> Roughness
invert (Roughness r) = Roughness (1.0 - r)

-- | Convert roughness to smoothness (1.0 - roughness)
-- |
-- | Unity's Standard shader uses smoothness instead of roughness:
-- | ```purescript
-- | toSmoothness mirror  -- 1.0 (perfectly smooth)
-- | toSmoothness matte   -- 0.0 (not smooth at all)
-- | ```
toSmoothness :: Roughness -> Number
toSmoothness (Roughness r) = 1.0 - r

-- | Convert from smoothness to roughness (1.0 - smoothness)
-- |
-- | Import from Unity or other smoothness-based workflows:
-- | ```purescript
-- | fromSmoothness 1.0  -- Roughness 0.0 (mirror)
-- | fromSmoothness 0.0  -- Roughness 1.0 (matte)
-- | ```
fromSmoothness :: Number -> Roughness
fromSmoothness s = roughness (1.0 - s)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if mirror smooth (roughness = 0.0)
-- |
-- | Perfectly smooth surfaces have perfect specular reflection with no diffusion.
-- | These are rare in nature but common in idealized rendering:
-- | ```purescript
-- | isMirror mirror  -- true
-- | isMirror glossy  -- false
-- | ```
isMirror :: Roughness -> Boolean
isMirror (Roughness r) = r == 0.0

-- | Check if glossy (roughness <= 0.3)
-- |
-- | Glossy surfaces have visible reflections with some blur. Includes polished
-- | metal, wet surfaces, lacquered wood, etc.:
-- | ```purescript
-- | isGlossy glossy           -- true (0.2)
-- | isGlossy mirror           -- true (0.0)
-- | isGlossy (roughness 0.3)  -- true
-- | isGlossy semiRough        -- false (0.6)
-- | ```
isGlossy :: Roughness -> Boolean
isGlossy (Roughness r) = r <= 0.3

-- | Check if semi-rough (0.3 < roughness < 0.8)
-- |
-- | Semi-rough surfaces have blurred reflections. Common for plastics, most
-- | wood, concrete, etc.:
-- | ```purescript
-- | isSemiRough semiRough        -- true (0.6)
-- | isSemiRough (roughness 0.5)  -- true
-- | isSemiRough glossy           -- false
-- | isSemiRough matte            -- false
-- | ```
isSemiRough :: Roughness -> Boolean
isSemiRough (Roughness r) = r > 0.3 && r < 0.8

-- | Check if matte (roughness >= 0.8)
-- |
-- | Matte surfaces have completely diffused reflections with no visible specular.
-- | Includes fabric, paper, unpolished stone, etc.:
-- | ```purescript
-- | isMatte matte            -- true (1.0)
-- | isMatte (roughness 0.8)  -- true
-- | isMatte semiRough        -- false (0.6)
-- | ```
isMatte :: Roughness -> Boolean
isMatte (Roughness r) = r >= 0.8
