-- | Lattice.Services.Physics.ForceFields - Force Field Calculations
-- |
-- | Pure mathematical functions for force field calculations:
-- | - Gravity (constant direction)
-- | - Wind (with turbulence noise)
-- | - Attraction/Repulsion (point forces with falloff)
-- | - Explosion (instantaneous radial impulse)
-- | - Buoyancy (submerged depth-based)
-- | - Vortex (tangential + inward)
-- | - Drag (linear and quadratic)
-- |
-- | All functions are total and deterministic.
-- |
-- | Source: ui/src/services/physics/PhysicsEngine.ts (ForceFieldProcessor)

module Lattice.Services.Physics.ForceFields
  ( ForceFieldType(..)
  , ForceResult(..)
  , calculateGravity
  , calculateWind
  , calculateAttraction
  , calculateExplosion
  , calculateBuoyancy
  , calculateVortex
  , calculateDrag
  , falloffLinear
  , falloffQuadratic
  , inBoundsRadius
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Math (sqrt, min, max)

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Types of force fields
data ForceFieldType
  = FieldGravity
  | FieldWind
  | FieldAttraction
  | FieldExplosion
  | FieldBuoyancy
  | FieldVortex
  | FieldDrag

derive instance eqForceFieldType :: Eq ForceFieldType

instance showForceFieldType :: Show ForceFieldType where
  show FieldGravity = "FieldGravity"
  show FieldWind = "FieldWind"
  show FieldAttraction = "FieldAttraction"
  show FieldExplosion = "FieldExplosion"
  show FieldBuoyancy = "FieldBuoyancy"
  show FieldVortex = "FieldVortex"
  show FieldDrag = "FieldDrag"

-- | Force calculation result
data ForceResult
  = ForceApplied Number Number     -- Force to apply (fx, fy)
  | ImpulseApplied Number Number   -- Impulse (direct velocity change)
  | NoForce                        -- Force doesn't apply

derive instance eqForceResult :: Eq ForceResult

instance showForceResult :: Show ForceResult where
  show (ForceApplied fx fy) = "ForceApplied " <> show fx <> " " <> show fy
  show (ImpulseApplied ix iy) = "ImpulseApplied " <> show ix <> " " <> show iy
  show NoForce = "NoForce"

-- ────────────────────────────────────────────────────────────────────────────
-- Gravity
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate gravity force.
calculateGravity :: Number -> Number -> Number -> Tuple Number Number
calculateGravity gx gy mass = Tuple (gx * mass) (gy * mass)

-- ────────────────────────────────────────────────────────────────────────────
-- Wind
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate wind force with turbulence.
calculateWind :: Number -> Number -> Number -> Number -> Number -> Tuple Number Number
calculateWind baseX baseY noiseX noiseY turbulence =
  Tuple (baseX + noiseX * turbulence) (baseY + noiseY * turbulence)

-- ────────────────────────────────────────────────────────────────────────────
-- Attraction/Repulsion
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate attraction force toward a point.
calculateAttraction
  :: Number -> Number  -- field center
  -> Number -> Number  -- body position
  -> Number            -- strength
  -> Number            -- radius (0 = infinite)
  -> Number            -- mass
  -> String            -- falloff
  -> Maybe (Tuple Number Number)
calculateAttraction cx cy px py strength radius mass falloff =
  let dx = cx - px
      dy = cy - py
      distSq = dx * dx + dy * dy
      dist = sqrt distSq
  in if radius > 0.0 && dist > radius
     then Nothing
     else if dist < 1.0
          then Nothing
          else
            let forceMag = case falloff of
                  "linear" -> if radius > 0.0
                              then strength * (radius - dist) / radius
                              else strength
                  "quadratic" -> strength / distSq
                  _ -> strength
                dirX = dx / dist
                dirY = dy / dist
            in Just (Tuple (dirX * forceMag * mass) (dirY * forceMag * mass))

-- ────────────────────────────────────────────────────────────────────────────
-- Explosion
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate explosion impulse.
calculateExplosion
  :: Number -> Number  -- explosion center
  -> Number -> Number  -- body position
  -> Number            -- strength
  -> Number            -- radius
  -> Maybe (Tuple Number Number)
calculateExplosion ex ey px py strength radius =
  let dx = px - ex
      dy = py - ey
      dist = sqrt (dx * dx + dy * dy)
  in if dist > radius || dist < 1.0
     then Nothing
     else let falloff = 1.0 - dist / radius
              nx = if dist > 0.0001 then dx / dist else 1.0
              ny = if dist > 0.0001 then dy / dist else 0.0
          in Just (Tuple (nx * strength * falloff) (ny * strength * falloff))

-- ────────────────────────────────────────────────────────────────────────────
-- Buoyancy
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate buoyancy force.
calculateBuoyancy
  :: Number  -- surface level
  -> Number  -- body Y
  -> Number  -- density
  -> Number  -- mass
  -> Number  -- radius
  -> Number  -- velX
  -> Number  -- velY
  -> Number  -- linearDrag
  -> Maybe (Tuple Number Number)
calculateBuoyancy surfaceLevel bodyY density mass radius velX velY linearDrag =
  let submergedDepth = bodyY - surfaceLevel
  in if submergedDepth <= 0.0
     then Nothing
     else
       let submergedRatio = min 1.0 (submergedDepth / (radius * 2.0))
           buoyancyForce = -density * submergedRatio * mass * 980.0
           dragX = -linearDrag * velX * submergedRatio
           dragY = -linearDrag * velY * submergedRatio
       in Just (Tuple dragX (buoyancyForce + dragY))

-- ────────────────────────────────────────────────────────────────────────────
-- Vortex
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate vortex force.
calculateVortex
  :: Number -> Number  -- center
  -> Number -> Number  -- body position
  -> Number            -- tangential strength
  -> Number            -- inward strength
  -> Number            -- radius
  -> Number            -- mass
  -> Maybe (Tuple Number Number)
calculateVortex cx cy px py tangentialStrength inwardStrength radius mass =
  let dx = px - cx
      dy = py - cy
      dist = sqrt (dx * dx + dy * dy)
  in if dist > radius || dist < 1.0
     then Nothing
     else
       let falloff = 1.0 - dist / radius
           nx = dx / dist
           ny = dy / dist
           tx = -ny
           ty = nx
           tangentialX = tx * tangentialStrength * falloff * mass
           tangentialY = ty * tangentialStrength * falloff * mass
           inwardX = -nx * inwardStrength * falloff * mass
           inwardY = -ny * inwardStrength * falloff * mass
       in Just (Tuple (tangentialX + inwardX) (tangentialY + inwardY))

-- ────────────────────────────────────────────────────────────────────────────
-- Drag
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate drag force.
calculateDrag
  :: Number -> Number  -- velocity
  -> Number            -- linear coefficient
  -> Number            -- quadratic coefficient
  -> Maybe (Tuple Number Number)
calculateDrag velX velY linear quadratic =
  let speed = sqrt (velX * velX + velY * velY)
  in if speed < 0.01
     then Nothing
     else
       let nx = velX / speed
           ny = velY / speed
           dragMag = linear * speed + quadratic * speed * speed
       in Just (Tuple (-nx * dragMag) (-ny * dragMag))

-- ────────────────────────────────────────────────────────────────────────────
-- Utility Functions
-- ────────────────────────────────────────────────────────────────────────────

-- | Linear falloff from 1 at center to 0 at radius
falloffLinear :: Number -> Number -> Number
falloffLinear dist radius
  | radius <= 0.0 = 1.0
  | dist >= radius = 0.0
  | otherwise = 1.0 - dist / radius

-- | Quadratic falloff
falloffQuadratic :: Number -> Number
falloffQuadratic dist
  | dist < 1.0 = 1.0
  | otherwise = 1.0 / (dist * dist)

-- | Check if position is within radius
inBoundsRadius :: Number -> Number -> Number -> Number -> Number -> Boolean
inBoundsRadius cx cy px py radius =
  let dx = px - cx
      dy = py - cy
  in dx * dx + dy * dy <= radius * radius
