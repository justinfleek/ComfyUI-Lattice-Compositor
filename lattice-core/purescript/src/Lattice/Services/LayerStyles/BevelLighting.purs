{-
  Lattice.Services.LayerStyles.BevelLighting - Bevel/Emboss Lighting Math

  Pure mathematical functions for bevel and emboss lighting:
  - Light direction vector from angle and altitude
  - Surface normal from alpha gradients
  - Lambertian diffuse lighting (dot product)

  Source: ui/src/services/effects/layerStyleRenderer.ts (lines 570-696)
-}

module Lattice.Services.LayerStyles.BevelLighting
  ( lightX
  , lightY
  , lightZ
  , lightDirection
  , gradientX
  , gradientY
  , normalX
  , normalY
  , normalZ
  , normalLength
  , lightingDot
  , highlightIntensity
  , shadowIntensity
  , bevelLighting
  ) where

import Prelude

import Data.Tuple (Tuple(..))
import Math (cos, pi, sin, sqrt)

-- ────────────────────────────────────────────────────────────────────────────
-- Light Direction
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate light direction X component.
lightX :: Number -> Number
lightX angleDeg =
  let angleRad = (angleDeg - 90.0) * pi / 180.0
  in cos angleRad

-- | Calculate light direction Y component.
lightY :: Number -> Number
lightY angleDeg =
  let angleRad = (angleDeg - 90.0) * pi / 180.0
  in -(sin angleRad)

-- | Calculate light direction Z component from altitude.
lightZ :: Number -> Number
lightZ altitudeDeg = sin (altitudeDeg * pi / 180.0)

-- | Calculate full light direction vector.
lightDirection :: Number -> Number -> { x :: Number, y :: Number, z :: Number }
lightDirection angleDeg altitudeDeg =
  { x: lightX angleDeg, y: lightY angleDeg, z: lightZ altitudeDeg }

-- ────────────────────────────────────────────────────────────────────────────
-- Surface Normal from Gradients
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate alpha gradient in X direction.
gradientX :: Number -> Number -> Number
gradientX leftAlpha rightAlpha = rightAlpha - leftAlpha

-- | Calculate alpha gradient in Y direction.
gradientY :: Number -> Number -> Number
gradientY topAlpha bottomAlpha = bottomAlpha - topAlpha

-- | Calculate surface normal X component from gradient.
normalX :: Number -> Number -> Number -> Number
normalX gradX_ size depth = -gradX_ * size * depth

-- | Calculate surface normal Y component from gradient.
normalY :: Number -> Number -> Number -> Number
normalY gradY_ size depth = -gradY_ * size * depth

-- | Calculate surface normal Z component.
normalZ :: Number
normalZ = 1.0

-- | Calculate normalized surface normal length.
normalLength :: Number -> Number -> Number -> Number
normalLength nx ny nz = sqrt (nx * nx + ny * ny + nz * nz)

-- ────────────────────────────────────────────────────────────────────────────
-- Lighting Calculation
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate dot product for Lambertian lighting.
lightingDot :: Number -> Number -> Number -> Number -> Number -> Number -> Number
lightingDot nx ny nz lx ly lz =
  let len = normalLength nx ny nz
  in if len < 0.0001
     then 0.0
     else (nx / len) * lx + (ny / len) * ly + (nz / len) * lz

-- | Calculate highlight intensity from dot product.
highlightIntensity :: Number -> Number -> Number -> Number
highlightIntensity dotVal opacity pixelAlpha =
  if dotVal > 0.0
  then min 255.0 (dotVal * opacity * pixelAlpha * 255.0)
  else 0.0

-- | Calculate shadow intensity from dot product.
shadowIntensity :: Number -> Number -> Number -> Number
shadowIntensity dotVal opacity pixelAlpha =
  if dotVal < 0.0
  then min 255.0 ((-dotVal) * opacity * pixelAlpha * 255.0)
  else 0.0

-- ────────────────────────────────────────────────────────────────────────────
-- Full Bevel Calculation
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate bevel lighting for a single pixel.
bevelLighting :: Number -> Number -> Number -> Number -> Number
              -> Number -> Number -> Number -> Number
              -> Tuple Number Number
bevelLighting leftAlpha rightAlpha topAlpha bottomAlpha pixelAlpha
              size depth angleDeg altitudeDeg =
  -- Calculate gradients
  let gradX_ = gradientX leftAlpha rightAlpha
      gradY_ = gradientY topAlpha bottomAlpha

      -- Calculate normal
      nx = normalX gradX_ size depth
      ny = normalY gradY_ size depth
      nz = normalZ

      -- Calculate light direction
      light = lightDirection angleDeg altitudeDeg

      -- Calculate lighting
      dotVal = lightingDot nx ny nz light.x light.y light.z

  -- Separate into highlight and shadow
  in if dotVal > 0.0
     then Tuple (dotVal * pixelAlpha) 0.0   -- Highlight
     else Tuple 0.0 ((-dotVal) * pixelAlpha)  -- Shadow
