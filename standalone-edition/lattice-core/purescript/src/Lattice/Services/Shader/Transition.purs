{-
  Lattice.Services.Shader.Transition - Shader Transition Math

  Pure mathematical functions for GPU shader transitions:
  - Dissolve (noise-based threshold)
  - Wipe (directional threshold)
  - Smoothstep interpolation

  Source: ui/src/services/glsl/ShaderEffects.ts (transition effects)
-}

module Lattice.Services.Shader.Transition
  ( clamp01
  , smoothstep
  , dissolveEdge
  , dissolveBlend
  , wipeProjection
  , wipeEdge
  , wipeBlend
  , radialDistance
  , radialWipeEdge
  , angleFromCenter
  , clockWipeEdge
  , lerp
  , lerpColor
  , lerpColorAlpha
  ) where

import Prelude

import Data.Tuple (Tuple(..))
import Math (atan2, cos, floor, pi, sin, sqrt)

-- ────────────────────────────────────────────────────────────────────────────
-- Smoothstep (Hermite interpolation)
-- ────────────────────────────────────────────────────────────────────────────

-- | Clamp value to [0, 1] range.
clamp01 :: Number -> Number
clamp01 x
  | x < 0.0   = 0.0
  | x > 1.0   = 1.0
  | otherwise = x

-- | Smoothstep interpolation: S-curve from 0 to 1.
smoothstep :: Number -> Number -> Number -> Number
smoothstep edge0 edge1 x
  | edge1 <= edge0 = if x < edge0 then 0.0 else 1.0
  | otherwise      = t * t * (3.0 - 2.0 * t)
  where
    t = clamp01 ((x - edge0) / (edge1 - edge0))

-- ────────────────────────────────────────────────────────────────────────────
-- Dissolve Transition
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate dissolve edge value.
dissolveEdge :: Number -> Number -> Number -> Number
dissolveEdge noiseValue progress softness =
  smoothstep (progress - softness) (progress + softness) noiseValue

-- | Calculate dissolve blend factor (0 = from, 1 = to).
dissolveBlend :: Number -> Number -> Number -> Number
dissolveBlend = dissolveEdge

-- ────────────────────────────────────────────────────────────────────────────
-- Wipe Transition
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate directional wipe projection.
wipeProjection :: Number -> Number -> Number -> Number
wipeProjection uvX uvY angleDeg =
  let rad = angleDeg * pi / 180.0
      dirX = cos rad
      dirY = sin rad
      relX = uvX - 0.5
      relY = uvY - 0.5
  in (relX * dirX + relY * dirY) + 0.5

-- | Calculate wipe edge value.
wipeEdge :: Number -> Number -> Number -> Number -> Number -> Number
wipeEdge uvX uvY angleDeg progress softness =
  let d = wipeProjection uvX uvY angleDeg
  in smoothstep (progress - softness) (progress + softness) d

-- | Calculate wipe blend factor (0 = from, 1 = to).
wipeBlend :: Number -> Number -> Number -> Number -> Number -> Number
wipeBlend = wipeEdge

-- ────────────────────────────────────────────────────────────────────────────
-- Radial Wipe
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate radial wipe distance from center.
radialDistance :: Number -> Number -> Number -> Number -> Number
radialDistance uvX uvY centerX centerY =
  let dx = uvX - centerX
      dy = uvY - centerY
  in sqrt (dx * dx + dy * dy)

-- | Calculate radial wipe edge value.
radialWipeEdge :: Number -> Number -> Number -> Number -> Number -> Number -> Number -> Boolean -> Number
radialWipeEdge uvX uvY centerX centerY progress softness maxRadius invert =
  let dist = radialDistance uvX uvY centerX centerY
      normalizedDist = dist / maxRadius
      threshold = if invert then 1.0 - progress else progress
  in smoothstep (threshold - softness) (threshold + softness) normalizedDist

-- ────────────────────────────────────────────────────────────────────────────
-- Clock Wipe
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate angle from center (in radians).
angleFromCenter :: Number -> Number -> Number -> Number -> Number
angleFromCenter uvX uvY centerX centerY =
  let dx = uvX - centerX
      dy = uvY - centerY
  in atan2 dy dx

-- | Calculate clock wipe edge value.
clockWipeEdge :: Number -> Number -> Number -> Number -> Number -> Number -> Number -> Boolean -> Number
clockWipeEdge uvX uvY centerX centerY startAngleDeg progress softness clockwise =
  let angle = angleFromCenter uvX uvY centerX centerY
      startRad = startAngleDeg * pi / 180.0
      relAngle = angle - startRad
      twoPi = 2.0 * pi
      wrapped = relAngle - twoPi * floor (relAngle / twoPi)
      normalizedAngle = wrapped / twoPi
      directedAngle = if clockwise then 1.0 - normalizedAngle else normalizedAngle
  in smoothstep (progress - softness) (progress + softness) directedAngle

-- ────────────────────────────────────────────────────────────────────────────
-- Linear Interpolation
-- ────────────────────────────────────────────────────────────────────────────

-- | Linear interpolation between two values.
lerp :: Number -> Number -> Number -> Number
lerp a b t = a + (b - a) * t

-- | Linear interpolation for RGB colors.
lerpColor :: Number -> Number -> Number -> Number -> Number -> Number -> Number -> Tuple Number (Tuple Number Number)
lerpColor r1 g1 b1 r2 g2 b2 t =
  Tuple (lerp r1 r2 t) (Tuple (lerp g1 g2 t) (lerp b1 b2 t))

-- | Linear interpolation for RGBA colors.
lerpColorAlpha :: Number -> Number -> Number -> Number -> Number -> Number -> Number -> Number -> Number -> Tuple Number (Tuple Number (Tuple Number Number))
lerpColorAlpha r1 g1 b1 a1 r2 g2 b2 a2 t =
  Tuple (lerp r1 r2 t) (Tuple (lerp g1 g2 t) (Tuple (lerp b1 b2 t) (lerp a1 a2 t)))
