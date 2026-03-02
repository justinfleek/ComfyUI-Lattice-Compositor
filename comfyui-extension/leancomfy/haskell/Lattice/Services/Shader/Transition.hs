{-|
{-# LANGUAGE OverloadedStrings #-}
  Lattice.Services.Shader.Transition - Shader Transition Math

  Pure mathematical functions for GPU shader transitions:
  - Dissolve (noise-based threshold)
  - Wipe (directional threshold)
  - Smoothstep interpolation

  Source: ui/src/services/glsl/ShaderEffects.ts (transition effects)
-}

module Lattice.Services.Shader.Transition
  ( -- * Smoothstep
    clamp01
  , smoothstep
    -- * Dissolve Transition
  , dissolveEdge
  , dissolveBlend
    -- * Wipe Transition
  , wipeProjection
  , wipeEdge
  , wipeBlend
    -- * Radial Wipe
  , radialDistance
  , radialWipeEdge
    -- * Clock Wipe
  , angleFromCenter
  , clockWipeEdge
    -- * Interpolation
  , lerp
  , lerpColor
  , lerpColorAlpha
  ) where

--------------------------------------------------------------------------------
-- Smoothstep (Hermite interpolation)
--------------------------------------------------------------------------------

-- | Clamp value to [0, 1] range.
clamp01 :: Double -> Double
clamp01 x
  | x < 0.0   = 0.0
  | x > 1.0   = 1.0
  | otherwise = x

-- | Smoothstep interpolation: S-curve from 0 to 1.
--
--   Standard GLSL smoothstep formula.
--   Returns 0 when x ≤ edge0, 1 when x ≥ edge1,
--   and smooth Hermite interpolation between.
smoothstep :: Double -> Double -> Double -> Double
smoothstep edge0 edge1 x
  | edge1 <= edge0 = if x < edge0 then 0.0 else 1.0
  | otherwise      = t * t * (3.0 - 2.0 * t)
  where
    t = clamp01 ((x - edge0) / (edge1 - edge0))

--------------------------------------------------------------------------------
-- Dissolve Transition
--------------------------------------------------------------------------------

-- | Calculate dissolve edge value.
--
--   Uses noise-based threshold with soft edges.
--   When noiseValue < progress - softness: fully transitioned (1.0)
--   When noiseValue > progress + softness: not transitioned (0.0)
--   Between: smooth interpolation
dissolveEdge :: Double  -- ^ Noise value at pixel (0-1)
             -> Double  -- ^ Transition progress (0-1)
             -> Double  -- ^ Edge softness
             -> Double
dissolveEdge noiseValue progress softness =
  smoothstep (progress - softness) (progress + softness) noiseValue

-- | Calculate dissolve blend factor.
--
--   Returns how much of the "to" image should be visible.
--   0 = show "from", 1 = show "to"
dissolveBlend :: Double -> Double -> Double -> Double
dissolveBlend = dissolveEdge

--------------------------------------------------------------------------------
-- Wipe Transition
--------------------------------------------------------------------------------

-- | Calculate directional wipe projection.
--
--   Projects UV coordinate onto wipe direction.
--   angleDeg: wipe angle (0 = left-to-right, 90 = bottom-to-top)
--   Returns value in approximately [0, 1] range.
wipeProjection :: Double  -- ^ UV X coordinate (0-1)
               -> Double  -- ^ UV Y coordinate (0-1)
               -> Double  -- ^ Wipe angle in degrees
               -> Double
wipeProjection uvX uvY angleDeg =
  let rad = angleDeg * pi / 180.0
      dirX = cos rad
      dirY = sin rad
      -- UV relative to center (0.5, 0.5)
      relX = uvX - 0.5
      relY = uvY - 0.5
  -- Dot product + offset to get [0, 1] range
  in (relX * dirX + relY * dirY) + 0.5

-- | Calculate wipe edge value.
--
--   Uses directional threshold with soft edges.
--   progress: 0 = show "from", 1 = show "to"
--   softness: edge feathering amount
wipeEdge :: Double  -- ^ UV X
         -> Double  -- ^ UV Y
         -> Double  -- ^ Angle in degrees
         -> Double  -- ^ Progress (0-1)
         -> Double  -- ^ Softness
         -> Double
wipeEdge uvX uvY angleDeg progress softness =
  let d = wipeProjection uvX uvY angleDeg
  in smoothstep (progress - softness) (progress + softness) d

-- | Calculate wipe blend factor.
--
--   Returns how much of the "to" image should be visible.
--   0 = show "from", 1 = show "to"
wipeBlend :: Double -> Double -> Double -> Double -> Double -> Double
wipeBlend = wipeEdge

--------------------------------------------------------------------------------
-- Radial Wipe
--------------------------------------------------------------------------------

-- | Calculate radial wipe distance from center.
--
--   Used for iris/circular wipe transitions.
--   Returns normalized distance.
radialDistance :: Double  -- ^ UV X
               -> Double  -- ^ UV Y
               -> Double  -- ^ Center X
               -> Double  -- ^ Center Y
               -> Double
radialDistance uvX uvY centerX centerY =
  let dx = uvX - centerX
      dy = uvY - centerY
  in sqrt (dx * dx + dy * dy)

-- | Calculate radial wipe edge value.
--
--   Expands or contracts from center point.
--   maxRadius: radius at which transition completes (typically ~0.707 for corners)
--   invert: True for iris-in (shrinking), False for iris-out (expanding)
radialWipeEdge :: Double  -- ^ UV X
               -> Double  -- ^ UV Y
               -> Double  -- ^ Center X
               -> Double  -- ^ Center Y
               -> Double  -- ^ Progress (0-1)
               -> Double  -- ^ Softness
               -> Double  -- ^ Max radius
               -> Bool    -- ^ Invert (iris-in vs iris-out)
               -> Double
radialWipeEdge uvX uvY centerX centerY progress softness maxRadius invert =
  let dist = radialDistance uvX uvY centerX centerY
      normalizedDist = dist / maxRadius
      threshold = if invert then 1.0 - progress else progress
  in smoothstep (threshold - softness) (threshold + softness) normalizedDist

--------------------------------------------------------------------------------
-- Clock Wipe
--------------------------------------------------------------------------------

-- | Calculate angle from center (in radians, 0 = right, counter-clockwise).
angleFromCenter :: Double  -- ^ UV X
                -> Double  -- ^ UV Y
                -> Double  -- ^ Center X
                -> Double  -- ^ Center Y
                -> Double
angleFromCenter uvX uvY centerX centerY =
  let dx = uvX - centerX
      dy = uvY - centerY
  in atan2 dy dx

-- | Calculate clock wipe edge value.
--
--   Sweeps around center point like a clock hand.
--   startAngleDeg: angle where wipe starts (0 = right)
--   clockwise: True for clockwise sweep
clockWipeEdge :: Double  -- ^ UV X
              -> Double  -- ^ UV Y
              -> Double  -- ^ Center X
              -> Double  -- ^ Center Y
              -> Double  -- ^ Start angle in degrees
              -> Double  -- ^ Progress (0-1)
              -> Double  -- ^ Softness
              -> Bool    -- ^ Clockwise
              -> Double
clockWipeEdge uvX uvY centerX centerY startAngleDeg progress softness clockwise =
  let angle = angleFromCenter uvX uvY centerX centerY
      startRad = startAngleDeg * pi / 180.0
      -- Normalize angle relative to start
      relAngle = angle - startRad
      -- Wrap to [0, 2π]
      twoPi = 2.0 * pi
      wrapped = relAngle - twoPi * fromIntegral (floor (relAngle / twoPi) :: Int)
      normalizedAngle = wrapped / twoPi
      -- Apply direction
      directedAngle = if clockwise then 1.0 - normalizedAngle else normalizedAngle
  in smoothstep (progress - softness) (progress + softness) directedAngle

--------------------------------------------------------------------------------
-- Linear Interpolation (for transition blending)
--------------------------------------------------------------------------------

-- | Linear interpolation between two values.
lerp :: Double -> Double -> Double -> Double
lerp a b t = a + (b - a) * t

-- | Linear interpolation for RGB colors.
lerpColor :: Double  -- ^ R1
          -> Double  -- ^ G1
          -> Double  -- ^ B1
          -> Double  -- ^ R2
          -> Double  -- ^ G2
          -> Double  -- ^ B2
          -> Double  -- ^ T
          -> (Double, Double, Double)
lerpColor r1 g1 b1 r2 g2 b2 t =
  (lerp r1 r2 t, lerp g1 g2 t, lerp b1 b2 t)

-- | Linear interpolation for RGBA colors.
lerpColorAlpha :: Double  -- ^ R1
               -> Double  -- ^ G1
               -> Double  -- ^ B1
               -> Double  -- ^ A1
               -> Double  -- ^ R2
               -> Double  -- ^ G2
               -> Double  -- ^ B2
               -> Double  -- ^ A2
               -> Double  -- ^ T
               -> (Double, Double, Double, Double)
lerpColorAlpha r1 g1 b1 a1 r2 g2 b2 a2 t =
  (lerp r1 r2 t, lerp g1 g2 t, lerp b1 b2 t, lerp a1 a2 t)
