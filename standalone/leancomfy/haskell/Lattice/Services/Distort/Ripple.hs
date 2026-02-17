{-|
  Lattice.Services.Distort.Ripple - Ripple Distortion Mathematics

  Pure mathematical functions for ripple/wave distortion:
  - Concentric wave calculation
  - Decay/falloff functions
  - Radial displacement

  Source: ui/src/services/effects/distortRenderer.ts (lines 1209-1324)
-}

module Lattice.Services.Distort.Ripple
  ( RippleConfig(..)
  , RippleResult(..)
  , rippleWave
  , decayFactor
  , linearFalloff
  , smoothFalloff
  , unitDirection
  , radialDisplace
  , calculateRipple
  , combineRipples
  , phaseToRadians
  , animatedPhase
  ) where

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Ripple configuration
data RippleConfig = RippleConfig
  { rcCenterX    :: !Double  -- ^ Center X (0-1 normalized)
  , rcCenterY    :: !Double  -- ^ Center Y (0-1 normalized)
  , rcRadius     :: !Double  -- ^ Maximum radius of effect (pixels)
  , rcWavelength :: !Double  -- ^ Distance between wave peaks (pixels)
  , rcAmplitude  :: !Double  -- ^ Maximum displacement (pixels)
  , rcPhase      :: !Double  -- ^ Phase offset (radians, for animation)
  , rcDecay      :: !Double  -- ^ Falloff exponent (0-1)
  } deriving (Show, Eq)

-- | Ripple displacement result
data RippleResult = RippleResult
  { rrSrcX     :: !Double
  , rrSrcY     :: !Double
  , rrInEffect :: !Bool     -- ^ Whether pixel is within ripple radius
  } deriving (Show, Eq)

--------------------------------------------------------------------------------
-- Wave Calculation
--------------------------------------------------------------------------------

-- | Calculate ripple wave value at a distance.
--
--   Uses sine wave with phase offset.
--
--   @param dist Distance from center (pixels)
--   @param wavelength Distance between peaks (pixels)
--   @param phase Phase offset (radians)
--   @return Wave value in [-1, 1]
rippleWave :: Double -> Double -> Double -> Double
rippleWave dist wavelength phase
  | wavelength < 0.0001 = 0.0
  | otherwise = sin ((dist / wavelength) * 2.0 * pi + phase)

--------------------------------------------------------------------------------
-- Decay/Falloff
--------------------------------------------------------------------------------

-- | Calculate decay factor based on distance from center.
--
--   Uses power function for smooth falloff.
--
--   @param dist Distance from center
--   @param radius Maximum effect radius
--   @param decay Decay exponent (higher = faster falloff)
--   @return Falloff factor in [0, 1]
decayFactor :: Double -> Double -> Double -> Double
decayFactor dist radius decay
  | radius <= 0.0 = 0.0
  | dist >= radius = 0.0
  | otherwise = (1.0 - dist / radius) ** decay

-- | Linear falloff (simple version).
--
--   @param dist Distance from center
--   @param radius Maximum radius
--   @return Linear falloff in [0, 1]
linearFalloff :: Double -> Double -> Double
linearFalloff dist radius
  | radius <= 0.0 = 0.0
  | otherwise = max 0.0 (1.0 - dist / radius)

-- | Smooth falloff using smoothstep.
--
--   @param dist Distance from center
--   @param radius Maximum radius
--   @return Smooth falloff in [0, 1]
smoothFalloff :: Double -> Double -> Double
smoothFalloff dist radius
  | radius <= 0.0 = 0.0
  | otherwise =
      let t = max 0.0 (min 1.0 (1.0 - dist / radius))
      in t * t * (3.0 - 2.0 * t)

--------------------------------------------------------------------------------
-- Radial Displacement
--------------------------------------------------------------------------------

-- | Calculate unit direction vector from center to point.
--
--   @param dx X distance from center
--   @param dy Y distance from center
--   @param dist Total distance (pre-computed)
--   @return (nx, ny) unit direction vector
unitDirection :: Double -> Double -> Double -> (Double, Double)
unitDirection dx dy dist
  | dist < 0.0001 = (0.0, 0.0)
  | otherwise = (dx / dist, dy / dist)

-- | Apply radial displacement along direction from center.
--
--   @param x Current X
--   @param y Current Y
--   @param nx Unit direction X
--   @param ny Unit direction Y
--   @param displacement Displacement amount (signed)
--   @return (newX, newY) displaced position
radialDisplace :: Double -> Double -> Double -> Double -> Double -> (Double, Double)
radialDisplace x y nx ny displacement =
  (x - nx * displacement, y - ny * displacement)

--------------------------------------------------------------------------------
-- Ripple Effect
--------------------------------------------------------------------------------

-- | Calculate ripple displacement for a single pixel.
--
--   @param x Pixel X coordinate
--   @param y Pixel Y coordinate
--   @param config Ripple configuration
--   @param width Image width (for center conversion)
--   @param height Image height (for center conversion)
--   @return Displaced source coordinates
calculateRipple :: Double -> Double -> RippleConfig -> Double -> Double -> RippleResult
calculateRipple x y config width height =
  let centerXPixels = rcCenterX config * width
      centerYPixels = rcCenterY config * height
      dx = x - centerXPixels
      dy = y - centerYPixels
      dist = sqrt (dx * dx + dy * dy)
  in
    -- Check if within effect radius
    if dist <= 0.0 then
      RippleResult { rrSrcX = x, rrSrcY = y, rrInEffect = False }
    else if dist >= rcRadius config then
      RippleResult { rrSrcX = x, rrSrcY = y, rrInEffect = False }
    else
      -- Calculate ripple displacement
      let wave = rippleWave dist (rcWavelength config) (rcPhase config)
          falloff = decayFactor dist (rcRadius config) (rcDecay config)
          displacement = wave * rcAmplitude config * falloff

          -- Get radial direction and displace
          (nx, ny) = unitDirection dx dy dist
          (srcX, srcY) = radialDisplace x y nx ny displacement

      in RippleResult { rrSrcX = srcX, rrSrcY = srcY, rrInEffect = True }

--------------------------------------------------------------------------------
-- Multiple Ripple Sources
--------------------------------------------------------------------------------

-- | Combine displacement from multiple ripple sources.
--
--   Uses additive blending of displacements.
--
--   @param x Pixel X
--   @param y Pixel Y
--   @param configs List of ripple configurations
--   @param width Image width
--   @param height Image height
--   @return Combined displaced coordinates
combineRipples :: Double -> Double -> [RippleConfig] -> Double -> Double -> (Double, Double)
combineRipples x y configs width height =
  let (totalDx, totalDy) = foldl accumDisplacement (0.0, 0.0) configs

      accumDisplacement (accDx, accDy) config =
        let result = calculateRipple x y config width height
        in if rrInEffect result
           then (accDx + (x - rrSrcX result), accDy + (y - rrSrcY result))
           else (accDx, accDy)

  in (x - totalDx, y - totalDy)

--------------------------------------------------------------------------------
-- Animation Helpers
--------------------------------------------------------------------------------

-- | Convert degrees to radians for phase.
--
--   @param degrees Phase in degrees
--   @return Phase in radians
phaseToRadians :: Double -> Double
phaseToRadians degrees = degrees * pi / 180.0

-- | Calculate animated phase for looping.
--
--   @param time Current time (0-1 normalized over loop period)
--   @param loops Number of complete wave cycles per period
--   @return Phase in radians
animatedPhase :: Double -> Int -> Double
animatedPhase time loops = time * fromIntegral loops * 2.0 * pi
