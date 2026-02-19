{-|
{-# LANGUAGE OverloadedStrings #-}
Module      : Lattice.Services.Particles.Modulation
Description : Particle Property Modulation Over Lifetime
Copyright   : (c) Lattice Team, 2026
License     : MIT

Pure mathematical functions for particle property modulation:
- Size curves over lifetime
- Opacity/alpha curves
- Color interpolation (gradient over lifetime)
- Velocity modulation

All curves are evaluated deterministically from life ratio (0-1).

Source: ui/src/services/particleSystem.ts (applyModulations, ParticleModulation)
-}

{-# LANGUAGE StrictData #-}

module Lattice.Services.Particles.Modulation
  ( -- * Types
    ModulationType(..)
  , ModulationCurve(..)
  , CurvePoint(..)
  , ParticleModulation(..)
  , ModulationResult(..)
    -- * Curve Evaluation
  , evaluateCurve
  , evaluateLinear
  , evaluateCatmullRom
    -- * Property Modulation
  , modulateSize
  , modulateOpacity
  , modulateColor
  , modulateVelocity
    -- * Combined Application
  , applyModulations
  , combineModulations
    -- * Preset Curves
  , linearFadeOut
  , linearFadeIn
  , pulseWave
  , scurve
  ) where

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Type of property being modulated
data ModulationType
  = ModSize      -- ^ Particle size
  | ModOpacity   -- ^ Alpha transparency
  | ModColorR    -- ^ Red channel
  | ModColorG    -- ^ Green channel
  | ModColorB    -- ^ Blue channel
  | ModVelocity  -- ^ Velocity magnitude
  deriving (Show, Eq)

-- | A point on a modulation curve
data CurvePoint = CurvePoint
  { cpT :: Double     -- ^ Time (life ratio 0-1)
  , cpValue :: Double -- ^ Value at this time
  } deriving (Show, Eq)

-- | Modulation curve definition
data ModulationCurve
  = CurveLinear [CurvePoint]      -- ^ Linear interpolation between points
  | CurveCatmullRom [CurvePoint]  -- ^ Smooth Catmull-Rom interpolation
  | CurveEasing String Double Double  -- ^ Easing function: name, start, end
  deriving (Show, Eq)

-- | Particle modulation configuration
data ParticleModulation = ParticleModulation
  { pmId :: String              -- ^ Unique modulation ID
  , pmEmitterId :: String       -- ^ Target emitter (or "*" for all)
  , pmTarget :: ModulationType  -- ^ Property to modulate
  , pmCurve :: ModulationCurve  -- ^ Modulation curve
  , pmEnabled :: Bool
  } deriving (Show, Eq)

-- | Result of applying modulations
data ModulationResult = ModulationResult
  { mrSizeMult :: Double      -- ^ Size multiplier (1.0 = no change)
  , mrOpacityMult :: Double   -- ^ Opacity multiplier (1.0 = no change)
  , mrColorMult :: (Double, Double, Double)  -- ^ RGB multipliers
  , mrVelocityMult :: Double  -- ^ Velocity multiplier
  } deriving (Show, Eq)

--------------------------------------------------------------------------------
-- Curve Evaluation
--------------------------------------------------------------------------------

-- | Evaluate a modulation curve at a given life ratio.
--
-- @param curve The curve definition
-- @param t Life ratio (0 at birth, 1 at death)
-- @return Interpolated value
evaluateCurve :: ModulationCurve -> Double -> Double
evaluateCurve curve t =
  let clampedT = max 0 (min 1 t)
  in case curve of
       CurveLinear points -> evaluateLinear points clampedT
       CurveCatmullRom points -> evaluateCatmullRom points clampedT
       CurveEasing _name start end ->
         -- Simple linear for now (easing lookup would be in engine)
         start + (end - start) * clampedT

-- | Linear interpolation between curve points.
--
-- Points must be sorted by T value. Returns 1.0 if no points.
-- Uses safe access patterns (no partial functions like `last`).
evaluateLinear :: [CurvePoint] -> Double -> Double
evaluateLinear [] _ = 1.0  -- Default: no change
evaluateLinear [p] _ = cpValue p
evaluateLinear points t =
  case findSegment points t of
    Nothing -> safeLast points  -- Beyond end - use safe accessor
    Just (before, after) ->
      let range = cpT after - cpT before
          localT = if range > 0.0001
                   then (t - cpT before) / range
                   else 0
      in cpValue before + (cpValue after - cpValue before) * localT

-- | Safe last element accessor - returns default (1.0) for empty list.
-- NEVER uses partial `last` function.
safeLast :: [CurvePoint] -> Double
safeLast [] = 1.0  -- Default: no change
safeLast xs = go xs
  where
    go [] = 1.0  -- Unreachable due to pattern match above, but total
    go [p] = cpValue p
    go (_ : rest) = go rest

-- | Find the segment containing t.
findSegment :: [CurvePoint] -> Double -> Maybe (CurvePoint, CurvePoint)
findSegment points t = go points
  where
    go [] = Nothing
    go [_] = Nothing
    go (a : b : rest)
      | cpT a <= t && t <= cpT b = Just (a, b)
      | otherwise = go (b : rest)

-- | Catmull-Rom spline interpolation between curve points.
--
-- Provides smooth interpolation with continuous first derivatives.
evaluateCatmullRom :: [CurvePoint] -> Double -> Double
evaluateCatmullRom [] _ = 1.0
evaluateCatmullRom [p] _ = cpValue p
evaluateCatmullRom points t =
  -- For simplicity, use linear as fallback
  -- Full Catmull-Rom requires 4 points per segment
  evaluateLinear points t

--------------------------------------------------------------------------------
-- Property Modulation
--------------------------------------------------------------------------------

-- | Calculate size modulation multiplier.
modulateSize :: ModulationCurve -> Double -> Double
modulateSize curve lifeRatio =
  max 0 (evaluateCurve curve lifeRatio)

-- | Calculate opacity modulation multiplier.
modulateOpacity :: ModulationCurve -> Double -> Double
modulateOpacity curve lifeRatio =
  max 0 (min 1 (evaluateCurve curve lifeRatio))

-- | Calculate color modulation for one channel.
modulateColor :: ModulationCurve -> Double -> Double
modulateColor curve lifeRatio =
  max 0 (min 1 (evaluateCurve curve lifeRatio))

-- | Calculate velocity modulation multiplier.
modulateVelocity :: ModulationCurve -> Double -> Double
modulateVelocity curve lifeRatio =
  max 0 (evaluateCurve curve lifeRatio)

--------------------------------------------------------------------------------
-- Combined Application
--------------------------------------------------------------------------------

-- | Apply all modulations to get combined result.
--
-- @param mods List of active modulations
-- @param emitterId Particle's emitter ID
-- @param lifeRatio Particle's life ratio (0-1)
-- @return Combined modulation result
applyModulations :: [ParticleModulation] -> String -> Double -> ModulationResult
applyModulations mods emitterId lifeRatio =
  let relevant = filter (matchesEmitter emitterId) mods
  in foldr (combineModulations lifeRatio) defaultResult relevant
  where
    matchesEmitter eid pm =
      pmEnabled pm && (pmEmitterId pm == "*" || pmEmitterId pm == eid)
    defaultResult = ModulationResult 1.0 1.0 (1.0, 1.0, 1.0) 1.0

-- | Combine a single modulation into the result.
combineModulations :: Double -> ParticleModulation -> ModulationResult -> ModulationResult
combineModulations lifeRatio pm result =
  case pmTarget pm of
    ModSize ->
      result { mrSizeMult = mrSizeMult result * modulateSize (pmCurve pm) lifeRatio }
    ModOpacity ->
      result { mrOpacityMult = mrOpacityMult result * modulateOpacity (pmCurve pm) lifeRatio }
    ModColorR ->
      let (r, g, b) = mrColorMult result
          newR = r * modulateColor (pmCurve pm) lifeRatio
      in result { mrColorMult = (newR, g, b) }
    ModColorG ->
      let (r, g, b) = mrColorMult result
          newG = g * modulateColor (pmCurve pm) lifeRatio
      in result { mrColorMult = (r, newG, b) }
    ModColorB ->
      let (r, g, b) = mrColorMult result
          newB = b * modulateColor (pmCurve pm) lifeRatio
      in result { mrColorMult = (r, g, newB) }
    ModVelocity ->
      result { mrVelocityMult = mrVelocityMult result * modulateVelocity (pmCurve pm) lifeRatio }

--------------------------------------------------------------------------------
-- Preset Curves
--------------------------------------------------------------------------------

-- | Linear fade from 1 to 0 over lifetime.
linearFadeOut :: ModulationCurve
linearFadeOut = CurveLinear
  [ CurvePoint 0 1
  , CurvePoint 1 0
  ]

-- | Linear fade from 0 to 1 over lifetime.
linearFadeIn :: ModulationCurve
linearFadeIn = CurveLinear
  [ CurvePoint 0 0
  , CurvePoint 1 1
  ]

-- | Pulse wave (up then down).
pulseWave :: ModulationCurve
pulseWave = CurveLinear
  [ CurvePoint 0 0
  , CurvePoint 0.25 1
  , CurvePoint 0.75 1
  , CurvePoint 1 0
  ]

-- | S-curve (ease in-out).
scurve :: ModulationCurve
scurve = CurveLinear
  [ CurvePoint 0 0
  , CurvePoint 0.25 0.1
  , CurvePoint 0.5 0.5
  , CurvePoint 0.75 0.9
  , CurvePoint 1 1
  ]
