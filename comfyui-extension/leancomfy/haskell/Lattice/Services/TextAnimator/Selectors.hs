{-|
{-# LANGUAGE OverloadedStrings #-}
Module      : Lattice.Services.TextAnimator.Selectors
Description : Text Animator Selector Math
Copyright   : (c) Lattice Team, 2026
License     : MIT

Pure mathematical functions for text animation selectors:
- Range selector shapes (square, ramp, triangle, round, smooth)
- Selector mode combinations (add, subtract, intersect, min, max, difference)
- Wiggly selector oscillation
- Character position calculations

Features:
- 6 selector shapes for character influence curves
- 6 selector modes for combining multiple selectors
- Temporal wiggly oscillation with correlation
- Ease high/low range mapping

Source: ui/src/services/textAnimator.ts
-}

{-# LANGUAGE StrictData #-}

module Lattice.Services.TextAnimator.Selectors
  ( -- * Types
    SelectorShape(..)
  , SelectorMode(..)
  , EaseConfig(..)
  , WigglyConfig(..)
    -- * Defaults
  , defaultEaseConfig
  , defaultWigglyConfig
    -- * Shape Functions
  , applyShapeRaw
  , applyShape
    -- * Selector Combination
  , combineSelectorValues
    -- * Character Position
  , characterPosition
  , isInRange
    -- * Wiggly Selector
  , calculateWigglyPhase
  , wigglyInfluenceFromPhase
  , calculateWigglyOffset
    -- * Utilities
  , applySmoothness
  , wrapTo100
  , applyOffset
  ) where

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Selector shape for character influence curves
data SelectorShape
  = ShapeSquare     -- ^ Constant 1 across range
  | ShapeRampUp     -- ^ Linear 0 to 1
  | ShapeRampDown   -- ^ Linear 1 to 0
  | ShapeTriangle   -- ^ Peak at center
  | ShapeRound      -- ^ Sinusoidal curve
  | ShapeSmooth     -- ^ Smooth step (ease in-out)
  deriving (Show, Eq)

-- | Selector mode for combining multiple selectors
data SelectorMode
  = ModeAdd        -- ^ Clamp(base + new, 0, 1)
  | ModeSubtract   -- ^ Clamp(base - new, 0, 1)
  | ModeIntersect  -- ^ base * new
  | ModeMin        -- ^ min(base, new)
  | ModeMax        -- ^ max(base, new)
  | ModeDifference -- ^ abs(base - new)
  deriving (Show, Eq)

-- | Ease configuration for range mapping
data EaseConfig = EaseConfig
  { ecHigh :: Double  -- ^ Output at shape value 1.0 (percentage)
  , ecLow  :: Double  -- ^ Output at shape value 0.0 (percentage)
  } deriving (Show, Eq)

-- | Default ease config
defaultEaseConfig :: EaseConfig
defaultEaseConfig = EaseConfig { ecHigh = 100, ecLow = 0 }

-- | Wiggly selector configuration
data WigglyConfig = WigglyConfig
  { wcWigglesPerSecond :: Double  -- ^ Oscillation frequency
  , wcCorrelation      :: Double  -- ^ 0-100, blend between individual/group
  , wcMinAmount        :: Double  -- ^ Minimum output (percentage)
  , wcMaxAmount        :: Double  -- ^ Maximum output (percentage)
  , wcLockDimensions   :: Bool    -- ^ Use same value for X and Y
  } deriving (Show, Eq)

-- | Default wiggly config
defaultWigglyConfig :: WigglyConfig
defaultWigglyConfig = WigglyConfig
  { wcWigglesPerSecond = 2
  , wcCorrelation = 50
  , wcMinAmount = 0
  , wcMaxAmount = 100
  , wcLockDimensions = False
  }

--------------------------------------------------------------------------------
-- Shape Functions
--------------------------------------------------------------------------------

-- | Apply selector shape to normalized position (0-1).
--
-- Returns the raw shape value before ease mapping.
applyShapeRaw :: Double -> SelectorShape -> Double
applyShapeRaw t shape = case shape of
  ShapeSquare   -> 1
  ShapeRampUp   -> t
  ShapeRampDown -> 1 - t
  ShapeTriangle -> 1 - abs (2 * t - 1)
  ShapeRound    -> sin (t * pi)
  ShapeSmooth   -> t * t * (3 - 2 * t)  -- Smooth step

-- | Apply selector shape with ease high/low mapping.
--
-- Maps shape output through [low, high] range.
applyShape :: Double -> SelectorShape -> EaseConfig -> Double
applyShape t shape ease =
  let value = applyShapeRaw t shape
      easeRange = (ecHigh ease - ecLow ease) / 100
  in ecLow ease / 100 + value * easeRange

--------------------------------------------------------------------------------
-- Selector Mode Combination
--------------------------------------------------------------------------------

-- | Combine two selector values based on mode.
--
-- All outputs are clamped to [0, 1].
combineSelectorValues :: Double -> Double -> SelectorMode -> Double
combineSelectorValues baseValue newValue mode = case mode of
  ModeAdd        -> min 1 (baseValue + newValue)
  ModeSubtract   -> max 0 (baseValue - newValue)
  ModeIntersect  -> baseValue * newValue
  ModeMin        -> min baseValue newValue
  ModeMax        -> max baseValue newValue
  ModeDifference -> abs (baseValue - newValue)

--------------------------------------------------------------------------------
-- Character Position Calculation
--------------------------------------------------------------------------------

-- | Calculate character position as percentage (0-100).
characterPosition :: Int -> Int -> Double
characterPosition charIndex totalChars
  | totalChars <= 1 = 0
  | otherwise = (fromIntegral charIndex / fromIntegral (totalChars - 1)) * 100

-- | Check if character is within selector range.
--
-- Handles wraparound when offset causes start > end.
-- Returns (inRange, positionInRange)
isInRange :: Double -> Double -> Double -> Bool -> (Bool, Double)
isInRange charPosition effectiveStart effectiveEnd rangeWraps
  | rangeWraps =
      if charPosition >= effectiveStart then
        -- In upper segment [effectiveStart, 100]
        let upperSegmentSize = 100 - effectiveStart
            totalRangeSize = upperSegmentSize + effectiveEnd
            posInRange = if totalRangeSize > 0
                         then (charPosition - effectiveStart) / totalRangeSize
                         else 0
        in (True, posInRange)
      else if charPosition <= effectiveEnd then
        -- In lower segment [0, effectiveEnd]
        let upperSegmentSize = 100 - effectiveStart
            totalRangeSize = upperSegmentSize + effectiveEnd
            posInRange = if totalRangeSize > 0
                         then (upperSegmentSize + charPosition) / totalRangeSize
                         else 1
        in (True, posInRange)
      else
        -- In the gap
        (False, 0)
  | otherwise =
      let normalizedStart = min effectiveStart effectiveEnd
          normalizedEnd = max effectiveStart effectiveEnd
      in if charPosition < normalizedStart || charPosition > normalizedEnd
         then (False, 0)
         else let rangeSize = normalizedEnd - normalizedStart
                  posInRange = if rangeSize > 0
                               then (charPosition - normalizedStart) / rangeSize
                               else 0.5
              in (True, posInRange)

--------------------------------------------------------------------------------
-- Wiggly Selector Math
--------------------------------------------------------------------------------

-- | Calculate wiggly phase with correlation.
--
-- Blends between individual character phase and group phase.
calculateWigglyPhase :: Double -> Double -> Double -> Double -> Double
calculateWigglyPhase time wigglesPerSecond baseRandom correlation =
  let wigglePhase = time * wigglesPerSecond * pi * 2
      correlationFactor = correlation / 100
      groupPhase = wigglePhase
      individualPhase = wigglePhase + baseRandom * pi * 2
  in individualPhase * (1 - correlationFactor) + groupPhase * correlationFactor

-- | Calculate wiggly influence from phase.
--
-- Maps sine wave output to [minAmount, maxAmount] range.
wigglyInfluenceFromPhase :: Double -> Double -> Double -> Double
wigglyInfluenceFromPhase phase minAmount maxAmount =
  let wiggleValue = sin phase  -- -1 to 1
      range = maxAmount - minAmount
      amount = minAmount + ((wiggleValue + 1) / 2) * range
  in amount / 100  -- Normalize to 0-1

-- | Calculate wiggly offset for 2D properties.
--
-- Returns (x, y) offsets.
calculateWigglyOffset :: Double -> WigglyConfig -> Double -> Double -> (Double, Double)
calculateWigglyOffset time config baseRandomX baseRandomY =
  let wigglePhase = time * wcWigglesPerSecond config * pi * 2
      correlationFactor = wcCorrelation config / 100

      -- Group phase
      groupPhaseX = sin wigglePhase
      groupPhaseY = if wcLockDimensions config then groupPhaseX else cos wigglePhase

      -- Individual phase
      individualPhaseX = sin (wigglePhase + baseRandomX * pi * 2)
      individualPhaseY = sin (wigglePhase + baseRandomY * pi * 2)

      -- Blend
      x = individualPhaseX * (1 - correlationFactor) + groupPhaseX * correlationFactor
      y = individualPhaseY * (1 - correlationFactor) + groupPhaseY * correlationFactor

      -- Scale by average amount
      amount = (wcMaxAmount config + wcMinAmount config) / 2 / 100

  in (x * amount, y * amount)

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

-- | Apply smoothness to influence value.
--
-- Interpolates towards 0.5 based on smoothness factor.
applySmoothness :: Double -> Double -> Double
applySmoothness influence smoothness
  | smoothness >= 100 = influence
  | otherwise = let smoothFactor = smoothness / 100
                in influence * smoothFactor + 0.5 * (1 - smoothFactor)

-- | Wrap value to 0-100 range.
--
-- 100 stays as 100, doesn't wrap to 0.
wrapTo100 :: Double -> Double
wrapTo100 val =
  let modVal = ((val `mod'` 100) + 100) `mod'` 100
  in if modVal == 0 && val /= 0 then 100 else modVal
  where
    mod' a b = a - b * fromIntegral (floor (a / b) :: Int)

-- | Apply offset to start/end values with wrapping.
applyOffset :: Double -> Double -> Double -> (Double, Double)
applyOffset startValue endValue offset =
  (wrapTo100 (startValue + offset), wrapTo100 (endValue + offset))
