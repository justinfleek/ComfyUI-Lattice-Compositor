-- | Lattice.Services.TextAnimator.Selectors - Text Animator Selector Math
-- |
-- | Pure mathematical functions for text animation selectors:
-- | - Range selector shapes (square, ramp, triangle, round, smooth)
-- | - Selector mode combinations (add, subtract, intersect, min, max, difference)
-- | - Wiggly selector oscillation
-- | - Character position calculations
-- |
-- | Features:
-- | - 6 selector shapes for character influence curves
-- | - 6 selector modes for combining multiple selectors
-- | - Temporal wiggly oscillation with correlation
-- | - Ease high/low range mapping
-- |
-- | Source: ui/src/services/textAnimator.ts

module Lattice.Services.TextAnimator.Selectors
  ( SelectorShape(..)
  , SelectorMode(..)
  , EaseConfig
  , WigglyConfig
  , defaultEaseConfig
  , defaultWigglyConfig
  , applyShapeRaw
  , applyShape
  , combineSelectorValues
  , characterPosition
  , isInRange
  , calculateWigglyPhase
  , wigglyInfluenceFromPhase
  , calculateWigglyOffset
  , applySmoothness
  , wrapTo100
  , applyOffset
  ) where

import Prelude

import Data.Tuple (Tuple(..))
import Math (abs, cos, floor, pi, sin)

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

derive instance eqSelectorShape :: Eq SelectorShape

-- | Selector mode for combining multiple selectors
data SelectorMode
  = ModeAdd        -- ^ Clamp(base + new, 0, 1)
  | ModeSubtract   -- ^ Clamp(base - new, 0, 1)
  | ModeIntersect  -- ^ base * new
  | ModeMin        -- ^ min(base, new)
  | ModeMax        -- ^ max(base, new)
  | ModeDifference -- ^ abs(base - new)

derive instance eqSelectorMode :: Eq SelectorMode

-- | Ease configuration for range mapping
type EaseConfig =
  { high :: Number  -- ^ Output at shape value 1.0 (percentage)
  , low  :: Number  -- ^ Output at shape value 0.0 (percentage)
  }

-- | Default ease config
defaultEaseConfig :: EaseConfig
defaultEaseConfig = { high: 100.0, low: 0.0 }

-- | Wiggly selector configuration
type WigglyConfig =
  { wigglesPerSecond :: Number  -- ^ Oscillation frequency
  , correlation      :: Number  -- ^ 0-100, blend between individual/group
  , minAmount        :: Number  -- ^ Minimum output (percentage)
  , maxAmount        :: Number  -- ^ Maximum output (percentage)
  , lockDimensions   :: Boolean -- ^ Use same value for X and Y
  }

-- | Default wiggly config
defaultWigglyConfig :: WigglyConfig
defaultWigglyConfig =
  { wigglesPerSecond: 2.0
  , correlation: 50.0
  , minAmount: 0.0
  , maxAmount: 100.0
  , lockDimensions: false
  }

--------------------------------------------------------------------------------
-- Shape Functions
--------------------------------------------------------------------------------

-- | Apply selector shape to normalized position (0-1).
-- |
-- | Returns the raw shape value before ease mapping.
applyShapeRaw :: Number -> SelectorShape -> Number
applyShapeRaw t shape = case shape of
  ShapeSquare   -> 1.0
  ShapeRampUp   -> t
  ShapeRampDown -> 1.0 - t
  ShapeTriangle -> 1.0 - abs (2.0 * t - 1.0)
  ShapeRound    -> sin (t * pi)
  ShapeSmooth   -> t * t * (3.0 - 2.0 * t)  -- Smooth step

-- | Apply selector shape with ease high/low mapping.
-- |
-- | Maps shape output through [low, high] range.
applyShape :: Number -> SelectorShape -> EaseConfig -> Number
applyShape t shape ease =
  let value = applyShapeRaw t shape
      easeRange = (ease.high - ease.low) / 100.0
  in ease.low / 100.0 + value * easeRange

--------------------------------------------------------------------------------
-- Selector Mode Combination
--------------------------------------------------------------------------------

-- | Combine two selector values based on mode.
-- |
-- | All outputs are clamped to [0, 1].
combineSelectorValues :: Number -> Number -> SelectorMode -> Number
combineSelectorValues baseValue newValue mode = case mode of
  ModeAdd        -> min 1.0 (baseValue + newValue)
  ModeSubtract   -> max 0.0 (baseValue - newValue)
  ModeIntersect  -> baseValue * newValue
  ModeMin        -> min baseValue newValue
  ModeMax        -> max baseValue newValue
  ModeDifference -> abs (baseValue - newValue)

--------------------------------------------------------------------------------
-- Character Position Calculation
--------------------------------------------------------------------------------

-- | Calculate character position as percentage (0-100).
characterPosition :: Int -> Int -> Number
characterPosition charIndex totalChars
  | totalChars <= 1 = 0.0
  | otherwise = (toNumber charIndex / toNumber (totalChars - 1)) * 100.0

-- | Check if character is within selector range.
-- |
-- | Handles wraparound when offset causes start > end.
-- | Returns Tuple(inRange, positionInRange)
isInRange :: Number -> Number -> Number -> Boolean -> Tuple Boolean Number
isInRange charPosition effectiveStart effectiveEnd rangeWraps
  | rangeWraps =
      if charPosition >= effectiveStart then
        -- In upper segment [effectiveStart, 100]
        let upperSegmentSize = 100.0 - effectiveStart
            totalRangeSize = upperSegmentSize + effectiveEnd
            posInRange = if totalRangeSize > 0.0
                         then (charPosition - effectiveStart) / totalRangeSize
                         else 0.0
        in Tuple true posInRange
      else if charPosition <= effectiveEnd then
        -- In lower segment [0, effectiveEnd]
        let upperSegmentSize = 100.0 - effectiveStart
            totalRangeSize = upperSegmentSize + effectiveEnd
            posInRange = if totalRangeSize > 0.0
                         then (upperSegmentSize + charPosition) / totalRangeSize
                         else 1.0
        in Tuple true posInRange
      else
        -- In the gap
        Tuple false 0.0
  | otherwise =
      let normalizedStart = min effectiveStart effectiveEnd
          normalizedEnd = max effectiveStart effectiveEnd
      in if charPosition < normalizedStart || charPosition > normalizedEnd
         then Tuple false 0.0
         else let rangeSize = normalizedEnd - normalizedStart
                  posInRange = if rangeSize > 0.0
                               then (charPosition - normalizedStart) / rangeSize
                               else 0.5
              in Tuple true posInRange

--------------------------------------------------------------------------------
-- Wiggly Selector Math
--------------------------------------------------------------------------------

-- | Calculate wiggly phase with correlation.
-- |
-- | Blends between individual character phase and group phase.
calculateWigglyPhase :: Number -> Number -> Number -> Number -> Number
calculateWigglyPhase time wigglesPerSecond baseRandom correlation =
  let wigglePhase = time * wigglesPerSecond * pi * 2.0
      correlationFactor = correlation / 100.0
      groupPhase = wigglePhase
      individualPhase = wigglePhase + baseRandom * pi * 2.0
  in individualPhase * (1.0 - correlationFactor) + groupPhase * correlationFactor

-- | Calculate wiggly influence from phase.
-- |
-- | Maps sine wave output to [minAmount, maxAmount] range.
wigglyInfluenceFromPhase :: Number -> Number -> Number -> Number
wigglyInfluenceFromPhase phase minAmount maxAmount =
  let wiggleValue = sin phase  -- -1 to 1
      range = maxAmount - minAmount
      amount = minAmount + ((wiggleValue + 1.0) / 2.0) * range
  in amount / 100.0  -- Normalize to 0-1

-- | Calculate wiggly offset for 2D properties.
-- |
-- | Returns Tuple(x, y) offsets.
calculateWigglyOffset :: Number -> WigglyConfig -> Number -> Number -> Tuple Number Number
calculateWigglyOffset time config baseRandomX baseRandomY =
  let wigglePhase = time * config.wigglesPerSecond * pi * 2.0
      correlationFactor = config.correlation / 100.0

      -- Group phase
      groupPhaseX = sin wigglePhase
      groupPhaseY = if config.lockDimensions then groupPhaseX else cos wigglePhase

      -- Individual phase
      individualPhaseX = sin (wigglePhase + baseRandomX * pi * 2.0)
      individualPhaseY = sin (wigglePhase + baseRandomY * pi * 2.0)

      -- Blend
      x = individualPhaseX * (1.0 - correlationFactor) + groupPhaseX * correlationFactor
      y = individualPhaseY * (1.0 - correlationFactor) + groupPhaseY * correlationFactor

      -- Scale by average amount
      amount = (config.maxAmount + config.minAmount) / 2.0 / 100.0

  in Tuple (x * amount) (y * amount)

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

-- | Apply smoothness to influence value.
-- |
-- | Interpolates towards 0.5 based on smoothness factor.
applySmoothness :: Number -> Number -> Number
applySmoothness influence smoothness
  | smoothness >= 100.0 = influence
  | otherwise = let smoothFactor = smoothness / 100.0
                in influence * smoothFactor + 0.5 * (1.0 - smoothFactor)

-- | Wrap value to 0-100 range.
-- |
-- | 100 stays as 100, doesn't wrap to 0.
wrapTo100 :: Number -> Number
wrapTo100 val =
  let modVal = mod' (mod' val 100.0 + 100.0) 100.0
  in if modVal == 0.0 && val /= 0.0 then 100.0 else modVal
  where
    mod' a b = a - b * floor (a / b)

-- | Apply offset to start/end values with wrapping.
applyOffset :: Number -> Number -> Number -> Tuple Number Number
applyOffset startValue endValue offset =
  Tuple (wrapTo100 (startValue + offset)) (wrapTo100 (endValue + offset))

-- | Convert Int to Number
toNumber :: Int -> Number
toNumber n = if n < 0 then negate (toNumberPos (negate n)) else toNumberPos n
  where
    toNumberPos :: Int -> Number
    toNumberPos 0 = 0.0
    toNumberPos i = 1.0 + toNumberPos (i - 1)
