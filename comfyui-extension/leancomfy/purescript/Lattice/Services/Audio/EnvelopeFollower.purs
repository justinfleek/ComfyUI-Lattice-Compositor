-- | Lattice.Services.Audio.EnvelopeFollower - Envelope Follower Math
-- |
-- | Pure mathematical functions for audio envelope following:
-- | - Attack/release envelope calculation
-- | - Smoothing (low-pass filter)
-- | - Peak hold and decay
-- |
-- | These are the stateless mathematical kernels - actual state management
-- | happens in the TypeScript AudioReactiveMapper class.
-- |
-- | Source: ui/src/services/audioReactiveMapping.ts (release envelope logic)

module Lattice.Services.Audio.EnvelopeFollower
  ( -- * Attack/Release Envelope
    envelopeStep
  , envelopeOutput
  , envelopeFollowerStep
    -- * Smoothing
  , smoothingStep
  , smoothingFromTimeConstant
    -- * Peak Hold
  , peakHoldStep
    -- * Combined Processing
  , processWithEnvelopeAndSmoothing
  ) where

import Prelude
import Math (exp, max) as Math

--------------------------------------------------------------------------------
-- Attack/Release Envelope
--------------------------------------------------------------------------------

-- | Calculate new envelope value with attack and release.
-- |
-- | currentValue: Current input signal value
-- | envelopeValue: Previous envelope state
-- | release: Release parameter [0, 1] where 0=instant, 1=slow decay
-- |
-- | Attack: Instantly follows input when input > envelope
-- | Release: Decays exponentially when input < envelope
envelopeStep :: Number -> Number -> Number -> Number
envelopeStep currentValue envelopeValue release
  | currentValue > envelopeValue = currentValue
  | otherwise =
      let decayRate = 1.0 - release * 0.98
      in envelopeValue * decayRate

-- | Calculate output value combining input with decaying envelope.
-- |
-- | Returns the maximum of current value and envelope for
-- | smooth decay behavior.
envelopeOutput :: Number -> Number -> Number
envelopeOutput currentValue envelopeValue = Math.max currentValue envelopeValue

-- | Full envelope follower step.
-- |
-- | Returns { newEnvelope, output } record.
envelopeFollowerStep :: Number -> Number -> Number
                    -> { newEnvelope :: Number, output :: Number }
envelopeFollowerStep currentValue envelopeValue release =
  let newEnvelope = envelopeStep currentValue envelopeValue release
      output = envelopeOutput currentValue newEnvelope
  in { newEnvelope, output }

--------------------------------------------------------------------------------
-- Smoothing (Low-Pass Filter)
--------------------------------------------------------------------------------

-- | Apply exponential smoothing (one-pole low-pass filter).
-- |
-- | currentValue: New input value
-- | previousSmoothed: Previous smoothed output
-- | smoothing: Smoothing factor [0, 1] where 0=no smoothing, 1=no change
-- |
-- | Higher smoothing = slower response to changes.
smoothingStep :: Number -> Number -> Number -> Number
smoothingStep currentValue previousSmoothed smoothing =
  previousSmoothed * smoothing + currentValue * (1.0 - smoothing)

-- | Calculate smoothing coefficient from time constant.
-- |
-- | tau: Time constant (frames for ~63% response)
smoothingFromTimeConstant :: Number -> Number
smoothingFromTimeConstant tau
  | tau <= 0.0 = 0.0
  | otherwise = Math.exp (-1.0 / tau)

--------------------------------------------------------------------------------
-- Peak Hold
--------------------------------------------------------------------------------

-- | Peak hold with decay.
-- |
-- | Holds peak value for holdFrames, then decays.
-- |
-- | Returns: { newPeak, newHoldCounter }
peakHoldStep :: Number -> Number -> Int -> Int -> Number
            -> { newPeak :: Number, newHoldCounter :: Int }
peakHoldStep currentValue peakValue holdCounter holdFrames decayRate
  | currentValue > peakValue = { newPeak: currentValue, newHoldCounter: holdFrames }
  | holdCounter > 0 = { newPeak: peakValue, newHoldCounter: holdCounter - 1 }
  | otherwise = { newPeak: peakValue * decayRate, newHoldCounter: 0 }

--------------------------------------------------------------------------------
-- Combined Processing
--------------------------------------------------------------------------------

-- | Apply full envelope + smoothing chain.
-- |
-- | 1. Envelope follower (attack/release)
-- | 2. Smoothing (low-pass)
-- |
-- | Returns { newEnvelope, smoothedOutput }
processWithEnvelopeAndSmoothing :: Number -> Number -> Number -> Number -> Number
                               -> { newEnvelope :: Number, smoothedOutput :: Number }
processWithEnvelopeAndSmoothing currentValue envelopeValue previousSmoothed release smoothing =
  let result = envelopeFollowerStep currentValue envelopeValue release
      smoothedOutput = smoothingStep result.output previousSmoothed smoothing
  in { newEnvelope: result.newEnvelope, smoothedOutput }
