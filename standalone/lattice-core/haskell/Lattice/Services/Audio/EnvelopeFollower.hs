{-# LANGUAGE StrictData #-}

{-|
Module      : Lattice.Services.Audio.EnvelopeFollower
Description : Envelope Follower Math
Copyright   : (c) Lattice, 2026
License     : MIT

Pure mathematical functions for audio envelope following:
- Attack/release envelope calculation
- Smoothing (low-pass filter)
- Peak hold and decay

These are the stateless mathematical kernels - actual state management
happens in the TypeScript AudioReactiveMapper class.

Source: ui/src/services/audioReactiveMapping.ts (release envelope logic)
-}

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

--------------------------------------------------------------------------------
-- Attack/Release Envelope
--------------------------------------------------------------------------------

-- | Calculate new envelope value with attack and release.
--
--   currentValue: Current input signal value
--   envelopeValue: Previous envelope state
--   release: Release parameter [0, 1] where 0=instant, 1=slow decay
--
--   Attack: Instantly follows input when input > envelope
--   Release: Decays exponentially when input < envelope
envelopeStep :: Double -> Double -> Double -> Double
envelopeStep currentValue envelopeValue release
  | currentValue > envelopeValue = currentValue
  | otherwise =
      let decayRate = 1 - release * 0.98
      in envelopeValue * decayRate

-- | Calculate output value combining input with decaying envelope.
--
--   Returns the maximum of current value and envelope for
--   smooth decay behavior.
envelopeOutput :: Double -> Double -> Double
envelopeOutput currentValue envelopeValue = max currentValue envelopeValue

-- | Full envelope follower step.
--
--   Returns (newEnvelope, outputValue) tuple.
envelopeFollowerStep :: Double -> Double -> Double -> (Double, Double)
envelopeFollowerStep currentValue envelopeValue release =
  let newEnvelope = envelopeStep currentValue envelopeValue release
      output = envelopeOutput currentValue newEnvelope
  in (newEnvelope, output)

--------------------------------------------------------------------------------
-- Smoothing (Low-Pass Filter)
--------------------------------------------------------------------------------

-- | Apply exponential smoothing (one-pole low-pass filter).
--
--   currentValue: New input value
--   previousSmoothed: Previous smoothed output
--   smoothing: Smoothing factor [0, 1] where 0=no smoothing, 1=no change
--
--   Higher smoothing = slower response to changes.
smoothingStep :: Double -> Double -> Double -> Double
smoothingStep currentValue previousSmoothed smoothing =
  previousSmoothed * smoothing + currentValue * (1 - smoothing)

-- | Calculate smoothing coefficient from time constant.
--
--   tau: Time constant (frames for ~63% response)
smoothingFromTimeConstant :: Double -> Double
smoothingFromTimeConstant tau
  | tau <= 0 = 0
  | otherwise = exp (-1 / tau)

--------------------------------------------------------------------------------
-- Peak Hold
--------------------------------------------------------------------------------

-- | Peak hold with decay.
--
--   Holds peak value for holdFrames, then decays.
--
--   Returns: (newPeak, newHoldCounter)
peakHoldStep :: Double -> Double -> Int -> Int -> Double -> (Double, Int)
peakHoldStep currentValue peakValue holdCounter holdFrames decayRate
  | currentValue > peakValue = (currentValue, holdFrames)
  | holdCounter > 0 = (peakValue, holdCounter - 1)
  | otherwise = (peakValue * decayRate, 0)

--------------------------------------------------------------------------------
-- Combined Processing
--------------------------------------------------------------------------------

-- | Apply full envelope + smoothing chain.
--
--   1. Envelope follower (attack/release)
--   2. Smoothing (low-pass)
--
--   Returns (newEnvelope, smoothedOutput)
processWithEnvelopeAndSmoothing :: Double -> Double -> Double -> Double -> Double
                               -> (Double, Double)
processWithEnvelopeAndSmoothing currentValue envelopeValue previousSmoothed release smoothing =
  let (newEnvelope, envelopeOut) = envelopeFollowerStep currentValue envelopeValue release
      smoothedOut = smoothingStep envelopeOut previousSmoothed smoothing
  in (newEnvelope, smoothedOut)
