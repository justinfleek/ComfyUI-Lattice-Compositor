-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // schema // audio // meter
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Audio metering and measurement types.
-- |
-- | ## Metering Standards
-- | - VU: Volume Units (standardized loudness)
-- | - Peak: Maximum sample level
-- | - RMS: Root Mean Square (average power)
-- | - LUFS: Loudness Units Full Scale (perceptual)
-- | - Phase: Stereo correlation
-- |
-- | ## Dependencies
-- | - Prelude
-- | - Audio.Level (DecibelFS, LinearGain)
-- | - Audio.Time (Duration)
-- |
-- | ## Dependents
-- | - UI.Meter (visual meters)
-- | - Analysis.* (loudness measurement)

module Hydrogen.Schema.Audio.Meter
  ( -- * Meter Type
    MeterType(MeterVU, MeterPeak, MeterRMS, MeterLUFS, MeterPhase)
  
    -- * Meter Value
  , MeterValue
  
    -- * VU Meter
  , VUMeter
  , vuMeter
  , vuMeterBounds
  , isOptimalVU
  , isClippingVU
  
    -- * Peak Meter
  , PeakMeter
  , peakMeter
  , peakMeterBounds
  , isClippingPeak
  , TruePeak
  , truePeakBounds
  
    -- * RMS Meter
  , RMSMeter
  , rmsMeter
  , rmsMeterBounds
  , rmsToPower
  , powerToRMS
  
    -- * LUFS Meter
  , LUFS
  , lufsMeter
  , lufsBounds
  , IntegratedLUFS
  , ShortTermLUFS
  , MomentaryLUFS
  , LoudnessRange
  , lraBounds
  , LUFSFP
  
    -- * Phase Meter
  , PhaseCorrelation
  , phaseCorrelation
  , phaseBounds
  , isMonoInPhase
  , isMonoOutOfPhase
  , isUncorrelated
  
    -- * Meter State
  , MeterState
  , defaultMeterState
  , isMeterClipping
  , isLUFSOnTarget
  ) where

import Prelude
import Data.Number (log, pow)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // meter // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Meter type
data MeterType = MeterVU | MeterPeak | MeterRMS | MeterLUFS | MeterPhase

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // meter // value  
-- ═════════════════════════════════════════════════════════════════════════════

-- | Meter reading value
type MeterValue = Number

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                         // vu
-- ═════════════════════════════════════════════════════════════════════════════

-- | VU (Volume Unit) meter reading
-- |
-- | VU meters show average loudness using a standardized ballistics curve.
-- | Range: -20dB to +3dB (standard), with 0dB = unity gain.
type VUMeter = Number

-- | VU meter reading bounds
vuMeterBounds :: { min :: Number, max :: Number, zero :: Number, peak :: Number }
vuMeterBounds = { min: -20.0, max: 3.0, zero: 0.0, peak: 3.0 }

-- | Create VU reading
vuMeter :: Number -> VUMeter
vuMeter n = if n < vuMeterBounds.min then vuMeterBounds.min
            else if n > vuMeterBounds.max then vuMeterBounds.max
            else n

-- | Check if VU is in optimal range
isOptimalVU :: VUMeter -> Boolean
isOptimalVU v = v >= -3.0 && v <= 0.0

-- | Check if VU is clipping
isClippingVU :: VUMeter -> Boolean
isClippingVU v = v > vuMeterBounds.zero

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // peak
-- ═════════════════════════════════════════════════════════════════════════════

-- | Peak meter reading
-- |
-- | Shows maximum sample value. True peak can exceed 0dB due to inter-sample peaks.
type PeakMeter = Number

-- | Peak meter bounds
peakMeterBounds :: { min :: Number, max :: Number, clip :: Number }
peakMeterBounds = { min: -60.0, max: 3.0, clip: 0.0 }

-- | Create peak reading
peakMeter :: Number -> PeakMeter
peakMeter n = if n < peakMeterBounds.min then peakMeterBounds.min
              else if n > peakMeterBounds.max then peakMeterBounds.max
              else n

-- | Check for clipping
isClippingPeak :: PeakMeter -> Boolean
isClippingPeak p = p > peakMeterBounds.clip

-- | True peak (can exceed 0dB due to reconstruction)
type TruePeak = Number

truePeakBounds :: { min :: Number, max :: Number, clip :: Number }
truePeakBounds = { min: -60.0, max: 6.0, clip: 0.0 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                        // rms
-- ═════════════════════════════════════════════════════════════════════════════

-- | RMS (Root Mean Square) meter reading
-- |
-- | Shows average power/energy of the signal. More accurate representation of perceived loudness than peak.
type RMSMeter = Number

-- | RMS meter bounds
rmsMeterBounds :: { min :: Number, max :: Number, unity :: Number }
rmsMeterBounds = { min: -60.0, max: 0.0, unity: -3.0 }

-- | Create RMS reading
rmsMeter :: Number -> RMSMeter
rmsMeter n = if n < rmsMeterBounds.min then rmsMeterBounds.min
             else if n > rmsMeterBounds.max then rmsMeterBounds.max
             else n

-- | RMS to average power conversion
rmsToPower :: RMSMeter -> Number
rmsToPower db = pow 10.0 (db / 10.0)

-- | Power to RMS conversion
powerToRMS :: Number -> RMSMeter
powerToRMS p = 10.0 * (log p) / (log 10.0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // lufs
-- ═════════════════════════════════════════════════════════════════════════════

-- | LUFS (Loudness Units Full Scale)
-- |
-- | Perceptual loudness measurement per ITU-R BS.1770 standard.
-- | Integrated loudness: overall program loudness
-- | Short-term: 3 second window
-- | Momentary: 400ms window
type LUFS = Number

-- | LUFS bounds
lufsBounds :: { min :: Number, max :: Number, target :: Number, silence :: Number }
lufsBounds = { min: -70.0, max: 0.0, target: -14.0, silence: -70.0 }

-- | Create LUFS reading
lufsMeter :: Number -> LUFS
lufsMeter n = if n < lufsBounds.min then lufsBounds.min
              else if n > lufsBounds.max then lufsBounds.max
              else n

-- | Integrated loudness (full program)
type IntegratedLUFS = LUFS

-- | Short-term loudness (3 second window)
type ShortTermLUFS = LUFS

-- | Momentary loudness (400ms window)
type MomentaryLUFS = LUFS

-- | Loudness Range (LRA) - dynamic range in LUFS
type LoudnessRange = Number

lraBounds :: { min :: Number, max :: Number }
lraBounds = { min: 0.0, max: 30.0 }

-- | True peak in LUFS measurement
type LUFSFP = TruePeak

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // phase
-- ═════════════════════════════════════════════════════════════════════════════

-- | Stereo phase correlation
-- |
-- | Range: -1 (mono out of phase) to +1 (mono in phase)
-- | 0 = stereo uncorrelated
type PhaseCorrelation = Number

-- | Phase correlation bounds
phaseBounds :: { monoOut :: Number, monoIn :: Number, uncorrelated :: Number }
phaseBounds = { monoOut: -1.0, monoIn: 1.0, uncorrelated: 0.0 }

-- | Create phase reading
phaseCorrelation :: Number -> PhaseCorrelation
phaseCorrelation n = if n < phaseBounds.monoOut then phaseBounds.monoOut
                     else if n > phaseBounds.monoIn then phaseBounds.monoIn
                     else n

-- | Check if mono in phase
isMonoInPhase :: PhaseCorrelation -> Boolean
isMonoInPhase p = p > 0.5

-- | Check if mono out of phase (phase cancellation risk)
isMonoOutOfPhase :: PhaseCorrelation -> Boolean
isMonoOutOfPhase p = p < -0.5

-- | Check if stereo uncorrelated
isUncorrelated :: PhaseCorrelation -> Boolean
isUncorrelated p = p > -0.3 && p < 0.3

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // meter // state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete meter state with all readings
type MeterState =
  { vu :: VUMeter
  , peak :: PeakMeter
  , truePeak :: TruePeak
  , rms :: RMSMeter
  , integratedLUFS :: IntegratedLUFS
  , shortTermLUFS :: ShortTermLUFS
  , momentaryLUFS :: MomentaryLUFS
  , loudnessRange :: LoudnessRange
  , phaseCorrelation :: PhaseCorrelation
  }

-- | Create default meter state
defaultMeterState :: MeterState
defaultMeterState =
  { vu: lufsBounds.silence
  , peak: peakMeterBounds.min
  , truePeak: truePeakBounds.min
  , rms: rmsMeterBounds.min
  , integratedLUFS: lufsBounds.silence
  , shortTermLUFS: lufsBounds.silence
  , momentaryLUFS: lufsBounds.silence
  , loudnessRange: 0.0
  , phaseCorrelation: 0.0
  }

-- | Check if any meter is clipping
isMeterClipping :: MeterState -> Boolean
isMeterClipping s = isClippingVU s.vu || isClippingPeak s.peak

-- | Check if LUFS is at target
isLUFSOnTarget :: MeterState -> Number -> Boolean
isLUFSOnTarget s target = 
  let diff = s.integratedLUFS - target
  in diff > -1.0 && diff < 1.0


