-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // audio // synthesis
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Synthesis parameter atoms for audio signal processing.
-- |
-- | ## Filter Parameters
-- | Cutoff frequency and resonance control filter behavior. These are the
-- | fundamental parameters for subtractive synthesis.
-- |
-- | ## Saturation and Drive
-- | Drive adds harmonic distortion, ranging from subtle warmth to heavy
-- | overdrive.
-- |
-- | ## Mix and Feedback
-- | Common parameters for effects: wet/dry mix and feedback amount.

module Hydrogen.Schema.Audio.Synthesis
  ( -- * Filter Parameters
    CutoffFreq(..)
  , Resonance(..)
  , ResonanceDb(..)
  , cutoffFreq
  , resonance
  , resonanceDb
  , unwrapCutoffFreq
  , unwrapResonance
  , unwrapResonanceDb
  
  -- * Saturation
  , Drive(..)
  , drive
  , unwrapDrive
  
  -- * Effects Parameters
  , Mix(..)
  , Feedback(..)
  , DecayTime(..)
  , mix
  , feedback
  , decayTime
  , unwrapMix
  , unwrapFeedback
  , unwrapDecayTime
  
  -- * Predefined Values
  , cutoff100
  , cutoff1k
  , cutoff5k
  , cutoff10k
  , cutoff20k
  , resonanceNone
  , resonanceMild
  , resonanceHigh
  , resonanceMax
  , mixDry
  , mixWet
  , mixHalf
  
  -- * Conversions
  , resonanceToDb
  , dbToResonance
  
  -- * Bounds
  , cutoffFreqBounds
  , resonanceBounds
  , resonanceDbBounds
  , driveBounds
  , mixBounds
  , feedbackBounds
  , decayTimeBounds
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , (*)
  , (/)
  , (<)
  , (>)
  , (<>)
  )

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // cutoff freq
-- ═════════════════════════════════════════════════════════════════════════════

-- | CutoffFreq - filter cutoff frequency in Hz.
-- | Controls where the filter begins attenuating frequencies.
-- | Clamped to [20, 20000] covering human hearing range.
newtype CutoffFreq = CutoffFreq Number

derive instance eqCutoffFreq :: Eq CutoffFreq
derive instance ordCutoffFreq :: Ord CutoffFreq

instance showCutoffFreq :: Show CutoffFreq where
  show (CutoffFreq n) = show n <> " Hz cutoff"

-- | Create a CutoffFreq value (clamped to 20-20000)
cutoffFreq :: Number -> CutoffFreq
cutoffFreq n
  | n < 20.0 = CutoffFreq 20.0
  | n > 20000.0 = CutoffFreq 20000.0
  | otherwise = CutoffFreq n

unwrapCutoffFreq :: CutoffFreq -> Number
unwrapCutoffFreq (CutoffFreq n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // resonance
-- ═════════════════════════════════════════════════════════════════════════════

-- | Resonance - filter resonance (Q factor) as normalized value.
-- | 0.0 = no resonance, 1.0 = maximum resonance (self-oscillation threshold).
-- | Controls the peak at the cutoff frequency.
newtype Resonance = Resonance Number

derive instance eqResonance :: Eq Resonance
derive instance ordResonance :: Ord Resonance

instance showResonance :: Show Resonance where
  show (Resonance n) = show n <> " Q"

-- | Create a Resonance value (clamped to 0.0-1.0)
resonance :: Number -> Resonance
resonance n
  | n < 0.0 = Resonance 0.0
  | n > 1.0 = Resonance 1.0
  | otherwise = Resonance n

unwrapResonance :: Resonance -> Number
unwrapResonance (Resonance n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // resonance db
-- ═════════════════════════════════════════════════════════════════════════════

-- | ResonanceDb - filter resonance in decibels.
-- | 0dB = flat, higher values = more peak at cutoff.
-- | Clamped to [0, 30] dB.
newtype ResonanceDb = ResonanceDb Number

derive instance eqResonanceDb :: Eq ResonanceDb
derive instance ordResonanceDb :: Ord ResonanceDb

instance showResonanceDb :: Show ResonanceDb where
  show (ResonanceDb n) = show n <> " dB resonance"

-- | Create a ResonanceDb value (clamped to 0-30)
resonanceDb :: Number -> ResonanceDb
resonanceDb n
  | n < 0.0 = ResonanceDb 0.0
  | n > 30.0 = ResonanceDb 30.0
  | otherwise = ResonanceDb n

unwrapResonanceDb :: ResonanceDb -> Number
unwrapResonanceDb (ResonanceDb n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // drive
-- ═════════════════════════════════════════════════════════════════════════════

-- | Drive - saturation/distortion amount.
-- | 0 = clean, higher values = more harmonic distortion.
-- | Clamped to [0, 10] covering subtle warmth to heavy overdrive.
newtype Drive = Drive Number

derive instance eqDrive :: Eq Drive
derive instance ordDrive :: Ord Drive

instance showDrive :: Show Drive where
  show (Drive n) = show n <> " drive"

-- | Create a Drive value (clamped to 0-10)
drive :: Number -> Drive
drive n
  | n < 0.0 = Drive 0.0
  | n > 10.0 = Drive 10.0
  | otherwise = Drive n

unwrapDrive :: Drive -> Number
unwrapDrive (Drive n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                        // mix
-- ═════════════════════════════════════════════════════════════════════════════

-- | Mix - wet/dry blend for effects.
-- | 0.0 = fully dry (unprocessed), 1.0 = fully wet (processed).
-- | 0.5 = equal blend of both signals.
newtype Mix = Mix Number

derive instance eqMix :: Eq Mix
derive instance ordMix :: Ord Mix

instance showMix :: Show Mix where
  show (Mix n) = show (n * 100.0) <> "% wet"

-- | Create a Mix value (clamped to 0.0-1.0)
mix :: Number -> Mix
mix n
  | n < 0.0 = Mix 0.0
  | n > 1.0 = Mix 1.0
  | otherwise = Mix n

unwrapMix :: Mix -> Number
unwrapMix (Mix n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // feedback
-- ═════════════════════════════════════════════════════════════════════════════

-- | Feedback - feedback amount for effects (delay, reverb, etc).
-- | 0.0 = no feedback, 1.0 = maximum stable feedback.
-- | Values approaching 1.0 create longer decay tails.
newtype Feedback = Feedback Number

derive instance eqFeedback :: Eq Feedback
derive instance ordFeedback :: Ord Feedback

instance showFeedback :: Show Feedback where
  show (Feedback n) = show (n * 100.0) <> "% feedback"

-- | Create a Feedback value (clamped to 0.0-1.0)
feedback :: Number -> Feedback
feedback n
  | n < 0.0 = Feedback 0.0
  | n > 1.0 = Feedback 1.0
  | otherwise = Feedback n

unwrapFeedback :: Feedback -> Number
unwrapFeedback (Feedback n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // decay time
-- ═════════════════════════════════════════════════════════════════════════════

-- | DecayTime - decay/release time in seconds.
-- | Used for reverb decay, envelope release, etc.
-- | Clamped to [0, 60] seconds.
newtype DecayTime = DecayTime Number

derive instance eqDecayTime :: Eq DecayTime
derive instance ordDecayTime :: Ord DecayTime

instance showDecayTime :: Show DecayTime where
  show (DecayTime n) = show n <> "s decay"

-- | Create a DecayTime value (clamped to 0-60)
decayTime :: Number -> DecayTime
decayTime n
  | n < 0.0 = DecayTime 0.0
  | n > 60.0 = DecayTime 60.0
  | otherwise = DecayTime n

unwrapDecayTime :: DecayTime -> Number
unwrapDecayTime (DecayTime n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // predefined values
-- ═════════════════════════════════════════════════════════════════════════════

-- | 100Hz cutoff (sub-bass)
cutoff100 :: CutoffFreq
cutoff100 = CutoffFreq 100.0

-- | 1kHz cutoff (midrange)
cutoff1k :: CutoffFreq
cutoff1k = CutoffFreq 1000.0

-- | 5kHz cutoff (presence)
cutoff5k :: CutoffFreq
cutoff5k = CutoffFreq 5000.0

-- | 10kHz cutoff (brilliance)
cutoff10k :: CutoffFreq
cutoff10k = CutoffFreq 10000.0

-- | 20kHz cutoff (fully open)
cutoff20k :: CutoffFreq
cutoff20k = CutoffFreq 20000.0

-- | No resonance (flat response)
resonanceNone :: Resonance
resonanceNone = Resonance 0.0

-- | Mild resonance (0.3)
resonanceMild :: Resonance
resonanceMild = Resonance 0.3

-- | High resonance (0.7)
resonanceHigh :: Resonance
resonanceHigh = Resonance 0.7

-- | Maximum resonance (1.0)
resonanceMax :: Resonance
resonanceMax = Resonance 1.0

-- | Fully dry (no effect)
mixDry :: Mix
mixDry = Mix 0.0

-- | Fully wet (100% effect)
mixWet :: Mix
mixWet = Mix 1.0

-- | 50/50 blend
mixHalf :: Mix
mixHalf = Mix 0.5

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // conversions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert normalized resonance (0-1) to decibels (0-30).
-- | Simple linear mapping.
resonanceToDb :: Resonance -> ResonanceDb
resonanceToDb (Resonance r) = ResonanceDb (r * 30.0)

-- | Convert decibel resonance (0-30) to normalized (0-1).
dbToResonance :: ResonanceDb -> Resonance
dbToResonance (ResonanceDb db) = Resonance (db / 30.0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds for CutoffFreq
-- |
-- | Min: 20.0 Hz (lower limit of hearing)
-- | Max: 20000.0 Hz (upper limit of hearing)
cutoffFreqBounds :: Bounded.NumberBounds
cutoffFreqBounds = Bounded.numberBounds 20.0 20000.0 "cutoffFreq" "Filter cutoff frequency in Hz (20-20000)"

-- | Bounds for Resonance
-- |
-- | Min: 0.0 (flat)
-- | Max: 1.0 (self-oscillation threshold)
resonanceBounds :: Bounded.NumberBounds
resonanceBounds = Bounded.numberBounds 0.0 1.0 "resonance" "Filter resonance (0-1)"

-- | Bounds for ResonanceDb
-- |
-- | Min: 0.0 dB (flat)
-- | Max: 30.0 dB (high resonance)
resonanceDbBounds :: Bounded.NumberBounds
resonanceDbBounds = Bounded.numberBounds 0.0 30.0 "resonanceDb" "Filter resonance in dB (0-30)"

-- | Bounds for Drive
-- |
-- | Min: 0.0 (clean)
-- | Max: 10.0 (heavy distortion)
driveBounds :: Bounded.NumberBounds
driveBounds = Bounded.numberBounds 0.0 10.0 "drive" "Saturation/drive amount (0-10)"

-- | Bounds for Mix
-- |
-- | Min: 0.0 (dry)
-- | Max: 1.0 (wet)
mixBounds :: Bounded.NumberBounds
mixBounds = Bounded.numberBounds 0.0 1.0 "mix" "Wet/dry mix (0-1)"

-- | Bounds for Feedback
-- |
-- | Min: 0.0 (no feedback)
-- | Max: 1.0 (maximum stable feedback)
feedbackBounds :: Bounded.NumberBounds
feedbackBounds = Bounded.numberBounds 0.0 1.0 "feedback" "Feedback amount (0-1)"

-- | Bounds for DecayTime
-- |
-- | Min: 0.0 seconds
-- | Max: 60.0 seconds
decayTimeBounds :: Bounded.NumberBounds
decayTimeBounds = Bounded.numberBounds 0.0 60.0 "decayTime" "Decay time in seconds (0-60)"
