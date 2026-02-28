-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // schema // audio // envelope
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ADSR envelope atoms for audio synthesis.
-- |
-- | ## ADSR Model
-- | The classic envelope model used in synthesizers:
-- | - **Attack**: Time to rise from 0 to peak
-- | - **Decay**: Time to fall from peak to sustain level
-- | - **Sustain**: Level held while note is pressed (0.0-1.0)
-- | - **Release**: Time to fall from sustain to 0 after note release
-- |
-- | ## AHDSR Extension
-- | Some envelopes add a Hold phase between Attack and Decay,
-- | where the signal stays at peak level for a duration.
-- |
-- | ## Time Ranges
-- | All time values are in seconds, allowing both snappy transients
-- | (0.001s) and slow pads (10+ seconds).

module Hydrogen.Schema.Audio.Envelope
  ( -- * ADSR Atoms
    AttackTime(..)
  , DecayTime(..)
  , SustainLevel(..)
  , ReleaseTime(..)
  , HoldTime(..)
  
  -- * Constructors
  , attackTime
  , decayTime
  , sustainLevel
  , releaseTime
  , holdTime
  
  -- * Accessors
  , unwrapAttackTime
  , unwrapDecayTime
  , unwrapSustainLevel
  , unwrapReleaseTime
  , unwrapHoldTime
  
  -- * ADSR Molecule
  , ADSR
  , adsr
  , adsrDefault
  , adsrSnappy
  , adsrPad
  , adsrPluck
  
  -- * AHDSR Molecule
  , AHDSR
  , ahdsr
  
  -- * Operations
  , totalAdsrTime
  , totalAhdsrTime
  , scaleAdsrTimes
  
  -- * Bounds
  , attackTimeBounds
  , decayTimeBounds
  , sustainLevelBounds
  , releaseTimeBounds
  , holdTimeBounds
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , (+)
  , (*)
  , (<)
  , (>)
  , (<>)
  )

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // attack time
-- ═════════════════════════════════════════════════════════════════════════════

-- | AttackTime - time to rise from 0 to peak in seconds.
-- | Clamped to [0, 10] seconds.
-- | Short attacks (0.001-0.01s) for percussive sounds.
-- | Long attacks (1-10s) for slow swells.
newtype AttackTime = AttackTime Number

derive instance eqAttackTime :: Eq AttackTime
derive instance ordAttackTime :: Ord AttackTime

instance showAttackTime :: Show AttackTime where
  show (AttackTime n) = show n <> "s attack"

-- | Create an AttackTime value (clamped to 0-10)
attackTime :: Number -> AttackTime
attackTime n
  | n < 0.0 = AttackTime 0.0
  | n > 10.0 = AttackTime 10.0
  | otherwise = AttackTime n

unwrapAttackTime :: AttackTime -> Number
unwrapAttackTime (AttackTime n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // decay time
-- ═════════════════════════════════════════════════════════════════════════════

-- | DecayTime - time to fall from peak to sustain level in seconds.
-- | Clamped to [0, 10] seconds.
newtype DecayTime = DecayTime Number

derive instance eqDecayTime :: Eq DecayTime
derive instance ordDecayTime :: Ord DecayTime

instance showDecayTime :: Show DecayTime where
  show (DecayTime n) = show n <> "s decay"

-- | Create a DecayTime value (clamped to 0-10)
decayTime :: Number -> DecayTime
decayTime n
  | n < 0.0 = DecayTime 0.0
  | n > 10.0 = DecayTime 10.0
  | otherwise = DecayTime n

unwrapDecayTime :: DecayTime -> Number
unwrapDecayTime (DecayTime n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // sustain level
-- ═════════════════════════════════════════════════════════════════════════════

-- | SustainLevel - level held while note is pressed.
-- | 0.0 = silence, 1.0 = full amplitude.
-- | This is a level, not a time.
newtype SustainLevel = SustainLevel Number

derive instance eqSustainLevel :: Eq SustainLevel
derive instance ordSustainLevel :: Ord SustainLevel

instance showSustainLevel :: Show SustainLevel where
  show (SustainLevel n) = show (n * 100.0) <> "% sustain"

-- | Create a SustainLevel value (clamped to 0.0-1.0)
sustainLevel :: Number -> SustainLevel
sustainLevel n
  | n < 0.0 = SustainLevel 0.0
  | n > 1.0 = SustainLevel 1.0
  | otherwise = SustainLevel n

unwrapSustainLevel :: SustainLevel -> Number
unwrapSustainLevel (SustainLevel n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // release time
-- ═════════════════════════════════════════════════════════════════════════════

-- | ReleaseTime - time to fall from sustain to 0 after note release.
-- | Clamped to [0, 30] seconds (longer for reverb-like releases).
newtype ReleaseTime = ReleaseTime Number

derive instance eqReleaseTime :: Eq ReleaseTime
derive instance ordReleaseTime :: Ord ReleaseTime

instance showReleaseTime :: Show ReleaseTime where
  show (ReleaseTime n) = show n <> "s release"

-- | Create a ReleaseTime value (clamped to 0-30)
releaseTime :: Number -> ReleaseTime
releaseTime n
  | n < 0.0 = ReleaseTime 0.0
  | n > 30.0 = ReleaseTime 30.0
  | otherwise = ReleaseTime n

unwrapReleaseTime :: ReleaseTime -> Number
unwrapReleaseTime (ReleaseTime n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // hold time
-- ═════════════════════════════════════════════════════════════════════════════

-- | HoldTime - time to stay at peak level (AHDSR model).
-- | Clamped to [0, 10] seconds.
-- | Used in AHDSR envelopes between Attack and Decay.
newtype HoldTime = HoldTime Number

derive instance eqHoldTime :: Eq HoldTime
derive instance ordHoldTime :: Ord HoldTime

instance showHoldTime :: Show HoldTime where
  show (HoldTime n) = show n <> "s hold"

-- | Create a HoldTime value (clamped to 0-10)
holdTime :: Number -> HoldTime
holdTime n
  | n < 0.0 = HoldTime 0.0
  | n > 10.0 = HoldTime 10.0
  | otherwise = HoldTime n

unwrapHoldTime :: HoldTime -> Number
unwrapHoldTime (HoldTime n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // adsr molecule
-- ═════════════════════════════════════════════════════════════════════════════

-- | ADSR envelope configuration.
-- | The classic 4-stage envelope used in most synthesizers.
type ADSR =
  { attack :: AttackTime
  , decay :: DecayTime
  , sustain :: SustainLevel
  , release :: ReleaseTime
  }

-- | Create an ADSR envelope with specified parameters.
adsr :: Number -> Number -> Number -> Number -> ADSR
adsr a d s r =
  { attack: attackTime a
  , decay: decayTime d
  , sustain: sustainLevel s
  , release: releaseTime r
  }

-- | Default ADSR: moderate attack, decay, full sustain, moderate release.
adsrDefault :: ADSR
adsrDefault =
  { attack: AttackTime 0.01
  , decay: DecayTime 0.1
  , sustain: SustainLevel 0.7
  , release: ReleaseTime 0.3
  }

-- | Snappy ADSR: instant attack, short decay, low sustain, quick release.
-- | Good for drums and percussive sounds.
adsrSnappy :: ADSR
adsrSnappy =
  { attack: AttackTime 0.001
  , decay: DecayTime 0.05
  , sustain: SustainLevel 0.0
  , release: ReleaseTime 0.05
  }

-- | Pad ADSR: slow attack, long decay, high sustain, long release.
-- | Good for ambient pads and strings.
adsrPad :: ADSR
adsrPad =
  { attack: AttackTime 0.5
  , decay: DecayTime 1.0
  , sustain: SustainLevel 0.8
  , release: ReleaseTime 2.0
  }

-- | Pluck ADSR: instant attack, medium decay, no sustain, short release.
-- | Good for plucked string sounds.
adsrPluck :: ADSR
adsrPluck =
  { attack: AttackTime 0.001
  , decay: DecayTime 0.3
  , sustain: SustainLevel 0.0
  , release: ReleaseTime 0.1
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // ahdsr molecule
-- ═════════════════════════════════════════════════════════════════════════════

-- | AHDSR envelope configuration.
-- | Extended envelope with Hold stage between Attack and Decay.
type AHDSR =
  { attack :: AttackTime
  , hold :: HoldTime
  , decay :: DecayTime
  , sustain :: SustainLevel
  , release :: ReleaseTime
  }

-- | Create an AHDSR envelope with specified parameters.
ahdsr :: Number -> Number -> Number -> Number -> Number -> AHDSR
ahdsr a h d s r =
  { attack: attackTime a
  , hold: holdTime h
  , decay: decayTime d
  , sustain: sustainLevel s
  , release: releaseTime r
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate total time of ADSR envelope (excluding sustain which is indefinite).
-- | Returns attack + decay + release.
totalAdsrTime :: ADSR -> Number
totalAdsrTime env =
  unwrapAttackTime env.attack +
  unwrapDecayTime env.decay +
  unwrapReleaseTime env.release

-- | Calculate total time of AHDSR envelope (excluding sustain).
-- | Returns attack + hold + decay + release.
totalAhdsrTime :: AHDSR -> Number
totalAhdsrTime env =
  unwrapAttackTime env.attack +
  unwrapHoldTime env.hold +
  unwrapDecayTime env.decay +
  unwrapReleaseTime env.release

-- | Scale all time values in an ADSR by a factor.
-- | Useful for tempo-synced envelopes.
scaleAdsrTimes :: Number -> ADSR -> ADSR
scaleAdsrTimes factor env =
  { attack: attackTime (unwrapAttackTime env.attack * factor)
  , decay: decayTime (unwrapDecayTime env.decay * factor)
  , sustain: env.sustain  -- Sustain level is not affected
  , release: releaseTime (unwrapReleaseTime env.release * factor)
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds for AttackTime
-- |
-- | Min: 0.0 seconds (instant)
-- | Max: 10.0 seconds (slow swell)
attackTimeBounds :: Bounded.NumberBounds
attackTimeBounds = Bounded.numberBounds 0.0 10.0 "attackTime" "Attack time in seconds (0-10)"

-- | Bounds for DecayTime
-- |
-- | Min: 0.0 seconds
-- | Max: 10.0 seconds
decayTimeBounds :: Bounded.NumberBounds
decayTimeBounds = Bounded.numberBounds 0.0 10.0 "decayTime" "Decay time in seconds (0-10)"

-- | Bounds for SustainLevel
-- |
-- | Min: 0.0 (silence)
-- | Max: 1.0 (full level)
sustainLevelBounds :: Bounded.NumberBounds
sustainLevelBounds = Bounded.numberBounds 0.0 1.0 "sustainLevel" "Sustain level (0-1)"

-- | Bounds for ReleaseTime
-- |
-- | Min: 0.0 seconds
-- | Max: 30.0 seconds (long reverb-like release)
releaseTimeBounds :: Bounded.NumberBounds
releaseTimeBounds = Bounded.numberBounds 0.0 30.0 "releaseTime" "Release time in seconds (0-30)"

-- | Bounds for HoldTime
-- |
-- | Min: 0.0 seconds
-- | Max: 10.0 seconds
holdTimeBounds :: Bounded.NumberBounds
holdTimeBounds = Bounded.numberBounds 0.0 10.0 "holdTime" "Hold time in seconds (0-10)"
