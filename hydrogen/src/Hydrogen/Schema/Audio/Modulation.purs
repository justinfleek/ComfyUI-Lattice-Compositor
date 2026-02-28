-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // audio // modulation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Modulation atoms for LFOs and modulators.
-- |
-- | ## LFO (Low Frequency Oscillator)
-- | LFOs generate periodic signals below audio rate (typically 0.01-50 Hz)
-- | to modulate other parameters like filter cutoff, pitch, or amplitude.
-- |
-- | ## Modulation Depth
-- | How much the modulator affects the target parameter.
-- | 0.0 = no effect, 1.0 = maximum effect.
-- |
-- | ## Sync Ratios
-- | For tempo-synced LFOs, the rate is expressed as a ratio to the beat.
-- | Common ratios: 1:4 (quarter note), 1:2 (half note), 1:1 (whole note).

module Hydrogen.Schema.Audio.Modulation
  ( -- * Modulation Atoms
    ModDepth(..)
  , ModRate(..)
  , LFOPhase(..)
  
  -- * Constructors
  , modDepth
  , modRate
  , lfoPhase
  
  -- * Accessors
  , unwrapModDepth
  , unwrapModRate
  , unwrapLFOPhase
  
  -- * Sync Ratios
  , SyncRatio(..)
  , syncRatioToMultiplier
  , syncRatioToString
  
  -- * LFO Molecule
  , LFO
  , lfo
  , lfoSynced
  
  -- * Predefined Rates
  , rateVerySlow
  , rateSlow
  , rateMedium
  , rateFast
  , rateVeryFast
  
  -- * Bounds
  , modDepthBounds
  , modRateBounds
  , lfoPhaseBounds
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , (*)
  , (/)
  , (-)
  , (+)
  , (<)
  , (>)
  , (>=)
  , (<>)
  )

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // mod depth
-- ═════════════════════════════════════════════════════════════════════════════

-- | ModDepth - modulation depth (0.0 to 1.0).
-- | Controls how much the modulator affects the target.
-- | 0.0 = no modulation, 1.0 = maximum modulation.
newtype ModDepth = ModDepth Number

derive instance eqModDepth :: Eq ModDepth
derive instance ordModDepth :: Ord ModDepth

instance showModDepth :: Show ModDepth where
  show (ModDepth n) = show (n * 100.0) <> "% depth"

-- | Create a ModDepth value (clamped to 0.0-1.0)
modDepth :: Number -> ModDepth
modDepth n
  | n < 0.0 = ModDepth 0.0
  | n > 1.0 = ModDepth 1.0
  | otherwise = ModDepth n

unwrapModDepth :: ModDepth -> Number
unwrapModDepth (ModDepth n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // mod rate
-- ═════════════════════════════════════════════════════════════════════════════

-- | ModRate - modulation rate in Hz.
-- | LFO frequency, typically 0.01-50 Hz.
-- | Higher rates (10-50 Hz) can create tremolo/vibrato effects.
newtype ModRate = ModRate Number

derive instance eqModRate :: Eq ModRate
derive instance ordModRate :: Ord ModRate

instance showModRate :: Show ModRate where
  show (ModRate n) = show n <> " Hz"

-- | Create a ModRate value (clamped to 0-50)
modRate :: Number -> ModRate
modRate n
  | n < 0.0 = ModRate 0.0
  | n > 50.0 = ModRate 50.0
  | otherwise = ModRate n

unwrapModRate :: ModRate -> Number
unwrapModRate (ModRate n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // lfo phase
-- ═════════════════════════════════════════════════════════════════════════════

-- | LFOPhase - phase offset for LFO in degrees.
-- | 0-360 degrees, wraps at boundaries.
-- | Use to offset multiple LFOs or align with rhythm.
newtype LFOPhase = LFOPhase Number

derive instance eqLFOPhase :: Eq LFOPhase
derive instance ordLFOPhase :: Ord LFOPhase

instance showLFOPhase :: Show LFOPhase where
  show (LFOPhase n) = show n <> "° phase"

-- | Create an LFOPhase value (wraps at 0-360)
lfoPhase :: Number -> LFOPhase
lfoPhase n = LFOPhase (wrapAngle n)
  where
    wrapAngle angle
      | angle >= 360.0 = wrapAngle (angle - 360.0)
      | angle < 0.0 = wrapAngle (angle + 360.0)
      | otherwise = angle

unwrapLFOPhase :: LFOPhase -> Number
unwrapLFOPhase (LFOPhase n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // sync ratios
-- ═════════════════════════════════════════════════════════════════════════════

-- | SyncRatio - tempo sync ratio for LFO.
-- | Expresses LFO rate relative to musical tempo.
data SyncRatio
  = Ratio1_16     -- ^ 1/16 note
  | Ratio1_8      -- ^ 1/8 note
  | Ratio1_4      -- ^ 1/4 note (quarter)
  | Ratio1_2      -- ^ 1/2 note (half)
  | Ratio1_1      -- ^ 1/1 (whole note)
  | Ratio2_1      -- ^ 2/1 (two bars in 4/4)
  | Ratio4_1      -- ^ 4/1 (four bars in 4/4)
  | Ratio1_8T     -- ^ 1/8 triplet
  | Ratio1_4T     -- ^ 1/4 triplet
  | Ratio1_8D     -- ^ 1/8 dotted
  | Ratio1_4D     -- ^ 1/4 dotted

derive instance eqSyncRatio :: Eq SyncRatio
derive instance ordSyncRatio :: Ord SyncRatio

instance showSyncRatio :: Show SyncRatio where
  show = syncRatioToString

-- | Convert sync ratio to string representation
syncRatioToString :: SyncRatio -> String
syncRatioToString Ratio1_16 = "1/16"
syncRatioToString Ratio1_8 = "1/8"
syncRatioToString Ratio1_4 = "1/4"
syncRatioToString Ratio1_2 = "1/2"
syncRatioToString Ratio1_1 = "1/1"
syncRatioToString Ratio2_1 = "2/1"
syncRatioToString Ratio4_1 = "4/1"
syncRatioToString Ratio1_8T = "1/8T"
syncRatioToString Ratio1_4T = "1/4T"
syncRatioToString Ratio1_8D = "1/8D"
syncRatioToString Ratio1_4D = "1/4D"

-- | Convert sync ratio to beat multiplier.
-- | 1.0 = one beat (quarter note in 4/4).
syncRatioToMultiplier :: SyncRatio -> Number
syncRatioToMultiplier Ratio1_16 = 0.25
syncRatioToMultiplier Ratio1_8 = 0.5
syncRatioToMultiplier Ratio1_4 = 1.0
syncRatioToMultiplier Ratio1_2 = 2.0
syncRatioToMultiplier Ratio1_1 = 4.0
syncRatioToMultiplier Ratio2_1 = 8.0
syncRatioToMultiplier Ratio4_1 = 16.0
syncRatioToMultiplier Ratio1_8T = 0.333333
syncRatioToMultiplier Ratio1_4T = 0.666667
syncRatioToMultiplier Ratio1_8D = 0.75
syncRatioToMultiplier Ratio1_4D = 1.5

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // lfo molecule
-- ═════════════════════════════════════════════════════════════════════════════

-- | LFO configuration.
-- | Combines rate, depth, and phase for modulation.
type LFO =
  { rate :: ModRate
  , depth :: ModDepth
  , phase :: LFOPhase
  }

-- | Create an LFO with free-running rate in Hz.
lfo :: Number -> Number -> Number -> LFO
lfo r d p =
  { rate: modRate r
  , depth: modDepth d
  , phase: lfoPhase p
  }

-- | Create a tempo-synced LFO.
-- | Rate is calculated from BPM and sync ratio.
-- | Formula: Hz = (BPM / 60) / beatMultiplier
lfoSynced :: Number -> SyncRatio -> Number -> Number -> LFO
lfoSynced bpmValue ratio d p =
  let beatMultiplier = syncRatioToMultiplier ratio
      hz = (bpmValue / 60.0) / beatMultiplier
  in { rate: modRate hz
     , depth: modDepth d
     , phase: lfoPhase p
     }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // predefined rates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Very slow LFO rate (0.1 Hz = 10 second cycle)
rateVerySlow :: ModRate
rateVerySlow = ModRate 0.1

-- | Slow LFO rate (0.5 Hz = 2 second cycle)
rateSlow :: ModRate
rateSlow = ModRate 0.5

-- | Medium LFO rate (2 Hz)
rateMedium :: ModRate
rateMedium = ModRate 2.0

-- | Fast LFO rate (8 Hz)
rateFast :: ModRate
rateFast = ModRate 8.0

-- | Very fast LFO rate (20 Hz, tremolo territory)
rateVeryFast :: ModRate
rateVeryFast = ModRate 20.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds for ModDepth
-- |
-- | Min: 0.0 (no modulation)
-- | Max: 1.0 (full modulation)
modDepthBounds :: Bounded.NumberBounds
modDepthBounds = Bounded.numberBounds 0.0 1.0 "modDepth" "Modulation depth (0-1)"

-- | Bounds for ModRate
-- |
-- | Min: 0.0 Hz (static)
-- | Max: 50.0 Hz (audio rate threshold)
modRateBounds :: Bounded.NumberBounds
modRateBounds = Bounded.numberBounds 0.0 50.0 "modRate" "Modulation rate in Hz (0-50)"

-- | Bounds for LFOPhase
-- |
-- | Min: 0.0 degrees
-- | Max: 360.0 degrees (wraps)
lfoPhaseBounds :: Bounded.NumberBounds
lfoPhaseBounds = Bounded.numberBounds 0.0 360.0 "lfoPhase" "LFO phase offset in degrees (0-360)"
