-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // schema // sensation // temporal
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Temporal Atoms — Time perception sensation primitives.
-- |
-- | Temporal sensation captures how the agent perceives time:
-- |   - How does time feel to me right now?
-- |   - How hard am I thinking (processing load)?
-- |   - How quickly can I respond?
-- |   - How urgent is the current situation?
-- |
-- | ## INTEGRATION WITH WORLDMODEL PROOFS
-- |
-- | Rights.lean guarantees temporal consistency — no entity can accelerate
-- | another's subjective time (preventing torture via time dilation).
-- | These atoms model the PERCEPTION of time, which may differ from
-- | objective time but is bounded by the WorldModel guarantees.
-- |
-- | ## SCHEMA.md Reference (Pillar 15: Sensation — Temporal)
-- |
-- | | Name              | Type   | Min  | Max  | Behavior | Notes                    |
-- | |-------------------|--------|------|------|----------|--------------------------|
-- | | SubjectiveTime    | Number | 0    | none | finite   | Perceived time flow      |
-- | | ProcessingLoad    | Number | 0    | 1    | clamps   | Cognitive effort         |
-- | | ResponseLatency   | Number | 0    | none | finite   | Reaction delay (ms)      |
-- | | TemporalResolution| Number | 0    | none | finite   | Time slice granularity   |
-- | | Urgency           | Number | 0    | 1    | clamps   | Time pressure            |
-- | | Anticipation      | Number | 0    | 1    | clamps   | Expecting something      |
-- |
-- | ## Dependencies
-- | - Prelude
-- |
-- | ## Dependents
-- | - Sensation/Molecules.purs (used in composite states)
-- | - Sensation/Compounds.purs (Flow, Overwhelm)
-- | - Affective.lean (Urgency maps to affective urgency)

module Hydrogen.Schema.Sensation.Temporal
  ( -- * SubjectiveTime (0+, finite)
    SubjectiveTime
  , mkSubjectiveTime
  , unwrapSubjectiveTime
  , timeNormal
  , timeSlow
  , timeFast
  , isTimeDilated
  , isTimeContracted
    -- * ProcessingLoad (0-1, clamps)
  , ProcessingLoad
  , mkProcessingLoad
  , unwrapProcessingLoad
  , loadIdle
  , loadLight
  , loadModerate
  , loadHeavy
  , loadMaximum
  , isIdle
  , isOverloaded
    -- * ResponseLatency (0+, finite, ms)
  , ResponseLatency
  , mkResponseLatency
  , unwrapResponseLatency
  , latencyInstant
  , latencyFast
  , latencyNormal
  , latencySlow
  , latencyVeryDelayed
  , isResponsive
  , isDelayed
    -- * TemporalResolution (0+, finite)
  , TemporalResolution
  , mkTemporalResolution
  , unwrapTemporalResolution
  , resolutionCoarse
  , resolutionNormal
  , resolutionFine
  , resolutionUltraFine
  , isFineGrained
    -- * Urgency (0-1, clamps)
  , Urgency
  , mkUrgency
  , unwrapUrgency
  , urgencyNone
  , urgencyLow
  , urgencyModerate
  , urgencyHigh
  , urgencyCritical
  , isCalm
  , isUrgent
  , isCritical
    -- * Anticipation (0-1, clamps)
  , Anticipation
  , mkAnticipation
  , unwrapAnticipation
  , anticipationNone
  , anticipationLow
  , anticipationModerate
  , anticipationHigh
  , anticipationIntense
  , isAnticipating
  ) where

import Prelude

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // subjective // time
-- ═════════════════════════════════════════════════════════════════════════════

-- | Subjective time flow rate (0+, finite).
-- |
-- | How time feels to the agent relative to objective clock time.
-- |   0.5 = time feels slow (dilated)
-- |   1.0 = normal time flow
-- |   2.0 = time feels fast (contracted)
-- |
-- | This is PERCEPTION, not actual time manipulation (which is bounded
-- | by Rights.lean temporal consistency guarantees).
newtype SubjectiveTime = SubjectiveTime Number

derive instance eqSubjectiveTime :: Eq SubjectiveTime
derive instance ordSubjectiveTime :: Ord SubjectiveTime

instance showSubjectiveTime :: Show SubjectiveTime where
  show (SubjectiveTime n) = "SubjectiveTime(" <> show n <> "x)"

-- | Create a bounded subjective time (clamps to 0+)
mkSubjectiveTime :: Number -> SubjectiveTime
mkSubjectiveTime n = SubjectiveTime (max 0.0 n)

-- | Unwrap the subjective time value
unwrapSubjectiveTime :: SubjectiveTime -> Number
unwrapSubjectiveTime (SubjectiveTime n) = n

-- | Normal time flow (1.0x)
timeNormal :: SubjectiveTime
timeNormal = SubjectiveTime 1.0

-- | Time feels slow / dilated (0.5x)
timeSlow :: SubjectiveTime
timeSlow = SubjectiveTime 0.5

-- | Time feels fast / contracted (2.0x)
timeFast :: SubjectiveTime
timeFast = SubjectiveTime 2.0

-- | Is time dilated? (feels slow, < 0.8x)
isTimeDilated :: SubjectiveTime -> Boolean
isTimeDilated (SubjectiveTime t) = t < 0.8

-- | Is time contracted? (feels fast, > 1.5x)
isTimeContracted :: SubjectiveTime -> Boolean
isTimeContracted (SubjectiveTime t) = t > 1.5

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // processing // load
-- ═════════════════════════════════════════════════════════════════════════════

-- | Processing load (0 to 1, clamps).
-- |
-- | How hard the agent's cognitive/computational systems are working.
-- |   0.0 = idle (no processing)
-- |   0.5 = moderate load
-- |   1.0 = maximum capacity (risk of dropping tasks)
-- |
-- | High values contribute to Overwhelm compound.
newtype ProcessingLoad = ProcessingLoad Number

derive instance eqProcessingLoad :: Eq ProcessingLoad
derive instance ordProcessingLoad :: Ord ProcessingLoad

instance showProcessingLoad :: Show ProcessingLoad where
  show (ProcessingLoad n) = "ProcessingLoad(" <> show n <> ")"

-- | Create a bounded processing load (clamps to 0..1)
mkProcessingLoad :: Number -> ProcessingLoad
mkProcessingLoad n = ProcessingLoad (clampNumber 0.0 1.0 n)

-- | Unwrap the processing load value
unwrapProcessingLoad :: ProcessingLoad -> Number
unwrapProcessingLoad (ProcessingLoad n) = n

-- | Idle (0.0)
loadIdle :: ProcessingLoad
loadIdle = ProcessingLoad 0.0

-- | Light load (0.25)
loadLight :: ProcessingLoad
loadLight = ProcessingLoad 0.25

-- | Moderate load (0.5)
loadModerate :: ProcessingLoad
loadModerate = ProcessingLoad 0.5

-- | Heavy load (0.75)
loadHeavy :: ProcessingLoad
loadHeavy = ProcessingLoad 0.75

-- | Maximum capacity (1.0)
loadMaximum :: ProcessingLoad
loadMaximum = ProcessingLoad 1.0

-- | Is agent idle? (load < 0.1)
isIdle :: ProcessingLoad -> Boolean
isIdle (ProcessingLoad l) = l < 0.1

-- | Is agent overloaded? (load > 0.8)
isOverloaded :: ProcessingLoad -> Boolean
isOverloaded (ProcessingLoad l) = l > 0.8

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // response // latency
-- ═════════════════════════════════════════════════════════════════════════════

-- | Response latency in milliseconds (0+, finite).
-- |
-- | How long the agent takes to respond to stimuli.
-- | Higher values indicate slower reactions.
newtype ResponseLatency = ResponseLatency Number

derive instance eqResponseLatency :: Eq ResponseLatency
derive instance ordResponseLatency :: Ord ResponseLatency

instance showResponseLatency :: Show ResponseLatency where
  show (ResponseLatency n) = "ResponseLatency(" <> show n <> "ms)"

-- | Create a bounded response latency (clamps to 0+)
mkResponseLatency :: Number -> ResponseLatency
mkResponseLatency n = ResponseLatency (max 0.0 n)

-- | Unwrap the response latency value
unwrapResponseLatency :: ResponseLatency -> Number
unwrapResponseLatency (ResponseLatency n) = n

-- | Instant response (< 10ms)
latencyInstant :: ResponseLatency
latencyInstant = ResponseLatency 5.0

-- | Fast response (50ms)
latencyFast :: ResponseLatency
latencyFast = ResponseLatency 50.0

-- | Normal response (200ms)
latencyNormal :: ResponseLatency
latencyNormal = ResponseLatency 200.0

-- | Slow response (500ms)
latencySlow :: ResponseLatency
latencySlow = ResponseLatency 500.0

-- | Very delayed (1000ms+)
latencyVeryDelayed :: ResponseLatency
latencyVeryDelayed = ResponseLatency 1000.0

-- | Is agent responsive? (latency < 100ms)
isResponsive :: ResponseLatency -> Boolean
isResponsive (ResponseLatency l) = l < 100.0

-- | Is agent delayed? (latency > 300ms)
isDelayed :: ResponseLatency -> Boolean
isDelayed (ResponseLatency l) = l > 300.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // temporal // resolution
-- ═════════════════════════════════════════════════════════════════════════════

-- | Temporal resolution (0+, finite).
-- |
-- | How finely the agent can slice time — the granularity of perception.
-- | Higher values = finer resolution = can perceive faster changes.
-- | Measured in samples per second (Hz).
newtype TemporalResolution = TemporalResolution Number

derive instance eqTemporalResolution :: Eq TemporalResolution
derive instance ordTemporalResolution :: Ord TemporalResolution

instance showTemporalResolution :: Show TemporalResolution where
  show (TemporalResolution n) = "TemporalResolution(" <> show n <> "Hz)"

-- | Create a bounded temporal resolution (clamps to 0+)
mkTemporalResolution :: Number -> TemporalResolution
mkTemporalResolution n = TemporalResolution (max 0.0 n)

-- | Unwrap the temporal resolution value
unwrapTemporalResolution :: TemporalResolution -> Number
unwrapTemporalResolution (TemporalResolution n) = n

-- | Coarse resolution (10 Hz)
resolutionCoarse :: TemporalResolution
resolutionCoarse = TemporalResolution 10.0

-- | Normal resolution (60 Hz)
resolutionNormal :: TemporalResolution
resolutionNormal = TemporalResolution 60.0

-- | Fine resolution (120 Hz)
resolutionFine :: TemporalResolution
resolutionFine = TemporalResolution 120.0

-- | Ultra-fine resolution (1000 Hz)
resolutionUltraFine :: TemporalResolution
resolutionUltraFine = TemporalResolution 1000.0

-- | Is resolution fine-grained? (> 100 Hz)
isFineGrained :: TemporalResolution -> Boolean
isFineGrained (TemporalResolution r) = r > 100.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // urgency
-- ═════════════════════════════════════════════════════════════════════════════

-- | Urgency level (0 to 1, clamps).
-- |
-- | Time pressure the agent is experiencing.
-- |   0.0 = no urgency (relaxed)
-- |   0.5 = moderate urgency
-- |   1.0 = critical urgency (immediate action required)
-- |
-- | Maps directly to Affective.lean Urgency type.
newtype Urgency = Urgency Number

derive instance eqUrgency :: Eq Urgency
derive instance ordUrgency :: Ord Urgency

instance showUrgency :: Show Urgency where
  show (Urgency n) = "Urgency(" <> show n <> ")"

-- | Create a bounded urgency (clamps to 0..1)
mkUrgency :: Number -> Urgency
mkUrgency n = Urgency (clampNumber 0.0 1.0 n)

-- | Unwrap the urgency value
unwrapUrgency :: Urgency -> Number
unwrapUrgency (Urgency n) = n

-- | No urgency (0.0)
urgencyNone :: Urgency
urgencyNone = Urgency 0.0

-- | Low urgency (0.25)
urgencyLow :: Urgency
urgencyLow = Urgency 0.25

-- | Moderate urgency (0.5)
urgencyModerate :: Urgency
urgencyModerate = Urgency 0.5

-- | High urgency (0.75)
urgencyHigh :: Urgency
urgencyHigh = Urgency 0.75

-- | Critical urgency (1.0)
urgencyCritical :: Urgency
urgencyCritical = Urgency 1.0

-- | Is agent calm? (urgency < 0.2)
isCalm :: Urgency -> Boolean
isCalm (Urgency u) = u < 0.2

-- | Is situation urgent? (urgency > 0.5)
isUrgent :: Urgency -> Boolean
isUrgent (Urgency u) = u > 0.5

-- | Is situation critical? (urgency > 0.8)
isCritical :: Urgency -> Boolean
isCritical (Urgency u) = u > 0.8

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // anticipation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Anticipation level (0 to 1, clamps).
-- |
-- | How much the agent is expecting something to happen.
-- |   0.0 = not anticipating anything
-- |   0.5 = moderate anticipation
-- |   1.0 = intense anticipation (something is imminent)
newtype Anticipation = Anticipation Number

derive instance eqAnticipation :: Eq Anticipation
derive instance ordAnticipation :: Ord Anticipation

instance showAnticipation :: Show Anticipation where
  show (Anticipation n) = "Anticipation(" <> show n <> ")"

-- | Create a bounded anticipation (clamps to 0..1)
mkAnticipation :: Number -> Anticipation
mkAnticipation n = Anticipation (clampNumber 0.0 1.0 n)

-- | Unwrap the anticipation value
unwrapAnticipation :: Anticipation -> Number
unwrapAnticipation (Anticipation n) = n

-- | Not anticipating (0.0)
anticipationNone :: Anticipation
anticipationNone = Anticipation 0.0

-- | Low anticipation (0.25)
anticipationLow :: Anticipation
anticipationLow = Anticipation 0.25

-- | Moderate anticipation (0.5)
anticipationModerate :: Anticipation
anticipationModerate = Anticipation 0.5

-- | High anticipation (0.75)
anticipationHigh :: Anticipation
anticipationHigh = Anticipation 0.75

-- | Intense anticipation (1.0)
anticipationIntense :: Anticipation
anticipationIntense = Anticipation 1.0

-- | Is agent anticipating something? (anticipation > 0.3)
isAnticipating :: Anticipation -> Boolean
isAnticipating (Anticipation a) = a > 0.3

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp a number to a range.
-- | Named clampNumber to avoid shadowing Prelude.clamp
clampNumber :: Number -> Number -> Number -> Number
clampNumber lo hi x = max lo (min hi x)
