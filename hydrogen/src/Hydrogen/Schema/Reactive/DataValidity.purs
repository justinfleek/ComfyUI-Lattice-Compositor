-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // schema // reactive // data-validity
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | DataValidity — Graduated failure modes for safety-critical systems.
-- |
-- | ## Purpose
-- |
-- | In safety-critical domains (avionics DO-178C DAL-A, medical FDA 21 CFR Part 11),
-- | a simple boolean "stale" flag is insufficient. Systems must distinguish between:
-- |
-- | - Data that is current and trustworthy
-- | - Data that is aging but still usable
-- | - Data that is stale and requires visual indication
-- | - Data that has failed and must be removed from display
-- | - Data from redundant sources that disagree
-- |
-- | ## DO-178C Requirements
-- |
-- | Avionics displays must show:
-- | - Fresh data (< 250ms): normal display
-- | - Aging data (250ms - 2s): yellow cross-hatch overlay
-- | - Stale data (2s - 10s): X through display element
-- | - Invalid data (> 10s or sensor failure): remove from display entirely
-- |
-- | ## FDA Requirements
-- |
-- | Medical displays must:
-- | - Track data provenance (which sensor, which timestamp)
-- | - Show signal quality indicators
-- | - Provide audible alarms for data failure
-- | - Never display potentially misleading information without warning

module Hydrogen.Schema.Reactive.DataValidity
  ( -- * Core Types
    DataValidity
      ( Valid
      , Degraded
      , Stale
      , SensorFailure
      , CommsLost
      , CrossCheckFailed
      , OutOfRange
      , RateOfChangeExceeded
      , NeverReceived
      )
  , DataAge
      ( Fresh
      , Aging
      , StaleAge
      , Invalid
      )
  , FailureMode
      ( HardwareFault
      , CalibrationError
      , RangeExceeded
      , SelfTestFailed
      , PowerFailure
      , ConnectionLost
      , UnknownFailure
      )
  , DegradationReason
      ( ReducedAccuracy
      , InterferenceDet
      , EnvironmentalLimit
      , BackupSensor
      , FilteredData
      , Interpolated
      )
  , SensorId
  , Timestamp
  , Duration
  , Percent
  
  -- * Display Response
  , DisplayResponse
      ( DisplayNormal
      , DisplayWithAge
      , DisplayCrossHatch
      , DisplayXThrough
      , DisplayRemove
      , DisplayWithFlag
      , DisplayFlash
      )
  , FailureFlag
      ( FlagSensorFail
      , FlagCommsLoss
      , FlagXCheck
      , FlagOutOfRange
      , FlagRateExceeded
      , FlagNoData
      , FlagDegraded
      )
  
  -- * Constructors
  , validData
  , degradedData
  , staleData
  , sensorFailure
  , commsLost
  , crossCheckFailed
  , outOfRange
  , rateExceeded
  , neverReceived
  
  -- * Queries
  , isValid
  , isUsable
  , isFailed
  , requiresWarning
  , shouldDisplay
  , getConfidence
  , getAge
  
  -- * Display Response Computation
  , computeDisplayResponse
  , dataAgeToResponse
  
  -- * Data Age Computation
  , computeDataAge
  , ageThresholds
  , DataAgeThresholds
  
  -- * Signal Quality
  , SignalQuality
      ( QualityGood
      , QualityMarginal
      , QualityPoor
      , QualityInvalid
      , QualityLeadOff
      )
  , signalQualityFromConfidence
  , signalQualityToString
  
  -- * Sensor Source Tracking
  , SensorSource
      ( Primary
      , Secondary
      , Tertiary
      , Computed
      , Synthesized
      )
  , isPrimarySensor
  , sensorSourcePriority
  , compareSensorSources
  , hasHigherPriority
  
  -- * Validity Comparisons
  , validityScore
  , isBetterThan
  , isWorseThan
  , isEquivalentTo
  
  -- * Validity Combining
  , worstValidity
  , bestValidity
  , anyFailed
  , allValid
  , allUsable
  
  -- * Age Arithmetic
  , computeAge
  , updateStaleAge
  , ageExceeds
  , timeUntilInvalid
  
  -- * Confidence Math
  , clampConfidence
  , averageConfidence
  , minimumConfidence
  , confidenceMeetsThreshold
  , degradeConfidence
  
  -- * Rate of Change
  , computeRateOfChange
  , rateWithinLimits
  , computeDisagreement
  
  -- * Compound Predicates
  , isValidPrimary
  , isUsableDegraded
  , isWarningState
  , requiresImmediateAttention
  , safeForCriticalUse
  , needsFallback
  , validityChanged
  , isOperatingDegraded
  , eitherRequiresAttention
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , Ordering
  , show
  , compare
  , otherwise
  , not
  , (&&)
  , (||)
  , (<)
  , (<=)
  , (<>)
  , (>)
  , (>=)
  , (==)
  , (/=)
  , (-)
  , (+)
  , (/)
  , (*)
  , ($)
  )

import Data.Array as Array
import Data.Foldable (foldl, any, all)
import Data.Int (toNumber)
import Data.Maybe (Maybe(Just, Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // core aliases
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sensor identifier (opaque string for now, could be UUID5)
type SensorId = String

-- | Unix timestamp in milliseconds
type Timestamp = Number

-- | Duration in milliseconds
type Duration = Number

-- | Percentage (0.0 to 100.0)
type Percent = Number

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // data validity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Graduated data validity states for safety-critical systems.
-- |
-- | Unlike simple boolean staleness, this captures the full spectrum of
-- | data integrity states required by DO-178C and FDA regulations.
data DataValidity
  = Valid 
      { confidence :: Percent    -- 0.0-100.0 confidence level
      , source :: SensorId       -- Which sensor provided this data
      , timestamp :: Timestamp   -- When data was sampled
      }
  | Degraded
      { reason :: DegradationReason
      , usable :: Boolean        -- Can still be used with caution
      , confidence :: Percent    -- Reduced confidence level
      , source :: SensorId
      , timestamp :: Timestamp
      }
  | Stale
      { age :: Duration          -- How long since last valid data
      , lastValid :: Timestamp   -- When data was last valid
      , source :: SensorId
      }
  | SensorFailure
      { sensor :: SensorId
      , failureMode :: FailureMode
      , detectedAt :: Timestamp
      }
  | CommsLost
      { since :: Duration        -- Duration of communication loss
      , lastPacket :: Timestamp  -- When last packet was received
      , source :: SensorId
      }
  | CrossCheckFailed
      { sources :: Array SensorId    -- Disagreeing sensors
      , disagreement :: Percent      -- How much they disagree
      , detectedAt :: Timestamp
      }
  | OutOfRange
      { value :: Number
      , minBound :: Number
      , maxBound :: Number
      , source :: SensorId
      , timestamp :: Timestamp
      }
  | RateOfChangeExceeded
      { current :: Number
      , previous :: Number
      , maxRate :: Number        -- Maximum allowed rate of change per second
      , source :: SensorId
      , timestamp :: Timestamp
      }
  | NeverReceived               -- Source never provided any data

derive instance eqDataValidity :: Eq DataValidity

instance showDataValidity :: Show DataValidity where
  show (Valid r) = "Valid(confidence=" <> show r.confidence <> "%, source=" <> r.source <> ")"
  show (Degraded r) = "Degraded(" <> show r.reason <> ", usable=" <> show r.usable <> ")"
  show (Stale r) = "Stale(age=" <> show r.age <> "ms)"
  show (SensorFailure r) = "SensorFailure(" <> r.sensor <> ", " <> show r.failureMode <> ")"
  show (CommsLost r) = "CommsLost(since=" <> show r.since <> "ms)"
  show (CrossCheckFailed r) = "CrossCheckFailed(disagreement=" <> show r.disagreement <> "%)"
  show (OutOfRange r) = "OutOfRange(value=" <> show r.value <> ")"
  show (RateOfChangeExceeded r) = "RateOfChangeExceeded(current=" <> show r.current <> ")"
  show NeverReceived = "NeverReceived"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // failure modes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Specific failure modes for sensor failures
data FailureMode
  = HardwareFault       -- Physical sensor failure
  | CalibrationError    -- Sensor needs recalibration
  | RangeExceeded       -- Value outside sensor capability
  | SelfTestFailed      -- Built-in test failed
  | PowerFailure        -- Sensor lost power
  | ConnectionLost      -- Physical connection broken
  | UnknownFailure      -- Undiagnosed failure

derive instance eqFailureMode :: Eq FailureMode
derive instance ordFailureMode :: Ord FailureMode

instance showFailureMode :: Show FailureMode where
  show HardwareFault = "HardwareFault"
  show CalibrationError = "CalibrationError"
  show RangeExceeded = "RangeExceeded"
  show SelfTestFailed = "SelfTestFailed"
  show PowerFailure = "PowerFailure"
  show ConnectionLost = "ConnectionLost"
  show UnknownFailure = "UnknownFailure"

-- | Reasons for degraded data quality
data DegradationReason
  = ReducedAccuracy     -- Sensor operating in degraded mode
  | InterferenceDet     -- Electromagnetic interference detected
  | EnvironmentalLimit  -- Temperature/pressure outside optimal range
  | BackupSensor        -- Using backup instead of primary
  | FilteredData        -- Data has been filtered/smoothed
  | Interpolated        -- Value interpolated from adjacent samples

derive instance eqDegradationReason :: Eq DegradationReason

instance showDegradationReason :: Show DegradationReason where
  show ReducedAccuracy = "ReducedAccuracy"
  show InterferenceDet = "InterferenceDetected"
  show EnvironmentalLimit = "EnvironmentalLimit"
  show BackupSensor = "BackupSensor"
  show FilteredData = "FilteredData"
  show Interpolated = "Interpolated"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // display response
-- ═════════════════════════════════════════════════════════════════════════════

-- | How to display data based on validity state
data DisplayResponse
  = DisplayNormal                            -- Show normally
  | DisplayWithAge { age :: Duration }       -- Show with age indicator
  | DisplayCrossHatch                        -- Yellow cross-hatch overlay
  | DisplayXThrough                          -- X through the display element
  | DisplayRemove                            -- Remove from display entirely
  | DisplayWithFlag { flag :: FailureFlag }  -- Show with specific failure flag
  | DisplayFlash { message :: String, rateHz :: Number }  -- Flashing warning

derive instance eqDisplayResponse :: Eq DisplayResponse

instance showDisplayResponse :: Show DisplayResponse where
  show DisplayNormal = "DisplayNormal"
  show (DisplayWithAge r) = "DisplayWithAge(" <> show r.age <> "ms)"
  show DisplayCrossHatch = "DisplayCrossHatch"
  show DisplayXThrough = "DisplayXThrough"
  show DisplayRemove = "DisplayRemove"
  show (DisplayWithFlag r) = "DisplayWithFlag(" <> show r.flag <> ")"
  show (DisplayFlash r) = "DisplayFlash(" <> r.message <> ")"

-- | Specific failure flags for safety-critical displays
data FailureFlag
  = FlagSensorFail      -- SENS FAIL
  | FlagCommsLoss       -- COMMS
  | FlagXCheck          -- X-CHECK
  | FlagOutOfRange      -- OOR
  | FlagRateExceeded    -- RATE
  | FlagNoData          -- NO DATA
  | FlagDegraded        -- DEGD

derive instance eqFailureFlag :: Eq FailureFlag

instance showFailureFlag :: Show FailureFlag where
  show FlagSensorFail = "SENS FAIL"
  show FlagCommsLoss = "COMMS"
  show FlagXCheck = "X-CHECK"
  show FlagOutOfRange = "OOR"
  show FlagRateExceeded = "RATE"
  show FlagNoData = "NO DATA"
  show FlagDegraded = "DEGD"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // data age
-- ═════════════════════════════════════════════════════════════════════════════

-- | Graduated data age per DO-178C requirements
data DataAge
  = Fresh               -- < freshThreshold (default 250ms)
  | Aging Duration      -- freshThreshold to staleThreshold (250ms - 2s)
  | StaleAge Duration   -- staleThreshold to invalidThreshold (2s - 10s)
  | Invalid             -- > invalidThreshold (10s) or sensor failure

derive instance eqDataAge :: Eq DataAge

instance showDataAge :: Show DataAge where
  show Fresh = "Fresh"
  show (Aging ms) = "Aging(" <> show ms <> "ms)"
  show (StaleAge ms) = "Stale(" <> show ms <> "ms)"
  show Invalid = "Invalid"

-- | Thresholds for data age classification
type DataAgeThresholds =
  { freshMs :: Duration      -- Below this = Fresh (default 250ms)
  , staleMs :: Duration      -- Above freshMs, below this = Aging (default 2000ms)
  , invalidMs :: Duration    -- Above staleMs, below this = Stale; above = Invalid (default 10000ms)
  }

-- | Default thresholds per DO-178C
ageThresholds :: DataAgeThresholds
ageThresholds =
  { freshMs: 250.0
  , staleMs: 2000.0
  , invalidMs: 10000.0
  }

-- | Compute data age category from milliseconds since last update
computeDataAge :: DataAgeThresholds -> Duration -> DataAge
computeDataAge thresholds ageMs
  | ageMs < thresholds.freshMs = Fresh
  | ageMs < thresholds.staleMs = Aging ageMs
  | ageMs < thresholds.invalidMs = StaleAge ageMs
  | otherwise = Invalid

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create valid data
validData :: Percent -> SensorId -> Timestamp -> DataValidity
validData confidence source timestamp = Valid { confidence, source, timestamp }

-- | Create degraded data
degradedData :: DegradationReason -> Boolean -> Percent -> SensorId -> Timestamp -> DataValidity
degradedData reason usable confidence source timestamp = 
  Degraded { reason, usable, confidence, source, timestamp }

-- | Create stale data
staleData :: Duration -> Timestamp -> SensorId -> DataValidity
staleData age lastValid source = Stale { age, lastValid, source }

-- | Create sensor failure
sensorFailure :: SensorId -> FailureMode -> Timestamp -> DataValidity
sensorFailure sensor failureMode detectedAt = 
  SensorFailure { sensor, failureMode, detectedAt }

-- | Create communications lost
commsLost :: Duration -> Timestamp -> SensorId -> DataValidity
commsLost since lastPacket source = CommsLost { since, lastPacket, source }

-- | Create cross-check failure
crossCheckFailed :: Array SensorId -> Percent -> Timestamp -> DataValidity
crossCheckFailed sources disagreement detectedAt = 
  CrossCheckFailed { sources, disagreement, detectedAt }

-- | Create out-of-range error
outOfRange :: Number -> Number -> Number -> SensorId -> Timestamp -> DataValidity
outOfRange value minBound maxBound source timestamp = 
  OutOfRange { value, minBound, maxBound, source, timestamp }

-- | Create rate-of-change exceeded
rateExceeded :: Number -> Number -> Number -> SensorId -> Timestamp -> DataValidity
rateExceeded current previous maxRate source timestamp = 
  RateOfChangeExceeded { current, previous, maxRate, source, timestamp }

-- | Create never received
neverReceived :: DataValidity
neverReceived = NeverReceived

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Is data currently valid (not degraded, stale, or failed)?
isValid :: DataValidity -> Boolean
isValid (Valid _) = true
isValid _ = false

-- | Is data usable (valid or usable-degraded)?
isUsable :: DataValidity -> Boolean
isUsable (Valid _) = true
isUsable (Degraded r) = r.usable
isUsable _ = false

-- | Has data failed completely?
isFailed :: DataValidity -> Boolean
isFailed (SensorFailure _) = true
isFailed (CommsLost _) = true
isFailed NeverReceived = true
isFailed _ = false

-- | Does this state require a warning to be displayed?
requiresWarning :: DataValidity -> Boolean
requiresWarning (Valid _) = false
requiresWarning _ = true

-- | Should this data be displayed at all?
shouldDisplay :: DataValidity -> Boolean
shouldDisplay NeverReceived = false
shouldDisplay (SensorFailure _) = false  -- Show failure flag, not data
shouldDisplay _ = true

-- | Get confidence level (0.0 for failed states)
getConfidence :: DataValidity -> Percent
getConfidence (Valid r) = r.confidence
getConfidence (Degraded r) = r.confidence
getConfidence _ = 0.0

-- | Get age of stale data (Nothing if not stale)
getAge :: DataValidity -> Maybe Duration
getAge (Stale r) = Just r.age
getAge (CommsLost r) = Just r.since
getAge _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // display response logic
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compute display response from data validity
computeDisplayResponse :: DataAgeThresholds -> DataValidity -> DisplayResponse
computeDisplayResponse thresholds validity = case validity of
  Valid _ -> 
    DisplayNormal
  
  Degraded r -> 
    if r.usable 
      then DisplayWithFlag { flag: FlagDegraded }
      else DisplayXThrough
  
  Stale r -> 
    dataAgeToResponse thresholds r.age
  
  SensorFailure _ -> 
    DisplayWithFlag { flag: FlagSensorFail }
  
  CommsLost r -> 
    if r.since < thresholds.invalidMs
      then DisplayWithFlag { flag: FlagCommsLoss }
      else DisplayRemove
  
  CrossCheckFailed _ -> 
    DisplayWithFlag { flag: FlagXCheck }
  
  OutOfRange _ -> 
    DisplayWithFlag { flag: FlagOutOfRange }
  
  RateOfChangeExceeded _ -> 
    DisplayWithFlag { flag: FlagRateExceeded }
  
  NeverReceived -> 
    DisplayRemove

-- | Convert data age to display response
dataAgeToResponse :: DataAgeThresholds -> Duration -> DisplayResponse
dataAgeToResponse thresholds ageMs
  | ageMs < thresholds.freshMs = DisplayNormal
  | ageMs < thresholds.staleMs = DisplayWithAge { age: ageMs }
  | ageMs < thresholds.invalidMs = DisplayXThrough
  | otherwise = DisplayRemove

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // signal quality
-- ═════════════════════════════════════════════════════════════════════════════

-- | Signal quality indicator for medical displays
data SignalQuality
  = QualityGood       -- Strong, reliable signal
  | QualityMarginal   -- Usable but suboptimal
  | QualityPoor       -- Degraded, may be unreliable
  | QualityInvalid    -- Not usable
  | QualityLeadOff    -- Sensor disconnected (medical specific)

derive instance eqSignalQuality :: Eq SignalQuality
derive instance ordSignalQuality :: Ord SignalQuality

instance showSignalQuality :: Show SignalQuality where
  show QualityGood = "Good"
  show QualityMarginal = "Marginal"
  show QualityPoor = "Poor"
  show QualityInvalid = "Invalid"
  show QualityLeadOff = "LeadOff"

-- | Convert confidence percentage to signal quality
signalQualityFromConfidence :: Percent -> SignalQuality
signalQualityFromConfidence confidence
  | confidence >= 80.0 = QualityGood
  | confidence >= 50.0 = QualityMarginal
  | confidence >= 20.0 = QualityPoor
  | confidence > 0.0 = QualityInvalid
  | otherwise = QualityLeadOff

-- | Convert signal quality to display string
signalQualityToString :: SignalQuality -> String
signalQualityToString QualityGood = "GOOD"
signalQualityToString QualityMarginal = "MARG"
signalQualityToString QualityPoor = "POOR"
signalQualityToString QualityInvalid = "INVL"
signalQualityToString QualityLeadOff = "LEAD OFF"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // sensor source
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sensor source for redundancy tracking
data SensorSource
  = Primary         -- Primary sensor
  | Secondary       -- Backup sensor
  | Tertiary        -- Third-level redundancy
  | Computed        -- Computed/derived value
  | Synthesized     -- Synthesized from multiple sources

derive instance eqSensorSource :: Eq SensorSource
derive instance ordSensorSource :: Ord SensorSource

instance showSensorSource :: Show SensorSource where
  show Primary = "Primary"
  show Secondary = "Secondary"
  show Tertiary = "Tertiary"
  show Computed = "Computed"
  show Synthesized = "Synthesized"

-- | Check if this is a primary sensor
isPrimarySensor :: SensorSource -> Boolean
isPrimarySensor Primary = true
isPrimarySensor _ = false

-- | Get priority order (lower = higher priority)
sensorSourcePriority :: SensorSource -> Int
sensorSourcePriority Primary = 0
sensorSourcePriority Secondary = 1
sensorSourcePriority Tertiary = 2
sensorSourcePriority Computed = 3
sensorSourcePriority Synthesized = 4

-- | Compare sensor sources by priority
compareSensorSources :: SensorSource -> SensorSource -> Ordering
compareSensorSources a b = compare (sensorSourcePriority a) (sensorSourcePriority b)

-- | Check if first sensor has higher priority than second
hasHigherPriority :: SensorSource -> SensorSource -> Boolean
hasHigherPriority a b = sensorSourcePriority a < sensorSourcePriority b

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // validity comparisons
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compare two validity states (more valid = greater)
-- |
-- | Valid > Degraded > Stale > Failed states
validityScore :: DataValidity -> Int
validityScore (Valid _) = 100
validityScore (Degraded r) = if r.usable then 75 else 50
validityScore (Stale _) = 25
validityScore (OutOfRange _) = 20
validityScore (RateOfChangeExceeded _) = 15
validityScore (CrossCheckFailed _) = 10
validityScore (CommsLost _) = 5
validityScore (SensorFailure _) = 2
validityScore NeverReceived = 0

-- | Is first validity state better than second?
isBetterThan :: DataValidity -> DataValidity -> Boolean
isBetterThan a b = validityScore a > validityScore b

-- | Is first validity state worse than second?
isWorseThan :: DataValidity -> DataValidity -> Boolean
isWorseThan a b = validityScore a < validityScore b

-- | Are two validity states equivalent in severity?
isEquivalentTo :: DataValidity -> DataValidity -> Boolean
isEquivalentTo a b = validityScore a == validityScore b

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // validity combining
-- ═════════════════════════════════════════════════════════════════════════════

-- | Combine two validity states (take the worse)
-- |
-- | Useful for derived values that depend on multiple inputs:
-- | if any input is invalid, the derived value is invalid.
worstValidity :: DataValidity -> DataValidity -> DataValidity
worstValidity a b = if validityScore a <= validityScore b then a else b

-- | Combine two validity states (take the better)
-- |
-- | Useful for redundant sensors: take the best available reading.
bestValidity :: DataValidity -> DataValidity -> DataValidity
bestValidity a b = if validityScore a >= validityScore b then a else b

-- | Check if any validity state in array is failed
anyFailed :: Array DataValidity -> Boolean
anyFailed = any isFailed

-- | Check if all validity states in array are valid
allValid :: Array DataValidity -> Boolean
allValid = all isValid

-- | Check if all validity states in array are at least usable
allUsable :: Array DataValidity -> Boolean
allUsable = all isUsable

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // age arithmetic
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compute age from timestamps
computeAge :: Timestamp -> Timestamp -> Duration
computeAge currentTime lastValidTime = currentTime - lastValidTime

-- | Update stale data with new age
updateStaleAge :: Timestamp -> DataValidity -> DataValidity
updateStaleAge currentTime validity = case validity of
  Stale r -> Stale $ r { age = currentTime - r.lastValid }
  CommsLost r -> CommsLost $ r { since = currentTime - r.lastPacket }
  other -> other

-- | Check if age exceeds threshold
ageExceeds :: Duration -> Duration -> Boolean
ageExceeds age threshold = age > threshold

-- | Compute time until state becomes invalid
timeUntilInvalid :: DataAgeThresholds -> Duration -> Duration
timeUntilInvalid thresholds currentAge = 
  if currentAge >= thresholds.invalidMs 
    then 0.0 
    else thresholds.invalidMs - currentAge

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // confidence math
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp confidence to valid range
clampConfidence :: Percent -> Percent
clampConfidence c
  | c < 0.0 = 0.0
  | c > 100.0 = 100.0
  | otherwise = c

-- | Average confidence of multiple readings
averageConfidence :: Array Percent -> Percent
averageConfidence arr = 
  let len = Array.length arr
  in if len == 0 
       then 0.0 
       else sumNumbers arr / toNumber len

-- | Minimum confidence of multiple readings (pessimistic)
minimumConfidence :: Array Percent -> Percent
minimumConfidence arr = foldl minNum 100.0 arr

-- | Check if confidence meets threshold
confidenceMeetsThreshold :: Percent -> Percent -> Boolean
confidenceMeetsThreshold confidence threshold = confidence >= threshold

-- | Degrade confidence by factor (0.0-1.0)
degradeConfidence :: Number -> Percent -> Percent
degradeConfidence factor confidence = clampConfidence (confidence * factor)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // rate of change
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compute rate of change between two values
computeRateOfChange :: Number -> Number -> Duration -> Number
computeRateOfChange current previous deltaMs =
  if deltaMs <= 0.0 
    then 0.0 
    else absNum (current - previous) / (deltaMs / 1000.0)

-- | Check if rate of change is within limits
rateWithinLimits :: Number -> Number -> Boolean
rateWithinLimits rate maxRate = rate <= maxRate

-- | Compute disagreement between two sensor readings
computeDisagreement :: Number -> Number -> Number -> Percent
computeDisagreement value1 value2 referenceRange =
  if referenceRange <= 0.0
    then 100.0
    else clampConfidence (absNum (value1 - value2) / referenceRange * 100.0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // compound predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Is data valid AND from primary sensor?
isValidPrimary :: DataValidity -> SensorSource -> Boolean
isValidPrimary validity source = isValid validity && isPrimarySensor source

-- | Is data usable but degraded?
isUsableDegraded :: DataValidity -> Boolean
isUsableDegraded (Degraded r) = r.usable
isUsableDegraded _ = false

-- | Is data in a warning state (not failed, but not fully valid)?
isWarningState :: DataValidity -> Boolean
isWarningState validity = requiresWarning validity && not (isFailed validity)

-- | Does data require immediate attention (failed or very stale)?
requiresImmediateAttention :: DataAgeThresholds -> DataValidity -> Boolean
requiresImmediateAttention thresholds validity = case validity of
  SensorFailure _ -> true
  CommsLost r -> r.since >= thresholds.staleMs
  Stale r -> r.age >= thresholds.staleMs
  CrossCheckFailed _ -> true
  NeverReceived -> true
  _ -> false

-- | Can data be used for safety-critical decisions?
safeForCriticalUse :: Percent -> DataValidity -> Boolean
safeForCriticalUse minConfidence validity = case validity of
  Valid r -> r.confidence >= minConfidence
  Degraded r -> r.usable && r.confidence >= minConfidence
  _ -> false

-- | Is data either failed OR below confidence threshold?
-- |
-- | Useful for triggering fallback to backup sensors.
needsFallback :: Percent -> DataValidity -> Boolean
needsFallback minConfidence validity = 
  isFailed validity || getConfidence validity < minConfidence

-- | Are two validity states different in severity?
-- |
-- | Useful for detecting state transitions that need logging.
validityChanged :: DataValidity -> DataValidity -> Boolean
validityChanged a b = validityScore a /= validityScore b

-- | Is data either stale OR from a non-primary source?
-- |
-- | Triggers "degraded operation" mode in some systems.
isOperatingDegraded :: DataValidity -> SensorSource -> Boolean
isOperatingDegraded validity source = 
  requiresWarning validity || not (isPrimarySensor source)

-- | Does either of two readings require attention?
-- |
-- | For redundant sensor pairs - alert if either has issues.
eitherRequiresAttention :: DataAgeThresholds -> DataValidity -> DataValidity -> Boolean
eitherRequiresAttention thresholds a b =
  requiresImmediateAttention thresholds a || requiresImmediateAttention thresholds b

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // helper functions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Absolute value helper
absNum :: Number -> Number
absNum n = if n < 0.0 then 0.0 - n else n

-- | Minimum of two numbers
minNum :: Number -> Number -> Number
minNum a b = if a <= b then a else b

-- | Sum an array of numbers
sumNumbers :: Array Number -> Number
sumNumbers = foldl (+) 0.0
