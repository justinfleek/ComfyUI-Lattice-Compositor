-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                     // hydrogen // schema // geometry // angle // subdivision
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Angular subdivision atoms — arc minutes and arc seconds.
-- |
-- | ## Purpose
-- |
-- | Arc minutes and arc seconds are fine angular subdivisions used in:
-- | - **Astronomy**: celestial coordinates, telescope pointing
-- | - **Navigation**: latitude/longitude precision
-- | - **Surveying**: land measurement
-- | - **Geodesy**: Earth measurement
-- |
-- | ## Relationships
-- |
-- | - 1 degree = 60 arc minutes
-- | - 1 arc minute = 60 arc seconds
-- | - 1 degree = 3600 arc seconds
-- |
-- | ## Notation
-- |
-- | - Arc minutes: ′ (prime symbol) or '
-- | - Arc seconds: ″ (double prime) or "
-- | - Example: 40° 26′ 46″ N (latitude of New York City)
-- |
-- | ## Dependencies
-- |
-- | - Schema.Geometry.Angle (Degrees for conversion)

module Hydrogen.Schema.Geometry.Angle.Subdivision
  ( -- * Arc Minute
    ArcMinute(ArcMinute)
  , arcMinute
  , arcMinutes
  , unwrapArcMinute
  , arcMinuteToDegrees
  , degreesToArcMinutes
  
  -- * Arc Second
  , ArcSecond(ArcSecond)
  , arcSecond
  , arcSeconds
  , unwrapArcSecond
  , arcSecondToDegrees
  , degreesToArcSeconds
  
  -- * Conversions
  , arcMinuteToArcSeconds
  , arcSecondsToArcMinute
  
  -- * DMS (Degrees-Minutes-Seconds)
  , DMS(DMS)
  , dms
  , dmsFromDegrees
  , dmsToDegrees
  , dmsIsNegative
  
  -- * Operations
  , addArcMinutes
  , addArcSeconds
  , scaleArcMinute
  , scaleArcSecond
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (>=)
  , negate
  )

import Data.Int (floor, toNumber) as Int
import Data.Number (abs, floor) as Number

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // arc minute
-- ═════════════════════════════════════════════════════════════════════════════

-- | Arc minute — 1/60 of a degree.
-- |
-- | Can be positive or negative. No wrapping behavior (unlike Degrees).
-- | This is a pure measurement atom, not a cyclic angle.
newtype ArcMinute = ArcMinute Number

derive instance eqArcMinute :: Eq ArcMinute
derive instance ordArcMinute :: Ord ArcMinute

instance showArcMinute :: Show ArcMinute where
  show (ArcMinute m) = show m <> "′"

-- | Create an arc minute value
arcMinute :: Number -> ArcMinute
arcMinute = ArcMinute

-- | Alias for arcMinute
arcMinutes :: Number -> ArcMinute
arcMinutes = ArcMinute

-- | Extract the raw value
unwrapArcMinute :: ArcMinute -> Number
unwrapArcMinute (ArcMinute m) = m

-- | Convert arc minutes to degrees
-- |
-- | 60 arc minutes = 1 degree
arcMinuteToDegrees :: ArcMinute -> Number
arcMinuteToDegrees (ArcMinute m) = m / 60.0

-- | Convert degrees to arc minutes
-- |
-- | 1 degree = 60 arc minutes
degreesToArcMinutes :: Number -> ArcMinute
degreesToArcMinutes d = ArcMinute (d * 60.0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // arc second
-- ═════════════════════════════════════════════════════════════════════════════

-- | Arc second — 1/60 of an arc minute, 1/3600 of a degree.
-- |
-- | Can be positive or negative. No wrapping behavior.
-- | This is a pure measurement atom for precise angular measurement.
newtype ArcSecond = ArcSecond Number

derive instance eqArcSecond :: Eq ArcSecond
derive instance ordArcSecond :: Ord ArcSecond

instance showArcSecond :: Show ArcSecond where
  show (ArcSecond s) = show s <> "″"

-- | Create an arc second value
arcSecond :: Number -> ArcSecond
arcSecond = ArcSecond

-- | Alias for arcSecond
arcSeconds :: Number -> ArcSecond
arcSeconds = ArcSecond

-- | Extract the raw value
unwrapArcSecond :: ArcSecond -> Number
unwrapArcSecond (ArcSecond s) = s

-- | Convert arc seconds to degrees
-- |
-- | 3600 arc seconds = 1 degree
arcSecondToDegrees :: ArcSecond -> Number
arcSecondToDegrees (ArcSecond s) = s / 3600.0

-- | Convert degrees to arc seconds
-- |
-- | 1 degree = 3600 arc seconds
degreesToArcSeconds :: Number -> ArcSecond
degreesToArcSeconds d = ArcSecond (d * 3600.0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // conversions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert arc minutes to arc seconds
-- |
-- | 1 arc minute = 60 arc seconds
arcMinuteToArcSeconds :: ArcMinute -> ArcSecond
arcMinuteToArcSeconds (ArcMinute m) = ArcSecond (m * 60.0)

-- | Convert arc seconds to arc minutes
-- |
-- | 60 arc seconds = 1 arc minute
arcSecondsToArcMinute :: ArcSecond -> ArcMinute
arcSecondsToArcMinute (ArcSecond s) = ArcMinute (s / 60.0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                              // dms (degrees-minutes-seconds)
-- ═════════════════════════════════════════════════════════════════════════════

-- | Degrees-Minutes-Seconds representation.
-- |
-- | Traditional notation for geographic coordinates and astronomy.
-- | Example: 40° 26′ 46″ represents 40 degrees, 26 arc minutes, 46 arc seconds.
-- |
-- | - **degrees**: Whole degrees (0-359 for positive, sign stored separately)
-- | - **minutes**: Arc minutes (0-59)
-- | - **seconds**: Arc seconds (0-59.999...)
-- | - **negative**: True if the angle is negative (South latitude, West longitude)
newtype DMS = DMS
  { degrees :: Int
  , minutes :: Int
  , seconds :: Number
  , negative :: Boolean
  }

derive instance eqDMS :: Eq DMS
derive instance ordDMS :: Ord DMS

instance showDMS :: Show DMS where
  show (DMS d) = 
    let sign = if d.negative then "-" else ""
    in sign <> show d.degrees <> "° " <> show d.minutes <> "′ " <> show d.seconds <> "″"

-- | Create a DMS value from components
dms :: Int -> Int -> Number -> Boolean -> DMS
dms deg mins secs neg = DMS
  { degrees: clampInt 0 359 deg
  , minutes: clampInt 0 59 mins
  , seconds: clampNumber 0.0 59.999999 secs
  , negative: neg
  }

-- | Clamp an Int to a range
clampInt :: Int -> Int -> Int -> Int
clampInt minVal maxVal n
  | n < minVal = minVal
  | n >= maxVal = maxVal
  | true = n

-- | Clamp a Number to a range
clampNumber :: Number -> Number -> Number -> Number
clampNumber minVal maxVal n
  | n < minVal = minVal
  | n >= maxVal = maxVal
  | true = n

-- | Convert decimal degrees to DMS
-- |
-- | Example: 40.446111 → 40° 26′ 46″
dmsFromDegrees :: Number -> DMS
dmsFromDegrees decimalDegrees =
  let
    neg = decimalDegrees < 0.0
    absVal = Number.abs decimalDegrees
    deg = Int.floor absVal
    remainderMinutes = (absVal - Int.toNumber deg) * 60.0
    mins = Int.floor remainderMinutes
    secs = (remainderMinutes - Int.toNumber mins) * 60.0
  in DMS
    { degrees: deg
    , minutes: mins
    , seconds: secs
    , negative: neg
    }

-- | Convert DMS to decimal degrees
-- |
-- | Example: 40° 26′ 46″ → 40.446111
dmsToDegrees :: DMS -> Number
dmsToDegrees (DMS d) =
  let
    absVal = Int.toNumber d.degrees 
           + Int.toNumber d.minutes / 60.0 
           + d.seconds / 3600.0
  in if d.negative then negate absVal else absVal

-- | Check if DMS represents a negative angle
dmsIsNegative :: DMS -> Boolean
dmsIsNegative (DMS d) = d.negative

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add two arc minute values
addArcMinutes :: ArcMinute -> ArcMinute -> ArcMinute
addArcMinutes (ArcMinute a) (ArcMinute b) = ArcMinute (a + b)

-- | Add two arc second values
addArcSeconds :: ArcSecond -> ArcSecond -> ArcSecond
addArcSeconds (ArcSecond a) (ArcSecond b) = ArcSecond (a + b)

-- | Scale an arc minute value
scaleArcMinute :: Number -> ArcMinute -> ArcMinute
scaleArcMinute factor (ArcMinute m) = ArcMinute (m * factor)

-- | Scale an arc second value
scaleArcSecond :: Number -> ArcSecond -> ArcSecond
scaleArcSecond factor (ArcSecond s) = ArcSecond (s * factor)
