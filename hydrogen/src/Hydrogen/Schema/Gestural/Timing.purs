-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // gestural // timing
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Timing - temporal atoms for gesture recognition.
-- |
-- | Models time-based parameters for tap detection, hold gestures,
-- | and multi-click recognition. Essential for distinguishing between
-- | single tap, double tap, long press, and click sequences.
-- |
-- | ## Dependencies
-- | - Prelude (Eq, Ord, Show)
-- | - Hydrogen.Schema.Bounded (bounds documentation)
-- |
-- | ## Dependents
-- | - Gestural.Gesture.Tap (uses TapInterval for multi-tap detection)
-- | - Gestural.Gesture.LongPress (uses HoldDuration)
-- | - Gestural.Trigger (uses ClickCount for easter eggs)

module Hydrogen.Schema.Gestural.Timing
  ( -- * Click Count
    ClickCount(ClickCount)
  , clickCount
  , singleClick
  , doubleClick
  , tripleClick
  , unwrapClickCount
  , incrementClick
  , resetClickCount
  , clickCountBounds
    -- * Hold Duration
  , HoldDuration(HoldDuration)
  , holdDuration
  , holdDurationMs
  , zeroHold
  , shortHold
  , longHold
  , unwrapHoldDuration
  , addHoldTime
  , isLongHold
  , holdDurationBounds
    -- * Tap Interval
  , TapInterval(TapInterval)
  , tapInterval
  , defaultTapInterval
  , fastTapInterval
  , slowTapInterval
  , unwrapTapInterval
  , isWithinInterval
  , tapIntervalBounds
    -- * Timing State (Molecule)
  , TimingState
  , initialTimingState
  , recordClick
  , recordHoldStart
  , recordHoldEnd
  , updateHold
  , timingClicks
  , timingHoldDuration
  , timingSinceLastClick
  , isMultiClick
  , isHolding
  ) where

import Prelude

import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // click count
-- ═════════════════════════════════════════════════════════════════════════════

-- | Number of consecutive clicks [1, ∞)
-- |
-- | Tracks rapid successive clicks for multi-click detection:
-- | - 1: Single click
-- | - 2: Double click (select word)
-- | - 3: Triple click (select paragraph)
-- | - 4+: Used for easter eggs and power-user features
-- |
-- | Reset when tap interval exceeded between clicks.
newtype ClickCount = ClickCount Int

derive instance eqClickCount :: Eq ClickCount
derive instance ordClickCount :: Ord ClickCount

instance showClickCount :: Show ClickCount where
  show (ClickCount n) = show n <> " clicks"

-- | Create click count (clamps to minimum of 1)
clickCount :: Int -> ClickCount
clickCount n = ClickCount (max 1 n)

-- | Single click
singleClick :: ClickCount
singleClick = ClickCount 1

-- | Double click
doubleClick :: ClickCount
doubleClick = ClickCount 2

-- | Triple click
tripleClick :: ClickCount
tripleClick = ClickCount 3

-- | Extract raw count
unwrapClickCount :: ClickCount -> Int
unwrapClickCount (ClickCount n) = n

-- | Increment click count
incrementClick :: ClickCount -> ClickCount
incrementClick (ClickCount n) = ClickCount (n + 1)

-- | Reset to single click
resetClickCount :: ClickCount
resetClickCount = singleClick

-- | Bounds for ClickCount
-- |
-- | Min: 1 (at least one click to register)
-- | Max: unbounded (practical limit ~10 for UI purposes)
clickCountBounds :: Bounded.IntBounds
clickCountBounds = Bounded.intBounds 1 100 "clickCount" "Consecutive click count (1+)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // hold duration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Duration of a press/hold gesture in milliseconds [0, ∞)
-- |
-- | Used for long press detection and hold-to-reveal gestures.
-- | Typical thresholds:
-- | - 0-100ms: Tap
-- | - 100-300ms: Short hold (preview)
-- | - 300-500ms: Medium hold (context menu)
-- | - 500ms+: Long hold (drag mode, peek/pop)
newtype HoldDuration = HoldDuration Number

derive instance eqHoldDuration :: Eq HoldDuration
derive instance ordHoldDuration :: Ord HoldDuration

instance showHoldDuration :: Show HoldDuration where
  show (HoldDuration ms) = show ms <> "ms hold"

-- | Create hold duration (clamps to non-negative)
holdDuration :: Number -> HoldDuration
holdDuration ms = HoldDuration (max 0.0 ms)

-- | Create hold duration from milliseconds (alias)
holdDurationMs :: Number -> HoldDuration
holdDurationMs = holdDuration

-- | Zero hold (instant release)
zeroHold :: HoldDuration
zeroHold = HoldDuration 0.0

-- | Short hold threshold (300ms)
shortHold :: HoldDuration
shortHold = HoldDuration 300.0

-- | Long hold threshold (500ms)
longHold :: HoldDuration
longHold = HoldDuration 500.0

-- | Extract raw duration in milliseconds
unwrapHoldDuration :: HoldDuration -> Number
unwrapHoldDuration (HoldDuration ms) = ms

-- | Add time to hold duration
addHoldTime :: Number -> HoldDuration -> HoldDuration
addHoldTime delta (HoldDuration ms) = HoldDuration (max 0.0 (ms + delta))

-- | Is this a long hold? (> 500ms by default)
isLongHold :: HoldDuration -> Boolean
isLongHold (HoldDuration ms) = ms >= 500.0

-- | Bounds for HoldDuration
-- |
-- | Min: 0 (instant)
-- | Max: unbounded (practical limit ~30000ms for UI)
holdDurationBounds :: Bounded.NumberBounds
holdDurationBounds = Bounded.numberBounds 0.0 30000.0 "holdDuration" "Hold duration in milliseconds"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // tap interval
-- ═════════════════════════════════════════════════════════════════════════════

-- | Maximum time between taps for multi-tap detection [0, ∞)
-- |
-- | If time between taps exceeds this interval, the tap sequence resets.
-- | Typical values:
-- | - 200ms: Fast (power users)
-- | - 300ms: Default (most users)
-- | - 500ms: Slow (accessibility)
newtype TapInterval = TapInterval Number

derive instance eqTapInterval :: Eq TapInterval
derive instance ordTapInterval :: Ord TapInterval

instance showTapInterval :: Show TapInterval where
  show (TapInterval ms) = show ms <> "ms interval"

-- | Create tap interval (clamps to non-negative)
tapInterval :: Number -> TapInterval
tapInterval ms = TapInterval (max 0.0 ms)

-- | Default tap interval (300ms)
defaultTapInterval :: TapInterval
defaultTapInterval = TapInterval 300.0

-- | Fast tap interval (200ms) for power users
fastTapInterval :: TapInterval
fastTapInterval = TapInterval 200.0

-- | Slow tap interval (500ms) for accessibility
slowTapInterval :: TapInterval
slowTapInterval = TapInterval 500.0

-- | Extract raw interval in milliseconds
unwrapTapInterval :: TapInterval -> Number
unwrapTapInterval (TapInterval ms) = ms

-- | Is elapsed time within tap interval?
isWithinInterval :: Number -> TapInterval -> Boolean
isWithinInterval elapsed (TapInterval maxInterval) = elapsed <= maxInterval

-- | Bounds for TapInterval
-- |
-- | Min: 0 (no multi-tap detection)
-- | Max: 10000ms (practical upper limit)
tapIntervalBounds :: Bounded.NumberBounds
tapIntervalBounds = Bounded.numberBounds 0.0 10000.0 "tapInterval" "Maximum ms between taps for multi-tap"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // timing state molecule
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete timing state for gesture recognition
-- |
-- | Tracks clicks, holds, and timing for composite gesture detection.
type TimingState =
  { clicks :: ClickCount           -- ^ Current click count
  , holdStart :: Maybe Number      -- ^ Timestamp when hold began
  , holdDuration :: HoldDuration   -- ^ Accumulated hold time
  , lastClickTime :: Maybe Number  -- ^ Timestamp of last click
  , tapInterval :: TapInterval     -- ^ Interval for multi-tap
  , currentTime :: Number          -- ^ Current timestamp
  }

-- | Initial timing state
initialTimingState :: TapInterval -> TimingState
initialTimingState interval =
  { clicks: singleClick
  , holdStart: Nothing
  , holdDuration: zeroHold
  , lastClickTime: Nothing
  , tapInterval: interval
  , currentTime: 0.0
  }

-- | Record a click event
recordClick :: Number -> TimingState -> TimingState
recordClick timestamp ts = case ts.lastClickTime of
  Nothing -> 
    ts { clicks = singleClick
       , lastClickTime = Just timestamp
       , currentTime = timestamp
       }
  Just lastTime ->
    let elapsed = timestamp - lastTime
    in if isWithinInterval elapsed ts.tapInterval
      then ts { clicks = incrementClick ts.clicks
              , lastClickTime = Just timestamp
              , currentTime = timestamp
              }
      else ts { clicks = singleClick
              , lastClickTime = Just timestamp
              , currentTime = timestamp
              }

-- | Record hold start
recordHoldStart :: Number -> TimingState -> TimingState
recordHoldStart timestamp ts =
  ts { holdStart = Just timestamp
     , holdDuration = zeroHold
     , currentTime = timestamp
     }

-- | Record hold end
recordHoldEnd :: Number -> TimingState -> TimingState
recordHoldEnd timestamp ts = case ts.holdStart of
  Nothing -> ts { currentTime = timestamp }
  Just start ->
    ts { holdStart = Nothing
       , holdDuration = holdDuration (timestamp - start)
       , currentTime = timestamp
       }

-- | Update hold duration (call during hold)
updateHold :: Number -> TimingState -> TimingState
updateHold timestamp ts = case ts.holdStart of
  Nothing -> ts { currentTime = timestamp }
  Just start ->
    ts { holdDuration = holdDuration (timestamp - start)
       , currentTime = timestamp
       }

-- | Get current click count
timingClicks :: TimingState -> Int
timingClicks ts = unwrapClickCount ts.clicks

-- | Get current hold duration
timingHoldDuration :: TimingState -> Number
timingHoldDuration ts = unwrapHoldDuration ts.holdDuration

-- | Get time since last click
timingSinceLastClick :: TimingState -> Maybe Number
timingSinceLastClick ts = case ts.lastClickTime of
  Nothing -> Nothing
  Just lastTime -> Just (ts.currentTime - lastTime)

-- | Is this a multi-click? (2+)
isMultiClick :: TimingState -> Boolean
isMultiClick ts = unwrapClickCount ts.clicks >= 2

-- | Is currently holding?
isHolding :: TimingState -> Boolean
isHolding ts = case ts.holdStart of
  Just _ -> true
  Nothing -> false
