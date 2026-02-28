-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // schema // trigger // atoms
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Trigger Atoms - bounded primitives for trigger timing and thresholds.
-- |
-- | These atoms define the bounded numerical values used in trigger
-- | configurations: delays, counts, cooldowns, time windows, and
-- | proximity radii. All values clamp to their defined bounds.
-- |
-- | ## SCHEMA.md Reference
-- | ```
-- | | TriggerDelay    | Number | 0    | 30000 | clamps   |
-- | | TriggerCount    | Int    | 1    | 100   | clamps   |
-- | | TriggerCooldown | Number | 0    | none  | finite   |
-- | | TriggerWindow   | Number | 0    | 10000 | clamps   |
-- | | ProximityRadius | Number | 0    | 500   | clamps   |
-- | ```
-- |
-- | ## Dependencies
-- | - Prelude (Eq, Ord, Show, min, max)
-- |
-- | ## Dependents
-- | - Trigger.purs (uses these atoms in molecules/compounds)
-- | - Component.* (configures trigger behavior)

module Hydrogen.Schema.Gestural.Trigger.Atoms
  ( -- * TriggerDelay (0-30000ms, clamps)
    TriggerDelay
  , mkTriggerDelay
  , unwrapTriggerDelay
  , minTriggerDelay
  , maxTriggerDelay
  , noDelay
  , shortDelay
  , mediumDelay
  , longDelay
    -- * TriggerCount (1-100, clamps)
  , TriggerCount
  , mkTriggerCount
  , unwrapTriggerCount
  , minTriggerCount
  , maxTriggerCount
  , singleTrigger
  , doubleTrigger
  , tripleTrigger
    -- * TriggerCooldown (0+, finite)
  , TriggerCooldown
  , mkTriggerCooldown
  , unwrapTriggerCooldown
  , noCooldown
  , shortCooldown
  , standardCooldown
    -- * TriggerWindow (0-10000ms, clamps)
  , TriggerWindow
  , mkTriggerWindow
  , unwrapTriggerWindow
  , minTriggerWindow
  , maxTriggerWindow
  , quickWindow
  , standardWindow
  , extendedWindow
    -- * ProximityRadius (0-500px, clamps)
  , ProximityRadius
  , mkProximityRadius
  , unwrapProximityRadius
  , minProximityRadius
  , maxProximityRadius
  , tightRadius
  , nearRadius
  , farRadius
  ) where

import Prelude

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // trigger // delay
-- ═════════════════════════════════════════════════════════════════════════════

-- | Delay before trigger activates (0-30000ms, clamps).
-- |
-- | Bounded: minimum 0ms (immediate), maximum 30000ms (30 seconds).
-- | Values outside this range are clamped.
newtype TriggerDelay = TriggerDelay Number

derive instance eqTriggerDelay :: Eq TriggerDelay
derive instance ordTriggerDelay :: Ord TriggerDelay

instance showTriggerDelay :: Show TriggerDelay where
  show (TriggerDelay ms) = "TriggerDelay(" <> show ms <> "ms)"

-- | Minimum trigger delay (0ms - immediate)
minTriggerDelay :: Number
minTriggerDelay = 0.0

-- | Maximum trigger delay (30000ms - 30 seconds)
maxTriggerDelay :: Number
maxTriggerDelay = 30000.0

-- | Create a bounded trigger delay (clamps to 0-30000)
mkTriggerDelay :: Number -> TriggerDelay
mkTriggerDelay ms = TriggerDelay (clampNumber minTriggerDelay maxTriggerDelay ms)

-- | Unwrap the millisecond value
unwrapTriggerDelay :: TriggerDelay -> Number
unwrapTriggerDelay (TriggerDelay ms) = ms

-- | No delay (immediate activation)
noDelay :: TriggerDelay
noDelay = TriggerDelay 0.0

-- | Short delay (100ms - quick hover detection)
shortDelay :: TriggerDelay
shortDelay = TriggerDelay 100.0

-- | Medium delay (300ms - intentional hover)
mediumDelay :: TriggerDelay
mediumDelay = TriggerDelay 300.0

-- | Long delay (500ms - deliberate hover)
longDelay :: TriggerDelay
longDelay = TriggerDelay 500.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // trigger // count
-- ═════════════════════════════════════════════════════════════════════════════

-- | Number of occurrences required to trigger (1-100, clamps).
-- |
-- | Bounded: minimum 1 (single occurrence), maximum 100.
-- | Values outside this range are clamped.
newtype TriggerCount = TriggerCount Int

derive instance eqTriggerCount :: Eq TriggerCount
derive instance ordTriggerCount :: Ord TriggerCount

instance showTriggerCount :: Show TriggerCount where
  show (TriggerCount n) = "TriggerCount(" <> show n <> ")"

-- | Minimum trigger count (1 - single occurrence)
minTriggerCount :: Int
minTriggerCount = 1

-- | Maximum trigger count (100)
maxTriggerCount :: Int
maxTriggerCount = 100

-- | Create a bounded trigger count (clamps to 1-100)
mkTriggerCount :: Int -> TriggerCount
mkTriggerCount n = TriggerCount (clampInt minTriggerCount maxTriggerCount n)

-- | Unwrap the count value
unwrapTriggerCount :: TriggerCount -> Int
unwrapTriggerCount (TriggerCount n) = n

-- | Single occurrence trigger
singleTrigger :: TriggerCount
singleTrigger = TriggerCount 1

-- | Double occurrence trigger
doubleTrigger :: TriggerCount
doubleTrigger = TriggerCount 2

-- | Triple occurrence trigger
tripleTrigger :: TriggerCount
tripleTrigger = TriggerCount 3

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // trigger // cooldown
-- ═════════════════════════════════════════════════════════════════════════════

-- | Time before trigger can reactivate (0+, finite, no upper bound).
-- |
-- | Bounded: minimum 0ms (no cooldown), no maximum.
-- | Negative values are clamped to 0.
newtype TriggerCooldown = TriggerCooldown Number

derive instance eqTriggerCooldown :: Eq TriggerCooldown
derive instance ordTriggerCooldown :: Ord TriggerCooldown

instance showTriggerCooldown :: Show TriggerCooldown where
  show (TriggerCooldown ms) = "TriggerCooldown(" <> show ms <> "ms)"

-- | Create a bounded trigger cooldown (clamps to 0+)
mkTriggerCooldown :: Number -> TriggerCooldown
mkTriggerCooldown ms = TriggerCooldown (max 0.0 ms)

-- | Unwrap the millisecond value
unwrapTriggerCooldown :: TriggerCooldown -> Number
unwrapTriggerCooldown (TriggerCooldown ms) = ms

-- | No cooldown (can retrigger immediately)
noCooldown :: TriggerCooldown
noCooldown = TriggerCooldown 0.0

-- | Short cooldown (500ms)
shortCooldown :: TriggerCooldown
shortCooldown = TriggerCooldown 500.0

-- | Standard cooldown (1000ms)
standardCooldown :: TriggerCooldown
standardCooldown = TriggerCooldown 1000.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // trigger // window
-- ═════════════════════════════════════════════════════════════════════════════

-- | Time window for sequence completion (0-10000ms, clamps).
-- |
-- | Bounded: minimum 0ms, maximum 10000ms (10 seconds).
-- | Values outside this range are clamped.
newtype TriggerWindow = TriggerWindow Number

derive instance eqTriggerWindow :: Eq TriggerWindow
derive instance ordTriggerWindow :: Ord TriggerWindow

instance showTriggerWindow :: Show TriggerWindow where
  show (TriggerWindow ms) = "TriggerWindow(" <> show ms <> "ms)"

-- | Minimum trigger window (0ms)
minTriggerWindow :: Number
minTriggerWindow = 0.0

-- | Maximum trigger window (10000ms - 10 seconds)
maxTriggerWindow :: Number
maxTriggerWindow = 10000.0

-- | Create a bounded trigger window (clamps to 0-10000)
mkTriggerWindow :: Number -> TriggerWindow
mkTriggerWindow ms = TriggerWindow (clampNumber minTriggerWindow maxTriggerWindow ms)

-- | Unwrap the millisecond value
unwrapTriggerWindow :: TriggerWindow -> Number
unwrapTriggerWindow (TriggerWindow ms) = ms

-- | Quick window (500ms - rapid sequences)
quickWindow :: TriggerWindow
quickWindow = TriggerWindow 500.0

-- | Standard window (2000ms - normal sequences)
standardWindow :: TriggerWindow
standardWindow = TriggerWindow 2000.0

-- | Extended window (5000ms - complex sequences)
extendedWindow :: TriggerWindow
extendedWindow = TriggerWindow 5000.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // proximity // radius
-- ═════════════════════════════════════════════════════════════════════════════

-- | Proximity detection radius (0-500px, clamps).
-- |
-- | Bounded: minimum 0px, maximum 500px.
-- | Values outside this range are clamped.
newtype ProximityRadius = ProximityRadius Number

derive instance eqProximityRadius :: Eq ProximityRadius
derive instance ordProximityRadius :: Ord ProximityRadius

instance showProximityRadius :: Show ProximityRadius where
  show (ProximityRadius px) = "ProximityRadius(" <> show px <> "px)"

-- | Minimum proximity radius (0px)
minProximityRadius :: Number
minProximityRadius = 0.0

-- | Maximum proximity radius (500px)
maxProximityRadius :: Number
maxProximityRadius = 500.0

-- | Create a bounded proximity radius (clamps to 0-500)
mkProximityRadius :: Number -> ProximityRadius
mkProximityRadius px = ProximityRadius (clampNumber minProximityRadius maxProximityRadius px)

-- | Unwrap the pixel value
unwrapProximityRadius :: ProximityRadius -> Number
unwrapProximityRadius (ProximityRadius px) = px

-- | Tight radius (50px - very close proximity)
tightRadius :: ProximityRadius
tightRadius = ProximityRadius 50.0

-- | Near radius (100px - close proximity)
nearRadius :: ProximityRadius
nearRadius = ProximityRadius 100.0

-- | Far radius (200px - extended proximity)
farRadius :: ProximityRadius
farRadius = ProximityRadius 200.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp a Number to a range
clampNumber :: Number -> Number -> Number -> Number
clampNumber lo hi x = max lo (min hi x)

-- | Clamp an Int to a range
clampInt :: Int -> Int -> Int -> Int
clampInt lo hi x = max lo (min hi x)
