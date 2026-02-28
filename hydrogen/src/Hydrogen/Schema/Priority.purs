-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                             // hydrogen // schema // priority
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Priority — Prioritization metadata for Schema entities.
-- |
-- | ## Purpose
-- |
-- | At billion-agent scale, resources are limited. Not all entities can be
-- | processed with equal priority. This module provides:
-- |
-- | 1. **Semantic priorities** — Critical/High/Normal/Low/Background
-- | 2. **Numeric priorities** — Fine-grained 0-1000 scale
-- | 3. **Priority queues** — Ordered processing of prioritized items
-- | 4. **Deadline metadata** — Time-sensitive priority adjustments
-- |
-- | ## Design Philosophy
-- |
-- | Priorities are metadata, not core Schema atoms. They guide:
-- | - Render order (critical content first)
-- | - Resource allocation (high-priority gets more GPU time)
-- | - Cache eviction (low-priority evicted first)
-- | - Network requests (background requests yield to user-facing)
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | -- Prioritize a render request
-- | let heroImage = prioritize Critical (loadImage "hero.png")
-- | let thumbnails = prioritize Background (loadThumbnails gallery)
-- | 
-- | -- Fine-grained numeric priority
-- | let userAction = withPriority (numericPriority 950) handleClick
-- | ```
-- |
-- | ## Invariants
-- |
-- | 1. **Bounded**: Numeric priority is always in [0, 1000]
-- | 2. **Deterministic**: Same inputs → same priority
-- | 3. **Monotonic ordering**: Critical > High > Normal > Low > Background

module Hydrogen.Schema.Priority
  ( -- * Semantic Priority
    Priority(Critical, High, Normal, Low, Background)
  , priorityToInt
  , intToPriority
  , priorityOrd
  
  -- * Numeric Priority
  , NumericPriority
  , numericPriority
  , numericPriorityUnsafe
  , unwrapNumericPriority
  , numericPriorityBounds
  
  -- * Prioritized Wrapper
  , Prioritized
  , prioritize
  , prioritizeNumeric
  , getPriority
  , getNumericPriority
  , getValue
  , setPriority
  , mapPrioritized
  
  -- * Priority Queue
  , PriorityQueue
  , emptyQueue
  , enqueue
  , dequeue
  , peek
  , queueSize
  , queueToArray
  , mergeQueues
  
  -- * Deadline Priority
  , Deadline(Immediate, Soon, Eventually, NoDeadline)
  , DeadlinedPriority
  , withDeadline
  , deadlineBoost
  , effectivePriority
  
  -- * Priority Utilities
  , higherPriority
  , lowerPriority
  , maxPriority
  , minPriority
  , averagePriority
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , compare
  , otherwise
  , map
  , ($)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (>)
  , (<=)
  , (>=)
  , (==)
  , (/=)
  , (<>)
  , Ordering(LT, GT, EQ)
  )

import Data.Array (length, index, foldl, snoc, filter, sortBy, head, uncons) as Array
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Bounded (clampInt, IntBounds, intBounds) as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // semantic priority
-- ═════════════════════════════════════════════════════════════════════════════

-- | Semantic priority levels.
-- |
-- | - **Critical**: Must be processed immediately (user-blocking)
-- | - **High**: Should be processed soon (user-visible)
-- | - **Normal**: Standard priority (default)
-- | - **Low**: Can be delayed (not immediately needed)
-- | - **Background**: Process when idle (prefetching, preloading)
data Priority
  = Critical
  | High
  | Normal
  | Low
  | Background

derive instance eqPriority :: Eq Priority

instance showPriority :: Show Priority where
  show Critical = "Critical"
  show High = "High"
  show Normal = "Normal"
  show Low = "Low"
  show Background = "Background"

instance ordPriority :: Ord Priority where
  compare a b = compare (priorityToInt a) (priorityToInt b)

-- | Convert priority to numeric value for comparison.
-- |
-- | Higher number = higher priority.
priorityToInt :: Priority -> Int
priorityToInt Critical = 1000
priorityToInt High = 750
priorityToInt Normal = 500
priorityToInt Low = 250
priorityToInt Background = 0

-- | Convert numeric value to semantic priority.
-- |
-- | Maps to nearest semantic level.
intToPriority :: Int -> Priority
intToPriority n
  | n >= 875 = Critical
  | n >= 625 = High
  | n >= 375 = Normal
  | n >= 125 = Low
  | otherwise = Background

-- | Compare two priorities, returning an Ordering.
priorityOrd :: Priority -> Priority -> Ordering
priorityOrd = compare

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // numeric priority
-- ═════════════════════════════════════════════════════════════════════════════

-- | Fine-grained numeric priority [0, 1000].
-- |
-- | Use when semantic priorities are too coarse.
-- | 0 = lowest (Background), 1000 = highest (Critical)
newtype NumericPriority = NumericPriority Int

derive instance eqNumericPriority :: Eq NumericPriority
derive instance ordNumericPriority :: Ord NumericPriority

instance showNumericPriority :: Show NumericPriority where
  show (NumericPriority n) = "Priority(" <> show n <> ")"

-- | Create a numeric priority (clamped to [0, 1000])
numericPriority :: Int -> NumericPriority
numericPriority n = NumericPriority (Bounded.clampInt 0 1000 n)

-- | Create a numeric priority without clamping (use with care)
numericPriorityUnsafe :: Int -> NumericPriority
numericPriorityUnsafe = NumericPriority

-- | Unwrap numeric priority to Int
unwrapNumericPriority :: NumericPriority -> Int
unwrapNumericPriority (NumericPriority n) = n

-- | Bounds documentation for NumericPriority
numericPriorityBounds :: Bounded.IntBounds
numericPriorityBounds = Bounded.intBounds 0 1000 "NumericPriority" "Fine-grained priority level"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // prioritized wrapper
-- ═════════════════════════════════════════════════════════════════════════════

-- | A value with attached priority metadata.
-- |
-- | Priorities are metadata — they don't change the semantic meaning
-- | of the wrapped value, only how it's scheduled/processed.
type Prioritized a =
  { value :: a
  , priority :: Priority
  , numericPriority :: NumericPriority
  }

-- | Wrap a value with semantic priority.
prioritize :: forall a. Priority -> a -> Prioritized a
prioritize p val =
  { value: val
  , priority: p
  , numericPriority: numericPriority (priorityToInt p)
  }

-- | Wrap a value with numeric priority.
prioritizeNumeric :: forall a. NumericPriority -> a -> Prioritized a
prioritizeNumeric np val =
  { value: val
  , priority: intToPriority (unwrapNumericPriority np)
  , numericPriority: np
  }

-- | Get the semantic priority
getPriority :: forall a. Prioritized a -> Priority
getPriority p = p.priority

-- | Get the numeric priority
getNumericPriority :: forall a. Prioritized a -> NumericPriority
getNumericPriority p = p.numericPriority

-- | Get the wrapped value
getValue :: forall a. Prioritized a -> a
getValue p = p.value

-- | Set a new priority
setPriority :: forall a. Priority -> Prioritized a -> Prioritized a
setPriority newP p =
  { value: p.value
  , priority: newP
  , numericPriority: numericPriority (priorityToInt newP)
  }

-- | Map over the wrapped value, preserving priority
mapPrioritized :: forall a b. (a -> b) -> Prioritized a -> Prioritized b
mapPrioritized f p =
  { value: f p.value
  , priority: p.priority
  , numericPriority: p.numericPriority
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // priority queue
-- ═════════════════════════════════════════════════════════════════════════════

-- | A priority queue for ordered processing.
-- |
-- | Items are dequeued in priority order (highest first).
-- | Items with equal priority maintain insertion order (FIFO).
newtype PriorityQueue a = PriorityQueue (Array (Prioritized a))

derive instance eqPriorityQueue :: Eq a => Eq (PriorityQueue a)

instance showPriorityQueue :: Show a => Show (PriorityQueue a) where
  show (PriorityQueue arr) = "PriorityQueue[" <> show (Array.length arr) <> " items]"

-- | Empty priority queue
emptyQueue :: forall a. PriorityQueue a
emptyQueue = PriorityQueue []

-- | Add an item to the queue with priority
enqueue :: forall a. Prioritized a -> PriorityQueue a -> PriorityQueue a
enqueue item (PriorityQueue arr) =
  let
    newArr = Array.snoc arr item
    sorted = Array.sortBy comparePrioritized newArr
  in
    PriorityQueue sorted

-- | Compare prioritized items (higher priority first)
comparePrioritized :: forall a. Prioritized a -> Prioritized a -> Ordering
comparePrioritized a b =
  compare (unwrapNumericPriority b.numericPriority) (unwrapNumericPriority a.numericPriority)

-- | Remove and return the highest priority item
dequeue :: forall a. PriorityQueue a -> Maybe { item :: Prioritized a, queue :: PriorityQueue a }
dequeue (PriorityQueue arr) =
  case Array.uncons arr of
    Nothing -> Nothing
    Just { head: item, tail: rest } -> Just { item: item, queue: PriorityQueue rest }

-- | Look at the highest priority item without removing
peek :: forall a. PriorityQueue a -> Maybe (Prioritized a)
peek (PriorityQueue arr) = Array.head arr

-- | Get the number of items in the queue
queueSize :: forall a. PriorityQueue a -> Int
queueSize (PriorityQueue arr) = Array.length arr

-- | Convert queue to array (in priority order)
queueToArray :: forall a. PriorityQueue a -> Array (Prioritized a)
queueToArray (PriorityQueue arr) = arr

-- | Merge two queues (maintaining priority order)
mergeQueues :: forall a. PriorityQueue a -> PriorityQueue a -> PriorityQueue a
mergeQueues (PriorityQueue a) (PriorityQueue b) =
  let
    merged = Array.foldl (\acc item -> Array.snoc acc item) a b
    sorted = Array.sortBy comparePrioritized merged
  in
    PriorityQueue sorted

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // deadline priority
-- ═════════════════════════════════════════════════════════════════════════════

-- | Deadline urgency levels.
-- |
-- | Deadlines boost effective priority as they approach.
data Deadline
  = Immediate    -- Must be done now (100% boost)
  | Soon         -- Should be done soon (50% boost)
  | Eventually   -- No rush (no boost)
  | NoDeadline   -- No time constraint

derive instance eqDeadline :: Eq Deadline

instance showDeadline :: Show Deadline where
  show Immediate = "Immediate"
  show Soon = "Soon"
  show Eventually = "Eventually"
  show NoDeadline = "NoDeadline"

-- | Priority with deadline metadata.
type DeadlinedPriority =
  { basePriority :: Priority
  , deadline :: Deadline
  }

-- | Create a priority with deadline
withDeadline :: Priority -> Deadline -> DeadlinedPriority
withDeadline p d = { basePriority: p, deadline: d }

-- | Get the deadline boost factor (0.0 to 1.0)
deadlineBoost :: Deadline -> Number
deadlineBoost Immediate = 1.0
deadlineBoost Soon = 0.5
deadlineBoost Eventually = 0.0
deadlineBoost NoDeadline = 0.0

-- | Calculate effective priority considering deadline.
-- |
-- | Effective = Base + (1000 - Base) * BoostFactor
-- | This ensures Immediate deadlines approach Critical priority.
effectivePriority :: DeadlinedPriority -> NumericPriority
effectivePriority dp =
  let
    baseInt = priorityToInt dp.basePriority
    boost = deadlineBoost dp.deadline
    headroom = 1000 - baseInt
    boosted = baseInt + roundToInt (intToNumber headroom * boost)
  in
    numericPriority boosted

-- | Round a Number to Int (helper)
roundToInt :: Number -> Int
roundToInt n = 
  let truncated = truncateNumber n
  in if n - intToNumber truncated >= 0.5 then truncated + 1 else truncated

-- | Truncate a Number to Int (helper)
truncateNumber :: Number -> Int
truncateNumber n = 
  if n < 0.0 then negateInt (truncatePositive (negateNumber n))
  else truncatePositive n

-- | Truncate a positive number
truncatePositive :: Number -> Int
truncatePositive n =
  if n < 1.0 then 0
  else 1 + truncatePositive (n - 1.0)

-- | Negate an Int (helper)
negateInt :: Int -> Int
negateInt n = 0 - n

-- | Negate a Number (helper)
negateNumber :: Number -> Number
negateNumber n = 0.0 - n

-- | Convert Int to Number (helper)
intToNumber :: Int -> Number
intToNumber n = 
  if n == 0 then 0.0
  else if n > 0 then intToNumberPositive n 0.0
  else 0.0 - intToNumberPositive (negateInt n) 0.0

intToNumberPositive :: Int -> Number -> Number
intToNumberPositive n acc =
  if n <= 0 then acc
  else intToNumberPositive (n - 1) (acc + 1.0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // priority utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Return the higher of two priorities
higherPriority :: Priority -> Priority -> Priority
higherPriority a b =
  if priorityToInt a >= priorityToInt b then a else b

-- | Return the lower of two priorities
lowerPriority :: Priority -> Priority -> Priority
lowerPriority a b =
  if priorityToInt a <= priorityToInt b then a else b

-- | Get maximum priority from an array
maxPriority :: Array Priority -> Priority
maxPriority arr = 
  Array.foldl higherPriority Background arr

-- | Get minimum priority from an array
minPriority :: Array Priority -> Priority
minPriority arr =
  Array.foldl lowerPriority Critical arr

-- | Calculate average priority from an array
averagePriority :: Array Priority -> Priority
averagePriority arr =
  if Array.length arr == 0
    then Normal
    else
      let
        total = Array.foldl (\acc p -> acc + priorityToInt p) 0 arr
        avg = total / Array.length arr
      in
        intToPriority avg
