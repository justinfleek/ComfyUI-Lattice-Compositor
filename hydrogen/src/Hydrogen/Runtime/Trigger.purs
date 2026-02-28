-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                             // hydrogen // runtime // trigger
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Trigger Runtime — Condition Evaluation Engine
-- |
-- | Bridges Schema.Gestural.Trigger types to runtime evaluation. The Schema
-- | defines WHAT triggers are (conditions, effects, timing). This module
-- | defines HOW to evaluate them against live runtime state.
-- |
-- | ## Architecture
-- |
-- | ```
-- | TriggerDef (Schema)     RuntimeContext (Live State)
-- |      ↓                         ↓
-- |      └──────────┬──────────────┘
-- |                 ↓
-- |          evaluateCondition
-- |                 ↓
-- |           Array Int (met condition indices)
-- |                 ↓
-- |         checkConditions (update TriggerState)
-- |                 ↓
-- |          pendingEffects → Array TriggerEffect
-- | ```
-- |
-- | ## Dependencies
-- | - Hydrogen.Schema.Gestural.Trigger (TriggerCondition, TriggerDef, TriggerState)
-- |
-- | ## Dependents
-- | - Hydrogen.Runtime.App (calls evaluateTriggers)
-- | - DOM Runtime (provides RuntimeContext)

module Hydrogen.Runtime.Trigger
  ( -- * Runtime Context
    RuntimeContext
  , mkRuntimeContext
  
  -- * Element Bounds (for proximity/hover)
  , ElementBounds
  , mkElementBounds
  , boundsContainsPoint
  , distanceToCenter
  , boundsOverlap
  , compareBoundsByArea
  
  -- * Condition Evaluation
  , evaluateCondition
  , evaluateAllConditions
  , getMetConditionIndices
  , anyConditionMet
  , allConditionsMet
  
  -- * Sequence Tracking
  , SequenceState
  , initialSequenceState
  , recordKeyPress
  , checkSequenceMatch
  
  -- * Hover Tracking
  , HoverState
  , initialHoverState
  , updateHoverState
  , getHoverDuration
  , isCurrentlyHovering
  
  -- * Generic Utilities
  , elementsEqual
  , findFirstMatching
  , sortByOrd
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , Ordering(LT, GT, EQ)
  , compare
  , not
  , otherwise
  , ($)
  , (&&)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (<=)
  , (==)
  , (>)
  , (>=)
  , (||)
  , (<>)
  )

import Data.Array (filter, length, snoc, take, drop, elem) as Array
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Gestural.Trigger
  ( TriggerCondition
      ( HoverFor
      , HoverWhile
      , ClickCount
      , KeyPattern
      , GesturePattern
      , ProximityEnter
      , ProximityExit
      , HoldFor
      , ScrollTo
      , IdleFor
      , VisitCount
      , TimeWindow
      , CustomCondition
      )
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // runtime context
-- ═════════════════════════════════════════════════════════════════════════════

-- | Runtime context for trigger evaluation
-- |
-- | Contains all live state needed to evaluate trigger conditions.
-- | Provided by the DOM runtime each frame.
type RuntimeContext =
  { mousePos :: { x :: Number, y :: Number }
  , activeKeys :: Array String
  , timestamp :: Number
  , scrollPosition :: Number
  , idleTime :: Number
  , visitCount :: Int
  , currentTime :: String
  , elementBounds :: Array { id :: String, bounds :: ElementBounds }
  , hoverState :: HoverState
  , sequenceState :: SequenceState
  , clickCounts :: Array { elementId :: String, count :: Int, lastClick :: Number }
  }

-- | Create a runtime context with default values
mkRuntimeContext :: RuntimeContext
mkRuntimeContext =
  { mousePos: { x: 0.0, y: 0.0 }
  , activeKeys: []
  , timestamp: 0.0
  , scrollPosition: 0.0
  , idleTime: 0.0
  , visitCount: 1
  , currentTime: "00:00"
  , elementBounds: []
  , hoverState: initialHoverState
  , sequenceState: initialSequenceState
  , clickCounts: []
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // element bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounding rectangle for an element
type ElementBounds =
  { x :: Number
  , y :: Number
  , width :: Number
  , height :: Number
  }

-- | Create element bounds
mkElementBounds :: Number -> Number -> Number -> Number -> ElementBounds
mkElementBounds x y width height = { x, y, width, height }

-- | Check if a point is inside bounds
boundsContainsPoint :: ElementBounds -> { x :: Number, y :: Number } -> Boolean
boundsContainsPoint bounds point =
  point.x >= bounds.x &&
  point.x <= bounds.x + bounds.width &&
  point.y >= bounds.y &&
  point.y <= bounds.y + bounds.height

-- | Calculate distance from point to center of bounds
distanceToCenter :: ElementBounds -> { x :: Number, y :: Number } -> Number
distanceToCenter bounds point =
  let
    centerX = bounds.x + bounds.width / 2.0
    centerY = bounds.y + bounds.height / 2.0
    dx = point.x - centerX
    dy = point.y - centerY
  in
    sqrt (dx * dx + dy * dy)

-- | Check if two bounds rectangles overlap
-- | Used for hit testing, collision detection between UI elements
boundsOverlap :: ElementBounds -> ElementBounds -> Boolean
boundsOverlap a b =
  not (a.x + a.width < b.x || b.x + b.width < a.x ||
       a.y + a.height < b.y || b.y + b.height < a.y)

-- | Compare two bounds by area (for z-ordering, priority)
-- | Smaller elements typically have higher interaction priority
compareBoundsByArea :: ElementBounds -> ElementBounds -> Ordering
compareBoundsByArea a b =
  let
    areaA = a.width * a.height
    areaB = b.width * b.height
  in
    compare areaA areaB

-- | Square root via Newton's method
sqrt :: Number -> Number
sqrt n
  | n <= 0.0 = 0.0
  | otherwise = sqrtIter n (n / 2.0) 20

sqrtIter :: Number -> Number -> Int -> Number
sqrtIter _ guess 0 = guess
sqrtIter n guess i =
  let newGuess = (guess + n / guess) / 2.0
  in sqrtIter n newGuess (i - 1)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // condition evaluation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Evaluate a single trigger condition against runtime context
evaluateCondition :: RuntimeContext -> TriggerCondition -> Boolean
evaluateCondition ctx condition = case condition of
  HoverFor duration elementId ->
    case getHoverDuration ctx.timestamp ctx.hoverState elementId of
      Nothing -> false
      Just d -> d >= duration
  
  HoverWhile elementId _ ->
    isHoveringOver ctx elementId
  
  ClickCount requiredClicks elementId ->
    getClickCount ctx elementId >= requiredClicks
  
  KeyPattern keys ->
    checkSequenceMatch ctx.sequenceState keys
  
  GesturePattern _ ->
    false  -- Requires gesture recognizer
  
  ProximityEnter radius elementId ->
    case findElementBounds ctx elementId of
      Nothing -> false
      Just bounds -> distanceToCenter bounds ctx.mousePos <= radius
  
  ProximityExit radius elementId ->
    case findElementBounds ctx elementId of
      Nothing -> true
      Just bounds -> distanceToCenter bounds ctx.mousePos > radius
  
  HoldFor duration elementId ->
    case getHoverDuration ctx.timestamp ctx.hoverState elementId of
      Nothing -> false
      Just d -> d >= duration
  
  ScrollTo position ->
    ctx.scrollPosition >= position
  
  IdleFor duration ->
    ctx.idleTime >= duration
  
  VisitCount count ->
    ctx.visitCount >= count
  
  TimeWindow startTime endTime ->
    ctx.currentTime >= startTime && ctx.currentTime <= endTime
  
  CustomCondition _ ->
    false  -- App-specific

-- | Evaluate all conditions
evaluateAllConditions :: RuntimeContext -> Array TriggerCondition -> Array Boolean
evaluateAllConditions ctx conditions =
  mapArray (evaluateCondition ctx) conditions

-- | Get indices of met conditions
getMetConditionIndices :: RuntimeContext -> Array TriggerCondition -> Array Int
getMetConditionIndices ctx conditions =
  indexedFilter (\_ c -> evaluateCondition ctx c) conditions

-- | Check if ANY condition is met (OR semantics)
-- | Useful for triggers that should fire when any of multiple conditions occur
anyConditionMet :: RuntimeContext -> Array TriggerCondition -> Boolean
anyConditionMet ctx conditions =
  Array.length (Array.filter (\c -> evaluateCondition ctx c) conditions) > 0

-- | Check if ALL conditions are met (AND semantics)
-- | Standard trigger behavior - all conditions must be satisfied
allConditionsMet :: RuntimeContext -> Array TriggerCondition -> Boolean
allConditionsMet ctx conditions =
  case conditions of
    [] -> true  -- Empty conditions = always met
    _  -> Array.length (getMetConditionIndices ctx conditions) == Array.length conditions

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // sequence tracking
-- ═════════════════════════════════════════════════════════════════════════════

-- | State for tracking key sequences (e.g., Konami code)
type SequenceState =
  { recentKeys :: Array String
  , maxLength :: Int
  , lastKeyTime :: Number
  , timeoutMs :: Number
  }

-- | Initial sequence state
initialSequenceState :: SequenceState
initialSequenceState =
  { recentKeys: []
  , maxLength: 20
  , lastKeyTime: 0.0
  , timeoutMs: 2000.0
  }

-- | Record a key press
recordKeyPress :: String -> Number -> SequenceState -> SequenceState
recordKeyPress key timestamp state =
  let
    shouldReset = timestamp - state.lastKeyTime > state.timeoutMs
    currentKeys = if shouldReset then [] else state.recentKeys
    newKeys = Array.take state.maxLength (Array.snoc currentKeys key)
  in
    state { recentKeys = newKeys, lastKeyTime = timestamp }

-- | Check if recent keys match pattern
checkSequenceMatch :: SequenceState -> Array String -> Boolean
checkSequenceMatch state pattern =
  let
    patternLen = Array.length pattern
    recentLen = Array.length state.recentKeys
  in
    if patternLen > recentLen
      then false
      else Array.drop (recentLen - patternLen) state.recentKeys == pattern

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // hover tracking
-- ═════════════════════════════════════════════════════════════════════════════

-- | State for tracking hover duration
type HoverState =
  { hoveredElements :: Array { elementId :: String, startTime :: Number }
  }

-- | Initial hover state
initialHoverState :: HoverState
initialHoverState = { hoveredElements: [] }

-- | Update hover state based on mouse position
updateHoverState 
  :: Number
  -> { x :: Number, y :: Number }
  -> Array { id :: String, bounds :: ElementBounds }
  -> HoverState
  -> HoverState
updateHoverState timestamp mousePos elements state =
  let
    currentlyHovered = elements
      # Array.filter (\e -> boundsContainsPoint e.bounds mousePos)
      # mapArray (\e -> e.id)
    
    stillHovered = state.hoveredElements
      # Array.filter (\h -> Array.elem h.elementId currentlyHovered)
    
    existingIds = mapArray (\h -> h.elementId) stillHovered
    newHovers = currentlyHovered
      # Array.filter (\id -> not (Array.elem id existingIds))
      # mapArray (\id -> { elementId: id, startTime: timestamp })
  in
    state { hoveredElements = stillHovered <> newHovers }

-- | Get hover duration for an element
-- | Returns the duration in milliseconds since hover started
getHoverDuration :: Number -> HoverState -> String -> Maybe Number
getHoverDuration currentTimestamp state elementId =
  case Array.filter (\h -> h.elementId == elementId) state.hoveredElements of
    [h] -> Just (currentTimestamp - h.startTime)
    _ -> Nothing

-- | Check if an element is currently being hovered
-- | Simpler check than duration - just presence in hover list
isCurrentlyHovering :: HoverState -> String -> Boolean
isCurrentlyHovering state elementId =
  Array.length (Array.filter (\h -> h.elementId == elementId) state.hoveredElements) > 0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if hovering over element
isHoveringOver :: RuntimeContext -> String -> Boolean
isHoveringOver ctx elementId =
  case findElementBounds ctx elementId of
    Nothing -> false
    Just bounds -> boundsContainsPoint bounds ctx.mousePos

-- | Find element bounds by ID
findElementBounds :: RuntimeContext -> String -> Maybe ElementBounds
findElementBounds ctx elementId =
  case Array.filter (\e -> e.id == elementId) ctx.elementBounds of
    [e] -> Just e.bounds
    _ -> Nothing

-- | Get click count for element
getClickCount :: RuntimeContext -> String -> Int
getClickCount ctx elementId =
  case Array.filter (\c -> c.elementId == elementId) ctx.clickCounts of
    [c] -> c.count
    _ -> 0

-- | Map over array (using Data.Functor.map)
mapArray :: forall a b. (a -> b) -> Array a -> Array b
mapArray = mapImpl

-- | Pure map implementation via fold
mapImpl :: forall a b. (a -> b) -> Array a -> Array b
mapImpl f = foldlArray (\acc x -> acc <> [f x]) []

-- | Filter with index, returning indices where predicate holds
indexedFilter :: forall a. (Int -> a -> Boolean) -> Array a -> Array Int
indexedFilter pred arr = go 0 arr []
  where
    go :: Int -> Array a -> Array Int -> Array Int
    go _ [] acc = acc
    go i xs acc = case Array.take 1 xs of
      [] -> acc
      [x] -> 
        let rest = Array.drop 1 xs
            newAcc = if pred i x then acc <> [i] else acc
        in go (i + 1) rest newAcc
      _ -> acc

-- | Fold left over array
foldlArray :: forall a b. (b -> a -> b) -> b -> Array a -> b
foldlArray f init arr = case Array.take 1 arr of
  [] -> init
  [x] -> foldlArray f (f init x) (Array.drop 1 arr)
  _ -> init

-- | Pipe operator
infixl 1 applyFlipped as #

applyFlipped :: forall a b. a -> (a -> b) -> b
applyFlipped x f = f x

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // generic utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if two arrays contain the same elements (order-sensitive)
-- | Generic over any Eq type
elementsEqual :: forall a. Eq a => Array a -> Array a -> Boolean
elementsEqual xs ys =
  Array.length xs == Array.length ys && go xs ys
  where
    go :: Array a -> Array a -> Boolean
    go [] [] = true
    go as bs = case Array.take 1 as of
      [] -> Array.length bs == 0
      [a] -> case Array.take 1 bs of
        [] -> false
        [b] -> a == b && go (Array.drop 1 as) (Array.drop 1 bs)
        _ -> false
      _ -> false

-- | Find first element matching predicate
-- | Uses $ for standard function application pattern
findFirstMatching :: forall a. (a -> Boolean) -> Array a -> Maybe a
findFirstMatching pred arr =
  let filtered = Array.filter pred $ arr
  in case Array.take 1 filtered of
    [x] -> Just x
    _ -> Nothing

-- | Simple insertion sort for small arrays using Ord
-- | For trigger priority ordering, element z-ordering
sortByOrd :: forall a. Ord a => (a -> a -> Ordering) -> Array a -> Array a
sortByOrd cmp arr = foldlArray insert [] arr
  where
    insert :: Array a -> a -> Array a
    insert [] x = [x]
    insert sorted x = 
      let 
        smaller = Array.filter (\y -> cmp y x == LT || cmp y x == EQ) sorted
        larger = Array.filter (\y -> cmp y x == GT) sorted
      in 
        smaller <> [x] <> larger

