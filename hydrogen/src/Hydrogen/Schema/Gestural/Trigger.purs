-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // gestural // trigger
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Trigger - interactive relationships and easter eggs.
-- |
-- | Models triggers that define relationships between input events
-- | and effects. Enables hover-to-reveal, proximity effects, secret
-- | sequences (Konami code), and delightful easter eggs.
-- |
-- | ## Design Philosophy
-- | A trigger is a first-class relationship: "when X happens to A,
-- | do Y to B". This makes progressive disclosure and delight
-- | composable primitives rather than ad-hoc implementations.
-- |
-- | ## Dependencies
-- | - Prelude (Eq, Ord, Show)
-- | - Data.Array (all, any, snoc, filter)
-- | - Data.Maybe (Maybe)
-- |
-- | ## Dependents
-- | - Component.* (interactive effects)
-- | - Interaction.* (delightful interactions)

module Hydrogen.Schema.Gestural.Trigger
  ( -- * Trigger Condition
    TriggerCondition
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
  , isHoverCondition
  , isProximityCondition
  , isTimeCondition
    -- * Trigger Effect
  , TriggerEffect
      ( Reveal
      , Hide
      , Morph
      , Animate
      , Navigate
      , PlaySound
      , TriggerHaptic
      , ShowToast
      , Confetti
      , Unlock
      , Achievement
      , CustomEffect
      )
  , isVisualEffect
  , isNavigationEffect
  , isFeedbackEffect
    -- * Trigger Target
  , TriggerTarget(TargetSelf, TargetElement, TargetGroup, TargetGlobal)
  , isSelfTarget
  , targetElementId
    -- * Trigger Timing
  , TriggerTiming
  , triggerTiming
  , timingDelay
  , timingDuration
  , timingCooldown
  , timingRepeat
  , immediatelyTiming
  , delayedTiming
    -- * Trigger Definition
  , TriggerDef
  , triggerDef
  , triggerId
  , triggerSource
  , triggerConditions
  , triggerTarget
  , triggerEffect
  , triggerDefTiming
  , triggerEnabled
    -- * Proximity Config
  , ProximityConfig
  , proximityConfig
  , proximityRadius
  , proximityFalloff
  , proximityStrength
    -- * Hover Trigger Builder
  , HoverTrigger
  , hoverReveal
  , hoverMorph
  , hoverChain
  , hoverDelay
    -- * Sequence Trigger (Easter Eggs)
  , SequenceTrigger
  , konamiCode
  , secretSequence
  , secretTaps
  , cornerGesture
    -- * Tracked Trigger
  , TrackedTrigger
    -- * Trigger State
  , TriggerState
  , initialTriggerState
  , registerTrigger
  , unregisterTrigger
  , activateTrigger
  , deactivateTrigger
  , isTriggerActive
  , checkConditions
  , pendingEffects
  , completedTriggers
  , resetTriggers
    -- * Condition Checking
  , allConditionsMet
  , isConditionMet
  , conditionIndices
  , hasValidTiming
  ) where

import Prelude

import Data.Array (all, any, elem, filter, length, notElem, snoc, (..))
import Data.Maybe (Maybe(Just, Nothing), isJust)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // trigger // condition
-- ═════════════════════════════════════════════════════════════════════════════

-- | Conditions that can trigger effects
data TriggerCondition
  = HoverFor Number String           -- ^ Hover over element for duration (ms)
  | HoverWhile String Boolean        -- ^ Hover while modifier key pressed
  | ClickCount Int String            -- ^ N rapid clicks on element
  | KeyPattern (Array String)        -- ^ Key sequence (e.g., Konami)
  | GesturePattern String            -- ^ Named gesture pattern
  | ProximityEnter Number String     -- ^ Cursor within radius of element
  | ProximityExit Number String      -- ^ Cursor leaves radius
  | HoldFor Number String            -- ^ Hold/press for duration
  | ScrollTo Number                  -- ^ Scroll to percentage (0-1)
  | IdleFor Number                   -- ^ User idle for duration
  | VisitCount Int                   -- ^ After N page visits
  | TimeWindow String String         -- ^ Between start and end time
  | CustomCondition String           -- ^ Custom condition by name

derive instance eqTriggerCondition :: Eq TriggerCondition

instance showTriggerCondition :: Show TriggerCondition where
  show (HoverFor ms elem) = "HoverFor(" <> show ms <> "," <> elem <> ")"
  show (HoverWhile elem _) = "HoverWhile(" <> elem <> ")"
  show (ClickCount n elem) = "ClickCount(" <> show n <> "," <> elem <> ")"
  show (KeyPattern keys) = "KeyPattern(" <> show (length keys) <> " keys)"
  show (GesturePattern name) = "GesturePattern(" <> name <> ")"
  show (ProximityEnter r elem) = "ProximityEnter(" <> show r <> "," <> elem <> ")"
  show (ProximityExit r elem) = "ProximityExit(" <> show r <> "," <> elem <> ")"
  show (HoldFor ms elem) = "HoldFor(" <> show ms <> "," <> elem <> ")"
  show (ScrollTo pct) = "ScrollTo(" <> show pct <> ")"
  show (IdleFor ms) = "IdleFor(" <> show ms <> ")"
  show (VisitCount n) = "VisitCount(" <> show n <> ")"
  show (TimeWindow start end) = "TimeWindow(" <> start <> "-" <> end <> ")"
  show (CustomCondition name) = "CustomCondition(" <> name <> ")"

-- | Is hover-based condition?
isHoverCondition :: TriggerCondition -> Boolean
isHoverCondition (HoverFor _ _) = true
isHoverCondition (HoverWhile _ _) = true
isHoverCondition _ = false

-- | Is proximity-based condition?
isProximityCondition :: TriggerCondition -> Boolean
isProximityCondition (ProximityEnter _ _) = true
isProximityCondition (ProximityExit _ _) = true
isProximityCondition _ = false

-- | Is time-based condition?
isTimeCondition :: TriggerCondition -> Boolean
isTimeCondition (HoverFor _ _) = true
isTimeCondition (HoldFor _ _) = true
isTimeCondition (IdleFor _) = true
isTimeCondition (TimeWindow _ _) = true
isTimeCondition _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // trigger // effect
-- ═════════════════════════════════════════════════════════════════════════════

-- | Effects that can be triggered
data TriggerEffect
  = Reveal String                    -- ^ Show element
  | Hide String                      -- ^ Hide element
  | Morph String String              -- ^ Transform from state A to B
  | Animate String String            -- ^ Play animation on element
  | Navigate String                  -- ^ Navigate to URL/route
  | PlaySound String                 -- ^ Play audio file
  | TriggerHaptic String             -- ^ Haptic feedback pattern
  | ShowToast String String          -- ^ Show toast (type, message)
  | Confetti                         -- ^ Visual celebration
  | Unlock String                    -- ^ Unlock feature by name
  | Achievement String String        -- ^ Award achievement (id, name)
  | CustomEffect String              -- ^ Custom effect by name

derive instance eqTriggerEffect :: Eq TriggerEffect

instance showTriggerEffect :: Show TriggerEffect where
  show (Reveal elem) = "Reveal(" <> elem <> ")"
  show (Hide elem) = "Hide(" <> elem <> ")"
  show (Morph elem state) = "Morph(" <> elem <> "," <> state <> ")"
  show (Animate elem anim) = "Animate(" <> elem <> "," <> anim <> ")"
  show (Navigate url) = "Navigate(" <> url <> ")"
  show (PlaySound sound) = "PlaySound(" <> sound <> ")"
  show (TriggerHaptic pattern) = "TriggerHaptic(" <> pattern <> ")"
  show (ShowToast t msg) = "ShowToast(" <> t <> "," <> msg <> ")"
  show Confetti = "Confetti"
  show (Unlock feature) = "Unlock(" <> feature <> ")"
  show (Achievement id name) = "Achievement(" <> id <> "," <> name <> ")"
  show (CustomEffect name) = "CustomEffect(" <> name <> ")"

-- | Is visual effect?
isVisualEffect :: TriggerEffect -> Boolean
isVisualEffect (Reveal _) = true
isVisualEffect (Hide _) = true
isVisualEffect (Morph _ _) = true
isVisualEffect (Animate _ _) = true
isVisualEffect Confetti = true
isVisualEffect _ = false

-- | Is navigation effect?
isNavigationEffect :: TriggerEffect -> Boolean
isNavigationEffect (Navigate _) = true
isNavigationEffect _ = false

-- | Is feedback effect?
isFeedbackEffect :: TriggerEffect -> Boolean
isFeedbackEffect (PlaySound _) = true
isFeedbackEffect (TriggerHaptic _) = true
isFeedbackEffect (ShowToast _ _) = true
isFeedbackEffect _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // trigger // target
-- ═════════════════════════════════════════════════════════════════════════════

-- | Target of trigger effect
data TriggerTarget
  = TargetSelf                       -- ^ Same element as source
  | TargetElement String             -- ^ Specific element by ID
  | TargetGroup String               -- ^ Group of elements
  | TargetGlobal                     -- ^ Global/page-level effect

derive instance eqTriggerTarget :: Eq TriggerTarget

instance showTriggerTarget :: Show TriggerTarget where
  show TargetSelf = "self"
  show (TargetElement id) = "element(" <> id <> ")"
  show (TargetGroup id) = "group(" <> id <> ")"
  show TargetGlobal = "global"

-- | Is self target?
isSelfTarget :: TriggerTarget -> Boolean
isSelfTarget TargetSelf = true
isSelfTarget _ = false

-- | Get target element ID if applicable
targetElementId :: TriggerTarget -> Maybe String
targetElementId (TargetElement id) = Just id
targetElementId _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // trigger // timing
-- ═════════════════════════════════════════════════════════════════════════════

-- | Timing configuration for trigger
type TriggerTiming =
  { delay :: Number          -- ^ Delay before effect (ms)
  , duration :: Number       -- ^ Effect duration (ms, 0 = instant)
  , cooldown :: Number       -- ^ Cooldown before re-trigger (ms)
  , repeat :: Boolean        -- ^ Can trigger multiple times
  }

-- | Create trigger timing
triggerTiming :: Number -> Number -> Number -> Boolean -> TriggerTiming
triggerTiming delay duration cooldown repeat =
  { delay, duration, cooldown, repeat }

-- | Get timing delay
timingDelay :: TriggerTiming -> Number
timingDelay tt = tt.delay

-- | Get timing duration
timingDuration :: TriggerTiming -> Number
timingDuration tt = tt.duration

-- | Get timing cooldown
timingCooldown :: TriggerTiming -> Number
timingCooldown tt = tt.cooldown

-- | Get timing repeat
timingRepeat :: TriggerTiming -> Boolean
timingRepeat tt = tt.repeat

-- | Immediate timing (no delay, instant, repeatable)
immediatelyTiming :: TriggerTiming
immediatelyTiming = { delay: 0.0, duration: 0.0, cooldown: 0.0, repeat: true }

-- | Delayed timing
delayedTiming :: Number -> TriggerTiming
delayedTiming delay = { delay, duration: 0.0, cooldown: 0.0, repeat: true }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // trigger // definition
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete trigger definition
type TriggerDef =
  { id :: String                        -- ^ Unique identifier
  , source :: String                    -- ^ Source element ID
  , conditions :: Array TriggerCondition  -- ^ All must be true
  , target :: TriggerTarget             -- ^ Effect target
  , effect :: TriggerEffect             -- ^ Effect to apply
  , timing :: TriggerTiming             -- ^ Timing config
  , enabled :: Boolean                  -- ^ Is trigger enabled
  }

-- | Create trigger definition
triggerDef :: String -> String -> Array TriggerCondition -> TriggerTarget -> TriggerEffect -> TriggerTiming -> TriggerDef
triggerDef id source conditions target effect timing =
  { id, source, conditions, target, effect, timing, enabled: true }

-- | Get trigger ID
triggerId :: TriggerDef -> String
triggerId td = td.id

-- | Get trigger source
triggerSource :: TriggerDef -> String
triggerSource td = td.source

-- | Get trigger conditions
triggerConditions :: TriggerDef -> Array TriggerCondition
triggerConditions td = td.conditions

-- | Get trigger target
triggerTarget :: TriggerDef -> TriggerTarget
triggerTarget td = td.target

-- | Get trigger effect
triggerEffect :: TriggerDef -> TriggerEffect
triggerEffect td = td.effect

-- | Get trigger timing (note: shadows module fn, need qualified use)
triggerDefTiming :: TriggerDef -> TriggerTiming
triggerDefTiming td = td.timing

-- | Is trigger enabled?
triggerEnabled :: TriggerDef -> Boolean
triggerEnabled td = td.enabled

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // proximity // config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for proximity effects
type ProximityConfig =
  { radius :: Number         -- ^ Activation radius (px)
  , falloff :: Number        -- ^ Falloff distance (px)
  , strength :: Number       -- ^ Effect strength at center (0-1)
  }

-- | Create proximity config
proximityConfig :: Number -> Number -> Number -> ProximityConfig
proximityConfig radius falloff strength = { radius, falloff, strength }

-- | Get proximity radius
proximityRadius :: ProximityConfig -> Number
proximityRadius pc = pc.radius

-- | Get proximity falloff
proximityFalloff :: ProximityConfig -> Number
proximityFalloff pc = pc.falloff

-- | Get proximity strength
proximityStrength :: ProximityConfig -> Number
proximityStrength pc = pc.strength

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // hover // trigger builder
-- ═════════════════════════════════════════════════════════════════════════════

-- | Hover trigger configuration
type HoverTrigger =
  { sourceId :: String       -- ^ Element to hover
  , targetId :: String       -- ^ Element to affect
  , effect :: TriggerEffect  -- ^ Effect to apply
  , delay :: Number          -- ^ Hover delay (ms)
  }

-- | Create hover-to-reveal trigger
hoverReveal :: String -> String -> Number -> HoverTrigger
hoverReveal sourceId targetId delay =
  { sourceId, targetId, effect: Reveal targetId, delay }

-- | Create hover-to-morph trigger
hoverMorph :: String -> String -> String -> Number -> HoverTrigger
hoverMorph sourceId targetId morphState delay =
  { sourceId, targetId, effect: Morph targetId morphState, delay }

-- | Create chained hover trigger
hoverChain :: String -> String -> TriggerEffect -> Number -> HoverTrigger
hoverChain sourceId targetId effect delay =
  { sourceId, targetId, effect, delay }

-- | Get hover delay
hoverDelay :: HoverTrigger -> Number
hoverDelay ht = ht.delay

-- ═════════════════════════════════════════════════════════════════════════════
--                                               // sequence // trigger (easter)
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sequence trigger for easter eggs
type SequenceTrigger =
  { id :: String                 -- ^ Trigger identifier
  , sequence :: Array String     -- ^ Key/gesture sequence
  , effect :: TriggerEffect      -- ^ Effect when triggered
  , timeout :: Number            -- ^ Sequence timeout (ms)
  }

-- | Classic Konami code trigger
konamiCode :: TriggerEffect -> SequenceTrigger
konamiCode effect =
  { id: "konami"
  , sequence: ["ArrowUp", "ArrowUp", "ArrowDown", "ArrowDown", "ArrowLeft", "ArrowRight", "ArrowLeft", "ArrowRight", "KeyB", "KeyA"]
  , effect
  , timeout: 2000.0
  }

-- | Create custom secret sequence
secretSequence :: String -> Array String -> TriggerEffect -> Number -> SequenceTrigger
secretSequence id sequence effect timeout =
  { id, sequence, effect, timeout }

-- | Secret tap pattern (N taps on element)
secretTaps :: String -> Int -> String -> TriggerEffect -> SequenceTrigger
secretTaps id count elementId effect =
  { id
  , sequence: map (\_ -> "tap:" <> elementId) (1 .. count)
  , effect
  , timeout: 3000.0
  }

-- | Corner gesture trigger
cornerGesture :: String -> String -> TriggerEffect -> SequenceTrigger
cornerGesture id corner effect =
  { id
  , sequence: ["swipe-from-" <> corner]
  , effect
  , timeout: 1000.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // trigger // state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Tracked trigger state
type TrackedTrigger =
  { def :: TriggerDef            -- ^ Trigger definition
  , active :: Boolean            -- ^ Is currently active
  , lastTriggered :: Number      -- ^ Last trigger timestamp
  , conditionsMet :: Array Int   -- ^ Indices of met conditions
  }

-- | Complete trigger state
type TriggerState =
  { triggers :: Array TrackedTrigger    -- ^ All registered triggers
  , activeEffects :: Array TriggerEffect  -- ^ Currently active effects
  , completed :: Array String           -- ^ Completed trigger IDs
  , timestamp :: Number                 -- ^ Last update
  }

-- | Initial trigger state
initialTriggerState :: TriggerState
initialTriggerState =
  { triggers: []
  , activeEffects: []
  , completed: []
  , timestamp: 0.0
  }

-- | Register a trigger
registerTrigger :: TriggerDef -> TriggerState -> TriggerState
registerTrigger def ts =
  let
    tracked = { def, active: false, lastTriggered: 0.0, conditionsMet: [] }
  in ts { triggers = snoc ts.triggers tracked }

-- | Unregister trigger by ID
unregisterTrigger :: String -> TriggerState -> TriggerState
unregisterTrigger trgId ts =
  ts { triggers = filter (\t -> t.def.id /= trgId) ts.triggers }

-- | Activate a trigger
activateTrigger :: String -> Number -> TriggerState -> TriggerState
activateTrigger trgId time ts =
  ts { triggers = map activate ts.triggers
     , activeEffects = snoc ts.activeEffects (findEffect trgId ts.triggers)
     , timestamp = time
     }
  where
    activate :: TrackedTrigger -> TrackedTrigger
    activate t =
      if t.def.id == trgId
        then t { active = true, lastTriggered = time }
        else t
    
    findEffect :: String -> Array TrackedTrigger -> TriggerEffect
    findEffect id trigs =
      case filter (\tr -> tr.def.id == id) trigs of
        [tr] -> tr.def.effect
        _ -> CustomEffect "unknown"

-- | Deactivate a trigger
deactivateTrigger :: String -> Number -> TriggerState -> TriggerState
deactivateTrigger trgId time ts =
  ts { triggers = map deactivate ts.triggers
     , completed = snoc ts.completed trgId
     , timestamp = time
     }
  where
    deactivate :: TrackedTrigger -> TrackedTrigger
    deactivate t =
      if t.def.id == trgId
        then t { active = false }
        else t

-- | Is trigger currently active?
isTriggerActive :: String -> TriggerState -> Boolean
isTriggerActive trgId ts =
  any (\t -> t.def.id == trgId && t.active) ts.triggers

-- | Check if conditions are met for trigger
checkConditions :: String -> Array Int -> TriggerState -> TriggerState
checkConditions trgId metIndices ts =
  ts { triggers = map update ts.triggers }
  where
    update :: TrackedTrigger -> TrackedTrigger
    update t =
      if t.def.id == trgId
        then t { conditionsMet = metIndices }
        else t

-- | Get pending effects (conditions met but not yet executed)
pendingEffects :: TriggerState -> Array TriggerEffect
pendingEffects ts =
  map (\t -> t.def.effect) $ filter isReady ts.triggers
  where
    isReady :: TrackedTrigger -> Boolean
    isReady t =
      t.def.enabled
      && not t.active
      && allConditionsMet t
      && hasValidTiming t.def
      && notElem t.def.id ts.completed

-- | Get completed trigger IDs
completedTriggers :: TriggerState -> Array String
completedTriggers ts = ts.completed

-- | Reset all triggers
resetTriggers :: TriggerState -> TriggerState
resetTriggers ts =
  ts { triggers = map reset ts.triggers
     , activeEffects = []
     , completed = []
     }
  where
    reset :: TrackedTrigger -> TrackedTrigger
    reset t = t { active = false, conditionsMet = [] }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // condition // checking
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if ALL conditions are met for a trigger
-- |
-- | Verifies that every condition index in the trigger's conditions
-- | has been marked as met. This is stronger than length comparison
-- | because it ensures the correct indices are satisfied.
allConditionsMet :: TrackedTrigger -> Boolean
allConditionsMet t =
  let indices = conditionIndices t.def
  in all (\i -> elem i t.conditionsMet) indices

-- | Check if a specific condition index is met
isConditionMet :: Int -> TrackedTrigger -> Boolean
isConditionMet idx t = elem idx t.conditionsMet

-- | Get all valid condition indices for a trigger definition
-- |
-- | Returns indices 0 to (n-1) where n is the number of conditions.
conditionIndices :: TriggerDef -> Array Int
conditionIndices td =
  if length td.conditions == 0
    then []
    else 0 .. (length td.conditions - 1)

-- | Check if trigger has valid timing configuration
-- |
-- | Valid timing means delay and duration are non-negative,
-- | cooldown is non-negative (0 means no cooldown).
hasValidTiming :: TriggerDef -> Boolean
hasValidTiming td =
  isJust (Just td.timing)  -- timing record exists
  && td.timing.delay >= 0.0
  && td.timing.duration >= 0.0
  && td.timing.cooldown >= 0.0
