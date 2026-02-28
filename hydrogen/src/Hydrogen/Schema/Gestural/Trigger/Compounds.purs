-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // trigger // compounds
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Trigger Compounds - complex trigger patterns for interactions and easter eggs.
-- |
-- | This module provides proximity-based triggers, device motion triggers,
-- | and easter egg patterns. These are the compound types that compose
-- | atoms and molecules into complete interaction patterns.
-- |
-- | ## SCHEMA.md Reference (Compounds)
-- | ```
-- | | ProximityGlow   | Cursor approaching causes glow           |
-- | | ProximityExpand | Cursor approaching expands element       |
-- | | ProximityAttract| Element subtly moves toward cursor       |
-- | | HoldToReveal    | Long-press reveals hidden content        |
-- | | ShakeToUndo     | Device shake triggers undo               |
-- | | TiltToScroll    | Device tilt affects scroll               |
-- | | EasterEgg       | Arbitrary hidden trigger + reward        |
-- | ```
-- |
-- | ## Dependencies
-- | - Prelude (Eq, Show, min, max)
-- | - Data.Maybe (Maybe)
-- | - Trigger.Atoms (ProximityRadius, TriggerDelay, etc.)
-- |
-- | ## Dependents
-- | - Component.* (uses these trigger patterns)
-- | - Interaction.* (delightful interactions)

module Hydrogen.Schema.Gestural.Trigger.Compounds
  ( -- * Proximity Triggers (Molecules)
    ProximityTrigger
  , proximityTrigger
  , proximityElement
  , proximityRadiusValue
  , proximityFalloffValue
  , proximityTargetId
    -- * Gesture Trigger (Molecule)
  , GestureTrigger
  , gestureTrigger
  , gesturePattern
  , gestureTargetId
  , gestureWindowMs
    -- * Time Trigger (Molecule)
  , TimeTrigger
  , timeTrigger
  , timeDuration
  , timeElementId
    -- * Combo Trigger (Molecule)
  , ComboTrigger
  , comboTrigger
  , comboConditions
  , comboWindowMs
    -- * Tap Count Trigger (Molecule)
  , TapCountTrigger
  , tapCountTrigger
  , tapElement
  , tapCount
  , tapWindowMs
    -- * ProximityGlow Compound
  , ProximityGlow
  , proximityGlow
  , glowElement
  , glowRadius
  , glowColor
  , glowIntensity
    -- * ProximityExpand Compound
  , ProximityExpand
  , proximityExpand
  , expandElement
  , expandRadius
  , expandScale
    -- * ProximityAttract Compound
  , ProximityAttract
  , proximityAttract
  , attractElement
  , attractRadius
  , attractStrength
  , AttractConstraint(AttractFree, AttractHorizontal, AttractVertical, AttractRadial)
    -- * HoldToReveal Compound
  , HoldToReveal
  , holdToReveal
  , holdToRevealSilent
  , holdElement
  , holdDuration
  , revealTarget
  , revealAnimation
    -- * ShakeToUndo Compound
  , ShakeToUndo
  , shakeToUndo
  , shakeThreshold
  , shakeCooldown
  , undoCallback
    -- * TiltToScroll Compound
  , TiltToScroll
  , tiltToScroll
  , tiltSensitivity
  , tiltDeadzone
  , scrollMultiplier
  , TiltAxis(TiltBeta, TiltGamma, TiltBoth)
    -- * EasterEgg Compound
  , EasterEgg
  , easterEgg
  , eggId
  , eggTriggerPattern
  , eggReward
  , eggUnlocked
  , EasterEggReward
      ( ConfettiReward
      , AchievementReward
      , UnlockReward
      , AnimationReward
      , SoundReward
      , ToastReward
      , CustomReward
      )
  ) where

import Prelude

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Gestural.Trigger.Atoms
  ( ProximityRadius
  , TriggerCooldown
  , TriggerCount
  , TriggerDelay
  , TriggerWindow
  , mkProximityRadius
  , mkTriggerCooldown
  , mkTriggerCount
  , mkTriggerDelay
  , mkTriggerWindow
  , unwrapProximityRadius
  , unwrapTriggerCooldown
  , unwrapTriggerCount
  , unwrapTriggerDelay
  , unwrapTriggerWindow
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // proximity // trigger
-- ═════════════════════════════════════════════════════════════════════════════

-- | Proximity trigger molecule: Element + Radius + Target + Effect
-- |
-- | Activates when cursor enters the radius around an element.
type ProximityTrigger =
  { elementId :: String           -- ^ Element to monitor
  , radius :: ProximityRadius     -- ^ Detection radius
  , falloff :: Number             -- ^ Falloff distance (0-1 strength curve)
  , targetId :: String            -- ^ Target element for effect
  , effectName :: String          -- ^ Effect to apply
  }

-- | Create a proximity trigger
proximityTrigger :: String -> Number -> Number -> String -> String -> ProximityTrigger
proximityTrigger elementId radiusPx falloff targetId effectName =
  { elementId
  , radius: mkProximityRadius radiusPx
  , falloff: clampNumber 0.0 1.0 falloff
  , targetId
  , effectName
  }

-- | Get proximity element ID
proximityElement :: ProximityTrigger -> String
proximityElement pt = pt.elementId

-- | Get proximity radius value
proximityRadiusValue :: ProximityTrigger -> Number
proximityRadiusValue pt = unwrapProximityRadius pt.radius

-- | Get proximity falloff
proximityFalloffValue :: ProximityTrigger -> Number
proximityFalloffValue pt = pt.falloff

-- | Get proximity target ID
proximityTargetId :: ProximityTrigger -> String
proximityTargetId pt = pt.targetId

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // gesture // trigger
-- ═════════════════════════════════════════════════════════════════════════════

-- | Gesture trigger molecule: GesturePattern + Target + Effect
-- |
-- | Activates when a specific gesture pattern is recognized.
type GestureTrigger =
  { pattern :: String             -- ^ Named gesture pattern
  , targetId :: String            -- ^ Target element for effect
  , effectName :: String          -- ^ Effect to apply
  , window :: TriggerWindow       -- ^ Time window for gesture completion
  }

-- | Create a gesture trigger
gestureTrigger :: String -> String -> String -> Number -> GestureTrigger
gestureTrigger pattern targetId effectName windowMs =
  { pattern
  , targetId
  , effectName
  , window: mkTriggerWindow windowMs
  }

-- | Get gesture pattern
gesturePattern :: GestureTrigger -> String
gesturePattern gt = gt.pattern

-- | Get gesture target ID
gestureTargetId :: GestureTrigger -> String
gestureTargetId gt = gt.targetId

-- | Get gesture window duration
gestureWindowMs :: GestureTrigger -> Number
gestureWindowMs gt = unwrapTriggerWindow gt.window

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // time // trigger
-- ═════════════════════════════════════════════════════════════════════════════

-- | Time trigger molecule: HoldDuration + Element + Effect
-- |
-- | Activates after holding/pressing for a duration.
type TimeTrigger =
  { duration :: TriggerDelay      -- ^ Hold duration (uses delay bounds)
  , elementId :: String           -- ^ Element to hold
  , effectName :: String          -- ^ Effect to apply
  , targetId :: String            -- ^ Target element for effect
  }

-- | Create a time trigger
timeTrigger :: Number -> String -> String -> String -> TimeTrigger
timeTrigger durationMs elementId targetId effectName =
  { duration: mkTriggerDelay durationMs
  , elementId
  , effectName
  , targetId
  }

-- | Get hold duration
timeDuration :: TimeTrigger -> Number
timeDuration tt = unwrapTriggerDelay tt.duration

-- | Get time trigger element ID
timeElementId :: TimeTrigger -> String
timeElementId tt = tt.elementId

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // combo // trigger
-- ═════════════════════════════════════════════════════════════════════════════

-- | Combo trigger molecule: Condition[] + Effect
-- |
-- | Activates when all conditions in the array are met.
type ComboTrigger =
  { conditions :: Array String    -- ^ Named conditions that must all be met
  , effectName :: String          -- ^ Effect to apply
  , targetId :: String            -- ^ Target element for effect
  , window :: TriggerWindow       -- ^ Time window for all conditions
  }

-- | Create a combo trigger
comboTrigger :: Array String -> String -> String -> Number -> ComboTrigger
comboTrigger conditions targetId effectName windowMs =
  { conditions
  , effectName
  , targetId
  , window: mkTriggerWindow windowMs
  }

-- | Get combo conditions
comboConditions :: ComboTrigger -> Array String
comboConditions ct = ct.conditions

-- | Get combo window duration
comboWindowMs :: ComboTrigger -> Number
comboWindowMs ct = unwrapTriggerWindow ct.window

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // tap // count // trigger
-- ═════════════════════════════════════════════════════════════════════════════

-- | Tap count trigger molecule: Element + Count + Window + Effect
-- |
-- | Activates after N taps on an element within the time window.
-- | Used for multi-tap interactions like "tap 5 times to reveal".
type TapCountTrigger =
  { elementId :: String           -- ^ Element to tap
  , count :: TriggerCount         -- ^ Number of taps required
  , window :: TriggerWindow       -- ^ Time window for all taps
  , effectName :: String          -- ^ Effect to apply
  , targetId :: String            -- ^ Target element for effect
  }

-- | Create a tap count trigger
tapCountTrigger :: String -> Int -> Number -> String -> String -> TapCountTrigger
tapCountTrigger elementId countN windowMs targetId effectName =
  { elementId
  , count: mkTriggerCount countN
  , window: mkTriggerWindow windowMs
  , effectName
  , targetId
  }

-- | Get tap element ID
tapElement :: TapCountTrigger -> String
tapElement tct = tct.elementId

-- | Get required tap count
tapCount :: TapCountTrigger -> Int
tapCount tct = unwrapTriggerCount tct.count

-- | Get tap window duration
tapWindowMs :: TapCountTrigger -> Number
tapWindowMs tct = unwrapTriggerWindow tct.window

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // proximity // glow
-- ═════════════════════════════════════════════════════════════════════════════

-- | ProximityGlow compound: Cursor approaching causes glow effect.
-- |
-- | The glow intensity scales from 0 at the radius edge to maximum
-- | at the element center, following the falloff curve.
type ProximityGlow =
  { elementId :: String           -- ^ Element that glows
  , radius :: ProximityRadius     -- ^ Detection radius
  , color :: String               -- ^ Glow color (CSS color string)
  , intensity :: Number           -- ^ Maximum glow intensity (0-1)
  , falloff :: Number             -- ^ Falloff curve exponent
  }

-- | Create a proximity glow effect
proximityGlow :: String -> Number -> String -> Number -> ProximityGlow
proximityGlow elementId radiusPx color intensity =
  { elementId
  , radius: mkProximityRadius radiusPx
  , color
  , intensity: clampNumber 0.0 1.0 intensity
  , falloff: 1.0  -- Linear falloff by default
  }

-- | Get glow element ID
glowElement :: ProximityGlow -> String
glowElement pg = pg.elementId

-- | Get glow radius
glowRadius :: ProximityGlow -> Number
glowRadius pg = unwrapProximityRadius pg.radius

-- | Get glow color
glowColor :: ProximityGlow -> String
glowColor pg = pg.color

-- | Get glow intensity
glowIntensity :: ProximityGlow -> Number
glowIntensity pg = pg.intensity

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // proximity // expand
-- ═════════════════════════════════════════════════════════════════════════════

-- | ProximityExpand compound: Cursor approaching expands element.
-- |
-- | The element scales from 1.0 at the radius edge to the configured
-- | scale at the element center.
type ProximityExpand =
  { elementId :: String           -- ^ Element that expands
  , radius :: ProximityRadius     -- ^ Detection radius
  , scale :: Number               -- ^ Maximum scale factor (1.0 = no change)
  , easing :: String              -- ^ Easing function name
  }

-- | Create a proximity expand effect
proximityExpand :: String -> Number -> Number -> ProximityExpand
proximityExpand elementId radiusPx scale =
  { elementId
  , radius: mkProximityRadius radiusPx
  , scale: max 0.1 scale  -- Minimum 10% scale
  , easing: "easeOut"
  }

-- | Get expand element ID
expandElement :: ProximityExpand -> String
expandElement pe = pe.elementId

-- | Get expand radius
expandRadius :: ProximityExpand -> Number
expandRadius pe = unwrapProximityRadius pe.radius

-- | Get expand scale
expandScale :: ProximityExpand -> Number
expandScale pe = pe.scale

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // proximity // attract
-- ═════════════════════════════════════════════════════════════════════════════

-- | ProximityAttract compound: Element subtly moves toward cursor.
-- |
-- | The element translates toward the cursor position, with maximum
-- | translation occurring at the radius edge and diminishing to zero
-- | at the center.
type ProximityAttract =
  { elementId :: String           -- ^ Element that moves
  , radius :: ProximityRadius     -- ^ Detection radius
  , strength :: Number            -- ^ Maximum translation (pixels)
  , constraint :: AttractConstraint  -- ^ Movement constraint
  }

-- | Constraint for attract movement
data AttractConstraint
  = AttractFree                   -- ^ Move in any direction
  | AttractHorizontal             -- ^ Move only horizontally
  | AttractVertical               -- ^ Move only vertically
  | AttractRadial                 -- ^ Move only toward/away from cursor

derive instance eqAttractConstraint :: Eq AttractConstraint

instance showAttractConstraint :: Show AttractConstraint where
  show AttractFree = "free"
  show AttractHorizontal = "horizontal"
  show AttractVertical = "vertical"
  show AttractRadial = "radial"

-- | Create a proximity attract effect
proximityAttract :: String -> Number -> Number -> ProximityAttract
proximityAttract elementId radiusPx strength =
  { elementId
  , radius: mkProximityRadius radiusPx
  , strength: max 0.0 strength
  , constraint: AttractFree
  }

-- | Get attract element ID
attractElement :: ProximityAttract -> String
attractElement pa = pa.elementId

-- | Get attract radius
attractRadius :: ProximityAttract -> Number
attractRadius pa = unwrapProximityRadius pa.radius

-- | Get attract strength
attractStrength :: ProximityAttract -> Number
attractStrength pa = pa.strength

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // hold // to // reveal
-- ═════════════════════════════════════════════════════════════════════════════

-- | HoldToReveal compound: Long-press reveals hidden content.
-- |
-- | After holding for the configured duration, the target element
-- | is revealed with an optional animation.
type HoldToReveal =
  { elementId :: String           -- ^ Element to hold
  , duration :: TriggerDelay      -- ^ Hold duration required
  , targetId :: String            -- ^ Element to reveal
  , animation :: Maybe String     -- ^ Optional reveal animation
  , haptic :: Boolean             -- ^ Trigger haptic on reveal
  }

-- | Create a hold-to-reveal trigger
holdToReveal :: String -> Number -> String -> HoldToReveal
holdToReveal elementId durationMs targetId =
  { elementId
  , duration: mkTriggerDelay durationMs
  , targetId
  , animation: Just "fadeIn"
  , haptic: true
  }

-- | Get hold element ID
holdElement :: HoldToReveal -> String
holdElement htr = htr.elementId

-- | Get hold duration
holdDuration :: HoldToReveal -> Number
holdDuration htr = unwrapTriggerDelay htr.duration

-- | Get reveal target ID
revealTarget :: HoldToReveal -> String
revealTarget htr = htr.targetId

-- | Get reveal animation name (if any)
revealAnimation :: HoldToReveal -> Maybe String
revealAnimation htr = htr.animation

-- | Create a hold-to-reveal trigger without animation
holdToRevealSilent :: String -> Number -> String -> HoldToReveal
holdToRevealSilent elementId durationMs targetId =
  { elementId
  , duration: mkTriggerDelay durationMs
  , targetId
  , animation: Nothing
  , haptic: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // shake // to // undo
-- ═════════════════════════════════════════════════════════════════════════════

-- | ShakeToUndo compound: Device shake triggers undo action.
-- |
-- | Uses device motion API to detect shake gestures. When the
-- | acceleration exceeds the threshold, triggers undo.
type ShakeToUndo =
  { threshold :: Number           -- ^ Acceleration threshold (m/s²)
  , cooldown :: TriggerCooldown   -- ^ Cooldown between shakes
  , callback :: String            -- ^ Callback action name
  , haptic :: Boolean             -- ^ Trigger haptic on undo
  }

-- | Create a shake-to-undo trigger
shakeToUndo :: Number -> Number -> String -> ShakeToUndo
shakeToUndo thresholdAccel cooldownMs callback =
  { threshold: max 5.0 thresholdAccel  -- Minimum 5 m/s² to avoid false positives
  , cooldown: mkTriggerCooldown cooldownMs
  , callback
  , haptic: true
  }

-- | Get shake threshold
shakeThreshold :: ShakeToUndo -> Number
shakeThreshold stu = stu.threshold

-- | Get shake cooldown
shakeCooldown :: ShakeToUndo -> Number
shakeCooldown stu = unwrapTriggerCooldown stu.cooldown

-- | Get undo callback name
undoCallback :: ShakeToUndo -> String
undoCallback stu = stu.callback

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // tilt // to // scroll
-- ═════════════════════════════════════════════════════════════════════════════

-- | TiltToScroll compound: Device tilt affects scroll position.
-- |
-- | Uses device orientation API to map tilt angle to scroll velocity.
-- | Includes a deadzone to prevent unintentional scrolling.
type TiltToScroll =
  { sensitivity :: Number         -- ^ Tilt sensitivity (0-1)
  , deadzone :: Number            -- ^ Tilt deadzone in degrees
  , multiplier :: Number          -- ^ Scroll speed multiplier
  , axis :: TiltAxis              -- ^ Which tilt axis to use
  }

-- | Tilt axis for scroll control
data TiltAxis
  = TiltBeta                      -- ^ Front-to-back tilt (pitch)
  | TiltGamma                     -- ^ Left-to-right tilt (roll)
  | TiltBoth                      -- ^ Both axes (2D scroll)

derive instance eqTiltAxis :: Eq TiltAxis

instance showTiltAxis :: Show TiltAxis where
  show TiltBeta = "beta"
  show TiltGamma = "gamma"
  show TiltBoth = "both"

-- | Create a tilt-to-scroll trigger
tiltToScroll :: Number -> Number -> Number -> TiltToScroll
tiltToScroll sensitivity deadzoneDeg multiplier =
  { sensitivity: clampNumber 0.0 1.0 sensitivity
  , deadzone: max 0.0 deadzoneDeg
  , multiplier: max 0.1 multiplier
  , axis: TiltBeta  -- Default to pitch (forward/back tilt)
  }

-- | Get tilt sensitivity
tiltSensitivity :: TiltToScroll -> Number
tiltSensitivity tts = tts.sensitivity

-- | Get tilt deadzone
tiltDeadzone :: TiltToScroll -> Number
tiltDeadzone tts = tts.deadzone

-- | Get scroll multiplier
scrollMultiplier :: TiltToScroll -> Number
scrollMultiplier tts = tts.multiplier

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // easter // egg
-- ═════════════════════════════════════════════════════════════════════════════

-- | EasterEgg compound: Arbitrary hidden trigger + reward.
-- |
-- | A generic easter egg container that can hold any trigger pattern
-- | and any reward. The trigger pattern is a string that can encode
-- | key sequences, gesture patterns, or other activation methods.
type EasterEgg =
  { id :: String                  -- ^ Unique easter egg identifier
  , triggerPattern :: String      -- ^ Encoded trigger pattern
  , reward :: EasterEggReward     -- ^ Reward when triggered
  , unlocked :: Boolean           -- ^ Has this egg been found?
  , persistent :: Boolean         -- ^ Remember across sessions?
  }

-- | Types of easter egg rewards
data EasterEggReward
  = ConfettiReward                -- ^ Visual celebration
  | AchievementReward String String  -- ^ Achievement (id, name)
  | UnlockReward String           -- ^ Unlock feature
  | AnimationReward String        -- ^ Play animation
  | SoundReward String            -- ^ Play sound
  | ToastReward String String     -- ^ Show toast (type, message)
  | CustomReward String           -- ^ Custom reward handler

derive instance eqEasterEggReward :: Eq EasterEggReward

instance showEasterEggReward :: Show EasterEggReward where
  show ConfettiReward = "confetti"
  show (AchievementReward id name) = "achievement(" <> id <> "," <> name <> ")"
  show (UnlockReward feature) = "unlock(" <> feature <> ")"
  show (AnimationReward anim) = "animation(" <> anim <> ")"
  show (SoundReward sound) = "sound(" <> sound <> ")"
  show (ToastReward t msg) = "toast(" <> t <> "," <> msg <> ")"
  show (CustomReward handler) = "custom(" <> handler <> ")"

-- | Create an easter egg
easterEgg :: String -> String -> EasterEggReward -> EasterEgg
easterEgg id triggerPattern reward =
  { id
  , triggerPattern
  , reward
  , unlocked: false
  , persistent: true
  }

-- | Get easter egg ID
eggId :: EasterEgg -> String
eggId ee = ee.id

-- | Get easter egg trigger pattern
eggTriggerPattern :: EasterEgg -> String
eggTriggerPattern ee = ee.triggerPattern

-- | Get easter egg reward
eggReward :: EasterEgg -> EasterEggReward
eggReward ee = ee.reward

-- | Check if easter egg is unlocked
eggUnlocked :: EasterEgg -> Boolean
eggUnlocked ee = ee.unlocked

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp a Number to a range
clampNumber :: Number -> Number -> Number -> Number
clampNumber lo hi x = max lo (min hi x)
