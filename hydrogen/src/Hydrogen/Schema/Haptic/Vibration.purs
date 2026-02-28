-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // haptic // vibration
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Vibration Parameters - bounded atoms for haptic feedback.
-- |
-- | These atoms define the bounded values for vibration-based haptic
-- | feedback: intensity, sharpness, frequency, duration, attack, and decay.
-- |
-- | ## SCHEMA.md Reference
-- | ```
-- | | Intensity     | Number | 0.0  | 1.0   | clamps   | Vibration strength        |
-- | | Sharpness     | Number | 0.0  | 1.0   | clamps   | Haptic sharpness (iOS)    |
-- | | Frequency     | Number | 0    | 500   | clamps   | Vibration frequency (Hz)  |
-- | | Duration      | Number | 0    | 10000 | clamps   | Haptic duration (ms)      |
-- | | Attack        | Number | 0    | none  | finite   | Ramp up time (ms)         |
-- | | Decay         | Number | 0    | none  | finite   | Ramp down time (ms)       |
-- | ```
-- |
-- | ## Dependencies
-- | - Prelude (Eq, Ord, Show, min, max)
-- |
-- | ## Dependents
-- | - Haptic/Feedback.purs (uses these in molecules/compounds)
-- | - Component.* (haptic feedback for interactions)

module Hydrogen.Schema.Haptic.Vibration
  ( -- * Intensity (0.0-1.0, clamps)
    Intensity
  , mkIntensity
  , unwrapIntensity
  , minIntensity
  , maxIntensity
  , noIntensity
  , lightIntensity
  , mediumIntensity
  , heavyIntensity
  , fullIntensity
    -- * Sharpness (0.0-1.0, clamps)
  , Sharpness
  , mkSharpness
  , unwrapSharpness
  , minSharpness
  , maxSharpness
  , softSharpness
  , mediumSharpness
  , sharpSharpness
    -- * Frequency (0-500 Hz, clamps)
  , HapticFrequency
  , mkHapticFrequency
  , unwrapHapticFrequency
  , minHapticFrequency
  , maxHapticFrequency
  , lowFrequency
  , midFrequency
  , highFrequency
    -- * Duration (0-10000 ms, clamps)
  , HapticDuration
  , mkHapticDuration
  , unwrapHapticDuration
  , minHapticDuration
  , maxHapticDuration
  , instantDuration
  , shortDuration
  , mediumDuration
  , longDuration
    -- * Attack (0+ ms, finite)
  , Attack
  , mkAttack
  , unwrapAttack
  , noAttack
  , quickAttack
  , slowAttack
    -- * Decay (0+ ms, finite)
  , Decay
  , mkDecay
  , unwrapDecay
  , noDecay
  , quickDecay
  , slowDecay
  ) where

import Prelude

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // intensity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Vibration intensity (0.0-1.0, clamps).
-- |
-- | Bounded: minimum 0.0 (no vibration), maximum 1.0 (full intensity).
-- | Values outside this range are clamped.
newtype Intensity = Intensity Number

derive instance eqIntensity :: Eq Intensity
derive instance ordIntensity :: Ord Intensity

instance showIntensity :: Show Intensity where
  show (Intensity n) = "Intensity(" <> show n <> ")"

-- | Minimum intensity (0.0 - no vibration)
minIntensity :: Number
minIntensity = 0.0

-- | Maximum intensity (1.0 - full power)
maxIntensity :: Number
maxIntensity = 1.0

-- | Create a bounded intensity (clamps to 0.0-1.0)
mkIntensity :: Number -> Intensity
mkIntensity n = Intensity (clampNumber minIntensity maxIntensity n)

-- | Unwrap the intensity value
unwrapIntensity :: Intensity -> Number
unwrapIntensity (Intensity n) = n

-- | No intensity (silent)
noIntensity :: Intensity
noIntensity = Intensity 0.0

-- | Light intensity (0.25)
lightIntensity :: Intensity
lightIntensity = Intensity 0.25

-- | Medium intensity (0.5)
mediumIntensity :: Intensity
mediumIntensity = Intensity 0.5

-- | Heavy intensity (0.75)
heavyIntensity :: Intensity
heavyIntensity = Intensity 0.75

-- | Full intensity (1.0)
fullIntensity :: Intensity
fullIntensity = Intensity 1.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // sharpness
-- ═════════════════════════════════════════════════════════════════════════════

-- | Haptic sharpness (0.0-1.0, clamps).
-- |
-- | iOS-specific parameter that controls the "feel" of haptic feedback.
-- | Low values feel soft/dull, high values feel sharp/crisp.
-- | Bounded: minimum 0.0, maximum 1.0.
newtype Sharpness = Sharpness Number

derive instance eqSharpness :: Eq Sharpness
derive instance ordSharpness :: Ord Sharpness

instance showSharpness :: Show Sharpness where
  show (Sharpness n) = "Sharpness(" <> show n <> ")"

-- | Minimum sharpness (0.0 - soft/dull)
minSharpness :: Number
minSharpness = 0.0

-- | Maximum sharpness (1.0 - crisp/sharp)
maxSharpness :: Number
maxSharpness = 1.0

-- | Create a bounded sharpness (clamps to 0.0-1.0)
mkSharpness :: Number -> Sharpness
mkSharpness n = Sharpness (clampNumber minSharpness maxSharpness n)

-- | Unwrap the sharpness value
unwrapSharpness :: Sharpness -> Number
unwrapSharpness (Sharpness n) = n

-- | Soft sharpness (0.25 - dull feel)
softSharpness :: Sharpness
softSharpness = Sharpness 0.25

-- | Medium sharpness (0.5 - balanced)
mediumSharpness :: Sharpness
mediumSharpness = Sharpness 0.5

-- | Sharp sharpness (0.85 - crisp feel)
sharpSharpness :: Sharpness
sharpSharpness = Sharpness 0.85

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // frequency
-- ═════════════════════════════════════════════════════════════════════════════

-- | Vibration frequency in Hz (0-500, clamps).
-- |
-- | The frequency of the vibration motor oscillation.
-- | Human perception of haptics is most sensitive around 200-300 Hz.
-- | Bounded: minimum 0 Hz, maximum 500 Hz.
newtype HapticFrequency = HapticFrequency Number

derive instance eqHapticFrequency :: Eq HapticFrequency
derive instance ordHapticFrequency :: Ord HapticFrequency

instance showHapticFrequency :: Show HapticFrequency where
  show (HapticFrequency n) = "HapticFrequency(" <> show n <> "Hz)"

-- | Minimum haptic frequency (0 Hz)
minHapticFrequency :: Number
minHapticFrequency = 0.0

-- | Maximum haptic frequency (500 Hz)
maxHapticFrequency :: Number
maxHapticFrequency = 500.0

-- | Create a bounded haptic frequency (clamps to 0-500)
mkHapticFrequency :: Number -> HapticFrequency
mkHapticFrequency n = HapticFrequency (clampNumber minHapticFrequency maxHapticFrequency n)

-- | Unwrap the frequency value
unwrapHapticFrequency :: HapticFrequency -> Number
unwrapHapticFrequency (HapticFrequency n) = n

-- | Low frequency (100 Hz - rumble)
lowFrequency :: HapticFrequency
lowFrequency = HapticFrequency 100.0

-- | Mid frequency (250 Hz - tactile sweet spot)
midFrequency :: HapticFrequency
midFrequency = HapticFrequency 250.0

-- | High frequency (400 Hz - buzz)
highFrequency :: HapticFrequency
highFrequency = HapticFrequency 400.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // duration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Haptic duration in milliseconds (0-10000, clamps).
-- |
-- | How long the haptic feedback plays.
-- | Bounded: minimum 0 ms, maximum 10000 ms (10 seconds).
newtype HapticDuration = HapticDuration Number

derive instance eqHapticDuration :: Eq HapticDuration
derive instance ordHapticDuration :: Ord HapticDuration

instance showHapticDuration :: Show HapticDuration where
  show (HapticDuration n) = "HapticDuration(" <> show n <> "ms)"

-- | Minimum haptic duration (0 ms)
minHapticDuration :: Number
minHapticDuration = 0.0

-- | Maximum haptic duration (10000 ms)
maxHapticDuration :: Number
maxHapticDuration = 10000.0

-- | Create a bounded haptic duration (clamps to 0-10000)
mkHapticDuration :: Number -> HapticDuration
mkHapticDuration n = HapticDuration (clampNumber minHapticDuration maxHapticDuration n)

-- | Unwrap the duration value
unwrapHapticDuration :: HapticDuration -> Number
unwrapHapticDuration (HapticDuration n) = n

-- | Instant duration (10 ms - quick tap)
instantDuration :: HapticDuration
instantDuration = HapticDuration 10.0

-- | Short duration (50 ms - standard click)
shortDuration :: HapticDuration
shortDuration = HapticDuration 50.0

-- | Medium duration (200 ms - noticeable pulse)
mediumDuration :: HapticDuration
mediumDuration = HapticDuration 200.0

-- | Long duration (500 ms - sustained feedback)
longDuration :: HapticDuration
longDuration = HapticDuration 500.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // attack
-- ═════════════════════════════════════════════════════════════════════════════

-- | Attack time in milliseconds (0+, finite).
-- |
-- | How long it takes for the vibration to ramp up from zero to
-- | full intensity. No upper bound (finite behavior).
newtype Attack = Attack Number

derive instance eqAttack :: Eq Attack
derive instance ordAttack :: Ord Attack

instance showAttack :: Show Attack where
  show (Attack n) = "Attack(" <> show n <> "ms)"

-- | Create a bounded attack (clamps to 0+)
mkAttack :: Number -> Attack
mkAttack n = Attack (max 0.0 n)

-- | Unwrap the attack value
unwrapAttack :: Attack -> Number
unwrapAttack (Attack n) = n

-- | No attack (instant start)
noAttack :: Attack
noAttack = Attack 0.0

-- | Quick attack (20 ms)
quickAttack :: Attack
quickAttack = Attack 20.0

-- | Slow attack (100 ms - gradual ramp up)
slowAttack :: Attack
slowAttack = Attack 100.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // decay
-- ═════════════════════════════════════════════════════════════════════════════

-- | Decay time in milliseconds (0+, finite).
-- |
-- | How long it takes for the vibration to ramp down from full
-- | intensity to zero. No upper bound (finite behavior).
newtype Decay = Decay Number

derive instance eqDecay :: Eq Decay
derive instance ordDecay :: Ord Decay

instance showDecay :: Show Decay where
  show (Decay n) = "Decay(" <> show n <> "ms)"

-- | Create a bounded decay (clamps to 0+)
mkDecay :: Number -> Decay
mkDecay n = Decay (max 0.0 n)

-- | Unwrap the decay value
unwrapDecay :: Decay -> Number
unwrapDecay (Decay n) = n

-- | No decay (instant stop)
noDecay :: Decay
noDecay = Decay 0.0

-- | Quick decay (30 ms)
quickDecay :: Decay
quickDecay = Decay 30.0

-- | Slow decay (150 ms - gradual fade out)
slowDecay :: Decay
slowDecay = Decay 150.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp a Number to a range
clampNumber :: Number -> Number -> Number -> Number
clampNumber lo hi x = max lo (min hi x)
