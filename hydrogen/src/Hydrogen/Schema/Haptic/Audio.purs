-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // schema // haptic // audio
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Audio Parameters - bounded atoms for audio feedback.
-- |
-- | These atoms define the bounded values for audio-based feedback:
-- | volume, pitch multiplier, and stereo pan.
-- |
-- | ## SCHEMA.md Reference
-- | ```
-- | | Volume        | Number | 0.0  | 1.0  | clamps   | Sound volume              |
-- | | Pitch         | Number | 0.1  | 4.0  | clamps   | Pitch multiplier          |
-- | | Pan           | Number | -1.0 | 1.0  | clamps   | Stereo pan                |
-- | ```
-- |
-- | ## Dependencies
-- | - Prelude (Eq, Ord, Show, min, max)
-- |
-- | ## Dependents
-- | - Haptic/Feedback.purs (uses these in AudioCue molecule)
-- | - Component.* (audio feedback for interactions)

module Hydrogen.Schema.Haptic.Audio
  ( -- * Volume (0.0-1.0, clamps)
    Volume
  , mkVolume
  , unwrapVolume
  , minVolume
  , maxVolume
  , muteVolume
  , quietVolume
  , normalVolume
  , loudVolume
  , maxedVolume
    -- * Pitch (0.1-4.0, clamps)
  , Pitch
  , mkPitch
  , unwrapPitch
  , minPitch
  , maxPitch
  , veryLowPitch
  , lowPitch
  , normalPitch
  , highPitch
  , veryHighPitch
    -- * Pan (-1.0 to 1.0, clamps)
  , Pan
  , mkPan
  , unwrapPan
  , minPan
  , maxPan
  , panLeft
  , panCenter
  , panRight
  , panHardLeft
  , panHardRight
    -- * SoundId (identifier)
  , SoundId
  , mkSoundId
  , unwrapSoundId
  ) where

import Prelude

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // volume
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sound volume (0.0-1.0, clamps).
-- |
-- | Linear amplitude scale where 0.0 is silent and 1.0 is full volume.
-- | Bounded: minimum 0.0, maximum 1.0.
newtype Volume = Volume Number

derive instance eqVolume :: Eq Volume
derive instance ordVolume :: Ord Volume

instance showVolume :: Show Volume where
  show (Volume n) = "Volume(" <> show n <> ")"

-- | Minimum volume (0.0 - silent)
minVolume :: Number
minVolume = 0.0

-- | Maximum volume (1.0 - full)
maxVolume :: Number
maxVolume = 1.0

-- | Create a bounded volume (clamps to 0.0-1.0)
mkVolume :: Number -> Volume
mkVolume n = Volume (clampNumber minVolume maxVolume n)

-- | Unwrap the volume value
unwrapVolume :: Volume -> Number
unwrapVolume (Volume n) = n

-- | Mute volume (0.0)
muteVolume :: Volume
muteVolume = Volume 0.0

-- | Quiet volume (0.25)
quietVolume :: Volume
quietVolume = Volume 0.25

-- | Normal volume (0.5)
normalVolume :: Volume
normalVolume = Volume 0.5

-- | Loud volume (0.75)
loudVolume :: Volume
loudVolume = Volume 0.75

-- | Maximum volume (1.0)
maxedVolume :: Volume
maxedVolume = Volume 1.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // pitch
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pitch multiplier (0.1-4.0, clamps).
-- |
-- | Multiplier for playback speed/pitch. 1.0 is normal, 0.5 is half-speed
-- | (one octave down), 2.0 is double-speed (one octave up).
-- | Bounded: minimum 0.1 (very slow), maximum 4.0 (two octaves up).
newtype Pitch = Pitch Number

derive instance eqPitch :: Eq Pitch
derive instance ordPitch :: Ord Pitch

instance showPitch :: Show Pitch where
  show (Pitch n) = "Pitch(" <> show n <> "x)"

-- | Minimum pitch (0.1 - very slow/low)
minPitch :: Number
minPitch = 0.1

-- | Maximum pitch (4.0 - very fast/high)
maxPitch :: Number
maxPitch = 4.0

-- | Create a bounded pitch (clamps to 0.1-4.0)
mkPitch :: Number -> Pitch
mkPitch n = Pitch (clampNumber minPitch maxPitch n)

-- | Unwrap the pitch value
unwrapPitch :: Pitch -> Number
unwrapPitch (Pitch n) = n

-- | Very low pitch (0.5 - one octave down)
veryLowPitch :: Pitch
veryLowPitch = Pitch 0.5

-- | Low pitch (0.75)
lowPitch :: Pitch
lowPitch = Pitch 0.75

-- | Normal pitch (1.0 - original speed)
normalPitch :: Pitch
normalPitch = Pitch 1.0

-- | High pitch (1.5)
highPitch :: Pitch
highPitch = Pitch 1.5

-- | Very high pitch (2.0 - one octave up)
veryHighPitch :: Pitch
veryHighPitch = Pitch 2.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                        // pan
-- ═════════════════════════════════════════════════════════════════════════════

-- | Stereo pan (-1.0 to 1.0, clamps).
-- |
-- | Position in the stereo field. -1.0 is hard left, 0.0 is center,
-- | 1.0 is hard right.
-- | Bounded: minimum -1.0, maximum 1.0.
newtype Pan = Pan Number

derive instance eqPan :: Eq Pan
derive instance ordPan :: Ord Pan

instance showPan :: Show Pan where
  show (Pan n) = "Pan(" <> show n <> ")"

-- | Minimum pan (-1.0 - hard left)
minPan :: Number
minPan = -1.0

-- | Maximum pan (1.0 - hard right)
maxPan :: Number
maxPan = 1.0

-- | Create a bounded pan (clamps to -1.0 to 1.0)
mkPan :: Number -> Pan
mkPan n = Pan (clampNumber minPan maxPan n)

-- | Unwrap the pan value
unwrapPan :: Pan -> Number
unwrapPan (Pan n) = n

-- | Pan hard left (-1.0)
panHardLeft :: Pan
panHardLeft = Pan (-1.0)

-- | Pan left (-0.5)
panLeft :: Pan
panLeft = Pan (-0.5)

-- | Pan center (0.0)
panCenter :: Pan
panCenter = Pan 0.0

-- | Pan right (0.5)
panRight :: Pan
panRight = Pan 0.5

-- | Pan hard right (1.0)
panHardRight :: Pan
panHardRight = Pan 1.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // sound id
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sound identifier.
-- |
-- | A string identifier for a sound asset. This is used to reference
-- | sounds in the AudioCue molecule.
newtype SoundId = SoundId String

derive instance eqSoundId :: Eq SoundId
derive instance ordSoundId :: Ord SoundId

instance showSoundId :: Show SoundId where
  show (SoundId s) = "SoundId(" <> s <> ")"

-- | Create a sound ID
mkSoundId :: String -> SoundId
mkSoundId = SoundId

-- | Unwrap the sound ID
unwrapSoundId :: SoundId -> String
unwrapSoundId (SoundId s) = s

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp a Number to a range
clampNumber :: Number -> Number -> Number -> Number
clampNumber lo hi x = max lo (min hi x)
