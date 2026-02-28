-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // audio // frequency
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Frequency and pitch atoms for audio processing.
-- |
-- | ## MIDI Note System
-- | MIDI note numbers span 0-127, where 60 is Middle C (C4) and 69 is A4 (440Hz).
-- | The formula: frequency = 440 * 2^((note - 69) / 12)
-- |
-- | ## Cents and Semitones
-- | Musical intervals are measured in semitones (half steps) and cents.
-- | 1 semitone = 100 cents = factor of 2^(1/12) ≈ 1.0595
-- | 1 octave = 12 semitones = 1200 cents = factor of 2
-- |
-- | ## Sample Rate and Bit Depth
-- | Digital audio parameters: CD quality is 44100Hz/16-bit,
-- | professional is 48000Hz or 96000Hz/24-bit.

module Hydrogen.Schema.Audio.Frequency
  ( -- * Types
    Hertz(..)
  , Kilohertz(..)
  , MidiNote(..)
  , MidiPitch(..)
  , Cent(..)
  , Semitone(..)
  , Octave(..)
  , SampleRate(..)
  , BitDepth(..)
  
  -- * Constructors
  , hertz
  , kilohertz
  , midiNote
  , midiPitch
  , cent
  , semitone
  , octave
  , sampleRate
  , bitDepth
  
  -- * Predefined Frequencies
  , a4
  , middleC
  , subBass
  , bass
  , midrange
  , presence
  , brilliance
  , nyquistCD
  , nyquist48k
  
  -- * Predefined Sample Rates
  , rate44100
  , rate48000
  , rate88200
  , rate96000
  , rate192000
  
  -- * Predefined Bit Depths
  , bit8
  , bit16
  , bit24
  , bit32
  
  -- * Accessors
  , unwrapHertz
  , unwrapKilohertz
  , unwrapMidiNote
  , unwrapMidiPitch
  , unwrapCent
  , unwrapSemitone
  , unwrapOctave
  , unwrapSampleRate
  , unwrapBitDepth
  
  -- * Conversions
  , midiToHertz
  , hertzToMidi
  , midiPitchToHertz
  , hertzToMidiPitch
  , hertzToKilohertz
  , kilohertzToHertz
  , centsToSemitones
  , semitonesToCents
  , semitonesToOctaves
  , octavesToSemitones
  , centsToRatio
  , ratioToCents
  , semitonesToRatio
  , ratioToSemitones
  
  -- * Operations
  , transposeByOctave
  , transposeBySemitone
  , transposeByCent
  , frequencyRatio
  , intervalInCents
  , intervalInSemitones
  
  -- * Note Names
  , NoteName(..)
  , allNoteNames
  , midiToNoteName
  , midiToOctaveNumber
  , noteNameToString
  
  -- * Bounds
  , hertzBounds
  , kilohertzBounds
  , midiNoteBounds
  , midiPitchBounds
  , centBounds
  , semitoneBounds
  , octaveBounds
  , sampleRateBounds
  , bitDepthBounds
  ) where

import Prelude

import Data.Int as Int
import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Math.Core as Math
import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // hertz
-- ═════════════════════════════════════════════════════════════════════════════

-- | Hertz - frequency in cycles per second.
-- | Clamped to [0, ∞) - no negative frequencies.
-- | Practical audio range: 20Hz - 20000Hz (human hearing)
newtype Hertz = Hertz Number

derive instance eqHertz :: Eq Hertz
derive instance ordHertz :: Ord Hertz

instance showHertz :: Show Hertz where
  show (Hertz n) = show n <> " Hz"

-- | Create a Hertz value (clamped to non-negative)
hertz :: Number -> Hertz
hertz n
  | n < 0.0 = Hertz 0.0
  | otherwise = Hertz n

unwrapHertz :: Hertz -> Number
unwrapHertz (Hertz n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // kilohertz
-- ═════════════════════════════════════════════════════════════════════════════

-- | Kilohertz - frequency in thousands of cycles per second.
-- | Useful for higher frequencies and sample rates.
newtype Kilohertz = Kilohertz Number

derive instance eqKilohertz :: Eq Kilohertz
derive instance ordKilohertz :: Ord Kilohertz

instance showKilohertz :: Show Kilohertz where
  show (Kilohertz n) = show n <> " kHz"

-- | Create a Kilohertz value (clamped to non-negative)
kilohertz :: Number -> Kilohertz
kilohertz n
  | n < 0.0 = Kilohertz 0.0
  | otherwise = Kilohertz n

unwrapKilohertz :: Kilohertz -> Number
unwrapKilohertz (Kilohertz n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // midi note
-- ═════════════════════════════════════════════════════════════════════════════

-- | MidiNote - MIDI note number (0-127).
-- | 60 = Middle C (C4), 69 = A4 (440Hz reference).
-- | Each increment is one semitone.
newtype MidiNote = MidiNote Int

derive instance eqMidiNote :: Eq MidiNote
derive instance ordMidiNote :: Ord MidiNote

instance showMidiNote :: Show MidiNote where
  show (MidiNote n) = "MIDI " <> show n

-- | Create a MidiNote value (clamped to 0-127)
midiNote :: Int -> MidiNote
midiNote n
  | n < 0 = MidiNote 0
  | n > 127 = MidiNote 127
  | otherwise = MidiNote n

unwrapMidiNote :: MidiNote -> Int
unwrapMidiNote (MidiNote n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // midi pitch
-- ═════════════════════════════════════════════════════════════════════════════

-- | MidiPitch - MIDI note with fractional pitch bend.
-- | Allows micro-tonal precision (e.g., 60.5 = C4 + 50 cents).
-- | Clamped to [0.0, 127.99].
newtype MidiPitch = MidiPitch Number

derive instance eqMidiPitch :: Eq MidiPitch
derive instance ordMidiPitch :: Ord MidiPitch

instance showMidiPitch :: Show MidiPitch where
  show (MidiPitch n) = "MIDI " <> show n

-- | Create a MidiPitch value (clamped to 0.0-127.99)
midiPitch :: Number -> MidiPitch
midiPitch n
  | n < 0.0 = MidiPitch 0.0
  | n > 127.99 = MidiPitch 127.99
  | otherwise = MidiPitch n

unwrapMidiPitch :: MidiPitch -> Number
unwrapMidiPitch (MidiPitch n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // cent
-- ═════════════════════════════════════════════════════════════════════════════

-- | Cent - pitch offset in cents (1/100 of a semitone).
-- | Clamped to [-100, 100] for single-semitone adjustments.
-- | 100 cents = 1 semitone.
newtype Cent = Cent Number

derive instance eqCent :: Eq Cent
derive instance ordCent :: Ord Cent

instance showCent :: Show Cent where
  show (Cent n) = show n <> " cents"

-- | Create a Cent value (clamped to -100 to 100)
cent :: Number -> Cent
cent n
  | n < (-100.0) = Cent (-100.0)
  | n > 100.0 = Cent 100.0
  | otherwise = Cent n

unwrapCent :: Cent -> Number
unwrapCent (Cent n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // semitone
-- ═════════════════════════════════════════════════════════════════════════════

-- | Semitone - pitch offset in semitones (half steps).
-- | Clamped to [-12, 12] for single-octave adjustments.
-- | 12 semitones = 1 octave.
newtype Semitone = Semitone Number

derive instance eqSemitone :: Eq Semitone
derive instance ordSemitone :: Ord Semitone

instance showSemitone :: Show Semitone where
  show (Semitone n) = show n <> " semitones"

-- | Create a Semitone value (clamped to -12 to 12)
semitone :: Number -> Semitone
semitone n
  | n < (-12.0) = Semitone (-12.0)
  | n > 12.0 = Semitone 12.0
  | otherwise = Semitone n

unwrapSemitone :: Semitone -> Number
unwrapSemitone (Semitone n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // octave
-- ═════════════════════════════════════════════════════════════════════════════

-- | Octave - pitch offset in octaves.
-- | Clamped to [-10, 10] for practical range.
-- | 1 octave = 12 semitones = frequency × 2.
newtype Octave = Octave Number

derive instance eqOctave :: Eq Octave
derive instance ordOctave :: Ord Octave

instance showOctave :: Show Octave where
  show (Octave n) = show n <> " octaves"

-- | Create an Octave value (clamped to -10 to 10)
octave :: Number -> Octave
octave n
  | n < (-10.0) = Octave (-10.0)
  | n > 10.0 = Octave 10.0
  | otherwise = Octave n

unwrapOctave :: Octave -> Number
unwrapOctave (Octave n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // sample rate
-- ═════════════════════════════════════════════════════════════════════════════

-- | SampleRate - audio sample rate in Hz.
-- | Clamped to [8000, 192000] covering all practical rates.
-- | Common: 44100 (CD), 48000 (video), 96000 (hi-res).
newtype SampleRate = SampleRate Int

derive instance eqSampleRate :: Eq SampleRate
derive instance ordSampleRate :: Ord SampleRate

instance showSampleRate :: Show SampleRate where
  show (SampleRate n) = show n <> " Hz"

-- | Create a SampleRate value (clamped to 8000-192000)
sampleRate :: Int -> SampleRate
sampleRate n
  | n < 8000 = SampleRate 8000
  | n > 192000 = SampleRate 192000
  | otherwise = SampleRate n

unwrapSampleRate :: SampleRate -> Int
unwrapSampleRate (SampleRate n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // bit depth
-- ═════════════════════════════════════════════════════════════════════════════

-- | BitDepth - bits per sample.
-- | Clamped to [8, 32] covering all practical depths.
-- | Common: 16 (CD), 24 (professional), 32 (float).
newtype BitDepth = BitDepth Int

derive instance eqBitDepth :: Eq BitDepth
derive instance ordBitDepth :: Ord BitDepth

instance showBitDepth :: Show BitDepth where
  show (BitDepth n) = show n <> "-bit"

-- | Create a BitDepth value (clamped to 8-32)
bitDepth :: Int -> BitDepth
bitDepth n
  | n < 8 = BitDepth 8
  | n > 32 = BitDepth 32
  | otherwise = BitDepth n

unwrapBitDepth :: BitDepth -> Int
unwrapBitDepth (BitDepth n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // predefined frequencies
-- ═════════════════════════════════════════════════════════════════════════════

-- | A4 = 440Hz (concert pitch standard)
a4 :: Hertz
a4 = Hertz 440.0

-- | Middle C = C4 ≈ 261.63Hz (MIDI note 60)
middleC :: Hertz
middleC = Hertz 261.6255653005986

-- | Sub-bass frequency range lower bound (20Hz)
subBass :: Hertz
subBass = Hertz 20.0

-- | Bass frequency range lower bound (60Hz)
bass :: Hertz
bass = Hertz 60.0

-- | Midrange frequency (1000Hz)
midrange :: Hertz
midrange = Hertz 1000.0

-- | Presence frequency range (4000Hz)
presence :: Hertz
presence = Hertz 4000.0

-- | Brilliance/air frequency range (10000Hz)
brilliance :: Hertz
brilliance = Hertz 10000.0

-- | Nyquist frequency for CD audio (22050Hz)
nyquistCD :: Hertz
nyquistCD = Hertz 22050.0

-- | Nyquist frequency for 48kHz audio (24000Hz)
nyquist48k :: Hertz
nyquist48k = Hertz 24000.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // predefined sample rates
-- ═════════════════════════════════════════════════════════════════════════════

-- | CD quality sample rate
rate44100 :: SampleRate
rate44100 = SampleRate 44100

-- | Video/broadcast standard sample rate
rate48000 :: SampleRate
rate48000 = SampleRate 48000

-- | Double CD rate (high resolution)
rate88200 :: SampleRate
rate88200 = SampleRate 88200

-- | Double video rate (high resolution)
rate96000 :: SampleRate
rate96000 = SampleRate 96000

-- | Maximum common sample rate
rate192000 :: SampleRate
rate192000 = SampleRate 192000

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // predefined bit depths
-- ═════════════════════════════════════════════════════════════════════════════

-- | 8-bit audio (lo-fi, games)
bit8 :: BitDepth
bit8 = BitDepth 8

-- | 16-bit audio (CD quality)
bit16 :: BitDepth
bit16 = BitDepth 16

-- | 24-bit audio (professional standard)
bit24 :: BitDepth
bit24 = BitDepth 24

-- | 32-bit float audio (mixing/mastering)
bit32 :: BitDepth
bit32 = BitDepth 32

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // conversions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert MIDI note to frequency in Hz.
-- | Formula: 440 * 2^((note - 69) / 12)
midiToHertz :: MidiNote -> Hertz
midiToHertz (MidiNote n) =
  let noteNum = Int.toNumber n
  in Hertz (440.0 * Math.pow 2.0 ((noteNum - 69.0) / 12.0))

-- | Convert frequency to nearest MIDI note.
-- | Formula: round(12 * log2(freq / 440) + 69)
-- | Returns Nothing if frequency is non-positive.
hertzToMidi :: Hertz -> Maybe MidiNote
hertzToMidi (Hertz f)
  | f <= 0.0 = Nothing
  | otherwise =
      let noteNum = Math.round (12.0 * Math.log2 (f / 440.0) + 69.0)
          clamped = Int.round noteNum
      in Just (midiNote clamped)

-- | Convert MIDI pitch (with fractional part) to frequency.
-- | Allows microtonal precision.
midiPitchToHertz :: MidiPitch -> Hertz
midiPitchToHertz (MidiPitch p) =
  Hertz (440.0 * Math.pow 2.0 ((p - 69.0) / 12.0))

-- | Convert frequency to precise MIDI pitch.
-- | Returns Nothing if frequency is non-positive.
hertzToMidiPitch :: Hertz -> Maybe MidiPitch
hertzToMidiPitch (Hertz f)
  | f <= 0.0 = Nothing
  | otherwise =
      let pitch = 12.0 * Math.log2 (f / 440.0) + 69.0
      in Just (midiPitch pitch)

-- | Convert Hertz to Kilohertz
hertzToKilohertz :: Hertz -> Kilohertz
hertzToKilohertz (Hertz f) = Kilohertz (f / 1000.0)

-- | Convert Kilohertz to Hertz
kilohertzToHertz :: Kilohertz -> Hertz
kilohertzToHertz (Kilohertz k) = Hertz (k * 1000.0)

-- | Convert cents to semitones (100 cents = 1 semitone)
centsToSemitones :: Cent -> Semitone
centsToSemitones (Cent c) = semitone (c / 100.0)

-- | Convert semitones to cents
semitonesToCents :: Semitone -> Cent
semitonesToCents (Semitone s) = cent (s * 100.0)

-- | Convert semitones to octaves (12 semitones = 1 octave)
semitonesToOctaves :: Semitone -> Octave
semitonesToOctaves (Semitone s) = octave (s / 12.0)

-- | Convert octaves to semitones
octavesToSemitones :: Octave -> Semitone
octavesToSemitones (Octave o) = semitone (o * 12.0)

-- | Convert cents to frequency ratio.
-- | Formula: 2^(cents / 1200)
centsToRatio :: Cent -> Number
centsToRatio (Cent c) = Math.pow 2.0 (c / 1200.0)

-- | Convert frequency ratio to cents.
-- | Formula: 1200 * log2(ratio)
ratioToCents :: Number -> Cent
ratioToCents ratio
  | ratio <= 0.0 = Cent 0.0
  | otherwise = cent (1200.0 * Math.log2 ratio)

-- | Convert semitones to frequency ratio.
-- | Formula: 2^(semitones / 12)
semitonesToRatio :: Semitone -> Number
semitonesToRatio (Semitone s) = Math.pow 2.0 (s / 12.0)

-- | Convert frequency ratio to semitones.
-- | Formula: 12 * log2(ratio)
ratioToSemitones :: Number -> Semitone
ratioToSemitones ratio
  | ratio <= 0.0 = Semitone 0.0
  | otherwise = semitone (12.0 * Math.log2 ratio)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Transpose a frequency by octaves.
-- | Positive = higher, negative = lower.
transposeByOctave :: Octave -> Hertz -> Hertz
transposeByOctave (Octave o) (Hertz f) =
  hertz (f * Math.pow 2.0 o)

-- | Transpose a frequency by semitones.
transposeBySemitone :: Semitone -> Hertz -> Hertz
transposeBySemitone (Semitone s) (Hertz f) =
  hertz (f * Math.pow 2.0 (s / 12.0))

-- | Transpose a frequency by cents.
transposeByCent :: Cent -> Hertz -> Hertz
transposeByCent (Cent c) (Hertz f) =
  hertz (f * Math.pow 2.0 (c / 1200.0))

-- | Calculate the frequency ratio between two frequencies.
-- | Result is f2/f1. Returns 0 if f1 is zero.
frequencyRatio :: Hertz -> Hertz -> Number
frequencyRatio (Hertz f1) (Hertz f2)
  | f1 <= 0.0 = 0.0
  | otherwise = f2 / f1

-- | Calculate the interval in cents between two frequencies.
intervalInCents :: Hertz -> Hertz -> Cent
intervalInCents (Hertz f1) (Hertz f2)
  | f1 <= 0.0 = Cent 0.0
  | f2 <= 0.0 = Cent 0.0
  | otherwise = cent (1200.0 * Math.log2 (f2 / f1))

-- | Calculate the interval in semitones between two frequencies.
intervalInSemitones :: Hertz -> Hertz -> Semitone
intervalInSemitones (Hertz f1) (Hertz f2)
  | f1 <= 0.0 = Semitone 0.0
  | f2 <= 0.0 = Semitone 0.0
  | otherwise = semitone (12.0 * Math.log2 (f2 / f1))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // note names
-- ═════════════════════════════════════════════════════════════════════════════

-- | Musical note names (chromatic scale)
data NoteName
  = C
  | CSharp
  | D
  | DSharp
  | E
  | F
  | FSharp
  | G
  | GSharp
  | A
  | ASharp
  | B

derive instance eqNoteName :: Eq NoteName
derive instance ordNoteName :: Ord NoteName

instance showNoteName :: Show NoteName where
  show n = noteNameToString n

-- | All note names for enumeration (chromatic scale)
allNoteNames :: Array NoteName
allNoteNames = [ C, CSharp, D, DSharp, E, F, FSharp, G, GSharp, A, ASharp, B ]

-- | Convert note name to string representation
noteNameToString :: NoteName -> String
noteNameToString C = "C"
noteNameToString CSharp = "C#"
noteNameToString D = "D"
noteNameToString DSharp = "D#"
noteNameToString E = "E"
noteNameToString F = "F"
noteNameToString FSharp = "F#"
noteNameToString G = "G"
noteNameToString GSharp = "G#"
noteNameToString A = "A"
noteNameToString ASharp = "A#"
noteNameToString B = "B"

-- | Get the note name from a MIDI note number
midiToNoteName :: MidiNote -> NoteName
midiToNoteName (MidiNote n) =
  case n `mod` 12 of
    0 -> C
    1 -> CSharp
    2 -> D
    3 -> DSharp
    4 -> E
    5 -> F
    6 -> FSharp
    7 -> G
    8 -> GSharp
    9 -> A
    10 -> ASharp
    _ -> B  -- 11

-- | Get the octave number from a MIDI note number.
-- | MIDI 0-11 = octave -1, 12-23 = octave 0, 60-71 = octave 4
midiToOctaveNumber :: MidiNote -> Int
midiToOctaveNumber (MidiNote n) = (n / 12) - 1

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds for Hertz (practical audio range)
-- |
-- | Min: 0.0
-- | Max: 20000.0 (human hearing upper limit)
hertzBounds :: Bounded.NumberBounds
hertzBounds = Bounded.numberBounds 0.0 20000.0 "hertz" "Frequency in Hz (0-20000)"

-- | Bounds for Kilohertz
-- |
-- | Min: 0.0
-- | Max: 200.0 (20kHz = 0.2kHz for audio, higher for RF)
kilohertzBounds :: Bounded.NumberBounds
kilohertzBounds = Bounded.numberBounds 0.0 200.0 "kilohertz" "Frequency in kHz (0-200)"

-- | Bounds for MidiNote
-- |
-- | Min: 0
-- | Max: 127
midiNoteBounds :: Bounded.IntBounds
midiNoteBounds = Bounded.intBounds 0 127 "midiNote" "MIDI note number (0-127)"

-- | Bounds for MidiPitch
-- |
-- | Min: 0.0
-- | Max: 127.99
midiPitchBounds :: Bounded.NumberBounds
midiPitchBounds = Bounded.numberBounds 0.0 127.99 "midiPitch" "MIDI pitch with microtonal (0-127.99)"

-- | Bounds for Cent
-- |
-- | Min: -100.0 (one semitone down)
-- | Max: 100.0 (one semitone up)
centBounds :: Bounded.NumberBounds
centBounds = Bounded.numberBounds (-100.0) 100.0 "cent" "Pitch offset in cents (-100 to 100)"

-- | Bounds for Semitone
-- |
-- | Min: -12.0 (one octave down)
-- | Max: 12.0 (one octave up)
semitoneBounds :: Bounded.NumberBounds
semitoneBounds = Bounded.numberBounds (-12.0) 12.0 "semitone" "Pitch offset in semitones (-12 to 12)"

-- | Bounds for Octave
-- |
-- | Min: -10.0
-- | Max: 10.0
octaveBounds :: Bounded.NumberBounds
octaveBounds = Bounded.numberBounds (-10.0) 10.0 "octave" "Pitch offset in octaves (-10 to 10)"

-- | Bounds for SampleRate
-- |
-- | Min: 8000 (telephony)
-- | Max: 192000 (high-resolution audio)
sampleRateBounds :: Bounded.IntBounds
sampleRateBounds = Bounded.intBounds 8000 192000 "sampleRate" "Audio sample rate in Hz (8000-192000)"

-- | Bounds for BitDepth
-- |
-- | Min: 8 (lo-fi)
-- | Max: 32 (float)
bitDepthBounds :: Bounded.IntBounds
bitDepthBounds = Bounded.intBounds 8 32 "bitDepth" "Bits per sample (8-32)"
