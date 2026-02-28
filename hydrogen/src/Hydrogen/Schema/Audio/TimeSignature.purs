-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // schema // audio // time signature
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Musical time signatures and tempo.
-- |
-- | ## TimeSignature
-- | Defines beats per bar and beat note value.
-- | Common signatures: 4/4, 3/4, 6/8, etc.
-- |
-- | ## Tempo
-- | Beats per minute (BPM) for musical timing.

module Hydrogen.Schema.Audio.TimeSignature
  ( -- * Time Signature
    TimeSignature(..)
  , timeSignature
  , timeSignatureNumerator
  , timeSignatureDenominator
  , timeSignatureLabel
  
  -- * Common Time Signatures
  , time4_4
  , time3_4
  , time2_4
  , time6_8
  , time5_4
  , time7_8
  , time9_8
  , time12_8
  , timeFree
  
  -- * Tempo
  , Tempo(..)
  , tempo
  , unwrapTempo
  , tempoBounds
  
  -- * Common Tempos
  , tempoLargo
  , tempoAdagio
  , tempoAndante
  , tempoModerato
  , tempoAllegro
  , tempoPresto
  
  -- * Musical Position
  , MusicalPosition
  , musicalPosition
  , positionBar
  , positionBeat
  , positionTick
  
  -- * Tick Resolution
  , TicksPerBeat(..)
  , ticksPerBeat
  , unwrapTicksPerBeat
  , ppq96
  , ppq480
  , ppq960
  
  -- * Time Conversion
  , beatsToMs
  , msToBeats
  , barsToBeats
  , beatsToBarPosition
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , (<>)
  , (<=)
  , (*)
  , (/)
  , (+)
  , max
  , min
  , mod
  )

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // time signature
-- ═════════════════════════════════════════════════════════════════════════════

-- | TimeSignature - musical time signature.
-- | Numerator is beats per bar, denominator is note value that gets one beat.
data TimeSignature
  = TimeSignature Int Int   -- ^ numerator / denominator
  | TimeFree                -- ^ Free time (rubato, no fixed meter)

derive instance eqTimeSignature :: Eq TimeSignature
derive instance ordTimeSignature :: Ord TimeSignature

instance showTimeSignature :: Show TimeSignature where
  show ts = "(TimeSignature " <> timeSignatureLabel ts <> ")"

-- | Construct a time signature with validation.
timeSignature :: Int -> Int -> TimeSignature
timeSignature num denom =
  let validNum = max 1 (min 32 num)
      validDenom = nearestPowerOf2 (max 1 (min 32 denom))
  in TimeSignature validNum validDenom

-- | Get numerator (beats per bar).
timeSignatureNumerator :: TimeSignature -> Int
timeSignatureNumerator TimeFree = 0
timeSignatureNumerator (TimeSignature n _) = n

-- | Get denominator (note value).
timeSignatureDenominator :: TimeSignature -> Int
timeSignatureDenominator TimeFree = 0
timeSignatureDenominator (TimeSignature _ d) = d

-- | Get display label.
timeSignatureLabel :: TimeSignature -> String
timeSignatureLabel TimeFree = "Free"
timeSignatureLabel (TimeSignature n d) = show n <> "/" <> show d

-- | Find nearest power of 2 (for valid denominators: 1, 2, 4, 8, 16, 32).
nearestPowerOf2 :: Int -> Int
nearestPowerOf2 x
  | x <= 1 = 1
  | x <= 2 = 2
  | x <= 4 = 4
  | x <= 8 = 8
  | x <= 16 = 16
  | otherwise = 32

-- | 4/4 - Common time
time4_4 :: TimeSignature
time4_4 = TimeSignature 4 4

-- | 3/4 - Waltz time
time3_4 :: TimeSignature
time3_4 = TimeSignature 3 4

-- | 2/4 - March time
time2_4 :: TimeSignature
time2_4 = TimeSignature 2 4

-- | 6/8 - Compound duple
time6_8 :: TimeSignature
time6_8 = TimeSignature 6 8

-- | 5/4 - Odd meter
time5_4 :: TimeSignature
time5_4 = TimeSignature 5 4

-- | 7/8 - Odd meter
time7_8 :: TimeSignature
time7_8 = TimeSignature 7 8

-- | 9/8 - Compound triple
time9_8 :: TimeSignature
time9_8 = TimeSignature 9 8

-- | 12/8 - Compound quadruple
time12_8 :: TimeSignature
time12_8 = TimeSignature 12 8

-- | Free time (rubato)
timeFree :: TimeSignature
timeFree = TimeFree

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // tempo
-- ═════════════════════════════════════════════════════════════════════════════

-- | Tempo - beats per minute.
-- | Bounded to 20-400 BPM for practical musical tempos.
newtype Tempo = Tempo Number

derive instance eqTempo :: Eq Tempo
derive instance ordTempo :: Ord Tempo

instance showTempo :: Show Tempo where
  show (Tempo t) = "(Tempo " <> show t <> " BPM)"

-- | Bounds for tempo.
tempoBounds :: Bounded.NumberBounds
tempoBounds = Bounded.numberBounds 20.0 400.0 "Tempo" "Beats per minute"

-- | Construct a bounded tempo.
tempo :: Number -> Tempo
tempo t = Tempo (Bounded.clampNumber 20.0 400.0 t)

-- | Unwrap tempo.
unwrapTempo :: Tempo -> Number
unwrapTempo (Tempo t) = t

-- | Largo: ~50 BPM
tempoLargo :: Tempo
tempoLargo = Tempo 50.0

-- | Adagio: ~70 BPM
tempoAdagio :: Tempo
tempoAdagio = Tempo 70.0

-- | Andante: ~90 BPM
tempoAndante :: Tempo
tempoAndante = Tempo 90.0

-- | Moderato: ~110 BPM
tempoModerato :: Tempo
tempoModerato = Tempo 110.0

-- | Allegro: ~140 BPM
tempoAllegro :: Tempo
tempoAllegro = Tempo 140.0

-- | Presto: ~180 BPM
tempoPresto :: Tempo
tempoPresto = Tempo 180.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // ticks per beat
-- ═════════════════════════════════════════════════════════════════════════════

-- | TicksPerBeat - MIDI-style tick resolution.
-- | PPQ (Pulses Per Quarter note) for sub-beat precision.
newtype TicksPerBeat = TicksPerBeat Int

derive instance eqTicksPerBeat :: Eq TicksPerBeat
derive instance ordTicksPerBeat :: Ord TicksPerBeat

instance showTicksPerBeat :: Show TicksPerBeat where
  show (TicksPerBeat t) = "(TicksPerBeat " <> show t <> " PPQ)"

-- | Construct ticks per beat.
ticksPerBeat :: Int -> TicksPerBeat
ticksPerBeat t = TicksPerBeat (max 24 (min 960 t))

-- | Unwrap ticks per beat.
unwrapTicksPerBeat :: TicksPerBeat -> Int
unwrapTicksPerBeat (TicksPerBeat t) = t

-- | 96 PPQ - Basic resolution
ppq96 :: TicksPerBeat
ppq96 = TicksPerBeat 96

-- | 480 PPQ - Standard MIDI resolution
ppq480 :: TicksPerBeat
ppq480 = TicksPerBeat 480

-- | 960 PPQ - High resolution
ppq960 :: TicksPerBeat
ppq960 = TicksPerBeat 960

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // musical position
-- ═════════════════════════════════════════════════════════════════════════════

-- | MusicalPosition - position in bars, beats, and ticks.
type MusicalPosition =
  { bar :: Int          -- 1-indexed bar number
  , beat :: Int         -- 1-indexed beat within bar
  , tick :: Int         -- 0-indexed tick within beat
  }

-- | Construct a musical position.
musicalPosition :: Int -> Int -> Int -> MusicalPosition
musicalPosition b bt t =
  { bar: max 1 b
  , beat: max 1 bt
  , tick: max 0 t
  }

-- | Get bar number.
positionBar :: MusicalPosition -> Int
positionBar p = p.bar

-- | Get beat number.
positionBeat :: MusicalPosition -> Int
positionBeat p = p.beat

-- | Get tick number.
positionTick :: MusicalPosition -> Int
positionTick p = p.tick

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // time conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert beats to milliseconds at given tempo.
beatsToMs :: Tempo -> Number -> Number
beatsToMs (Tempo bpm) beats =
  (beats * 60000.0) / bpm

-- | Convert milliseconds to beats at given tempo.
msToBeats :: Tempo -> Number -> Number
msToBeats (Tempo bpm) ms =
  (ms * bpm) / 60000.0

-- | Convert bars to beats given time signature.
barsToBeats :: TimeSignature -> Int -> Int
barsToBeats TimeFree _ = 0
barsToBeats (TimeSignature num _) bars = bars * num

-- | Convert total beats to bar/beat position.
beatsToBarPosition :: TimeSignature -> Int -> { bar :: Int, beat :: Int }
beatsToBarPosition TimeFree totalBeats = { bar: 1, beat: totalBeats + 1 }
beatsToBarPosition (TimeSignature num _) totalBeats =
  { bar: (totalBeats / num) + 1
  , beat: (totalBeats `mod` num) + 1
  }
