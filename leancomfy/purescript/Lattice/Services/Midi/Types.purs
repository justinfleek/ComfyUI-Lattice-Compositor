-- | Lattice.Services.Midi.Types - MIDI types and message parsing
-- |
-- | Pure types and message parsing for Web MIDI API integration.
-- | No FFI required - just data types and pure functions.
-- |
-- | Source: ui/src/services/midi/MIDIService.ts (types section)

module Lattice.Services.Midi.Types
  ( -- * Device Types
    MIDIDeviceInfo
  , MIDIDeviceType(..)
  , MIDIDeviceState(..)
    -- * Message Types
  , MIDIMessage
  , MIDIMessageType(..)
  , MIDIRawData
    -- * Filter Types
  , MIDIFilter
  , NoteRange
  , VelocityRange
    -- * Mapping Types
  , MIDIMapping
  , MappingMode(..)
    -- * Parsing
  , parseMIDIStatus
  , midiNoteToName
  , noteNameToMidi
  , ccToNormalized
  , normalizedToCC
    -- * Constants
  , noteNames
  , noteNameToSemitone
  ) where

import Prelude
import Data.Array (index, length, filter)
import Data.Int (floor, toNumber, round)
import Data.Int.Bits ((.&.), (.|.), shr, shl)
import Data.Maybe (Maybe(..))
import Data.String (Pattern(..), split, toUpper)
import Data.String.CodeUnits (take, drop)
import Data.String.Regex (regex, match)
import Data.String.Regex.Flags (ignoreCase)
import Foreign.Object (Object)
import Foreign.Object as Obj
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

--------------------------------------------------------------------------------
-- Device Types
--------------------------------------------------------------------------------

-- | MIDI device type
data MIDIDeviceType = MIDIInput | MIDIOutput

derive instance Eq MIDIDeviceType
derive instance Generic MIDIDeviceType _
instance Show MIDIDeviceType where show = genericShow

-- | MIDI device state
data MIDIDeviceState = MIDIConnected | MIDIDisconnected

derive instance Eq MIDIDeviceState
derive instance Generic MIDIDeviceState _
instance Show MIDIDeviceState where show = genericShow

-- | MIDI device information
type MIDIDeviceInfo =
  { id :: String
  , name :: String
  , manufacturer :: String
  , deviceType :: MIDIDeviceType
  , state :: MIDIDeviceState
  }

--------------------------------------------------------------------------------
-- Message Types
--------------------------------------------------------------------------------

-- | MIDI message type
data MIDIMessageType
  = NoteOn
  | NoteOff
  | ControlChange
  | ProgramChange
  | PitchBend
  | Aftertouch
  | ChannelPressure
  | SystemMessage

derive instance Eq MIDIMessageType
derive instance Generic MIDIMessageType _
instance Show MIDIMessageType where show = genericShow

-- | Raw MIDI data bytes
type MIDIRawData = Array Int

-- | Parsed MIDI message
type MIDIMessage =
  { timestamp :: Number
  , msgType :: MIDIMessageType
  , channel :: Int              -- 1-16
  , note :: Maybe Int           -- 0-127 for note events
  , velocity :: Maybe Int       -- 0-127 for note events
  , controller :: Maybe Int     -- 0-127 for CC events
  , value :: Maybe Int          -- 0-127 for CC, 0-16383 for pitch bend
  , program :: Maybe Int        -- 0-127 for program change
  , raw :: MIDIRawData
  }

--------------------------------------------------------------------------------
-- Filter Types
--------------------------------------------------------------------------------

-- | Note range for filtering
type NoteRange = { min :: Int, max :: Int }

-- | Velocity range for filtering
type VelocityRange = { min :: Int, max :: Int }

-- | MIDI message filter
type MIDIFilter =
  { channels :: Maybe (Array Int)           -- 1-16, Nothing = all
  , types :: Maybe (Array MIDIMessageType)
  , noteRange :: Maybe NoteRange            -- 0-127
  , velocityRange :: Maybe VelocityRange    -- 0-127
  , controllers :: Maybe (Array Int)        -- Specific CC numbers
  }

--------------------------------------------------------------------------------
-- Mapping Types
--------------------------------------------------------------------------------

-- | Mapping mode
data MappingMode
  = ModeAbsolute
  | ModeRelative
  | ModeToggle
  | ModeTrigger

derive instance Eq MappingMode
derive instance Generic MappingMode _
instance Show MappingMode where show = genericShow

-- | MIDI to property mapping configuration
type MIDIMapping =
  { id :: String
  , enabled :: Boolean
  , deviceId :: String
  , midiFilter :: MIDIFilter
  -- Target
  , targetLayerId :: String
  , targetPropertyPath :: String
  -- Transform
  , inputMin :: Int             -- 0-127
  , inputMax :: Int             -- 0-127
  , outputMin :: Number
  , outputMax :: Number
  , smoothing :: Number         -- 0-1
  -- Mode
  , mode :: MappingMode
  -- For note events
  , useVelocity :: Boolean
  , useNoteNumber :: Boolean
  }

--------------------------------------------------------------------------------
-- Message Parsing
--------------------------------------------------------------------------------

-- | Parse MIDI status byte into message type and channel
parseMIDIStatus :: Int -> { msgType :: MIDIMessageType, channel :: Int }
parseMIDIStatus status =
  let messageType = status .&. 0xF0
      channel = (status .&. 0x0F) + 1  -- MIDI channels are 1-16
  in { msgType: statusToType messageType, channel }

-- | Convert status byte to message type
statusToType :: Int -> MIDIMessageType
statusToType status = case status of
  0x90 -> NoteOn       -- Note On (velocity 0 handled at message level)
  0x80 -> NoteOff      -- Note Off
  0xB0 -> ControlChange
  0xC0 -> ProgramChange
  0xE0 -> PitchBend
  0xA0 -> Aftertouch   -- Polyphonic aftertouch
  0xD0 -> ChannelPressure
  0xF0 -> SystemMessage
  _    -> SystemMessage

-- | Create empty filter (matches all messages)
emptyFilter :: MIDIFilter
emptyFilter =
  { channels: Nothing
  , types: Nothing
  , noteRange: Nothing
  , velocityRange: Nothing
  , controllers: Nothing
  }

--------------------------------------------------------------------------------
-- Note Name Conversion
--------------------------------------------------------------------------------

-- | Note names (C through B)
noteNames :: Array String
noteNames = ["C", "C#", "D", "D#", "E", "F", "F#", "G", "G#", "A", "A#", "B"]

-- | Note name to semitone (0-11)
noteNameToSemitone :: Object Int
noteNameToSemitone = Obj.fromFoldable
  [ { key: "C", value: 0 }
  , { key: "C#", value: 1 }
  , { key: "D", value: 2 }
  , { key: "D#", value: 3 }
  , { key: "E", value: 4 }
  , { key: "F", value: 5 }
  , { key: "F#", value: 6 }
  , { key: "G", value: 7 }
  , { key: "G#", value: 8 }
  , { key: "A", value: 9 }
  , { key: "A#", value: 10 }
  , { key: "B", value: 11 }
  ]

-- | Convert MIDI note number to note name
-- | Note 60 = C4 (middle C)
midiNoteToName :: Int -> String
midiNoteToName note =
  let octave = (note / 12) - 1
      nameIndex = note `mod` 12
      name = case index noteNames nameIndex of
        Just n -> n
        Nothing -> "?"
  in name <> show octave

-- | Convert note name to MIDI note number
-- | Returns Nothing for invalid note names
noteNameToMidi :: String -> Maybe Int
noteNameToMidi name =
  case parseNoteName name of
    Nothing -> Nothing
    Just { noteName, octave } ->
      case Obj.lookup (toUpper noteName) noteNameToSemitone of
        Nothing -> Nothing
        Just semitone -> Just ((octave + 1) * 12 + semitone)

-- | Parse note name like "C4" or "C#-1"
parseNoteName :: String -> Maybe { noteName :: String, octave :: Int }
parseNoteName name =
  -- Pattern: note (C-G, optional #) followed by octave (-1 to 9)
  case regex "^([A-Ga-g]#?)(-?[0-9])$" ignoreCase of
    Left _ -> Nothing
    Right r -> case match r name of
      Just matches -> do
        noteName <- join (index matches 1)
        octaveStr <- join (index matches 2)
        octave <- parseOctave octaveStr
        Just { noteName, octave }
      Nothing -> Nothing

-- | Parse octave string to int
parseOctave :: String -> Maybe Int
parseOctave s = case s of
  "-1" -> Just (-1)
  "0" -> Just 0
  "1" -> Just 1
  "2" -> Just 2
  "3" -> Just 3
  "4" -> Just 4
  "5" -> Just 5
  "6" -> Just 6
  "7" -> Just 7
  "8" -> Just 8
  "9" -> Just 9
  _ -> Nothing

--------------------------------------------------------------------------------
-- Value Conversion
--------------------------------------------------------------------------------

-- | Convert CC value (0-127) to normalized (0-1)
ccToNormalized :: Int -> Number
ccToNormalized value = toNumber value / 127.0

-- | Convert normalized (0-1) to CC value (0-127)
normalizedToCC :: Number -> Int
normalizedToCC value = round (value * 127.0)

--------------------------------------------------------------------------------
-- Internal Helpers
--------------------------------------------------------------------------------

-- | Integer division
div :: Int -> Int -> Int
div a b = floor (toNumber a / toNumber b)

-- | Modulo
mod :: Int -> Int -> Int
mod a b = a - (a `div` b) * b

-- | Join Maybe Maybe into Maybe
join :: forall a. Maybe (Maybe a) -> Maybe a
join Nothing = Nothing
join (Just ma) = ma
