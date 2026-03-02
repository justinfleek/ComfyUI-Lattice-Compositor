-- | Lattice.Services.Midi.Service - MIDI configuration types
-- |
-- | Pure types representing MIDI configuration and requests.
-- | Actual Web MIDI API interaction is delegated to the runtime or backend.
-- |
-- | Source: ui/src/services/midi/MIDIService.ts (service section)

module Lattice.Services.Midi.Service
  ( -- * Service Configuration
    MIDIServiceConfig
  , defaultMIDIConfig
    -- * Request Types
  , MIDIRequest(..)
  , MIDIDeviceRequest(..)
  , MIDIListenerRequest(..)
  , MIDISendRequest(..)
    -- * Pure Functions
  , matchesFilter
  , calculateMappedValue
  , buildNoteOnMessage
  , buildNoteOffMessage
  , buildCCMessage
    -- * Re-exports
  , module Lattice.Services.Midi.Types
  ) where

import Prelude
import Data.Array (elem)
import Data.Int (toNumber)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

import Lattice.Services.Midi.Types
  ( MIDIMessage
  , MIDIMessageType(..)
  , MIDIDeviceInfo
  , MIDIDeviceType(..)
  , MIDIFilter
  , MIDIMapping
  )

-- | MIDI service configuration
-- |
-- | Pure configuration for MIDI service behavior.
type MIDIServiceConfig =
  { historySize :: Int           -- Maximum messages to keep in history
  , smoothingDefault :: Number   -- Default smoothing factor (0-1)
  , autoConnect :: Boolean       -- Auto-connect to devices on init
  }

-- | Default MIDI configuration
defaultMIDIConfig :: MIDIServiceConfig
defaultMIDIConfig =
  { historySize: 100
  , smoothingDefault: 0.1
  , autoConnect: true
  }

-- | MIDI device requests
data MIDIDeviceRequest
  = ListDevices
  | ListInputDevices
  | ListOutputDevices

derive instance Eq MIDIDeviceRequest
derive instance Generic MIDIDeviceRequest _
instance Show MIDIDeviceRequest where show = genericShow

-- | MIDI listener requests
data MIDIListenerRequest
  = AddGlobalListener String      -- Listener ID
  | RemoveGlobalListener String   -- Listener ID
  | AddDeviceListener String String  -- Device ID, Listener ID
  | RemoveDeviceListener String String
  | AddFilteredListener String MIDIFilter  -- Listener ID, Filter

derive instance Eq MIDIListenerRequest
derive instance Generic MIDIListenerRequest _
instance Show MIDIListenerRequest where show = genericShow

-- | MIDI send requests
data MIDISendRequest
  = SendRaw String (Array Int)    -- Device ID, raw bytes
  | SendNoteOn String Int Int Int -- Device ID, channel, note, velocity
  | SendNoteOff String Int Int Int
  | SendCC String Int Int Int     -- Device ID, channel, controller, value

derive instance Eq MIDISendRequest
derive instance Generic MIDISendRequest _
instance Show MIDISendRequest where show = genericShow

-- | Top-level MIDI request
-- |
-- | Send these to the runtime/backend for execution.
data MIDIRequest
  = Initialize
  | Dispose
  | DeviceReq MIDIDeviceRequest
  | ListenerReq MIDIListenerRequest
  | SendReq MIDISendRequest
  | GetCCValue Int Int            -- Channel, Controller
  | GetNoteState Int Int          -- Channel, Note
  | GetHeldNotes
  | GetMessageHistory (Maybe Int) -- Limit

derive instance Eq MIDIRequest
derive instance Generic MIDIRequest _
instance Show MIDIRequest where show = genericShow

-- | Check if a message passes a filter (pure function)
matchesFilter :: MIDIMessage -> MIDIFilter -> Boolean
matchesFilter msg midiFilter =
  channelMatches && typeMatches && noteMatches && velocityMatches && controllerMatches
  where
    -- Channel filter
    channelMatches = case midiFilter.channels of
      Nothing -> true
      Just channels -> msg.channel `elem` channels

    -- Type filter
    typeMatches = case midiFilter.types of
      Nothing -> true
      Just types -> msg.msgType `elem` types

    -- Note range filter
    noteMatches = case midiFilter.noteRange of
      Nothing -> true
      Just range -> case msg.note of
        Nothing -> true
        Just n -> n >= range.min && n <= range.max

    -- Velocity range filter
    velocityMatches = case midiFilter.velocityRange of
      Nothing -> true
      Just range -> case msg.velocity of
        Nothing -> true
        Just v -> v >= range.min && v <= range.max

    -- Controller filter
    controllerMatches = case midiFilter.controllers of
      Nothing -> true
      Just controllers -> case msg.controller of
        Nothing -> true
        Just c -> c `elem` controllers

-- | Calculate mapped value from MIDI input (pure function)
-- |
-- | @param mapping The MIDI mapping configuration
-- | @param inputValue The raw input value (0-127 for most MIDI)
-- | @param currentSmoothed The current smoothed value (for smoothing)
-- | @returns The mapped and smoothed output value
calculateMappedValue :: MIDIMapping -> Number -> Number -> Number
calculateMappedValue mapping inputValue currentSmoothed =
  let
    -- Normalize input to 0-1 range
    normalizedInput = (inputValue - toNumber mapping.inputMin) /
                      (toNumber mapping.inputMax - toNumber mapping.inputMin)
    clampedInput = max 0.0 (min 1.0 normalizedInput)

    -- Map to output range
    rawOutput = mapping.outputMin + clampedInput * (mapping.outputMax - mapping.outputMin)

    -- Apply smoothing
    smoothedOutput = currentSmoothed + (rawOutput - currentSmoothed) * (1.0 - mapping.smoothing)
  in
    smoothedOutput

-- | Build Note On MIDI message bytes
buildNoteOnMessage :: Int -> Int -> Int -> Array Int
buildNoteOnMessage channel note velocity =
  let status = 0x90 + (channel - 1)
  in [status, note, velocity]

-- | Build Note Off MIDI message bytes
buildNoteOffMessage :: Int -> Int -> Int -> Array Int
buildNoteOffMessage channel note velocity =
  let status = 0x80 + (channel - 1)
  in [status, note, velocity]

-- | Build Control Change MIDI message bytes
buildCCMessage :: Int -> Int -> Int -> Array Int
buildCCMessage channel controller value =
  let status = 0xB0 + (channel - 1)
  in [status, controller, value]

-- | Helper: max for Number
max :: Number -> Number -> Number
max a b = if a > b then a else b

-- | Helper: min for Number
min :: Number -> Number -> Number
min a b = if a < b then a else b
