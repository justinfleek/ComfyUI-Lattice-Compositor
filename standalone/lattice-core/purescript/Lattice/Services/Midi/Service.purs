-- | Lattice.Services.Midi.Service - MIDI service with Web MIDI API
-- |
-- | Browser integration for MIDI device capture, message filtering, and property mapping.
-- | Uses Web MIDI API via FFI.
-- |
-- | Source: ui/src/services/midi/MIDIService.ts (service section)

module Lattice.Services.Midi.Service
  ( -- * Service
    MIDIService
  , getMIDIService
  , disposeMIDIService
    -- * Initialization
  , initialize
  , isAvailable
  , isReady
    -- * Device Management
  , getDevices
  , getInputDevices
  , getOutputDevices
    -- * Listeners
  , addGlobalListener
  , removeGlobalListener
  , addDeviceListener
  , removeDeviceListener
  , addFilteredListener
    -- * Value Access
  , getCCValue
  , getNoteState
  , isNoteOn
  , getHeldNotes
  , getMessageHistory
    -- * Mapping
  , getMappedValue
  , matchesFilter
    -- * Output
  , sendMessage
  , sendNoteOn
  , sendNoteOff
  , sendCC
  ) where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Data.Array (filter, elem, length)
import Data.Int (toNumber)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Tuple (Tuple(..))

import Lattice.Services.Midi.Types
  ( MIDIMessage
  , MIDIMessageType(..)
  , MIDIDeviceInfo
  , MIDIDeviceType(..)
  , MIDIFilter
  , MIDIMapping
  )

--------------------------------------------------------------------------------
-- FFI Types
--------------------------------------------------------------------------------

-- | Opaque MIDI service handle
foreign import data MIDIServiceHandle :: Type

-- | MIDI event callback
type MIDIEventCallback = MIDIMessage -> Effect Unit

--------------------------------------------------------------------------------
-- FFI Imports
--------------------------------------------------------------------------------

-- | Check if Web MIDI API is available
foreign import isWebMIDIAvailable :: Effect Boolean

-- | Initialize MIDI access
foreign import initializeMIDIImpl :: Effect (Aff Boolean)

-- | Get connected devices
foreign import getDevicesImpl :: MIDIServiceHandle -> Effect (Array MIDIDeviceInfo)

-- | Add global listener
foreign import addGlobalListenerImpl :: MIDIServiceHandle -> MIDIEventCallback -> Effect Unit

-- | Remove global listener
foreign import removeGlobalListenerImpl :: MIDIServiceHandle -> MIDIEventCallback -> Effect Unit

-- | Add device listener
foreign import addDeviceListenerImpl :: MIDIServiceHandle -> String -> MIDIEventCallback -> Effect Unit

-- | Remove device listener
foreign import removeDeviceListenerImpl :: MIDIServiceHandle -> String -> MIDIEventCallback -> Effect Unit

-- | Get CC value
foreign import getCCValueImpl :: MIDIServiceHandle -> Int -> Int -> Effect (Maybe Int)

-- | Get note state
foreign import getNoteStateImpl :: MIDIServiceHandle -> Int -> Int -> Effect (Maybe { velocity :: Int, timestamp :: Number })

-- | Get held notes
foreign import getHeldNotesImpl :: MIDIServiceHandle -> Effect (Array { channel :: Int, note :: Int, velocity :: Int })

-- | Get message history
foreign import getMessageHistoryImpl :: MIDIServiceHandle -> Maybe Int -> Effect (Array MIDIMessage)

-- | Send raw MIDI message
foreign import sendMessageImpl :: MIDIServiceHandle -> String -> Array Int -> Effect Boolean

-- | Dispose service
foreign import disposeImpl :: MIDIServiceHandle -> Effect Unit

-- | Get or create singleton instance
foreign import getServiceInstanceImpl :: Effect MIDIServiceHandle

-- | Check if initialized
foreign import isInitializedImpl :: MIDIServiceHandle -> Effect Boolean

--------------------------------------------------------------------------------
-- Service Type
--------------------------------------------------------------------------------

-- | MIDI service wrapper
newtype MIDIService = MIDIService
  { handle :: MIDIServiceHandle
  , smoothedValues :: Ref (Map String Number)
  }

--------------------------------------------------------------------------------
-- Initialization
--------------------------------------------------------------------------------

-- | Get the singleton MIDI service instance
getMIDIService :: Effect MIDIService
getMIDIService = do
  handle <- getServiceInstanceImpl
  smoothedRef <- Ref.new Map.empty
  pure $ MIDIService { handle, smoothedValues: smoothedRef }

-- | Dispose the MIDI service
disposeMIDIService :: MIDIService -> Effect Unit
disposeMIDIService (MIDIService { handle }) =
  disposeImpl handle

-- | Initialize MIDI access
initialize :: MIDIService -> Aff Boolean
initialize (MIDIService { handle }) = do
  aff <- liftEffect initializeMIDIImpl
  aff

-- | Check if Web MIDI API is available
isAvailable :: Effect Boolean
isAvailable = isWebMIDIAvailable

-- | Check if MIDI service is initialized
isReady :: MIDIService -> Effect Boolean
isReady (MIDIService { handle }) =
  isInitializedImpl handle

--------------------------------------------------------------------------------
-- Device Management
--------------------------------------------------------------------------------

-- | Get all connected MIDI devices
getDevices :: MIDIService -> Effect (Array MIDIDeviceInfo)
getDevices (MIDIService { handle }) =
  getDevicesImpl handle

-- | Get input devices only
getInputDevices :: MIDIService -> Effect (Array MIDIDeviceInfo)
getInputDevices service = do
  devices <- getDevices service
  pure (filter (\d -> d.deviceType == MIDIInput) devices)

-- | Get output devices only
getOutputDevices :: MIDIService -> Effect (Array MIDIDeviceInfo)
getOutputDevices service = do
  devices <- getDevices service
  pure (filter (\d -> d.deviceType == MIDIOutput) devices)

--------------------------------------------------------------------------------
-- Listeners
--------------------------------------------------------------------------------

-- | Add a listener for all MIDI messages
addGlobalListener :: MIDIService -> MIDIEventCallback -> Effect Unit
addGlobalListener (MIDIService { handle }) callback =
  addGlobalListenerImpl handle callback

-- | Remove a global listener
removeGlobalListener :: MIDIService -> MIDIEventCallback -> Effect Unit
removeGlobalListener (MIDIService { handle }) callback =
  removeGlobalListenerImpl handle callback

-- | Add a listener for a specific device
addDeviceListener :: MIDIService -> String -> MIDIEventCallback -> Effect Unit
addDeviceListener (MIDIService { handle }) deviceId callback =
  addDeviceListenerImpl handle deviceId callback

-- | Remove a device-specific listener
removeDeviceListener :: MIDIService -> String -> MIDIEventCallback -> Effect Unit
removeDeviceListener (MIDIService { handle }) deviceId callback =
  removeDeviceListenerImpl handle deviceId callback

-- | Add a filtered listener (returns cleanup function)
addFilteredListener :: MIDIService -> MIDIFilter -> MIDIEventCallback -> Effect (Effect Unit)
addFilteredListener service midiFilter callback = do
  let wrappedCallback msg =
        if matchesFilter msg midiFilter
          then callback msg
          else pure unit
  addGlobalListener service wrappedCallback
  pure (removeGlobalListener service wrappedCallback)

--------------------------------------------------------------------------------
-- Message Filtering
--------------------------------------------------------------------------------

-- | Check if a message passes a filter
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

--------------------------------------------------------------------------------
-- Value Access
--------------------------------------------------------------------------------

-- | Get the current value of a CC controller
getCCValue :: MIDIService -> Int -> Int -> Effect (Maybe Int)
getCCValue (MIDIService { handle }) channel controller =
  getCCValueImpl handle channel controller

-- | Get the current state of a note
getNoteState :: MIDIService -> Int -> Int -> Effect (Maybe { velocity :: Int, timestamp :: Number })
getNoteState (MIDIService { handle }) channel note =
  getNoteStateImpl handle channel note

-- | Check if a note is currently held
isNoteOn :: MIDIService -> Int -> Int -> Effect Boolean
isNoteOn service channel note = do
  state <- getNoteState service channel note
  pure (state /= Nothing)

-- | Get all currently held notes
getHeldNotes :: MIDIService -> Effect (Array { channel :: Int, note :: Int, velocity :: Int })
getHeldNotes (MIDIService { handle }) =
  getHeldNotesImpl handle

-- | Get message history
getMessageHistory :: MIDIService -> Maybe Int -> Effect (Array MIDIMessage)
getMessageHistory (MIDIService { handle }) limit =
  getMessageHistoryImpl handle limit

--------------------------------------------------------------------------------
-- Property Mapping
--------------------------------------------------------------------------------

-- | Calculate mapped value from MIDI input
getMappedValue :: MIDIService -> MIDIMapping -> Maybe MIDIMessage -> Effect Number
getMappedValue (MIDIService { handle, smoothedValues }) mapping maybeMsg = do
  inputValue <- case maybeMsg of
    Just msg -> getInputFromMessage msg mapping
    Nothing -> do
      cached <- Ref.read smoothedValues
      pure (fromMaybe mapping.outputMin (Map.lookup mapping.id cached))

  -- Map input range to output range
  let normalizedInput = (inputValue - toNumber mapping.inputMin) / (toNumber mapping.inputMax - toNumber mapping.inputMin)
      clampedInput = max 0.0 (min 1.0 normalizedInput)
      rawOutput = mapping.outputMin + clampedInput * (mapping.outputMax - mapping.outputMin)

  -- Apply smoothing
  cached <- Ref.read smoothedValues
  let currentSmoothed = fromMaybe rawOutput (Map.lookup mapping.id cached)
      smoothedOutput = currentSmoothed + (rawOutput - currentSmoothed) * (1.0 - mapping.smoothing)

  -- Store smoothed value
  Ref.modify_ (Map.insert mapping.id smoothedOutput) smoothedValues

  pure smoothedOutput

-- | Extract input value from MIDI message based on mapping config
getInputFromMessage :: MIDIMessage -> MIDIMapping -> Effect Number
getInputFromMessage msg mapping =
  pure $
    if mapping.useVelocity
      then toNumber (fromMaybe 0 msg.velocity)
    else if mapping.useNoteNumber
      then toNumber (fromMaybe 0 msg.note)
    else case msg.value of
      Just v ->
        if msg.msgType == PitchBend
          then (toNumber v / 16383.0) * 127.0  -- Normalize pitch bend
          else toNumber v
      Nothing -> case msg.controller of
        Just _ -> 0.0  -- Would need to look up stored CC value
        Nothing -> 0.0

--------------------------------------------------------------------------------
-- MIDI Output
--------------------------------------------------------------------------------

-- | Send a raw MIDI message to an output device
sendMessage :: MIDIService -> String -> Array Int -> Effect Boolean
sendMessage (MIDIService { handle }) deviceId message =
  sendMessageImpl handle deviceId message

-- | Send a Note On message
sendNoteOn :: MIDIService -> String -> Int -> Int -> Int -> Effect Boolean
sendNoteOn service deviceId channel note velocity =
  let status = 0x90 + (channel - 1)
  in sendMessage service deviceId [status, note, velocity]

-- | Send a Note Off message
sendNoteOff :: MIDIService -> String -> Int -> Int -> Int -> Effect Boolean
sendNoteOff service deviceId channel note velocity =
  let status = 0x80 + (channel - 1)
  in sendMessage service deviceId [status, note, velocity]

-- | Send a Control Change message
sendCC :: MIDIService -> String -> Int -> Int -> Int -> Effect Boolean
sendCC service deviceId channel controller value =
  let status = 0xB0 + (channel - 1)
  in sendMessage service deviceId [status, controller, value]

--------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------

max :: Number -> Number -> Number
max a b = if a > b then a else b

min :: Number -> Number -> Number
min a b = if a < b then a else b
