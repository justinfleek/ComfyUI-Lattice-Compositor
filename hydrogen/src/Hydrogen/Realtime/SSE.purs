-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                            // hydrogen // sse
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Server-Sent Events (SSE) client
-- |
-- | For unidirectional server-to-client streaming.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Realtime.SSE as SSE
-- |
-- | -- Connect to SSE endpoint
-- | sse <- SSE.connect "/api/events"
-- |   { onMessage: \msg -> handleMessage msg
-- |   , onError: \err -> Console.log err
-- |   }
-- |
-- | -- Listen for specific event types
-- | SSE.on sse "user-update" \data -> updateUser data
-- | SSE.on sse "notification" \data -> showNotification data
-- |
-- | -- Close connection
-- | SSE.close sse
-- | ```
module Hydrogen.Realtime.SSE
  ( -- * Types
    EventSource
  , SSEConfig
  , SSEState(..)
    -- * Connection
  , connect
  , close
    -- * Events
  , on
  , onMessage
  , off
    -- * State
  , getState
  , isConnected
  ) where

import Prelude

import Data.Maybe (Maybe(Nothing, Just))
import Effect (Effect)
import Effect.Ref (Ref)
import Effect.Ref as Ref

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | EventSource wrapper
newtype EventSource = EventSource
  { source :: Ref (Maybe EventSourceRaw)
  , url :: String
  , state :: Ref SSEState
  }

-- | Configuration for SSE
type SSEConfig =
  { onMessage :: String -> Effect Unit
  , onError :: String -> Effect Unit
  , onOpen :: Effect Unit
  , withCredentials :: Boolean
  }

-- | SSE connection state
data SSEState
  = SSEConnecting
  | SSEOpen
  | SSEClosed

derive instance eqSSEState :: Eq SSEState

instance showSSEState :: Show SSEState where
  show SSEConnecting = "Connecting"
  show SSEOpen = "Open"
  show SSEClosed = "Closed"

-- | Raw EventSource (FFI)
foreign import data EventSourceRaw :: Type

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // FFI
-- ═════════════════════════════════════════════════════════════════════════════

foreign import newEventSource :: String -> Boolean -> Effect EventSourceRaw

foreign import sseOnOpen :: EventSourceRaw -> Effect Unit -> Effect Unit

foreign import sseOnMessage :: EventSourceRaw -> (String -> Effect Unit) -> Effect Unit

foreign import sseOnError :: EventSourceRaw -> (String -> Effect Unit) -> Effect Unit

foreign import sseAddEventListener :: EventSourceRaw -> String -> (String -> Effect Unit) -> Effect Unit

foreign import sseRemoveEventListener :: EventSourceRaw -> String -> Effect Unit

foreign import sseClose :: EventSourceRaw -> Effect Unit

foreign import sseReadyState :: EventSourceRaw -> Effect Int

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // connection
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default SSE configuration
defaultConfig :: SSEConfig
defaultConfig =
  { onMessage: \_ -> pure unit
  , onError: \_ -> pure unit
  , onOpen: pure unit
  , withCredentials: false
  }

-- | Connect to an SSE endpoint
connect :: String -> SSEConfig -> Effect EventSource
connect url config = do
  sourceRef <- Ref.new Nothing
  stateRef <- Ref.new SSEConnecting
  
  source <- newEventSource url config.withCredentials
  Ref.write (Just source) sourceRef
  
  sseOnOpen source do
    Ref.write SSEOpen stateRef
    config.onOpen
  
  sseOnMessage source config.onMessage
  
  sseOnError source \err -> do
    config.onError err
  
  pure $ EventSource { source: sourceRef, url, state: stateRef }

-- | Close the SSE connection
close :: EventSource -> Effect Unit
close (EventSource { source, state }) = do
  Ref.write SSEClosed state
  maybeSource <- Ref.read source
  case maybeSource of
    Nothing -> pure unit
    Just s -> sseClose s

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // events
-- ═════════════════════════════════════════════════════════════════════════════

-- | Listen for a specific event type
on :: EventSource -> String -> (String -> Effect Unit) -> Effect Unit
on (EventSource { source }) eventType handler = do
  maybeSource <- Ref.read source
  case maybeSource of
    Nothing -> pure unit
    Just s -> sseAddEventListener s eventType handler

-- | Listen for the default message event
onMessage :: EventSource -> (String -> Effect Unit) -> Effect Unit
onMessage es = on es "message"

-- | Remove event listener
off :: EventSource -> String -> Effect Unit
off (EventSource { source }) eventType = do
  maybeSource <- Ref.read source
  case maybeSource of
    Nothing -> pure unit
    Just s -> sseRemoveEventListener s eventType

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get current connection state
getState :: EventSource -> Effect SSEState
getState (EventSource { state }) = Ref.read state

-- | Check if connected
isConnected :: EventSource -> Effect Boolean
isConnected es = do
  s <- getState es
  pure $ s == SSEOpen
