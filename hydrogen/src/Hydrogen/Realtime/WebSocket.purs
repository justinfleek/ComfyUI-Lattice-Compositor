-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                      // hydrogen // websocket
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | WebSocket client with automatic reconnection
-- |
-- | Type-safe WebSocket management with JSON serialization,
-- | heartbeats, and automatic reconnection with exponential backoff.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Realtime.WebSocket as WS
-- |
-- | -- Create connection
-- | ws <- WS.connect "wss://api.example.com/ws"
-- |   { onOpen: Console.log "Connected!"
-- |   , onClose: Console.log "Disconnected"
-- |   , onError: \err -> Console.log $ "Error: " <> err
-- |   , onMessage: \msg -> handleMessage msg
-- |   , reconnect: true
-- |   }
-- |
-- | -- Send messages
-- | WS.send ws { type: "subscribe", channel: "updates" }
-- |
-- | -- Close connection
-- | WS.close ws
-- | ```
module Hydrogen.Realtime.WebSocket
  ( -- * Types
    WebSocketConnection
  , WebSocketConfig
  , WebSocketState(..)
  , CloseCode
    -- * Configuration
  , defaultConfig
    -- * Connection
  , connect
  , connectWithProtocol
  , close
  , closeWithCode
    -- * Messaging
  , send
  , sendJson
  , sendText
    -- * State
  , getState
  , isConnected
  , getUrl
    -- * Subscription channels
  , Channel
  , createChannel
  , subscribeChannel
  , unsubscribeChannel
  ) where

import Prelude
  ( class Eq
  , class Show
  , Unit
  , bind
  , discard
  , flip
  , pure
  , show
  , unit
  , void
  , when
  , ($)
  , (+)
  , (-)
  , (*)
  , (<=)
  , (==)
  , (/=)
  , (<)
  )

import Data.Array as Array
import Data.Argonaut (class DecodeJson, class EncodeJson, Json, decodeJson, encodeJson, stringify, parseJson)
import Data.Either (Either(Left, Right), hush)
import Data.Maybe (Maybe(Nothing, Just))
import Data.Time.Duration (Milliseconds(Milliseconds))
import Effect (Effect)
import Effect.Aff (delay, launchAff_)
import Effect.Class (liftEffect)
import Effect.Ref (Ref)
import Effect.Ref as Ref

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | WebSocket connection wrapper
newtype WebSocketConnection = WebSocketConnection
  { socket :: Ref (Maybe WebSocketRaw)
  , url :: String
  , config :: WebSocketConfig
  , state :: Ref WebSocketState
  , retryCount :: Ref Int
  , channels :: Ref (Array Channel)
  }

-- | Configuration for WebSocket connection
type WebSocketConfig =
  { onOpen :: Effect Unit
  , onClose :: Effect Unit
  , onError :: String -> Effect Unit
  , onMessage :: String -> Effect Unit
  , reconnect :: Boolean
  , maxRetries :: Int
  , heartbeatInterval :: Maybe Milliseconds
  , protocols :: Array String
  }

-- | WebSocket connection state
data WebSocketState
  = Connecting
  | Open
  | Closing
  | Closed

derive instance eqWebSocketState :: Eq WebSocketState

instance showWebSocketState :: Show WebSocketState where
  show Connecting = "Connecting"
  show Open = "Open"
  show Closing = "Closing"
  show Closed = "Closed"

-- | Close code for WebSocket
type CloseCode = Int

-- | Raw WebSocket (FFI)
foreign import data WebSocketRaw :: Type

-- | Subscription channel
newtype Channel = Channel
  { name :: String
  , handlers :: Ref (Array { id :: Int, callback :: String -> Effect Unit })
  , nextHandlerId :: Ref Int
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // FFI
-- ═════════════════════════════════════════════════════════════════════════════

foreign import newWebSocket :: String -> Array String -> Effect WebSocketRaw

foreign import wsOnOpen :: WebSocketRaw -> Effect Unit -> Effect Unit

foreign import wsOnClose :: WebSocketRaw -> Effect Unit -> Effect Unit

foreign import wsOnError :: WebSocketRaw -> (String -> Effect Unit) -> Effect Unit

foreign import wsOnMessage :: WebSocketRaw -> (String -> Effect Unit) -> Effect Unit

foreign import wsSend :: WebSocketRaw -> String -> Effect Unit

foreign import wsClose :: WebSocketRaw -> Effect Unit

foreign import wsCloseWithCode :: WebSocketRaw -> Int -> String -> Effect Unit

foreign import wsReadyState :: WebSocketRaw -> Effect Int

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // connection
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default WebSocket configuration
defaultConfig :: WebSocketConfig
defaultConfig =
  { onOpen: pure unit
  , onClose: pure unit
  , onError: \_ -> pure unit
  , onMessage: \_ -> pure unit
  , reconnect: true
  , maxRetries: 5
  , heartbeatInterval: Just (Milliseconds 30000.0)
  , protocols: []
  }

-- | Connect to a WebSocket server
connect :: String -> WebSocketConfig -> Effect WebSocketConnection
connect url config = connectWithProtocol url config.protocols config

-- | Connect with specific subprotocols
connectWithProtocol :: String -> Array String -> WebSocketConfig -> Effect WebSocketConnection
connectWithProtocol url protocols config = do
  socketRef <- Ref.new Nothing
  stateRef <- Ref.new Connecting
  retryRef <- Ref.new 0
  channelsRef <- Ref.new []
  
  let 
    conn = WebSocketConnection
      { socket: socketRef
      , url
      , config
      , state: stateRef
      , retryCount: retryRef
      , channels: channelsRef
      }
  
  -- Initial connection
  doConnect conn
  
  pure conn

-- | Internal connection logic
doConnect :: WebSocketConnection -> Effect Unit
doConnect conn@(WebSocketConnection { socket, url, config, state, retryCount }) = do
  Ref.write Connecting state
  
  ws <- newWebSocket url config.protocols
  Ref.write (Just ws) socket
  
  -- Set up handlers
  wsOnOpen ws do
    Ref.write Open state
    Ref.write 0 retryCount
    config.onOpen
  
  wsOnClose ws do
    Ref.write Closed state
    config.onClose
    -- Attempt reconnect if enabled
    when config.reconnect do
      retries <- Ref.read retryCount
      when (retries < config.maxRetries) do
        Ref.modify_ (_ + 1) retryCount
        -- Exponential backoff
        let delayMs = Milliseconds (1000.0 * (2.0 `pow` toNumber retries))
        launchAff_ do
          delay delayMs
          liftEffect $ doConnect conn
  
  wsOnError ws \err -> do
    config.onError err
  
  wsOnMessage ws \msg -> do
    config.onMessage msg
    -- Route to channels
    channels <- Ref.read (unwrapConn conn).channels
    forChannels channels \(Channel ch) -> do
      handlers <- Ref.read ch.handlers
      forHandlers handlers \h -> h.callback msg
  where
  unwrapConn (WebSocketConnection c) = c
  forChannels :: Array Channel -> (Channel -> Effect Unit) -> Effect Unit
  forChannels arr f = void $ Array.foldM (\_ x -> f x) unit arr
  forHandlers :: Array { id :: Int, callback :: String -> Effect Unit } -> ({ id :: Int, callback :: String -> Effect Unit } -> Effect Unit) -> Effect Unit
  forHandlers arr f = void $ Array.foldM (\_ x -> f x) unit arr
  pow base exp = if exp <= 0.0 then 1.0 else base * pow base (exp - 1.0)
  toNumber n = if n == 0 then 0.0 else toNumber (n - 1) + 1.0

-- | Close the WebSocket connection
close :: WebSocketConnection -> Effect Unit
close (WebSocketConnection { socket, state }) = do
  Ref.write Closing state
  maybeWs <- Ref.read socket
  case maybeWs of
    Nothing -> pure unit
    Just ws -> wsClose ws

-- | Close with a specific code and reason
closeWithCode :: WebSocketConnection -> CloseCode -> String -> Effect Unit
closeWithCode (WebSocketConnection { socket, state }) code reason = do
  Ref.write Closing state
  maybeWs <- Ref.read socket
  case maybeWs of
    Nothing -> pure unit
    Just ws -> wsCloseWithCode ws code reason

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // messaging
-- ═════════════════════════════════════════════════════════════════════════════

-- | Send a JSON-encodable message
send :: forall a. EncodeJson a => WebSocketConnection -> a -> Effect Unit
send conn msg = sendJson conn (encodeJson msg)

-- | Send raw JSON
sendJson :: WebSocketConnection -> Json -> Effect Unit
sendJson conn json = sendText conn (stringify json)

-- | Send raw text
sendText :: WebSocketConnection -> String -> Effect Unit
sendText (WebSocketConnection { socket }) text = do
  maybeWs <- Ref.read socket
  case maybeWs of
    Nothing -> pure unit
    Just ws -> wsSend ws text

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get current connection state
getState :: WebSocketConnection -> Effect WebSocketState
getState (WebSocketConnection { state }) = Ref.read state

-- | Check if connected
isConnected :: WebSocketConnection -> Effect Boolean
isConnected conn = do
  s <- getState conn
  pure $ s == Open

-- | Get the WebSocket URL
getUrl :: WebSocketConnection -> String
getUrl (WebSocketConnection { url }) = url

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // channels
-- ═════════════════════════════════════════════════════════════════════════════

-- | Channel handler with ID
type ChannelHandler = { id :: Int, callback :: String -> Effect Unit }

-- | Create a named channel for message routing
createChannel :: String -> Effect Channel
createChannel name = do
  handlers <- Ref.new ([] :: Array ChannelHandler)
  nextHandlerId <- Ref.new 0
  pure $ Channel { name, handlers, nextHandlerId }

-- | Subscribe to a channel
subscribeChannel :: WebSocketConnection -> Channel -> (String -> Effect Unit) -> Effect (Effect Unit)
subscribeChannel (WebSocketConnection { channels }) channel@(Channel ch) handler = do
  -- Add channel if not already registered
  chans <- Ref.read channels
  let hasChannel = Array.any (\(Channel c) -> c.name == ch.name) chans
  unless hasChannel do
    Ref.modify_ (flip Array.snoc channel) channels
  -- Add handler with ID
  handlerId <- Ref.read ch.nextHandlerId
  Ref.write (handlerId + 1) ch.nextHandlerId
  let h = { id: handlerId, callback: handler }
  Ref.modify_ (flip Array.snoc h) ch.handlers
  -- Return unsubscribe
  pure $ Ref.modify_ (Array.filter (\x -> x.id /= handlerId)) ch.handlers
  where
  unless cond act = if cond then pure unit else act

-- | Unsubscribe from a channel entirely
unsubscribeChannel :: WebSocketConnection -> Channel -> Effect Unit
unsubscribeChannel (WebSocketConnection { channels }) (Channel ch) =
  Ref.modify_ (Array.filter (\(Channel c) -> c.name /= ch.name)) channels
