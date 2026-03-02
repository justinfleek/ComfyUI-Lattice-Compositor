{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-|
Module      : Lattice.Services.Bridge.Server
Description : WebSocket server for PureScript UI bridge
Copyright   : (c) Lattice, 2026
License     : MIT

WebSocket server that bridges PureScript UI to Haskell backend.
Handles all operations that were previously JS FFI:
- WebGL/Canvas rendering
- IndexedDB/localStorage persistence
- WebCodecs video encoding
- Bitwise math for deterministic PRNG

The server listens on a configurable port and handles multiple
concurrent connections. Each request includes a MessageId for
async response correlation.
-}

module Lattice.Services.Bridge.Server
  ( -- * Server
    runServer
  , ServerConfig(..)
  , defaultConfig
    -- * Handlers
  , Handler
  , Handlers(..)
  , defaultHandlers
  ) where

import Control.Concurrent (forkIO, threadDelay)
import Control.Concurrent.STM
import Control.Exception (catch, SomeException, bracket)
import Control.Monad (forever, void, when)
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as LBS
import Data.IORef
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Network.Socket (Socket, Family(AF_INET), SocketType(Stream))
import qualified Network.Socket as Socket
import qualified Network.WebSockets as WS

import Lattice.Services.Bridge.Protocol

-- ────────────────────────────────────────────────────────────────────────────
-- Configuration
-- ────────────────────────────────────────────────────────────────────────────

data ServerConfig = ServerConfig
  { scHost :: !Text
  , scPort :: !Int
  , scPingInterval :: !Int      -- seconds
  , scMaxConnections :: !Int
  } deriving (Eq, Show)

defaultConfig :: ServerConfig
defaultConfig = ServerConfig
  { scHost = "127.0.0.1"
  , scPort = 9876
  , scPingInterval = 30
  , scMaxConnections = 100
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Handler Types
-- ────────────────────────────────────────────────────────────────────────────

type Handler a = a -> IO Response

data Handlers = Handlers
  { hRender :: Handler RenderOp
  , hStorage :: Handler StorageOp
  , hExport :: Handler ExportOp
  , hMath :: Handler MathOp
  }

-- | Default handlers that return errors (to be replaced with real implementations)
defaultHandlers :: Handlers
defaultHandlers = Handlers
  { hRender = \op -> pure $ RespError 0 $ "Render not implemented: " <> T.pack (show op)
  , hStorage = \op -> pure $ RespError 0 $ "Storage not implemented: " <> T.pack (show op)
  , hExport = \op -> pure $ RespError 0 $ "Export not implemented: " <> T.pack (show op)
  , hMath = \op -> pure $ RespError 0 $ "Math not implemented: " <> T.pack (show op)
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Server
-- ────────────────────────────────────────────────────────────────────────────

-- | Run the WebSocket bridge server
runServer :: ServerConfig -> Handlers -> IO ()
runServer cfg handlers = do
  TIO.putStrLn $ "Starting Lattice Bridge on " <> scHost cfg <> ":" <> T.pack (show (scPort cfg))
  
  -- Connection counter
  connCount <- newTVarIO (0 :: Int)
  
  let options = WS.defaultConnectionOptions
  
  WS.runServer (T.unpack $ scHost cfg) (scPort cfg) $ \pending -> do
    -- Check max connections
    canAccept <- atomically $ do
      count <- readTVar connCount
      if count < scMaxConnections cfg
        then do
          writeTVar connCount (count + 1)
          pure True
        else pure False
    
    if canAccept
      then do
        conn <- WS.acceptRequest pending
        handleConnection conn handlers `catch` \(e :: SomeException) ->
          TIO.putStrLn $ "Connection error: " <> T.pack (show e)
        atomically $ modifyTVar' connCount (subtract 1)
      else do
        WS.rejectRequest pending "Too many connections"

-- ────────────────────────────────────────────────────────────────────────────
-- Connection Handler
-- ────────────────────────────────────────────────────────────────────────────

handleConnection :: WS.Connection -> Handlers -> IO ()
handleConnection conn handlers = do
  TIO.putStrLn "Client connected"
  
  -- Ping thread to keep connection alive
  pingThread <- forkIO $ forever $ do
    threadDelay (30 * 1000000)  -- 30 seconds
    WS.sendPing conn ("ping" :: ByteString)
  
  -- Message loop
  loop `catch` \(e :: SomeException) -> do
    TIO.putStrLn $ "Connection closed: " <> T.pack (show e)
  where
    loop = forever $ do
      msg <- WS.receiveData conn
      case decodeRequest msg of
        Nothing -> do
          let resp = RespError 0 "Failed to decode request"
          WS.sendBinaryData conn (encodeResponse resp)
        
        Just req -> do
          resp <- handleRequest handlers req
          WS.sendBinaryData conn (encodeResponse resp)

-- ────────────────────────────────────────────────────────────────────────────
-- Request Handler
-- ────────────────────────────────────────────────────────────────────────────

handleRequest :: Handlers -> Request -> IO Response
handleRequest handlers = \case
  ReqPing msgId -> 
    pure $ RespPong msgId
  
  ReqRender msgId op -> do
    resp <- hRender handlers op
    pure $ setMessageId msgId resp
  
  ReqStorage msgId op -> do
    resp <- hStorage handlers op
    pure $ setMessageId msgId resp
  
  ReqExport msgId op -> do
    resp <- hExport handlers op
    pure $ setMessageId msgId resp
  
  ReqMath msgId op -> do
    resp <- hMath handlers op
    pure $ setMessageId msgId resp

-- | Set the message ID on a response
setMessageId :: MessageId -> Response -> Response
setMessageId mid = \case
  RespOk _ -> RespOk mid
  RespData _ d -> RespData mid d
  RespFrame _ f -> RespFrame mid f
  RespDepth _ d -> RespDepth mid d
  RespNumber _ n -> RespNumber mid n
  RespNumbers _ ns -> RespNumbers mid ns
  RespBool _ b -> RespBool mid b
  RespText _ t -> RespText mid t
  RespError _ e -> RespError mid e
  RespPong _ -> RespPong mid
