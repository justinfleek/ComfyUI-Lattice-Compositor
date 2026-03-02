-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                   Client.purs
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- | WebSocket client for Haskell backend bridge
-- |
-- | All heavy operations (WebGL, Canvas, IndexedDB, WebCodecs) are proxied
-- | to the Haskell backend over WebSocket. This replaces all JS FFI.
module Lattice.Services.Bridge.Client
  ( BridgeClient
  , Request(..)
  , Response(..)
  , RenderOp(..)
  , StorageOp(..)
  , ExportOp(..)
  , MathOp(..)
  , GenerateOp(..)
  , connect
  , disconnect
  , isConnected
  , send
  , request
  , onDisconnect
    -- * Operations
  , renderFrame
  , compileShader
  , storageGet
  , storagePut
  , storageDelete
  , storageGetAll
  , storageCount
  , storageClear
  , storageLocalGet
  , storageLocalSet
  , storageSessionGet
  , storageSessionSet
  , seededRandom
  , bitXor
  , bitAnd
  , bitOr
  , bitShl
  , bitShr
  , bitZshr
  , imul
    -- * Export operations
  , createEncoder
  , encodeFrame
  , finalizeExport
  , cancelExport
    -- * Generation operations (AI)
  , generateImage
  , generateVideo
  , GenerateConfig(..)
  , GenerateResult(..)
  , GenerateProgress(..)
  ) where

import Prelude

import Data.Argonaut.Core (Json, stringify, jsonEmptyObject)
import Data.Argonaut.Decode (class DecodeJson, decodeJson, JsonDecodeError(..), printJsonDecodeError)
import Data.Argonaut.Encode (class EncodeJson, encodeJson)
import Data.Argonaut.Decode.Generic (genericDecodeJson)
import Data.Argonaut.Encode.Generic (genericEncodeJson)
import Data.Argonaut.Parser (jsonParser)
import Data.Either (Either(..), either)
import Data.Generic.Rep (class Generic)
import Data.Int (toNumber, floor)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), maybe)
import Data.Number as Number
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Aff (Aff, makeAff, nonCanceler, Canceler(..), launchAff_)
import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Class (class MonadEffect, liftEffect)
import Effect.Console as Console
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Web.Event.Event (Event)
import Web.Event.EventTarget (EventTarget, addEventListener, eventListener, removeEventListener)
import Web.Socket.WebSocket as WS
import Web.Socket.Event.EventTypes (onOpen, onMessage, onError, onClose) as WSE
import Web.Socket.Event.MessageEvent as ME
import Foreign (Foreign, unsafeFromForeign)
import Web.Socket.ReadyState (ReadyState(..))
import Effect.Exception (Error, error)
import Data.Array (uncons, fromFoldable)

-- ════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ════════════════════════════════════════════════════════════════════════════

-- | Bridge client handle
newtype BridgeClient = BridgeClient
  { socket :: Ref (Maybe WS.WebSocket)
  , url :: String
  , messageId :: Ref Int
  , pending :: Ref (Map Int (Either Error Response -> Effect Unit))
  , disconnectCallbacks :: Ref (Array (Effect Unit))
  }

-- | Request message to backend
data Request
  = ReqRender Int RenderOp
  | ReqStorage Int StorageOp
  | ReqExport Int ExportOp
  | ReqMath Int MathOp
  | ReqGenerate Int GenerateOp
  | ReqPing Int

derive instance Generic Request _
instance EncodeJson Request where encodeJson = genericEncodeJson

-- | Response from backend
data Response
  = RespOk Int
  | RespData Int String           -- base64 encoded
  | RespNumber Int Number
  | RespNumbers Int (Array Number)
  | RespBool Int Boolean
  | RespText Int String
  | RespError Int String
  | RespPong Int
  | RespProgress Int Number String  -- msgId, percentage (0-100), stage

derive instance Generic Response _
instance DecodeJson Response where decodeJson = genericDecodeJson

-- | Render operations
data RenderOp
  = RenderCompileShader String String
  | RenderSetShader String
  | RenderSetUniforms Json
  | RenderFrame Int Int
  | RenderFrameWithUniforms Int Int Json
  | RenderDepth Int Int String
  | RenderDispose
  | RenderIsContextLost
  | RenderCreateCanvas Int Int
  | RenderCanvasClear Int Int Int Int
  | RenderCanvasGetContext2D

derive instance Generic RenderOp _
instance EncodeJson RenderOp where encodeJson = genericEncodeJson

-- | Storage operations
data StorageOp
  = StorageOpen String Int String
  | StorageClose String
  | StoragePut String String String
  | StorageGet String String
  | StorageDelete String String
  | StorageGetAll String
  | StorageClear String
  | StorageCount String
  | StorageLocalGet String
  | StorageLocalSet String String
  | StorageSessionGet String
  | StorageSessionSet String String

derive instance Generic StorageOp _
instance EncodeJson StorageOp where encodeJson = genericEncodeJson

-- | Export operations
data ExportOp
  = ExportCreateEncoder String Int Int Int Int
  | ExportEncodeFrame String Int Boolean
  | ExportFinalize
  | ExportCancel
  | ExportGetSupportedCodecs
  | ExportCreateZip (Array { filename :: String, content :: String })
  | ExportDownload String String

derive instance Generic ExportOp _
instance EncodeJson ExportOp where encodeJson = genericEncodeJson

-- | Math operations (exact bitwise)
data MathOp
  = MathSeededRandom Int Int      -- seed, count
  | MathMulberry32Next Int        -- state
  | MathBitXor Int Int
  | MathBitAnd Int Int
  | MathBitOr Int Int
  | MathBitShl Int Int
  | MathBitShr Int Int
  | MathBitZshr Int Int
  | MathImul Int Int

derive instance Generic MathOp _
instance EncodeJson MathOp where encodeJson = genericEncodeJson

-- | Generation configuration for AI models
type GenerateConfig =
  { prompt :: String
  , negativePrompt :: Maybe String
  , width :: Int
  , height :: Int
  , numFrames :: Maybe Int          -- For video generation
  , fps :: Maybe Number             -- For video generation
  , model :: String                 -- Model identifier
  , seed :: Maybe Int
  , steps :: Maybe Int
  , cfgScale :: Maybe Number
  , controlnetImage :: Maybe String -- Base64 encoded control image
  , controlnetType :: Maybe String  -- "depth", "canny", "pose", etc.
  , controlnetStrength :: Maybe Number
  }

-- | Result from generation
type GenerateResult =
  { success :: Boolean
  , frames :: Array String          -- Base64 encoded frames
  , error :: Maybe String
  , seed :: Int                     -- Actual seed used
  , timeTaken :: Number             -- Milliseconds
  }

-- | Progress update during generation
type GenerateProgress =
  { step :: Int                     -- Current step (0-indexed)
  , totalSteps :: Int               -- Total steps
  , stage :: String                 -- "encoding" | "sampling" | "decoding"
  , percentage :: Number            -- 0.0 to 100.0
  , eta :: Maybe Number             -- Estimated seconds remaining
  , previewFrame :: Maybe String    -- Optional preview (base64)
  }

-- | Generation operations (AI diffusion models)
data GenerateOp
  = GenerateImage GenerateConfig
  | GenerateVideo GenerateConfig
  | GenerateCancel
  | GenerateGetModels
  | GenerateGetStatus

derive instance Generic GenerateOp _
instance EncodeJson GenerateOp where encodeJson = genericEncodeJson

-- ════════════════════════════════════════════════════════════════════════════
--                                                                 // connection
-- ════════════════════════════════════════════════════════════════════════════

-- | Connect to the Haskell backend
connect :: String -> Aff BridgeClient
connect url = makeAff \callback -> do
  socketRef <- Ref.new Nothing
  messageId <- Ref.new 0
  pending <- Ref.new Map.empty
  disconnectCallbacks <- Ref.new []
  
  let client = BridgeClient { socket: socketRef, url, messageId, pending, disconnectCallbacks }
  
  -- Create WebSocket
  ws <- WS.create url []
  Ref.write (Just ws) socketRef
  
  let target = WS.toEventTarget ws
  
  -- On open
  openListener <- eventListener \_ -> do
    Console.log $ "Bridge connected to " <> url
    callback (Right client)
  addEventListener WSE.onOpen openListener false target
  
  -- On message
  messageListener <- eventListener \event -> do
    case ME.fromEvent event of
      Nothing -> pure unit
      Just msgEvent -> do
        let msgData = unsafeFromForeign (ME.data_ msgEvent) :: String
        -- Parse response and dispatch to pending callback
        case decodeJson =<< parseJsonString msgData of
          Left err -> Console.error $ "Failed to decode response: " <> printJsonDecodeError err
          Right (resp :: Response) -> do
            let msgId = getResponseId resp
            pendingMap <- Ref.read pending
            case Map.lookup msgId pendingMap of
              Nothing -> Console.warn $ "No pending callback for message " <> show msgId
              Just cb -> do
                Ref.modify_ (Map.delete msgId) pending
                cb (Right resp)
  addEventListener WSE.onMessage messageListener false target
  
  -- On close
  closeListener <- eventListener \_ -> do
    Console.log "Bridge disconnected"
    Ref.write Nothing socketRef
    -- Call disconnect callbacks
    cbs <- Ref.read disconnectCallbacks
    for_ cbs identity
    -- Reject all pending requests
    pendingMap <- Ref.read pending
    Ref.write Map.empty pending
    for_ (fromFoldable (Map.values pendingMap)) \cb ->
      cb (Left (error "Connection closed"))
  addEventListener WSE.onClose closeListener false target
  
  -- On error
  errorListener <- eventListener \_ -> do
    Console.error "Bridge WebSocket error"
    callback (Left (error "WebSocket connection failed"))
  addEventListener WSE.onError errorListener false target
  
  pure nonCanceler

-- | Disconnect from backend
disconnect :: BridgeClient -> Effect Unit
disconnect (BridgeClient client) = do
  mSocket <- Ref.read client.socket
  case mSocket of
    Nothing -> pure unit
    Just ws -> WS.close ws

-- | Check if connected
isConnected :: BridgeClient -> Effect Boolean
isConnected (BridgeClient client) = do
  mSocket <- Ref.read client.socket
  case mSocket of
    Nothing -> pure false
    Just ws -> do
      state <- WS.readyState ws
      pure $ state == Open

-- | Register a disconnect callback
onDisconnect :: BridgeClient -> Effect Unit -> Effect Unit
onDisconnect (BridgeClient client) cb = do
  Ref.modify_ (\cbs -> cbs <> [cb]) client.disconnectCallbacks

-- | Get next message ID
nextMessageId :: BridgeClient -> Effect Int
nextMessageId (BridgeClient client) = do
  id <- Ref.read client.messageId
  Ref.write (id + 1) client.messageId
  pure id

-- ════════════════════════════════════════════════════════════════════════════
--                                                                  // messaging
-- ════════════════════════════════════════════════════════════════════════════

-- | Send a request and wait for response
send :: BridgeClient -> Request -> Aff Response
send (BridgeClient client) req = makeAff \callback -> do
  mSocket <- Ref.read client.socket
  case mSocket of
    Nothing -> callback (Left (error "Not connected"))
    Just ws -> do
      state <- WS.readyState ws
      if state /= Open
        then callback (Left (error "WebSocket not open"))
        else do
          -- Register pending callback
          let msgId = getRequestId req
          Ref.modify_ (Map.insert msgId (callback <<< map identity)) client.pending
          
          -- Send request
          let json = stringify (encodeJson req)
          WS.sendString ws json
  
  pure $ Canceler \_ -> liftEffect do
    -- Remove from pending on cancel
    let msgId = getRequestId req
    Ref.modify_ (Map.delete msgId) client.pending

-- | Send a request and decode the response
request :: forall a. DecodeJson a => BridgeClient -> Request -> Aff (Either String a)
request client req = do
  resp <- send client req
  pure $ case resp of
    RespError _ msg -> Left msg
    RespText _ txt -> Left "Expected decoded value, got text"
    _ -> Left "Unexpected response type"

-- | Get message ID from request
getRequestId :: Request -> Int
getRequestId = case _ of
  ReqRender id _ -> id
  ReqStorage id _ -> id
  ReqExport id _ -> id
  ReqMath id _ -> id
  ReqGenerate id _ -> id
  ReqPing id -> id

-- | Get message ID from response
getResponseId :: Response -> Int
getResponseId = case _ of
  RespOk id -> id
  RespData id _ -> id
  RespNumber id _ -> id
  RespNumbers id _ -> id
  RespBool id _ -> id
  RespText id _ -> id
  RespError id _ -> id
  RespPong id -> id
  RespProgress id _ _ -> id

-- | Parse JSON from string
parseJsonString :: String -> Either JsonDecodeError Json
parseJsonString str = case jsonParser str of
  Left err -> Left (TypeMismatch err)
  Right json -> Right json

-- ════════════════════════════════════════════════════════════════════════════
--                                                                 // render ops
-- ════════════════════════════════════════════════════════════════════════════

-- | Compile a shader program
compileShader :: BridgeClient -> String -> String -> Aff (Either String String)
compileShader client vertex fragment = do
  msgId <- liftEffect $ nextMessageId client
  resp <- send client (ReqRender msgId (RenderCompileShader vertex fragment))
  pure $ case resp of
    RespText _ shaderId -> Right shaderId
    RespError _ msg -> Left msg
    _ -> Left "Unexpected response"

-- | Render a frame
renderFrame :: BridgeClient -> Int -> Int -> Aff (Either String String)
renderFrame client width height = do
  msgId <- liftEffect $ nextMessageId client
  resp <- send client (ReqRender msgId (RenderFrame width height))
  pure $ case resp of
    RespData _ base64 -> Right base64
    RespError _ msg -> Left msg
    _ -> Left "Unexpected response"

-- ════════════════════════════════════════════════════════════════════════════
--                                                                // storage ops
-- ════════════════════════════════════════════════════════════════════════════

-- | Get from object store
storageGet :: BridgeClient -> String -> String -> Aff (Maybe String)
storageGet client store key = do
  msgId <- liftEffect $ nextMessageId client
  resp <- send client (ReqStorage msgId (StorageGet store key))
  pure $ case resp of
    RespText _ value | value /= "" -> Just value
    _ -> Nothing

-- | Put to object store
storagePut :: BridgeClient -> String -> String -> String -> Aff Boolean
storagePut client store key value = do
  msgId <- liftEffect $ nextMessageId client
  resp <- send client (ReqStorage msgId (StoragePut store key value))
  pure $ case resp of
    RespOk _ -> true
    _ -> false

-- | Get from localStorage
storageLocalGet :: BridgeClient -> String -> Aff (Maybe String)
storageLocalGet client key = do
  msgId <- liftEffect $ nextMessageId client
  resp <- send client (ReqStorage msgId (StorageLocalGet key))
  pure $ case resp of
    RespText _ value | value /= "" -> Just value
    _ -> Nothing

-- | Set in localStorage
storageLocalSet :: BridgeClient -> String -> String -> Aff Boolean
storageLocalSet client key value = do
  msgId <- liftEffect $ nextMessageId client
  resp <- send client (ReqStorage msgId (StorageLocalSet key value))
  pure $ case resp of
    RespOk _ -> true
    _ -> false

-- | Get from sessionStorage
storageSessionGet :: BridgeClient -> String -> Aff (Maybe String)
storageSessionGet client key = do
  msgId <- liftEffect $ nextMessageId client
  resp <- send client (ReqStorage msgId (StorageSessionGet key))
  pure $ case resp of
    RespText _ value | value /= "" -> Just value
    _ -> Nothing

-- | Set in sessionStorage
storageSessionSet :: BridgeClient -> String -> String -> Aff Boolean
storageSessionSet client key value = do
  msgId <- liftEffect $ nextMessageId client
  resp <- send client (ReqStorage msgId (StorageSessionSet key value))
  pure $ case resp of
    RespOk _ -> true
    _ -> false

-- | Delete from object store
storageDelete :: BridgeClient -> String -> String -> Aff Boolean
storageDelete client store key = do
  msgId <- liftEffect $ nextMessageId client
  resp <- send client (ReqStorage msgId (StorageDelete store key))
  pure $ case resp of
    RespOk _ -> true
    _ -> false

-- | Get all entries from object store
-- | Returns array of JSON-encoded entries
storageGetAll :: BridgeClient -> String -> Aff (Array String)
storageGetAll client store = do
  msgId <- liftEffect $ nextMessageId client
  resp <- send client (ReqStorage msgId (StorageGetAll store))
  pure $ case resp of
    RespText _ json -> parseJsonArray json
    _ -> []
  where
    -- Parse JSON array string to Array String
    -- Each element is a JSON-encoded entry
    parseJsonArray :: String -> Array String
    parseJsonArray str = case decodeJson =<< parseJsonString str of
      Right arr -> arr
      Left _ -> []

-- | Count entries in object store
storageCount :: BridgeClient -> String -> Aff Int
storageCount client store = do
  msgId <- liftEffect $ nextMessageId client
  resp <- send client (ReqStorage msgId (StorageCount store))
  pure $ case resp of
    RespNumber _ n -> floor n
    _ -> 0

-- | Clear all entries from object store
storageClear :: BridgeClient -> String -> Aff Boolean
storageClear client store = do
  msgId <- liftEffect $ nextMessageId client
  resp <- send client (ReqStorage msgId (StorageClear store))
  pure $ case resp of
    RespOk _ -> true
    _ -> false

-- ════════════════════════════════════════════════════════════════════════════
--                                                                 // export ops
-- ════════════════════════════════════════════════════════════════════════════

-- | Create video encoder
createEncoder :: BridgeClient -> String -> Int -> Int -> Int -> Int -> Aff (Either String String)
createEncoder client codec width height fps bitrate = do
  msgId <- liftEffect $ nextMessageId client
  resp <- send client (ReqExport msgId (ExportCreateEncoder codec width height fps bitrate))
  pure $ case resp of
    RespText _ encoderId -> Right encoderId
    RespError _ msg -> Left msg
    _ -> Left "Unexpected response"

-- | Encode a frame
encodeFrame :: BridgeClient -> String -> Int -> Boolean -> Aff Boolean
encodeFrame client frameData timestamp isKeyframe = do
  msgId <- liftEffect $ nextMessageId client
  resp <- send client (ReqExport msgId (ExportEncodeFrame frameData timestamp isKeyframe))
  pure $ case resp of
    RespOk _ -> true
    _ -> false

-- | Finalize export
finalizeExport :: BridgeClient -> Aff (Either String String)
finalizeExport client = do
  msgId <- liftEffect $ nextMessageId client
  resp <- send client (ReqExport msgId ExportFinalize)
  pure $ case resp of
    RespData _ videoData -> Right videoData
    RespError _ msg -> Left msg
    _ -> Left "Unexpected response"

-- | Cancel export
cancelExport :: BridgeClient -> Aff Unit
cancelExport client = do
  msgId <- liftEffect $ nextMessageId client
  _ <- send client (ReqExport msgId ExportCancel)
  pure unit

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // math ops
-- ════════════════════════════════════════════════════════════════════════════

-- | Generate seeded random numbers
seededRandom :: BridgeClient -> Int -> Int -> Aff (Array Number)
seededRandom client seed count = do
  msgId <- liftEffect $ nextMessageId client
  resp <- send client (ReqMath msgId (MathSeededRandom seed count))
  pure $ case resp of
    RespNumbers _ nums -> nums
    _ -> []

-- | Bitwise XOR
bitXor :: BridgeClient -> Int -> Int -> Aff Int
bitXor client a b = do
  msgId <- liftEffect $ nextMessageId client
  resp <- send client (ReqMath msgId (MathBitXor a b))
  pure $ case resp of
    RespNumber _ n -> floor n
    _ -> 0

-- | Bitwise AND
bitAnd :: BridgeClient -> Int -> Int -> Aff Int
bitAnd client a b = do
  msgId <- liftEffect $ nextMessageId client
  resp <- send client (ReqMath msgId (MathBitAnd a b))
  pure $ case resp of
    RespNumber _ n -> floor n
    _ -> 0

-- | Bitwise OR
bitOr :: BridgeClient -> Int -> Int -> Aff Int
bitOr client a b = do
  msgId <- liftEffect $ nextMessageId client
  resp <- send client (ReqMath msgId (MathBitOr a b))
  pure $ case resp of
    RespNumber _ n -> floor n
    _ -> 0

-- | Bitwise shift left
bitShl :: BridgeClient -> Int -> Int -> Aff Int
bitShl client a n = do
  msgId <- liftEffect $ nextMessageId client
  resp <- send client (ReqMath msgId (MathBitShl a n))
  pure $ case resp of
    RespNumber _ num -> floor num
    _ -> 0

-- | Bitwise signed shift right
bitShr :: BridgeClient -> Int -> Int -> Aff Int
bitShr client a n = do
  msgId <- liftEffect $ nextMessageId client
  resp <- send client (ReqMath msgId (MathBitShr a n))
  pure $ case resp of
    RespNumber _ num -> floor num
    _ -> 0

-- | Bitwise unsigned shift right (zero-fill)
bitZshr :: BridgeClient -> Int -> Int -> Aff Int
bitZshr client a n = do
  msgId <- liftEffect $ nextMessageId client
  resp <- send client (ReqMath msgId (MathBitZshr a n))
  pure $ case resp of
    RespNumber _ num -> floor num
    _ -> 0

-- | 32-bit integer multiply (JavaScript semantics)
imul :: BridgeClient -> Int -> Int -> Aff Int
imul client a b = do
  msgId <- liftEffect $ nextMessageId client
  resp <- send client (ReqMath msgId (MathImul a b))
  pure $ case resp of
    RespNumber _ num -> floor num
    _ -> 0

-- ════════════════════════════════════════════════════════════════════════════
--                                                              // generation ops
-- ════════════════════════════════════════════════════════════════════════════

-- | Generate an image using AI diffusion model
-- | Returns base64 encoded image on success
generateImage :: BridgeClient -> GenerateConfig -> Aff (Either String GenerateResult)
generateImage client config = do
  msgId <- liftEffect $ nextMessageId client
  resp <- send client (ReqGenerate msgId (GenerateImage config))
  pure $ decodeGenerateResult resp

-- | Generate a video using AI diffusion model
-- | Returns array of base64 encoded frames on success
generateVideo :: BridgeClient -> GenerateConfig -> Aff (Either String GenerateResult)
generateVideo client config = do
  msgId <- liftEffect $ nextMessageId client
  resp <- send client (ReqGenerate msgId (GenerateVideo config))
  pure $ decodeGenerateResult resp

-- | Decode a generation response
decodeGenerateResult :: Response -> Either String GenerateResult
decodeGenerateResult = case _ of
  RespData _ jsonStr -> 
    case decodeJson =<< parseJsonString jsonStr of
      Left err -> Left $ printJsonDecodeError err
      Right result -> Right result
  RespError _ msg -> Left msg
  _ -> Left "Unexpected response type"

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // helpers
-- ════════════════════════════════════════════════════════════════════════════

for_ :: forall a. Array a -> (a -> Effect Unit) -> Effect Unit
for_ arr f = case uncons arr of
  Nothing -> pure unit
  Just { head: x, tail: xs } -> f x *> for_ xs f
