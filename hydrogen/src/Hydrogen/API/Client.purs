-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                  // hydrogen // api // client
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Generic HTTP API client infrastructure
-- |
-- | This module provides a typed HTTP client with:
-- | - Configuration (base URL, auth token)
-- | - JSON encoding/decoding via Argonaut
-- | - Error handling with descriptive messages
-- | - Request logging (configurable)
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | -- Define your config
-- | config :: ApiConfig
-- | config = defaultConfig 
-- |   { baseUrl = "https://api.example.com"
-- |   } # withAuth myToken
-- |
-- | -- Make requests
-- | getUsers :: Aff (Either String (Array User))
-- | getUsers = get config "/users"
-- |
-- | createUser :: User -> Aff (Either String User)
-- | createUser user = post config "/users" user
-- | ```
module Hydrogen.API.Client
  ( -- * Configuration
    ApiConfig
  , defaultConfig
  , withAuth
  , withLogging
    -- * HTTP methods
  , get
  , post
  , put
  , patch
  , delete
    -- * Low-level
  , request
  , ApiResult
  ) where

import Prelude
  ( Unit
  , bind
  , discard
  , pure
  , show
  , unit
  , when
  , ($)
  , (<>)
  , (<<<)
  , (<$>)
  )

import Affjax.Web as AX
import Affjax.RequestBody as RequestBody
import Affjax.ResponseFormat as ResponseFormat
import Affjax.RequestHeader (RequestHeader(ContentType, RequestHeader))
import Data.Argonaut.Core (Json)
import Data.Argonaut.Decode (class DecodeJson, decodeJson, printJsonDecodeError)
import Data.Argonaut.Encode (class EncodeJson, encodeJson)
import Data.Either (Either(Left, Right))
import Data.HTTP.Method (Method(GET, POST, PUT, PATCH, DELETE))
import Data.Maybe (Maybe(Nothing, Just))
import Data.MediaType (MediaType(MediaType))
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Console as Console

-- ============================================================
-- CONFIGURATION
-- ============================================================

-- | API client configuration
type ApiConfig =
  { baseUrl :: String      -- ^ Base URL for all requests (e.g., "https://api.example.com")
  , authToken :: Maybe String  -- ^ Optional Bearer token for authentication
  , logging :: Boolean     -- ^ Whether to log requests/responses to console
  }

-- | Default configuration with empty base URL and no auth
defaultConfig :: ApiConfig
defaultConfig =
  { baseUrl: ""
  , authToken: Nothing
  , logging: false
  }

-- | Add Bearer token authentication to config
withAuth :: String -> ApiConfig -> ApiConfig
withAuth token config = config { authToken = Just token }

-- | Enable/disable request logging
withLogging :: Boolean -> ApiConfig -> ApiConfig
withLogging enabled config = config { logging = enabled }

-- ============================================================
-- TYPES
-- ============================================================

-- | Result type for API calls
type ApiResult a = Aff (Either String a)

-- ============================================================
-- HTTP METHODS
-- ============================================================

-- | Perform a GET request
get :: forall a. DecodeJson a => ApiConfig -> String -> ApiResult a
get config path = request config GET path (Nothing :: Maybe Unit)

-- | Perform a POST request with JSON body
post :: forall body a. EncodeJson body => DecodeJson a => ApiConfig -> String -> body -> ApiResult a
post config path body = request config POST path (Just body)

-- | Perform a PUT request with JSON body
put :: forall body a. EncodeJson body => DecodeJson a => ApiConfig -> String -> body -> ApiResult a
put config path body = request config PUT path (Just body)

-- | Perform a PATCH request with JSON body
patch :: forall body a. EncodeJson body => DecodeJson a => ApiConfig -> String -> body -> ApiResult a
patch config path body = request config PATCH path (Just body)

-- | Perform a DELETE request (no response body expected)
delete :: ApiConfig -> String -> Aff (Either String Unit)
delete config path = do
  let url = config.baseUrl <> path
  logRequest config "DELETE" url
  
  result <- AX.request $ AX.defaultRequest
    { url = url
    , method = Left DELETE
    , headers = headers config
    , responseFormat = ResponseFormat.json
    }
  
  case result of
    Left err -> do
      let errMsg = AX.printError err
      logError config "DELETE" url errMsg
      pure $ Left errMsg
    Right _ -> do
      logSuccess config "DELETE" url
      pure $ Right unit

-- ============================================================
-- LOW-LEVEL REQUEST
-- ============================================================

-- | Perform an HTTP request with optional JSON body
request 
  :: forall body a
   . EncodeJson body 
  => DecodeJson a 
  => ApiConfig 
  -> Method 
  -> String 
  -> Maybe body 
  -> ApiResult a
request config method path maybeBody = do
  let url = config.baseUrl <> path
  let methodStr = show method
  logRequest config methodStr url
  
  result <- AX.request $ AX.defaultRequest
    { url = url
    , method = Left method
    , headers = headers config
    , content = RequestBody.json <<< encodeJson <$> maybeBody
    , responseFormat = ResponseFormat.json
    }
  
  case result of
    Left err -> do
      let errMsg = AX.printError err
      logError config methodStr url errMsg
      pure $ Left errMsg
    Right response -> do
      logSuccess config methodStr url
      pure $ decode response.body

-- ============================================================
-- HELPERS
-- ============================================================

headers :: ApiConfig -> Array RequestHeader
headers config = case config.authToken of
  Nothing -> [ ContentType (MediaType "application/json") ]
  Just token ->
    [ ContentType (MediaType "application/json")
    , RequestHeader "Authorization" ("Bearer " <> token)
    ]

decode :: forall a. DecodeJson a => Json -> Either String a
decode json = case decodeJson json of
  Left err -> Left (printJsonDecodeError err)
  Right val -> Right val

logRequest :: ApiConfig -> String -> String -> Aff Unit
logRequest config method url =
  when config.logging do
    liftEffect $ Console.log $ "[API] " <> method <> " " <> url

logSuccess :: ApiConfig -> String -> String -> Aff Unit
logSuccess config method url =
  when config.logging do
    liftEffect $ Console.log $ "[API] " <> method <> " " <> url <> " OK"

logError :: ApiConfig -> String -> String -> String -> Aff Unit
logError config method url err =
  when config.logging do
    liftEffect $ Console.error $ "[API] " <> method <> " " <> url <> " FAILED: " <> err
