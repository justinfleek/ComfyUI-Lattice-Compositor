# Hydrogen.API.Client

HTTP client with JSON encoding, authentication, and logging.

## Overview

```purescript
import Hydrogen.API.Client (get, post, put, patch, delete, defaultConfig, withAuth)

-- Configure
config :: ApiConfig
config = defaultConfig
  { baseUrl = "https://api.example.com/v1"
  , logging = true
  }
  # withAuth token

-- Make requests
users <- get config "/users"              -- GET
user <- post config "/users" newUser      -- POST with body
user <- put config "/users/123" userData  -- PUT
user <- patch config "/users/123" updates -- PATCH
_ <- delete config "/users/123"           -- DELETE
```

## Configuration

```purescript
type ApiConfig =
  { baseUrl :: String
  , authToken :: Maybe String
  , logging :: Boolean
  }

defaultConfig :: ApiConfig
defaultConfig =
  { baseUrl: ""
  , authToken: Nothing
  , logging: false
  }
```

### Adding Auth

```purescript
-- Bearer token auth
configWithAuth = config # withAuth "my-jwt-token"
-- Adds header: Authorization: Bearer my-jwt-token

-- Check if authed
isAuthed = isJust config.authToken
```

### Logging

When `logging = true`, requests are logged to console:

```
[API] GET /users -> 200 (142ms)
[API] POST /users -> 201 (89ms)
[API] GET /users/999 -> 404 (45ms)
```

## Request Functions

All requests return `Aff (Either String a)`:

```purescript
get :: forall a. DecodeJson a => ApiConfig -> String -> Aff (Either String a)
post :: forall a b. EncodeJson a => DecodeJson b => ApiConfig -> String -> a -> Aff (Either String b)
put :: forall a b. EncodeJson a => DecodeJson b => ApiConfig -> String -> a -> Aff (Either String b)
patch :: forall a b. EncodeJson a => DecodeJson b => ApiConfig -> String -> a -> Aff (Either String b)
delete :: forall a. DecodeJson a => ApiConfig -> String -> Aff (Either String a)
```

### Error Handling

Errors are returned as `Left String`:

```purescript
result <- get config "/users"
case result of
  Left err -> logError err   -- "404: Not Found" or "Network error: ..."
  Right users -> handleUsers users
```

### JSON Encoding

Request bodies are automatically encoded via Argonaut:

```purescript
newtype User = User { name :: String, email :: String }
derive instance Generic User _
instance EncodeJson User where encodeJson = genericEncodeJson
instance DecodeJson User where decodeJson = genericDecodeJson

-- Just pass the value
result <- post config "/users" (User { name: "Alice", email: "alice@example.com" })
```

## Integration with Query

Use API client functions as the `fetch` in Query:

```purescript
import Hydrogen.Query as Q

userQuery userId = Q.query client
  { key: ["user", userId]
  , fetch: get apiConfig ("/users/" <> userId)
  , staleTime: Just (Milliseconds 30000.0)
  , retry: 2
  , retryDelay: Milliseconds 1000.0
  }
```
