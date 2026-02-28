-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                 // hydrogen // runtime // cmd
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Hydrogen Commands — Pure Descriptions of Side Effects
-- |
-- | Commands are data, not effects. They describe what should happen:
-- |
-- | ```purescript
-- | -- A command to fetch user data
-- | fetchUser :: Int -> Cmd Msg
-- | fetchUser id = Http
-- |   { method: GET
-- |   , url: "/api/users/" <> show id
-- |   , expect: UserLoaded
-- |   }
-- | ```
-- |
-- | The runtime interprets commands, turning descriptions into effects.
-- | This separation enables:
-- |
-- | - **Testing** — Verify commands without executing effects
-- | - **Determinism** — Same inputs produce same command descriptions
-- | - **Composition** — Batch, sequence, and transform commands
-- |
-- | ## The Update Signature
-- |
-- | With commands, update returns both new state and commands:
-- |
-- | ```purescript
-- | update :: msg -> state -> Transition state msg
-- |
-- | type Transition state msg =
-- |   { state :: state
-- |   , cmd :: Cmd msg
-- |   }
-- | ```
-- |
-- | ## Building Commands
-- |
-- | ```purescript
-- | -- No effect
-- | none :: Cmd msg
-- |
-- | -- Combine commands
-- | batch :: Array (Cmd msg) -> Cmd msg
-- |
-- | -- Delay then dispatch
-- | delay :: Milliseconds -> msg -> Cmd msg
-- |
-- | -- HTTP request
-- | http :: HttpRequest msg -> Cmd msg
-- | ```
module Hydrogen.Runtime.Cmd
  ( -- * Command Type
    Cmd(..)
  
  -- * Transition Type
  , Transition
  , transition
  , noCmd
  
  -- * Building Commands
  , none
  , batch
  , delay
  , interval
  , animationFrame
  , http
  , focus
  , blur
  , pushUrl
  , replaceUrl
  , back
  , forward
  , getStorage
  , setStorage
  , removeStorage
  , copyToClipboard
  , log
  
  -- * HTTP Types
  , HttpRequest
  , HttpMethod(..)
  , HttpResult(..)
  , HttpSuccess
  , HttpError(..)
  , HttpErrorContext
  
  -- * HTTP Result Constructors (for FFI)
  , mkHttpOk
  , mkTimeoutError
  , mkNetworkError
  , mkCorsError
  , mkMixedContentError
  , mkInvalidUrlError
  , mkAbortedError
  , mkUnknownError
  
  -- * Transforming Commands
  , mapCmd
  ) where

import Prelude
  ( class Functor
  , class Show
  , map
  , show
  , (<>)
  )

import Data.Array (length) as Array
import Data.Maybe (Maybe)
import Data.Tuple (Tuple)
import Foreign (Foreign)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // command type
-- ═════════════════════════════════════════════════════════════════════════════

-- | A Command is a pure description of a side effect.
-- |
-- | Commands are data. They don't do anything until the runtime interprets them.
-- | The `msg` type parameter is the message type that will be dispatched when
-- | the effect completes.
data Cmd msg
  = None
    -- ^ No effect
  
  | Batch (Array (Cmd msg))
    -- ^ Multiple commands executed in parallel
  
  | Delay Number msg
    -- ^ Dispatch message after delay (milliseconds)
  
  | Interval Number msg
    -- ^ Dispatch message repeatedly at interval (milliseconds)
    -- ^ Returns a subscription that can be cancelled
  
  | AnimationFrame (Number -> msg)
    -- ^ Request animation frame, pass timestamp to message
  
  | Http (HttpRequest msg)
    -- ^ HTTP request
  
  | Focus String
    -- ^ Focus element by ID
  
  | Blur String
    -- ^ Blur element by ID
  
  | PushUrl String
    -- ^ Push URL to browser history
  
  | ReplaceUrl String
    -- ^ Replace current URL in browser history
  
  | Back
    -- ^ Navigate back in history
  
  | Forward
    -- ^ Navigate forward in history
  
  | GetStorage String (Maybe String -> msg)
    -- ^ Get value from localStorage
  
  | SetStorage String String
    -- ^ Set value in localStorage
  
  | RemoveStorage String
    -- ^ Remove key from localStorage
  
  | CopyToClipboard String
    -- ^ Copy text to clipboard
  
  | Log String
    -- ^ Log to console (for debugging)

instance functorCmd :: Functor Cmd where
  map f = case _ of
    None -> None
    Batch cmds -> Batch (map (map f) cmds)
    Delay ms msg -> Delay ms (f msg)
    Interval ms msg -> Interval ms (f msg)
    AnimationFrame g -> AnimationFrame (f <<< g)
    Http req -> Http req { expect = f <<< req.expect }
    Focus id -> Focus id
    Blur id -> Blur id
    PushUrl url -> PushUrl url
    ReplaceUrl url -> ReplaceUrl url
    Back -> Back
    Forward -> Forward
    GetStorage key g -> GetStorage key (f <<< g)
    SetStorage key value -> SetStorage key value
    RemoveStorage key -> RemoveStorage key
    CopyToClipboard text -> CopyToClipboard text
    Log text -> Log text

instance showCmd :: Show (Cmd msg) where
  show = case _ of
    None -> "None"
    Batch cmds -> "Batch [" <> show (length cmds) <> " commands]"
    Delay ms _ -> "Delay " <> show ms <> "ms"
    Interval ms _ -> "Interval " <> show ms <> "ms"
    AnimationFrame _ -> "AnimationFrame"
    Http req -> "Http " <> show req.method <> " " <> req.url
    Focus id -> "Focus " <> show id
    Blur id -> "Blur " <> show id
    PushUrl url -> "PushUrl " <> show url
    ReplaceUrl url -> "ReplaceUrl " <> show url
    Back -> "Back"
    Forward -> "Forward"
    GetStorage key _ -> "GetStorage " <> show key
    SetStorage key _ -> "SetStorage " <> show key
    RemoveStorage key -> "RemoveStorage " <> show key
    CopyToClipboard _ -> "CopyToClipboard"
    Log text -> "Log " <> show text

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // transition type
-- ═════════════════════════════════════════════════════════════════════════════

-- | A Transition is the result of an update: new state plus commands.
-- |
-- | ```purescript
-- | update :: Msg -> State -> Transition State Msg
-- | update msg state = case msg of
-- |   Increment -> noCmd state { count = state.count + 1 }
-- |   FetchData -> transition state { loading = true } (http fetchRequest)
-- | ```
type Transition state msg =
  { state :: state
  , cmd :: Cmd msg
  }

-- | Create a transition with state and command
transition :: forall state msg. state -> Cmd msg -> Transition state msg
transition state cmd = { state, cmd }

-- | Create a transition with no command
noCmd :: forall state msg. state -> Transition state msg
noCmd state = { state, cmd: None }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // command constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | No effect command
none :: forall msg. Cmd msg
none = None

-- | Batch multiple commands to execute in parallel
batch :: forall msg. Array (Cmd msg) -> Cmd msg
batch = Batch

-- | Dispatch a message after a delay (milliseconds)
delay :: forall msg. Number -> msg -> Cmd msg
delay = Delay

-- | Dispatch a message repeatedly at an interval (milliseconds)
-- |
-- | The returned subscription ID can be used to cancel via another command.
interval :: forall msg. Number -> msg -> Cmd msg
interval = Interval

-- | Request animation frame
-- |
-- | Calls back with high-resolution timestamp for smooth animations.
animationFrame :: forall msg. (Number -> msg) -> Cmd msg
animationFrame = AnimationFrame

-- | Make an HTTP request
http :: forall msg. HttpRequest msg -> Cmd msg
http = Http

-- | Focus an element by ID
focus :: forall msg. String -> Cmd msg
focus = Focus

-- | Blur an element by ID
blur :: forall msg. String -> Cmd msg
blur = Blur

-- | Push a URL to browser history (triggers navigation)
pushUrl :: forall msg. String -> Cmd msg
pushUrl = PushUrl

-- | Replace current URL in browser history
replaceUrl :: forall msg. String -> Cmd msg
replaceUrl = ReplaceUrl

-- | Navigate back in browser history
back :: forall msg. Cmd msg
back = Back

-- | Navigate forward in browser history
forward :: forall msg. Cmd msg
forward = Forward

-- | Get a value from localStorage
getStorage :: forall msg. String -> (Maybe String -> msg) -> Cmd msg
getStorage = GetStorage

-- | Set a value in localStorage
setStorage :: forall msg. String -> String -> Cmd msg
setStorage = SetStorage

-- | Remove a key from localStorage
removeStorage :: forall msg. String -> Cmd msg
removeStorage = RemoveStorage

-- | Copy text to clipboard
copyToClipboard :: forall msg. String -> Cmd msg
copyToClipboard = CopyToClipboard

-- | Log a message to console (for debugging)
log :: forall msg. String -> Cmd msg
log = Log

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // http types
-- ═════════════════════════════════════════════════════════════════════════════

-- | HTTP request configuration
type HttpRequest msg =
  { method :: HttpMethod
  , url :: String
  , headers :: Array (Tuple String String)
  , body :: Maybe Foreign
  , expect :: HttpResult -> msg
  , timeout :: Maybe Number
  }

-- | HTTP methods
data HttpMethod
  = GET
  | POST
  | PUT
  | PATCH
  | DELETE
  | HEAD
  | OPTIONS

instance showHttpMethod :: Show HttpMethod where
  show = case _ of
    GET -> "GET"
    POST -> "POST"
    PUT -> "PUT"
    PATCH -> "PATCH"
    DELETE -> "DELETE"
    HEAD -> "HEAD"
    OPTIONS -> "OPTIONS"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // http // result
-- ═════════════════════════════════════════════════════════════════════════════

-- | HTTP result — either success or a structured error
-- |
-- | This type makes failure explicit at the type level. There is no ambiguity:
-- | - `HttpOk` means the request completed and the server responded
-- | - `HttpErr` means something prevented the request from completing
data HttpResult
  = HttpOk HttpSuccess
  | HttpErr HttpError

-- | Successful HTTP response
-- |
-- | Note: "Success" here means "the server responded" — even 4xx/5xx status
-- | codes are HttpOk because the HTTP transaction completed. The application
-- | decides whether a 404 is an error for its use case.
type HttpSuccess =
  { status :: Int
  , statusText :: String
  , headers :: Array (Tuple String String)
  , body :: Foreign
  }

-- | HTTP error — something prevented the request from completing
-- |
-- | Each variant describes a specific failure mode with:
-- | - What happened (the constructor)
-- | - Context (url, method, timestamp)
-- | - Why it happened (cause)
-- | - How to fix it (suggestions array)
data HttpError
  = TimeoutError HttpErrorContext
    -- ^ Request exceeded the specified timeout
  
  | NetworkError HttpErrorContext
    -- ^ Could not establish connection (DNS failure, connection refused,
    -- ^ server unreachable, no internet)
  
  | CorsError HttpErrorContext
    -- ^ Server rejected request due to CORS policy
  
  | MixedContentError HttpErrorContext
    -- ^ HTTPS page tried to load HTTP resource
  
  | InvalidUrlError HttpErrorContext
    -- ^ URL is malformed or invalid
  
  | AbortedError HttpErrorContext
    -- ^ Request was manually aborted
  
  | UnknownError HttpErrorContext
    -- ^ Unexpected error — check context for details

-- | Context for HTTP errors
-- |
-- | Every error includes full context so debugging never requires guesswork.
type HttpErrorContext =
  { url :: String
    -- ^ The URL that was requested
  , method :: String
    -- ^ The HTTP method (GET, POST, etc.)
  , timestamp :: String
    -- ^ ISO 8601 timestamp when error occurred
  , cause :: String
    -- ^ Human-readable explanation of why this happened
  , suggestions :: Array String
    -- ^ Actionable steps to resolve the error
  , browserError :: String
    -- ^ Raw error name from browser (for debugging)
  , browserMessage :: String
    -- ^ Raw error message from browser (for debugging)
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                             // http // result // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | These functions are used by the FFI to construct HttpResult values.
-- | They're simple wrappers around the data constructors that can be called
-- | from JavaScript.

-- | Construct a successful HTTP result
mkHttpOk :: HttpSuccess -> HttpResult
mkHttpOk = HttpOk

-- | Construct a timeout error
mkTimeoutError :: HttpErrorContext -> HttpResult
mkTimeoutError ctx = HttpErr (TimeoutError ctx)

-- | Construct a network error
mkNetworkError :: HttpErrorContext -> HttpResult
mkNetworkError ctx = HttpErr (NetworkError ctx)

-- | Construct a CORS error
mkCorsError :: HttpErrorContext -> HttpResult
mkCorsError ctx = HttpErr (CorsError ctx)

-- | Construct a mixed content error
mkMixedContentError :: HttpErrorContext -> HttpResult
mkMixedContentError ctx = HttpErr (MixedContentError ctx)

-- | Construct an invalid URL error
mkInvalidUrlError :: HttpErrorContext -> HttpResult
mkInvalidUrlError ctx = HttpErr (InvalidUrlError ctx)

-- | Construct an aborted request error
mkAbortedError :: HttpErrorContext -> HttpResult
mkAbortedError ctx = HttpErr (AbortedError ctx)

-- | Construct an unknown error
mkUnknownError :: HttpErrorContext -> HttpResult
mkUnknownError ctx = HttpErr (UnknownError ctx)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // command transformation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Transform messages in a command
-- |
-- | Useful for composing commands from child components:
-- |
-- | ```purescript
-- | mapCmd CounterMsg counterCmd
-- | ```
mapCmd :: forall a b. (a -> b) -> Cmd a -> Cmd b
mapCmd = map

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- Function composition operator
infixr 9 compose as <<<

compose :: forall a b c. (b -> c) -> (a -> b) -> (a -> c)
compose f g x = f (g x)

-- Array length (needed for Show instance)
-- Pure implementation using Data.Array.length
length :: forall a. Array a -> Int
length = Array.length
