-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                // hydrogen // auth // session
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Session and authentication management
-- |
-- | Handles user sessions, token storage, refresh, and auth state.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Auth.Session as Session
-- |
-- | -- Create session manager
-- | session <- Session.create
-- |   { storage: Session.LocalStorage
-- |   , tokenKey: "auth_token"
-- |   , refreshKey: "refresh_token"
-- |   , onExpire: handleLogout
-- |   }
-- |
-- | -- Login
-- | Session.setTokens session { accessToken, refreshToken, expiresIn }
-- |
-- | -- Check auth
-- | isAuthed <- Session.isAuthenticated session
-- |
-- | -- Get token for API calls
-- | maybeToken <- Session.getAccessToken session
-- |
-- | -- Logout
-- | Session.clear session
-- | ```
module Hydrogen.Auth.Session
  ( -- * Types
    Session
  , SessionConfig
  , AuthTokens
  , StorageType(LocalStorage, SessionStorage, MemoryOnly)
  , AuthState(Unauthenticated, Authenticating, Authenticated, Refreshing, Expired)
    -- * Session Management
  , create
  , setTokens
  , clear
  , refresh
    -- * Token Access
  , getAccessToken
  , getRefreshToken
  , isAuthenticated
  , isExpired
    -- * Auth State
  , getAuthState
  , onAuthStateChange
    -- * User Data
  , setUser
  , getUser
  , clearUser
  ) where

import Prelude

import Data.Argonaut (class DecodeJson, class EncodeJson, decodeJson, encodeJson, parseJson, stringify)
import Data.Array as Array
import Data.Either (hush)
import Data.Foldable (traverse_)
import Data.Maybe (Maybe(Nothing, Just), isJust)
import Data.Time.Duration (Milliseconds(Milliseconds))
import Effect (Effect)
import Effect.Aff (Aff, delay, launchAff_)
import Effect.Class (liftEffect)
import Effect.Now (now)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Data.DateTime.Instant (Instant, unInstant)
import Data.Newtype (unwrap)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Session manager
newtype Session user = Session
  { config :: SessionConfig
  , accessToken :: Ref (Maybe String)
  , refreshToken :: Ref (Maybe String)
  , expiresAt :: Ref (Maybe Instant)
  , user :: Ref (Maybe user)
  , authState :: Ref AuthState
  , listeners :: Ref (Array { id :: Int, callback :: AuthState -> Effect Unit })
  }

-- | Session configuration
type SessionConfig =
  { storage :: StorageType
  , tokenKey :: String
  , refreshKey :: String
  , userKey :: String
  , onExpire :: Effect Unit
  , refreshThreshold :: Milliseconds  -- Refresh when this much time left
  , autoRefresh :: Boolean
  }

-- | Auth tokens from login response
type AuthTokens =
  { accessToken :: String
  , refreshToken :: Maybe String
  , expiresIn :: Int  -- Seconds until expiration
  }

-- | Storage backend
data StorageType
  = LocalStorage
  | SessionStorage
  | MemoryOnly

derive instance eqStorageType :: Eq StorageType

-- | Authentication state
data AuthState
  = Unauthenticated
  | Authenticating
  | Authenticated
  | Refreshing
  | Expired

derive instance eqAuthState :: Eq AuthState

instance showAuthState :: Show AuthState where
  show Unauthenticated = "Unauthenticated"
  show Authenticating = "Authenticating"
  show Authenticated = "Authenticated"
  show Refreshing = "Refreshing"
  show Expired = "Expired"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // FFI
-- ═════════════════════════════════════════════════════════════════════════════

foreign import getStorageItem :: String -> String -> Effect (Maybe String)

foreign import setStorageItem :: String -> String -> String -> Effect Unit

foreign import removeStorageItem :: String -> String -> Effect Unit

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // session management
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default session configuration
defaultConfig :: SessionConfig
defaultConfig =
  { storage: LocalStorage
  , tokenKey: "hydrogen_access_token"
  , refreshKey: "hydrogen_refresh_token"
  , userKey: "hydrogen_user"
  , onExpire: pure unit
  , refreshThreshold: Milliseconds 60000.0  -- Refresh when < 1 min left
  , autoRefresh: true
  }

-- | Create a new session manager
create :: forall user. DecodeJson user => SessionConfig -> Effect (Session user)
create config = do
  accessToken <- Ref.new Nothing
  refreshToken <- Ref.new Nothing
  expiresAt <- Ref.new Nothing
  user <- Ref.new Nothing
  authState <- Ref.new Unauthenticated
  listeners <- Ref.new []
  
  let session = Session
        { config
        , accessToken
        , refreshToken
        , expiresAt
        , user
        , authState
        , listeners
        }
  
  -- Try to restore from storage
  restoreFromStorage session
  
  pure session

-- | Restore session from storage
restoreFromStorage :: forall user. DecodeJson user => Session user -> Effect Unit
restoreFromStorage session@(Session s) = do
  let storageKey = storageTypeToKey s.config.storage
  
  -- Restore access token
  maybeToken <- getStorageItem storageKey s.config.tokenKey
  case maybeToken of
    Nothing -> pure unit
    Just token -> do
      Ref.write (Just token) s.accessToken
      setAuthState session Authenticated
  
  -- Restore refresh token
  maybeRefresh <- getStorageItem storageKey s.config.refreshKey
  Ref.write maybeRefresh s.refreshToken
  
  -- Restore user
  maybeUserJson <- getStorageItem storageKey s.config.userKey
  case maybeUserJson >>= (parseJson >>> hush) >>= (decodeJson >>> hush) of
    Nothing -> pure unit
    Just u -> Ref.write (Just u) s.user

-- | Set tokens after login
setTokens :: forall user. Session user -> AuthTokens -> Effect Unit
setTokens session@(Session s) tokens = do
  let storageKey = storageTypeToKey s.config.storage
  
  -- Store access token
  Ref.write (Just tokens.accessToken) s.accessToken
  setStorageItem storageKey s.config.tokenKey tokens.accessToken
  
  -- Store refresh token if provided
  case tokens.refreshToken of
    Nothing -> pure unit
    Just rt -> do
      Ref.write (Just rt) s.refreshToken
      setStorageItem storageKey s.config.refreshKey rt
  
  -- Calculate expiration
  currentTime <- now
  let expiresMs = unwrap (unInstant currentTime) + (toNumber tokens.expiresIn * 1000.0)
  -- Note: Would need to convert back to Instant properly
  
  setAuthState session Authenticated

-- | Clear session (logout)
clear :: forall user. Session user -> Effect Unit
clear session@(Session s) = do
  let storageKey = storageTypeToKey s.config.storage
  
  Ref.write Nothing s.accessToken
  Ref.write Nothing s.refreshToken
  Ref.write Nothing s.expiresAt
  Ref.write Nothing s.user
  
  removeStorageItem storageKey s.config.tokenKey
  removeStorageItem storageKey s.config.refreshKey
  removeStorageItem storageKey s.config.userKey
  
  setAuthState session Unauthenticated

-- | Refresh the session (call your refresh endpoint)
refresh :: forall user. Session user -> Aff AuthTokens -> Aff (Maybe AuthTokens)
refresh session@(Session s) refreshFn = do
  liftEffect $ setAuthState session Refreshing
  
  maybeRefreshToken <- liftEffect $ Ref.read s.refreshToken
  case maybeRefreshToken of
    Nothing -> do
      liftEffect $ setAuthState session Expired
      liftEffect $ s.config.onExpire
      pure Nothing
    Just _ -> do
      result <- refreshFn
      liftEffect $ setTokens session result
      pure $ Just result

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // token access
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the current access token
getAccessToken :: forall user. Session user -> Effect (Maybe String)
getAccessToken (Session { accessToken }) = Ref.read accessToken

-- | Get the current refresh token
getRefreshToken :: forall user. Session user -> Effect (Maybe String)
getRefreshToken (Session { refreshToken }) = Ref.read refreshToken

-- | Check if user is authenticated
isAuthenticated :: forall user. Session user -> Effect Boolean
isAuthenticated (Session { accessToken }) = do
  token <- Ref.read accessToken
  pure $ isJust token

-- | Check if session is expired
isExpired :: forall user. Session user -> Effect Boolean
isExpired (Session { expiresAt }) = do
  maybeExpires <- Ref.read expiresAt
  case maybeExpires of
    Nothing -> pure false
    Just expires -> do
      currentTime <- now
      pure $ unInstant currentTime > unInstant expires

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // auth state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get current auth state
getAuthState :: forall user. Session user -> Effect AuthState
getAuthState (Session { authState }) = Ref.read authState

-- | Set auth state and notify listeners
setAuthState :: forall user. Session user -> AuthState -> Effect Unit
setAuthState (Session { authState, listeners }) newState = do
  Ref.write newState authState
  subs <- Ref.read listeners
  for_ subs \listener -> listener.callback newState
  where
  for_ arr f = traverse_ f arr

-- | Subscribe to auth state changes
onAuthStateChange :: forall user. Session user -> (AuthState -> Effect Unit) -> Effect (Effect Unit)
onAuthStateChange (Session { listeners }) callback = do
  subs <- Ref.read listeners
  let nextId = case Array.last subs of
        Nothing -> 0
        Just s -> s.id + 1
  let sub = { id: nextId, callback }
  Ref.modify_ (flip Array.snoc sub) listeners
  pure $ Ref.modify_ (Array.filter (\s -> s.id /= nextId)) listeners

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // user data
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set user data
setUser :: forall user. EncodeJson user => Session user -> user -> Effect Unit
setUser (Session s) userData = do
  Ref.write (Just userData) s.user
  let storageKey = storageTypeToKey s.config.storage
  setStorageItem storageKey s.config.userKey (stringify $ encodeJson userData)

-- | Get user data
getUser :: forall user. Session user -> Effect (Maybe user)
getUser (Session { user }) = Ref.read user

-- | Clear user data
clearUser :: forall user. Session user -> Effect Unit
clearUser (Session s) = do
  Ref.write Nothing s.user
  let storageKey = storageTypeToKey s.config.storage
  removeStorageItem storageKey s.config.userKey

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

storageTypeToKey :: StorageType -> String
storageTypeToKey = case _ of
  LocalStorage -> "localStorage"
  SessionStorage -> "sessionStorage"
  MemoryOnly -> "memory"

toNumber :: Int -> Number
toNumber n = if n <= 0 then 0.0 else 1.0 + toNumber (n - 1)
