-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                 // hydrogen // service-worker
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Service Worker registration and communication
-- |
-- | PWA support with service worker lifecycle management.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Offline.ServiceWorker as SW
-- |
-- | -- Register service worker
-- | registration <- SW.register "/sw.js"
-- |
-- | -- Check for updates
-- | SW.checkForUpdate registration
-- |
-- | -- Listen for state changes
-- | SW.onStateChange registration \state ->
-- |   case state of
-- |     SW.Installing -> showToast "Installing update..."
-- |     SW.Activated -> showToast "App updated!"
-- |     _ -> pure unit
-- |
-- | -- Post message to SW
-- | SW.postMessage registration { type: "SKIP_WAITING" }
-- | ```
module Hydrogen.Offline.ServiceWorker
  ( -- * Types
    Registration
  , ServiceWorkerState(..)
  , UpdateFoundHandler
    -- * Registration
  , register
  , unregister
  , getRegistration
    -- * Updates
  , checkForUpdate
  , skipWaiting
  , onUpdateFound
    -- * State
  , getState
  , onStateChange
    -- * Communication
  , postMessage
  , onMessage
    -- * Utilities
  , isSupported
  , isControlled
  ) where

import Prelude

import Data.Either (Either(Left, Right))
import Data.Maybe (Maybe(Just, Nothing))
import Effect (Effect)
import Effect.Aff (Aff, makeAff, nonCanceler)
import Effect.Exception (Error)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Service Worker Registration
foreign import data Registration :: Type

-- | Service Worker state
data ServiceWorkerState
  = Installing
  | Installed
  | Activating
  | Activated
  | Redundant

derive instance eqServiceWorkerState :: Eq ServiceWorkerState

instance showServiceWorkerState :: Show ServiceWorkerState where
  show Installing = "installing"
  show Installed = "installed"
  show Activating = "activating"
  show Activated = "activated"
  show Redundant = "redundant"

-- | Handler for update found events
type UpdateFoundHandler = Effect Unit

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // FFI
-- ═════════════════════════════════════════════════════════════════════════════

foreign import isSupportedImpl :: Effect Boolean

foreign import registerImpl 
  :: String 
  -> (Error -> Effect Unit) 
  -> (Registration -> Effect Unit) 
  -> Effect Unit

foreign import unregisterImpl 
  :: Registration 
  -> (Error -> Effect Unit) 
  -> (Boolean -> Effect Unit) 
  -> Effect Unit

foreign import getRegistrationImpl 
  :: (Error -> Effect Unit) 
  -> (Registration -> Effect Unit) 
  -> Effect Unit 
  -> Effect Unit

foreign import updateImpl 
  :: Registration 
  -> (Error -> Effect Unit) 
  -> Effect Unit 
  -> Effect Unit

foreign import onUpdateFoundImpl :: Registration -> Effect Unit -> Effect Unit

foreign import onStateChangeImpl :: Registration -> (String -> Effect Unit) -> Effect Unit

foreign import postMessageImpl :: Registration -> String -> Effect Unit

foreign import onMessageImpl :: (String -> Effect Unit) -> Effect Unit

foreign import isControlledImpl :: Effect Boolean

foreign import skipWaitingImpl :: Registration -> Effect Unit

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // registration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if service workers are supported
isSupported :: Effect Boolean
isSupported = isSupportedImpl

-- | Register a service worker
register :: String -> Aff Registration
register scriptUrl = makeAff \callback -> do
  registerImpl scriptUrl
    (\err -> callback (Left err))
    (\reg -> callback (Right reg))
  pure nonCanceler

-- | Unregister a service worker
unregister :: Registration -> Aff Boolean
unregister reg = makeAff \callback -> do
  unregisterImpl reg
    (\err -> callback (Left err))
    (\success -> callback (Right success))
  pure nonCanceler

-- | Get existing registration
getRegistration :: Aff (Maybe Registration)
getRegistration = makeAff \callback -> do
  getRegistrationImpl
    (\err -> callback (Left err))
    (\reg -> callback (Right (Just reg)))
    (callback (Right Nothing))
  pure nonCanceler

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // updates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check for service worker updates
checkForUpdate :: Registration -> Aff Unit
checkForUpdate reg = makeAff \callback -> do
  updateImpl reg
    (\err -> callback (Left err))
    (callback (Right unit))
  pure nonCanceler

-- | Tell waiting service worker to skip waiting and activate
skipWaiting :: Registration -> Effect Unit
skipWaiting = skipWaitingImpl

-- | Listen for update found events
onUpdateFound :: Registration -> UpdateFoundHandler -> Effect Unit
onUpdateFound = onUpdateFoundImpl

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get current service worker state
getState :: Registration -> Effect (Maybe ServiceWorkerState)
getState _reg = pure Nothing  -- Would need FFI

-- | Listen for state changes
onStateChange :: Registration -> (ServiceWorkerState -> Effect Unit) -> Effect Unit
onStateChange reg callback = 
  onStateChangeImpl reg \stateStr -> 
    callback (parseState stateStr)
  where
  parseState = case _ of
    "installing" -> Installing
    "installed" -> Installed
    "activating" -> Activating
    "activated" -> Activated
    "redundant" -> Redundant
    _ -> Redundant

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // communication
-- ═════════════════════════════════════════════════════════════════════════════

-- | Post a message to the service worker
postMessage :: Registration -> String -> Effect Unit
postMessage = postMessageImpl

-- | Listen for messages from the service worker
onMessage :: (String -> Effect Unit) -> Effect Unit
onMessage = onMessageImpl

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if page is controlled by a service worker
isControlled :: Effect Boolean
isControlled = isControlledImpl
