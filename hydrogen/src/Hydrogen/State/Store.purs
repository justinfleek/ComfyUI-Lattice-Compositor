-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                 // hydrogen // state // store
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Redux-style centralized store with actions and reducers
-- |
-- | For applications that prefer a single source of truth with
-- | predictable state updates via actions.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.State.Store as Store
-- |
-- | -- Define your state
-- | type AppState = { count :: Int, user :: Maybe User }
-- |
-- | -- Define actions
-- | data Action = Increment | Decrement | SetUser User | Logout
-- |
-- | -- Define reducer
-- | reducer :: AppState -> Action -> AppState
-- | reducer state = case _ of
-- |   Increment -> state { count = state.count + 1 }
-- |   Decrement -> state { count = state.count - 1 }
-- |   SetUser u -> state { user = Just u }
-- |   Logout -> state { user = Nothing }
-- |
-- | -- Create store
-- | store <- Store.createStore { count: 0, user: Nothing } reducer
-- |
-- | -- Dispatch actions
-- | Store.dispatch store Increment
-- |
-- | -- Get state
-- | state <- Store.getState store
-- |
-- | -- Subscribe
-- | unsub <- Store.subscribe store \state -> render state
-- | ```
module Hydrogen.State.Store
  ( -- * Store Types
    Store
  , Reducer
  , Middleware
  , Listener
    -- * Store Creation
  , createStore
  , createStoreWithMiddleware
    -- * Store Operations
  , dispatch
  , getState
  , subscribe
  , replaceReducer
    -- * Middleware
  , loggerMiddleware
  , thunkMiddleware
    -- * Selectors
  , select
  , selectWith
    -- * Utilities
  , combineReducers
  ) where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(Just, Nothing))
import Effect (Effect)
import Effect.Aff (Aff, launchAff_)
import Effect.Class (liftEffect)
import Effect.Class.Console as Console
import Effect.Ref (Ref)
import Effect.Ref as Ref

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | A store holds state and manages updates via a reducer
newtype Store state action = Store
  { state :: Ref state
  , reducer :: Ref (Reducer state action)
  , listeners :: Ref (Array (StoreListener state))
  , middleware :: Array (Middleware state action)
  , nextListenerId :: Ref Int
  }

-- | A reducer takes state and action, returns new state
type Reducer state action = state -> action -> state

-- | A listener is called when state changes
type Listener state = state -> Effect Unit

-- | Listener with ID for unsubscription
type StoreListener state = { id :: Int, callback :: state -> Effect Unit }

-- | Middleware can intercept actions before they reach the reducer
type Middleware state action = 
  { getState :: Effect state
  , dispatch :: action -> Effect Unit
  } -> (action -> Effect Unit) -> action -> Effect Unit

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // store creation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a new store with initial state and reducer
createStore :: forall state action. state -> Reducer state action -> Effect (Store state action)
createStore initialState reducer = createStoreWithMiddleware initialState reducer []

-- | Create a store with middleware
createStoreWithMiddleware 
  :: forall state action
   . state 
  -> Reducer state action 
  -> Array (Middleware state action)
  -> Effect (Store state action)
createStoreWithMiddleware initialState reducer middleware = do
  stateRef <- Ref.new initialState
  reducerRef <- Ref.new reducer
  listenersRef <- Ref.new []
  nextListenerIdRef <- Ref.new 0
  pure $ Store 
    { state: stateRef
    , reducer: reducerRef
    , listeners: listenersRef
    , middleware
    , nextListenerId: nextListenerIdRef
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // store operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Dispatch an action to update state
dispatch :: forall state action. Store state action -> action -> Effect Unit
dispatch store@(Store { state, reducer, listeners, middleware }) action = do
  -- Build middleware chain
  let 
    baseDispatch :: action -> Effect Unit
    baseDispatch act = do
      currentReducer <- Ref.read reducer
      currentState <- Ref.read state
      let newState = currentReducer currentState act
      Ref.write newState state
      -- Notify listeners
      subs <- Ref.read listeners
      for_ subs \listener -> listener.callback newState
    
    storeApi = 
      { getState: Ref.read state
      , dispatch: dispatch store
      }
    
    chain = Array.foldr (\mw next -> mw storeApi next) baseDispatch middleware
  
  chain action
  where
  for_ arr f = void $ Array.foldM (\_ x -> f x) unit arr

-- | Get current state
getState :: forall state action. Store state action -> Effect state
getState (Store { state }) = Ref.read state

-- | Subscribe to state changes, returns unsubscribe function
subscribe :: forall state action. Store state action -> Listener state -> Effect (Effect Unit)
subscribe (Store { listeners, nextListenerId }) listener = do
  id <- Ref.read nextListenerId
  Ref.write (id + 1) nextListenerId
  let sub = { id, callback: listener }
  Ref.modify_ (Array.cons sub) listeners
  pure $ Ref.modify_ (Array.filter (\s -> s.id /= id)) listeners

-- | Replace the reducer (useful for hot reloading)
replaceReducer :: forall state action. Store state action -> Reducer state action -> Effect Unit
replaceReducer (Store { reducer }) newReducer = Ref.write newReducer reducer

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // middleware
-- ═════════════════════════════════════════════════════════════════════════════

-- | Logger middleware - logs all actions and state changes
loggerMiddleware :: forall state action. Show action => Show state => Middleware state action
loggerMiddleware store next action = do
  prevState <- store.getState
  Console.log $ "Action: " <> show action
  Console.log $ "Prev State: " <> show prevState
  next action
  newState <- store.getState
  Console.log $ "Next State: " <> show newState

-- | Thunk middleware - allows dispatching functions
-- | Note: In PureScript, we handle this differently via Aff
thunkMiddleware :: forall state action. Middleware state action
thunkMiddleware _store next action = next action

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // selectors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Select a slice of state
select :: forall state action a. Store state action -> (state -> a) -> Effect a
select store selector = do
  state <- getState store
  pure $ selector state

-- | Subscribe to a selected slice of state (only fires when slice changes)
selectWith 
  :: forall state action a
   . Eq a 
  => Store state action 
  -> (state -> a) 
  -> (a -> Effect Unit) 
  -> Effect (Effect Unit)
selectWith store selector callback = do
  initialValue <- select store selector
  lastValueRef <- Ref.new initialValue
  subscribe store \newState -> do
    let newValue = selector newState
    lastValue <- Ref.read lastValueRef
    when (newValue /= lastValue) do
      Ref.write newValue lastValueRef
      callback newValue

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Combine multiple reducers into one
-- | Each reducer handles a slice of state
combineReducers 
  :: forall state action
   . Array (state -> action -> state) 
  -> Reducer state action
combineReducers reducers state action = 
  Array.foldl (\s r -> r s action) state reducers
