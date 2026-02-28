-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                   // hydrogen // event // bus
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Type-safe event bus for pub/sub communication
-- |
-- | The event bus provides a decoupled communication mechanism between
-- | components. Events are typed and can carry arbitrary payloads.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Event.Bus as Bus
-- |
-- | -- Define your events
-- | data AppEvent
-- |   = UserLoggedIn User
-- |   | CartUpdated Cart
-- |   | ThemeChanged Theme
-- |
-- | -- Create an event bus
-- | bus <- Bus.create
-- |
-- | -- Subscribe to events
-- | unsubscribe <- Bus.subscribe bus \event -> case event of
-- |   UserLoggedIn user -> Console.log $ "Welcome " <> user.name
-- |   CartUpdated cart -> updateCartUI cart
-- |   ThemeChanged theme -> applyTheme theme
-- |
-- | -- Emit events
-- | Bus.emit bus (UserLoggedIn { name: "Alice" })
-- |
-- | -- Clean up
-- | unsubscribe
-- | ```
module Hydrogen.Event.Bus
  ( -- * Event Bus
    EventBus
  , Subscriber
  , create
  , createNamed
    -- * Subscriptions
  , subscribe
  , subscribeOnce
  , subscribeWithFilter
  , unsubscribeAll
    -- * Emitting
  , emit
  , emitAsync
  , emitDelayed
    -- * Channels
  , Channel
  , channel
  , channelNamed
  , onChannel
  , emitToChannel
    -- * History
  , History
  , withHistory
  , getHistory
  , clearHistory
  , replay
    -- * Debugging
  , debugBus
  , getSubscriberCount
    -- * Typed Channels
  , TypedChannel
  , AnyEvent
  , typedChannel
  , subscribeTyped
  , emitTyped
  ) where

import Prelude hiding (map, when)

import Control.Monad (unless, when)
import Data.Array as Array
import Data.DateTime.Instant (unInstant) as Instant
import Data.Functor (map) as Functor
import Data.Maybe (Maybe(Just, Nothing))
import Data.Time.Duration (Milliseconds(Milliseconds)) as Duration
import Data.Traversable (traverse) as Traversable
import Effect (Effect)
import Effect.Aff (Aff, Milliseconds(Milliseconds), delay)
import Effect.Class (liftEffect)
import Effect.Now (now) as Now
import Effect.Ref (Ref)
import Effect.Ref as Ref

-- ═════════════════════════════════════════════════════════════════════════════
-- Event Bus Core
-- ═════════════════════════════════════════════════════════════════════════════

-- | An event bus for type-safe pub/sub
type EventBus a =
  { name :: Maybe String
  , subscribers :: Ref (Array (Subscriber a))
  , nextId :: Ref Int
  , history :: Maybe (History a)
  , debugMode :: Ref Boolean
  }

-- | A subscriber with metadata
type Subscriber a =
  { id :: Int
  , handler :: a -> Effect Unit
  , once :: Boolean
  , filter :: Maybe (a -> Boolean)
  }

-- | Create a new event bus
create :: forall a. Effect (EventBus a)
create = do
  subscribers <- Ref.new []
  nextId <- Ref.new 0
  debugMode <- Ref.new false
  pure
    { name: Nothing
    , subscribers
    , nextId
    , history: Nothing
    , debugMode
    }

-- | Create a named event bus (useful for debugging)
createNamed :: forall a. String -> Effect (EventBus a)
createNamed name = do
  bus <- create
  pure bus { name = Just name }

-- ═════════════════════════════════════════════════════════════════════════════
-- Subscriptions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Subscribe to events on the bus
-- | Returns an unsubscribe function
subscribe :: forall a. EventBus a -> (a -> Effect Unit) -> Effect (Effect Unit)
subscribe bus handler = do
  id <- Ref.read bus.nextId
  Ref.write (id + 1) bus.nextId
  
  let subscriber = { id, handler, once: false, filter: Nothing }
  Ref.modify_ (flip Array.snoc subscriber) bus.subscribers
  
  -- Return unsubscribe function
  pure $ unsubscribe bus id

-- | Subscribe to a single event, then automatically unsubscribe
subscribeOnce :: forall a. EventBus a -> (a -> Effect Unit) -> Effect (Effect Unit)
subscribeOnce bus handler = do
  id <- Ref.read bus.nextId
  Ref.write (id + 1) bus.nextId
  
  let subscriber = { id, handler, once: true, filter: Nothing }
  Ref.modify_ (flip Array.snoc subscriber) bus.subscribers
  
  pure $ unsubscribe bus id

-- | Subscribe with a filter predicate
-- | Handler only called when filter returns true
subscribeWithFilter
  :: forall a
   . EventBus a
  -> (a -> Boolean)
  -> (a -> Effect Unit)
  -> Effect (Effect Unit)
subscribeWithFilter bus predicate handler = do
  id <- Ref.read bus.nextId
  Ref.write (id + 1) bus.nextId
  
  let subscriber = { id, handler, once: false, filter: Just predicate }
  Ref.modify_ (flip Array.snoc subscriber) bus.subscribers
  
  pure $ unsubscribe bus id

-- | Internal unsubscribe by ID
unsubscribe :: forall a. EventBus a -> Int -> Effect Unit
unsubscribe bus id = do
  Ref.modify_ (Array.filter (\s -> s.id /= id)) bus.subscribers

-- | Remove all subscribers
unsubscribeAll :: forall a. EventBus a -> Effect Unit
unsubscribeAll bus = Ref.write [] bus.subscribers

-- ═════════════════════════════════════════════════════════════════════════════
-- Emitting Events
-- ═════════════════════════════════════════════════════════════════════════════

-- | Emit an event to all subscribers
emit :: forall a. EventBus a -> a -> Effect Unit
emit bus event = do
  -- Record in history if enabled
  case bus.history of
    Just h -> recordEvent h event
    Nothing -> pure unit
  
  -- Debug logging
  isDebug <- Ref.read bus.debugMode
  when isDebug $ logEvent bus.name event
  
  -- Get current subscribers
  subs <- Ref.read bus.subscribers
  
  -- Call matching handlers
  let 
    matchingSubs = Array.filter (shouldHandle event) subs
    onceSubs = Array.filter _.once matchingSubs
  
  -- Remove one-time subscribers
  unless (Array.null onceSubs) do
    let onceIds = map _.id onceSubs
    Ref.modify_ (Array.filter (\s -> not (Array.elem s.id onceIds))) bus.subscribers
  
  -- Invoke handlers
  for_ matchingSubs \sub -> sub.handler event
  where
  shouldHandle :: a -> Subscriber a -> Boolean
  shouldHandle e sub = case sub.filter of
    Nothing -> true
    Just f -> f e
  
  for_ :: forall b. Array b -> (b -> Effect Unit) -> Effect Unit
  for_ arr f = void $ traverse f arr
  
  traverse :: forall b c. (b -> Effect c) -> Array b -> Effect (Array c)
  traverse = Traversable.traverse

-- | Log an event to the console (for debugging)
-- | Uses FFI because event type may not have Show instance
-- | JavaScript console.log can display any value
foreign import logEvent :: forall a. Maybe String -> a -> Effect Unit

-- | Emit an event asynchronously (non-blocking)
emitAsync :: forall a. EventBus a -> a -> Aff Unit
emitAsync bus event = liftEffect $ emit bus event

-- | Emit an event after a delay
emitDelayed :: forall a. EventBus a -> Milliseconds -> a -> Aff Unit
emitDelayed bus (Milliseconds ms) event = do
  delay (Milliseconds ms)
  liftEffect $ emit bus event

-- ═════════════════════════════════════════════════════════════════════════════
-- Channels (Namespaced Events)
-- ═════════════════════════════════════════════════════════════════════════════

-- | A named channel for organizing events
newtype Channel = Channel String

derive instance eqChannel :: Eq Channel
derive instance ordChannel :: Ord Channel

instance showChannel :: Show Channel where
  show (Channel name) = "Channel(" <> name <> ")"

-- | Create a channel
channel :: String -> Channel
channel = Channel

-- | Create a named channel (alias)
channelNamed :: String -> Channel
channelNamed = Channel

-- | Channeled event wrapper
type ChanneledEvent a =
  { channel :: Channel
  , payload :: a
  }

-- | Subscribe to a specific channel
onChannel
  :: forall a
   . EventBus (ChanneledEvent a)
  -> Channel
  -> (a -> Effect Unit)
  -> Effect (Effect Unit)
onChannel bus ch handler =
  subscribeWithFilter bus
    (\e -> e.channel == ch)
    (\e -> handler e.payload)

-- | Emit to a specific channel
emitToChannel :: forall a. EventBus (ChanneledEvent a) -> Channel -> a -> Effect Unit
emitToChannel bus ch payload =
  emit bus { channel: ch, payload }

-- ═════════════════════════════════════════════════════════════════════════════
-- History
-- ═════════════════════════════════════════════════════════════════════════════

-- | Event history for replay/debugging
type History a =
  { events :: Ref (Array { event :: a, timestamp :: Number })
  , maxSize :: Int
  }

-- | Create a bus with history tracking
withHistory :: forall a. Int -> Effect (EventBus a)
withHistory maxSize = do
  bus <- create
  events <- Ref.new []
  pure bus { history = Just { events, maxSize } }

-- | Record an event in history
recordEvent :: forall a. History a -> a -> Effect Unit
recordEvent history event = do
  timestamp <- nowImpl
  Ref.modify_ (\arr ->
    let newArr = Array.snoc arr { event, timestamp }
    in if Array.length newArr > history.maxSize
       then Array.drop 1 newArr
       else newArr
  ) history.events

-- | Get current timestamp in milliseconds (pure implementation)
nowImpl :: Effect Number
nowImpl = do
  instant <- Now.now
  let Duration.Milliseconds ms = Instant.unInstant instant
  pure ms

-- | Get the event history
getHistory :: forall a. EventBus a -> Effect (Array { event :: a, timestamp :: Number })
getHistory bus = case bus.history of
  Just h -> Ref.read h.events
  Nothing -> pure []

-- | Clear the event history
clearHistory :: forall a. EventBus a -> Effect Unit
clearHistory bus = case bus.history of
  Just h -> Ref.write [] h.events
  Nothing -> pure unit

-- | Replay all events in history to a handler
replay :: forall a. EventBus a -> (a -> Effect Unit) -> Effect Unit
replay bus handler = do
  events <- getHistory bus
  for_ events \{ event } -> handler event
  where
  for_ :: forall b. Array b -> (b -> Effect Unit) -> Effect Unit
  for_ arr f = void $ Traversable.traverse f arr

-- ═════════════════════════════════════════════════════════════════════════════
-- Debugging
-- ═════════════════════════════════════════════════════════════════════════════

-- | Enable debug mode for a bus
debugBus :: forall a. EventBus a -> Boolean -> Effect Unit
debugBus bus enabled = Ref.write enabled bus.debugMode

-- | Get the number of active subscribers
getSubscriberCount :: forall a. EventBus a -> Effect Int
getSubscriberCount bus = Array.length <$> Ref.read bus.subscribers

-- ═════════════════════════════════════════════════════════════════════════════
-- Typed Channels (Heterogeneous Events)
-- ═════════════════════════════════════════════════════════════════════════════

-- | A typed channel that carries a specific event type
-- | Used for heterogeneous event buses
newtype TypedChannel :: Type -> Type
newtype TypedChannel a = TypedChannel String

derive instance eqTypedChannel :: Eq (TypedChannel a)
derive instance ordTypedChannel :: Ord (TypedChannel a)

-- | Create a typed channel
typedChannel :: forall a. String -> TypedChannel a
typedChannel = TypedChannel

-- | Wrapper for heterogeneous events
foreign import data AnyEvent :: Type

foreign import wrapEvent :: forall a. String -> a -> AnyEvent
foreign import unwrapEventImpl :: forall a. (a -> Maybe a) -> Maybe a -> String -> AnyEvent -> Maybe a

-- | Unwrap an event if it matches the expected type
unwrapEvent :: forall a. String -> AnyEvent -> Maybe a
unwrapEvent = unwrapEventImpl Just Nothing

-- | Subscribe to a typed channel on a heterogeneous bus
subscribeTyped
  :: forall a
   . EventBus AnyEvent
  -> TypedChannel a
  -> (a -> Effect Unit)
  -> Effect (Effect Unit)
subscribeTyped bus (TypedChannel name) handler =
  subscribeWithFilter bus
    (\_ -> true) -- Let the handler filter
    (\anyEvent -> case unwrapEvent name anyEvent of
      Just event -> handler event
      Nothing -> pure unit)

-- | Emit to a typed channel
emitTyped :: forall a. EventBus AnyEvent -> TypedChannel a -> a -> Effect Unit
emitTyped bus (TypedChannel name) event =
  emit bus (wrapEvent name event)

-- ═════════════════════════════════════════════════════════════════════════════
-- Utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- Note: Using Control.Monad.when and Control.Monad.unless from standard library

-- | Map function for arrays (pure implementation)
map :: forall a b. (a -> b) -> Array a -> Array b
map = Functor.map
