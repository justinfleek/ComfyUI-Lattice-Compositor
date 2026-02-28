-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                           // hydrogen // analytics // tracker
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Analytics and performance tracking
-- |
-- | Provides a unified interface for tracking page views, custom events,
-- | and Core Web Vitals. Supports multiple analytics backends and
-- | respects user privacy preferences.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Analytics.Tracker as Analytics
-- |
-- | -- Initialize tracker
-- | tracker <- Analytics.create
-- |   { providers: [ Analytics.console, Analytics.googleAnalytics "GA-123" ]
-- |   , respectDoNotTrack: true
-- |   }
-- |
-- | -- Track page views
-- | Analytics.trackPageView tracker { path: "/home", title: "Home" }
-- |
-- | -- Track custom events
-- | Analytics.trackEvent tracker "button_click"
-- |   { button: "signup", location: "header" }
-- |
-- | -- Track Core Web Vitals
-- | Analytics.trackWebVitals tracker
-- | ```
module Hydrogen.Analytics.Tracker
  ( -- * Tracker
    Tracker
  , QueuedEvent
  , TrackerConfig
  , create
  , createWithConfig
    -- * Page Views
  , PageViewData
  , trackPageView
  , trackPageViewWithData
    -- * Events
  , EventData
  , trackEvent
  , trackEventWithValue
  , trackTiming
    -- * User Identity
  , identify
  , setUserProperties
  , reset
    -- * E-commerce
  , trackPurchase
  , trackAddToCart
  , trackRemoveFromCart
  , trackCheckout
    -- * Core Web Vitals
  , WebVitals
  , WebVitalMetric(LCP, FID, CLS, FCP, TTFB, INP)
  , trackWebVitals
  , trackVital
  , onVital
    -- * Providers
  , Provider
  , ProviderConfig
  , console
  , googleAnalytics
  , plausible
  , mixpanel
  , customProvider
    -- * Privacy
  , PrivacyMode(FullTracking, AnonymousOnly, NoTracking)
  , setPrivacyMode
  , optOut
  , optIn
  , isTracking
    -- * Batching
  , flush
  , setBufferSize
    -- * Debug
  , enableDebug
  , getQueue
  ) where

import Prelude hiding (when)

import Control.Monad (when)
import Data.Array as Array
import Data.Foldable (for_)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(Nothing, Just), fromMaybe)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(Tuple))
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Foreign.Object (Object)
import Foreign.Object as Object

-- ═════════════════════════════════════════════════════════════════════════════
-- Core Types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Analytics tracker instance
type Tracker =
  { providers :: Array Provider
  , queue :: Ref (Array QueuedEvent)
  , config :: TrackerConfig
  , isEnabled :: Ref Boolean
  , userId :: Ref (Maybe String)
  , userProperties :: Ref (Map String String)
  , sessionId :: String
  , debug :: Ref Boolean
  }

-- | Tracker configuration
type TrackerConfig =
  { providers :: Array ProviderConfig
  , respectDoNotTrack :: Boolean
  , bufferSize :: Int
  , flushInterval :: Maybe Int
  , sessionTimeout :: Int
  , anonymizeIp :: Boolean
  , cookieDomain :: Maybe String
  }

-- | Default configuration
defaultConfig :: TrackerConfig
defaultConfig =
  { providers: []
  , respectDoNotTrack: true
  , bufferSize: 10
  , flushInterval: Just 5000
  , sessionTimeout: 1800000  -- 30 minutes
  , anonymizeIp: true
  , cookieDomain: Nothing
  }

-- | A queued analytics event
type QueuedEvent =
  { eventType :: String
  , data :: Object String
  , timestamp :: Number
  }

-- ═════════════════════════════════════════════════════════════════════════════
-- Tracker Creation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a tracker with default config
create :: Array ProviderConfig -> Effect Tracker
create providerConfigs = createWithConfig defaultConfig { providers = providerConfigs }

-- | Create a tracker with custom config
createWithConfig :: TrackerConfig -> Effect Tracker
createWithConfig config = do
  -- Check Do Not Track
  shouldTrack <- if config.respectDoNotTrack
    then not <$> getDoNotTrack
    else pure true
  
  providers <- traverse initProvider config.providers
  queue <- Ref.new []
  isEnabled <- Ref.new shouldTrack
  userId <- Ref.new Nothing
  userProperties <- Ref.new Map.empty
  sessionId <- generateSessionId
  debug <- Ref.new false
  
  let tracker = { providers, queue, config, isEnabled, userId, userProperties, sessionId, debug }
  
  -- Set up flush interval if configured
  case config.flushInterval of
    Just interval -> setupFlushInterval tracker interval
    Nothing -> pure unit
  
  pure tracker

foreign import getDoNotTrack :: Effect Boolean
foreign import generateSessionId :: Effect String
foreign import setupFlushInterval :: Tracker -> Int -> Effect Unit

-- ═════════════════════════════════════════════════════════════════════════════
-- Page Views
-- ═════════════════════════════════════════════════════════════════════════════

-- | Page view data
type PageViewData =
  { path :: String
  , title :: Maybe String
  , referrer :: Maybe String
  , customData :: Object String
  }

-- | Track a simple page view
trackPageView :: Tracker -> { path :: String, title :: String } -> Effect Unit
trackPageView tracker { path, title } =
  trackPageViewWithData tracker
    { path
    , title: Just title
    , referrer: Nothing
    , customData: Object.empty
    }

-- | Track a page view with full data
trackPageViewWithData :: Tracker -> PageViewData -> Effect Unit
trackPageViewWithData tracker pageData = do
  enabled <- Ref.read tracker.isEnabled
  when enabled do
    let eventData = Object.fromFoldable
          [ "path" /\ pageData.path
          , "title" /\ fromMaybe "" pageData.title
          , "referrer" /\ fromMaybe "" pageData.referrer
          ]
    queueEvent tracker "pageview" (Object.union eventData pageData.customData)

-- ═════════════════════════════════════════════════════════════════════════════
-- Custom Events
-- ═════════════════════════════════════════════════════════════════════════════

-- | Event data type
type EventData = Object String

-- | Track a custom event
trackEvent :: Tracker -> String -> EventData -> Effect Unit
trackEvent tracker eventName eventData = do
  enabled <- Ref.read tracker.isEnabled
  when enabled do
    let data' = Object.insert "event_name" eventName eventData
    queueEvent tracker "event" data'

-- | Track an event with a numeric value
trackEventWithValue :: Tracker -> String -> Number -> EventData -> Effect Unit
trackEventWithValue tracker eventName value eventData = do
  let data' = Object.insert "value" (show value) eventData
  trackEvent tracker eventName data'

-- | Track a timing event
trackTiming :: Tracker -> String -> Int -> EventData -> Effect Unit
trackTiming tracker category duration eventData = do
  enabled <- Ref.read tracker.isEnabled
  when enabled do
    let data' = Object.fromFoldable
          [ "category" /\ category
          , "duration" /\ show duration
          ]
    queueEvent tracker "timing" (Object.union data' eventData)

-- ═════════════════════════════════════════════════════════════════════════════
-- User Identity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Identify a user
identify :: Tracker -> String -> Effect Unit
identify tracker uid = do
  Ref.write (Just uid) tracker.userId
  for_ tracker.providers \provider ->
    provider.identify uid

-- | Set user properties
setUserProperties :: Tracker -> Map String String -> Effect Unit
setUserProperties tracker props = do
  Ref.modify_ (Map.union props) tracker.userProperties
  let propsArray :: Array (Tuple String String)
      propsArray = Map.toUnfoldable props
      propsObj = Object.fromFoldable propsArray
  for_ tracker.providers \provider ->
    provider.setUserProperties propsObj

-- | Reset user identity (e.g., on logout)
reset :: Tracker -> Effect Unit
reset tracker = do
  Ref.write Nothing tracker.userId
  Ref.write Map.empty tracker.userProperties
  for_ tracker.providers \provider ->
    provider.reset

-- ═════════════════════════════════════════════════════════════════════════════
-- E-commerce Tracking
-- ═════════════════════════════════════════════════════════════════════════════

-- | Track a purchase
trackPurchase
  :: Tracker
  -> { transactionId :: String, total :: Number, currency :: String, items :: Array ProductData }
  -> Effect Unit
trackPurchase tracker purchase = do
  let data' = Object.fromFoldable
        [ "transaction_id" /\ purchase.transactionId
        , "total" /\ show purchase.total
        , "currency" /\ purchase.currency
        , "item_count" /\ show (Array.length purchase.items)
        ]
  trackEvent tracker "purchase" data'

-- | Product data for e-commerce
type ProductData =
  { id :: String
  , name :: String
  , price :: Number
  , quantity :: Int
  , category :: Maybe String
  }

-- | Track adding item to cart
trackAddToCart :: Tracker -> ProductData -> Effect Unit
trackAddToCart tracker product = do
  let data' = Object.fromFoldable
        [ "product_id" /\ product.id
        , "product_name" /\ product.name
        , "price" /\ show product.price
        , "quantity" /\ show product.quantity
        ]
  trackEvent tracker "add_to_cart" data'

-- | Track removing item from cart
trackRemoveFromCart :: Tracker -> ProductData -> Effect Unit
trackRemoveFromCart tracker product = do
  let data' = Object.fromFoldable
        [ "product_id" /\ product.id
        , "product_name" /\ product.name
        ]
  trackEvent tracker "remove_from_cart" data'

-- | Track checkout step
trackCheckout :: Tracker -> Int -> Maybe String -> Effect Unit
trackCheckout tracker step paymentMethod = do
  let data' = Object.fromFoldable
        [ "step" /\ show step
        , "payment_method" /\ fromMaybe "" paymentMethod
        ]
  trackEvent tracker "checkout" data'

-- ═════════════════════════════════════════════════════════════════════════════
-- Core Web Vitals
-- ═════════════════════════════════════════════════════════════════════════════

-- | Web Vitals metrics
type WebVitals =
  { lcp :: Maybe Number    -- Largest Contentful Paint
  , fid :: Maybe Number    -- First Input Delay
  , cls :: Maybe Number    -- Cumulative Layout Shift
  , fcp :: Maybe Number    -- First Contentful Paint
  , ttfb :: Maybe Number   -- Time to First Byte
  , inp :: Maybe Number    -- Interaction to Next Paint
  }

-- | Individual web vital metric
data WebVitalMetric
  = LCP Number
  | FID Number
  | CLS Number
  | FCP Number
  | TTFB Number
  | INP Number

derive instance eqWebVitalMetric :: Eq WebVitalMetric

instance showWebVitalMetric :: Show WebVitalMetric where
  show = case _ of
    LCP n -> "LCP(" <> show n <> "ms)"
    FID n -> "FID(" <> show n <> "ms)"
    CLS n -> "CLS(" <> show n <> ")"
    FCP n -> "FCP(" <> show n <> "ms)"
    TTFB n -> "TTFB(" <> show n <> "ms)"
    INP n -> "INP(" <> show n <> "ms)"

-- | Track all Core Web Vitals automatically
trackWebVitals :: Tracker -> Effect (Effect Unit)
trackWebVitals tracker = do
  observeWebVitals \metric -> do
    enabled <- Ref.read tracker.isEnabled
    when enabled do
      trackVital tracker metric

foreign import observeWebVitals :: (WebVitalMetric -> Effect Unit) -> Effect (Effect Unit)

-- | Track a single vital metric
trackVital :: Tracker -> WebVitalMetric -> Effect Unit
trackVital tracker metric = do
  let (name /\ value) = case metric of
        LCP n -> "lcp" /\ n
        FID n -> "fid" /\ n
        CLS n -> "cls" /\ n
        FCP n -> "fcp" /\ n
        TTFB n -> "ttfb" /\ n
        INP n -> "inp" /\ n
  let data' = Object.fromFoldable
        [ "metric" /\ name
        , "value" /\ show value
        ]
  queueEvent tracker "web_vital" data'

-- | Subscribe to vital metrics
onVital :: Tracker -> (WebVitalMetric -> Effect Unit) -> Effect (Effect Unit)
onVital _tracker handler = observeWebVitals handler

-- ═════════════════════════════════════════════════════════════════════════════
-- Providers
-- ═════════════════════════════════════════════════════════════════════════════

-- | An analytics provider
type Provider =
  { name :: String
  , track :: String -> Object String -> Effect Unit
  , identify :: String -> Effect Unit
  , setUserProperties :: Object String -> Effect Unit
  , reset :: Effect Unit
  , flush :: Effect Unit
  }

-- | Provider configuration
type ProviderConfig =
  { name :: String
  , init :: Effect Provider
  }

-- | Console provider (for development)
console :: ProviderConfig
console =
  { name: "console"
  , init: pure
      { name: "console"
      , track: \eventType eventData -> logAnalytics eventType eventData
      , identify: \uid -> logIdentify uid
      , setUserProperties: \props -> logUserProps props
      , reset: logReset
      , flush: pure unit
      }
  }

foreign import logAnalytics :: String -> Object String -> Effect Unit
foreign import logIdentify :: String -> Effect Unit
foreign import logUserProps :: Object String -> Effect Unit
foreign import logReset :: Effect Unit

-- | Google Analytics 4 provider
googleAnalytics :: String -> ProviderConfig
googleAnalytics measurementId =
  { name: "google-analytics"
  , init: initGoogleAnalytics measurementId
  }

foreign import initGoogleAnalytics :: String -> Effect Provider

-- | Plausible Analytics provider
plausible :: String -> ProviderConfig
plausible domain =
  { name: "plausible"
  , init: initPlausible domain
  }

foreign import initPlausible :: String -> Effect Provider

-- | Mixpanel provider
mixpanel :: String -> ProviderConfig
mixpanel token =
  { name: "mixpanel"
  , init: initMixpanel token
  }

foreign import initMixpanel :: String -> Effect Provider

-- | Create a custom provider
customProvider
  :: String
  -> (String -> Object String -> Effect Unit)
  -> ProviderConfig
customProvider name trackFn =
  { name
  , init: pure
      { name
      , track: trackFn
      , identify: \_ -> pure unit
      , setUserProperties: \_ -> pure unit
      , reset: pure unit
      , flush: pure unit
      }
  }

-- | Initialize a provider from config
initProvider :: ProviderConfig -> Effect Provider
initProvider config = config.init

-- ═════════════════════════════════════════════════════════════════════════════
-- Privacy
-- ═════════════════════════════════════════════════════════════════════════════

-- | Privacy mode settings
data PrivacyMode
  = FullTracking
  | AnonymousOnly
  | NoTracking

derive instance eqPrivacyMode :: Eq PrivacyMode

-- | Set privacy mode
setPrivacyMode :: Tracker -> PrivacyMode -> Effect Unit
setPrivacyMode tracker mode = case mode of
  FullTracking -> Ref.write true tracker.isEnabled
  AnonymousOnly -> do
    Ref.write true tracker.isEnabled
    reset tracker
  NoTracking -> Ref.write false tracker.isEnabled

-- | Opt out of tracking
optOut :: Tracker -> Effect Unit
optOut tracker = do
  Ref.write false tracker.isEnabled
  persistOptOut true

-- | Opt back in to tracking
optIn :: Tracker -> Effect Unit
optIn tracker = do
  Ref.write true tracker.isEnabled
  persistOptOut false

foreign import persistOptOut :: Boolean -> Effect Unit

-- | Check if tracking is enabled
isTracking :: Tracker -> Effect Boolean
isTracking tracker = Ref.read tracker.isEnabled

-- ═════════════════════════════════════════════════════════════════════════════
-- Event Queue & Batching
-- ═════════════════════════════════════════════════════════════════════════════

-- | Queue an event for sending
queueEvent :: Tracker -> String -> Object String -> Effect Unit
queueEvent tracker eventType eventData = do
  timestamp <- now
  userId <- Ref.read tracker.userId
  userProps <- Ref.read tracker.userProperties
  
  let enrichedData = eventData
        # Object.insert "session_id" tracker.sessionId
        # Object.insert "timestamp" (show timestamp)
        # maybeInsert "user_id" userId
  
  -- Debug logging
  isDebug <- Ref.read tracker.debug
  when isDebug do
    logAnalytics eventType enrichedData
  
  Ref.modify_ (flip Array.snoc { eventType, data: enrichedData, timestamp }) tracker.queue
  
  -- Check if we should flush
  queue <- Ref.read tracker.queue
  when (Array.length queue >= tracker.config.bufferSize) do
    flush tracker

-- | Flush queued events to providers
flush :: Tracker -> Effect Unit
flush tracker = do
  queue <- Ref.read tracker.queue
  Ref.write [] tracker.queue
  
  for_ queue \event ->
    for_ tracker.providers \provider ->
      provider.track event.eventType event.data
  
  for_ tracker.providers \provider ->
    provider.flush

-- | Set the buffer size
setBufferSize :: Tracker -> Int -> Effect Unit
setBufferSize tracker size = pure unit -- Would update config

-- ═════════════════════════════════════════════════════════════════════════════
-- Debug
-- ═════════════════════════════════════════════════════════════════════════════

-- | Enable debug mode
enableDebug :: Tracker -> Boolean -> Effect Unit
enableDebug tracker enabled = Ref.write enabled tracker.debug

-- | Get the current event queue (for debugging)
getQueue :: Tracker -> Effect (Array QueuedEvent)
getQueue tracker = Ref.read tracker.queue

-- ═════════════════════════════════════════════════════════════════════════════
-- Utilities
-- ═════════════════════════════════════════════════════════════════════════════

foreign import now :: Effect Number

-- | Insert a value into an Object only if the Maybe contains a value
maybeInsert :: String -> Maybe String -> Object String -> Object String
maybeInsert key = case _ of
  Just val -> Object.insert key val
  Nothing -> identity

infixr 0 Tuple as /\
