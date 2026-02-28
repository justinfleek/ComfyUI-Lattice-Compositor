-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                               // hydrogen // feature // flags
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Feature flags and A/B testing system
-- |
-- | Enables gradual rollouts, experimentation, and runtime configuration
-- | without code changes. Supports percentage-based rollouts, user targeting,
-- | and variant assignment.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Feature.Flags as Flags
-- |
-- | -- Define flags
-- | newFeature = Flags.flag "new-checkout-flow"
-- | darkMode = Flags.flag "dark-mode"
-- |
-- | -- Create a flag provider
-- | provider <- Flags.createProvider defaultFlags
-- |
-- | -- Check if enabled
-- | isEnabled <- Flags.isEnabled provider newFeature
-- | when isEnabled do
-- |   renderNewCheckout
-- |
-- | -- A/B testing with variants
-- | buttonColorTest = Flags.experiment "button-color" ["red", "blue", "green"]
-- | variant <- Flags.getVariant provider buttonColorTest
-- | ```
module Hydrogen.Feature.Flags
  ( -- * Feature Flags
    Flag
  , flag
  , flagWithDefault
    -- * Provider
  , FlagProvider
  , ProviderConfig
  , createProvider
  , createProviderWithConfig
    -- * Flag Operations
  , isEnabled
  , isDisabled
  , getValue
  , getValueOr
    -- * Experiments / A/B Tests
  , Experiment
  , Variant
  , experiment
  , getVariant
  , getVariantIndex
  , trackExposure
    -- * Targeting
  , TargetingRule
  , TargetingCondition(Percentage, UserIds, UserAttribute, Environment, Always, Never, AllOf, AnyOf)
  , TargetingContext
  , percentage
  , userIds
  , userAttribute
  , environment
  , always
  , never
  , allOf
  , anyOf
    -- * Flag Definitions
  , FlagDefinition
  , FlagValue(BoolValue, StringValue, NumberValue, JsonValue)
  , defineBoolFlag
  , defineStringFlag
  , defineNumberFlag
  , defineJsonFlag
    -- * Dynamic Updates
  , subscribe
  , refresh
  , setOverride
  , clearOverride
  , clearAllOverrides
    -- * Persistence
  , loadFromJson
  , loadFromUrl
    -- * DevTools
  , getAllFlags
  , getFlagState
  , FlagState
  ) where

import Prelude hiding (when)

import Control.Monad (when)
import Data.Array as Array
import Data.Int (toNumber) as Int
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(Nothing, Just), fromMaybe)
import Data.Tuple (Tuple(Tuple))
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Aff as Aff
import Effect.Class (liftEffect)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Foreign.Object (Object)

-- ═════════════════════════════════════════════════════════════════════════════
-- Core Types
-- ═════════════════════════════════════════════════════════════════════════════

-- | A feature flag identifier
newtype Flag = Flag String

derive instance eqFlag :: Eq Flag
derive instance ordFlag :: Ord Flag

instance showFlag :: Show Flag where
  show (Flag name) = "Flag(" <> name <> ")"

-- | Create a flag reference
flag :: String -> Flag
flag = Flag

-- | Create a flag with a default value
flagWithDefault :: String -> Boolean -> FlagDefinition
flagWithDefault name defaultVal =
  { flag: Flag name
  , defaultValue: BoolValue defaultVal
  , rules: []
  , metadata: { description: Nothing, tags: [] }
  }

-- | A flag value can be boolean, string, number, or JSON
data FlagValue
  = BoolValue Boolean
  | StringValue String
  | NumberValue Number
  | JsonValue (Object FlagValue)

derive instance eqFlagValue :: Eq FlagValue

instance showFlagValue :: Show FlagValue where
  show = case _ of
    BoolValue b -> "BoolValue(" <> show b <> ")"
    StringValue s -> "StringValue(" <> s <> ")"
    NumberValue n -> "NumberValue(" <> show n <> ")"
    JsonValue _ -> "JsonValue(...)"

-- | Complete flag definition with targeting rules
type FlagDefinition =
  { flag :: Flag
  , defaultValue :: FlagValue
  , rules :: Array TargetingRule
  , metadata :: { description :: Maybe String, tags :: Array String }
  }

-- ═════════════════════════════════════════════════════════════════════════════
-- Provider
-- ═════════════════════════════════════════════════════════════════════════════

-- | Feature flag provider that manages flag state
type FlagProvider =
  { definitions :: Ref (Map Flag FlagDefinition)
  , overrides :: Ref (Map Flag FlagValue)
  , context :: Ref TargetingContext
  , subscribers :: Ref (Array (Flag -> FlagValue -> Effect Unit))
  , config :: ProviderConfig
  }

-- | Provider configuration
type ProviderConfig =
  { persistOverrides :: Boolean     -- ^ Save overrides to localStorage
  , refreshInterval :: Maybe Int    -- ^ Auto-refresh interval in ms
  , trackExposures :: Boolean       -- ^ Track when flags are evaluated
  , onExposure :: Maybe (Flag -> FlagValue -> Effect Unit)
  }

-- | Default provider configuration
defaultConfig :: ProviderConfig
defaultConfig =
  { persistOverrides: true
  , refreshInterval: Nothing
  , trackExposures: false
  , onExposure: Nothing
  }

-- | Create a flag provider with default config
createProvider :: Array FlagDefinition -> Effect FlagProvider
createProvider defs = createProviderWithConfig defs defaultConfig

-- | Create a flag provider with custom config
createProviderWithConfig :: Array FlagDefinition -> ProviderConfig -> Effect FlagProvider
createProviderWithConfig defs config = do
  let defMap = Map.fromFoldable $ map (\d -> d.flag /\ d) defs
  definitions <- Ref.new defMap
  overrides <- Ref.new Map.empty
  context <- Ref.new emptyContext
  subscribers <- Ref.new []
  
  -- Load persisted overrides
  when config.persistOverrides do
    loadPersistedOverrides overrides
  
  pure { definitions, overrides, context, subscribers, config }

-- ═════════════════════════════════════════════════════════════════════════════
-- Flag Operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if a flag is enabled (boolean flags)
isEnabled :: FlagProvider -> Flag -> Effect Boolean
isEnabled provider f = do
  value <- getValue provider f
  pure $ case value of
    Just (BoolValue b) -> b
    _ -> false

-- | Check if a flag is disabled
isDisabled :: FlagProvider -> Flag -> Effect Boolean
isDisabled provider f = not <$> isEnabled provider f

-- | Get a flag's value
getValue :: FlagProvider -> Flag -> Effect (Maybe FlagValue)
getValue provider f = do
  -- Check overrides first
  overrides <- Ref.read provider.overrides
  case Map.lookup f overrides of
    Just val -> do
      maybeTrackExposure provider f val
      pure $ Just val
    Nothing -> do
      -- Evaluate against definitions
      definitions <- Ref.read provider.definitions
      ctx <- Ref.read provider.context
      case Map.lookup f definitions of
        Just def -> do
          let val = evaluateFlag def ctx
          maybeTrackExposure provider f val
          pure $ Just val
        Nothing -> pure Nothing

-- | Get a flag's value with a default
getValueOr :: forall a. FlagProvider -> Flag -> a -> (FlagValue -> Maybe a) -> Effect a
getValueOr provider f defaultVal extract = do
  maybeValue <- getValue provider f
  pure $ case maybeValue >>= extract of
    Just val -> val
    Nothing -> defaultVal

-- | Track flag exposure if configured
maybeTrackExposure :: FlagProvider -> Flag -> FlagValue -> Effect Unit
maybeTrackExposure provider f val =
  when provider.config.trackExposures do
    case provider.config.onExposure of
      Just handler -> handler f val
      Nothing -> pure unit

-- | Evaluate a flag against targeting rules
evaluateFlag :: FlagDefinition -> TargetingContext -> FlagValue
evaluateFlag def ctx =
  case findMatchingRule def.rules ctx of
    Just value -> value
    Nothing -> def.defaultValue

-- | Find the first matching targeting rule
findMatchingRule :: Array TargetingRule -> TargetingContext -> Maybe FlagValue
findMatchingRule rules ctx =
  rules
    # Array.filter (\r -> evaluateRule r ctx)
    # Array.head
    # map _.value

-- ═════════════════════════════════════════════════════════════════════════════
-- Experiments / A/B Testing
-- ═════════════════════════════════════════════════════════════════════════════

-- | An A/B experiment with variants
type Experiment =
  { name :: String
  , variants :: Array Variant
  }

-- | A variant in an experiment
type Variant =
  { id :: String
  , weight :: Number  -- Percentage weight (0-100)
  }

-- | Create an experiment with equal-weight variants
experiment :: String -> Array String -> Experiment
experiment name variantIds =
  let 
    weight = 100.0 / toNumber (Array.length variantIds)
    variants = map (\id -> { id, weight }) variantIds
  in
    { name, variants }

-- | Get the assigned variant for an experiment
getVariant :: FlagProvider -> Experiment -> Effect (Maybe String)
getVariant provider exp = do
  ctx <- Ref.read provider.context
  let hash = hashString (exp.name <> fromMaybe "" ctx.userId)
  pure $ assignVariant exp.variants hash

-- | Get the variant index (0-based)
getVariantIndex :: FlagProvider -> Experiment -> Effect (Maybe Int)
getVariantIndex provider exp = do
  variant <- getVariant provider exp
  pure $ variant >>= \v -> Array.findIndex (\var -> var.id == v) exp.variants

-- | Track that a user was exposed to an experiment
trackExposure :: FlagProvider -> Experiment -> String -> Effect Unit
trackExposure provider exp variantId =
  case provider.config.onExposure of
    Just handler -> handler (Flag $ "experiment:" <> exp.name) (StringValue variantId)
    Nothing -> pure unit

-- | Assign a variant based on hash
assignVariant :: Array Variant -> Int -> Maybe String
assignVariant variants hash =
  let
    normalized = toNumber (hash `mod` 100)
    go :: Number -> Array Variant -> Maybe String
    go acc arr = case Array.uncons arr of
      Nothing -> Nothing
      Just { head: v, tail: rest } ->
        if normalized < acc + v.weight
        then Just v.id
        else go (acc + v.weight) rest
  in
    go 0.0 variants

-- ═════════════════════════════════════════════════════════════════════════════
-- Targeting
-- ═════════════════════════════════════════════════════════════════════════════

-- | A targeting rule determines when a flag value applies
type TargetingRule =
  { condition :: TargetingCondition
  , value :: FlagValue
  }

-- | Targeting conditions
data TargetingCondition
  = Percentage Number                           -- ^ Enable for X% of users
  | UserIds (Array String)                      -- ^ Enable for specific users
  | UserAttribute String (String -> Boolean)    -- ^ Check user attribute
  | Environment String                          -- ^ Check environment
  | Always                                      -- ^ Always match
  | Never                                       -- ^ Never match
  | AllOf (Array TargetingCondition)            -- ^ AND conditions
  | AnyOf (Array TargetingCondition)            -- ^ OR conditions

-- | Targeting context provided by the application
type TargetingContext =
  { userId :: Maybe String
  , attributes :: Map String String
  , environment :: String
  }

-- | Empty targeting context
emptyContext :: TargetingContext
emptyContext =
  { userId: Nothing
  , attributes: Map.empty
  , environment: "development"
  }

-- | Create a percentage-based targeting rule
percentage :: Number -> FlagValue -> TargetingRule
percentage pct value = { condition: Percentage pct, value }

-- | Create a user ID targeting rule
userIds :: Array String -> FlagValue -> TargetingRule
userIds ids value = { condition: UserIds ids, value }

-- | Create a user attribute targeting rule
userAttribute :: String -> (String -> Boolean) -> FlagValue -> TargetingRule
userAttribute attr predicate value = { condition: UserAttribute attr predicate, value }

-- | Create an environment targeting rule
environment :: String -> FlagValue -> TargetingRule
environment env value = { condition: Environment env, value }

-- | Always match (useful for default overrides)
always :: FlagValue -> TargetingRule
always value = { condition: Always, value }

-- | Never match
never :: FlagValue -> TargetingRule
never value = { condition: Never, value }

-- | All conditions must match
allOf :: Array TargetingCondition -> FlagValue -> TargetingRule
allOf conditions value = { condition: AllOf conditions, value }

-- | Any condition must match
anyOf :: Array TargetingCondition -> FlagValue -> TargetingRule
anyOf conditions value = { condition: AnyOf conditions, value }

-- | Evaluate a targeting condition
evaluateRule :: TargetingRule -> TargetingContext -> Boolean
evaluateRule rule ctx = evaluateCondition rule.condition ctx

evaluateCondition :: TargetingCondition -> TargetingContext -> Boolean
evaluateCondition condition ctx = case condition of
  Always -> true
  Never -> false
  
  Percentage pct ->
    case ctx.userId of
      Just uid -> toNumber (hashString uid `mod` 100) < pct
      Nothing -> false
  
  UserIds ids ->
    case ctx.userId of
      Just uid -> Array.elem uid ids
      Nothing -> false
  
  UserAttribute attr predicate ->
    case Map.lookup attr ctx.attributes of
      Just val -> predicate val
      Nothing -> false
  
  Environment env -> ctx.environment == env
  
  AllOf conditions -> Array.all (\c -> evaluateCondition c ctx) conditions
  
  AnyOf conditions -> Array.any (\c -> evaluateCondition c ctx) conditions

-- ═════════════════════════════════════════════════════════════════════════════
-- Flag Definitions Helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Define a boolean flag
defineBoolFlag :: String -> Boolean -> Array TargetingRule -> FlagDefinition
defineBoolFlag name defaultVal rules =
  { flag: Flag name
  , defaultValue: BoolValue defaultVal
  , rules
  , metadata: { description: Nothing, tags: [] }
  }

-- | Define a string flag
defineStringFlag :: String -> String -> Array TargetingRule -> FlagDefinition
defineStringFlag name defaultVal rules =
  { flag: Flag name
  , defaultValue: StringValue defaultVal
  , rules
  , metadata: { description: Nothing, tags: [] }
  }

-- | Define a number flag
defineNumberFlag :: String -> Number -> Array TargetingRule -> FlagDefinition
defineNumberFlag name defaultVal rules =
  { flag: Flag name
  , defaultValue: NumberValue defaultVal
  , rules
  , metadata: { description: Nothing, tags: [] }
  }

-- | Define a JSON flag
defineJsonFlag :: String -> Object FlagValue -> Array TargetingRule -> FlagDefinition
defineJsonFlag name defaultVal rules =
  { flag: Flag name
  , defaultValue: JsonValue defaultVal
  , rules
  , metadata: { description: Nothing, tags: [] }
  }

-- ═════════════════════════════════════════════════════════════════════════════
-- Dynamic Updates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Subscribe to flag changes
subscribe :: FlagProvider -> (Flag -> FlagValue -> Effect Unit) -> Effect (Effect Unit)
subscribe provider handler = do
  Ref.modify_ (flip Array.snoc handler) provider.subscribers
  pure $ Ref.modify_ (Array.filter (\h -> unsafeRefEq h handler # not)) provider.subscribers

foreign import unsafeRefEq :: forall a. a -> a -> Boolean

-- | Refresh flags from remote source
refresh :: FlagProvider -> Aff Unit
refresh provider = pure unit  -- Implementation would fetch from remote

-- | Set a local override for a flag
setOverride :: FlagProvider -> Flag -> FlagValue -> Effect Unit
setOverride provider f value = do
  Ref.modify_ (Map.insert f value) provider.overrides
  notifySubscribers provider f value
  when provider.config.persistOverrides do
    persistOverrides provider.overrides

-- | Clear an override
clearOverride :: FlagProvider -> Flag -> Effect Unit
clearOverride provider f = do
  Ref.modify_ (Map.delete f) provider.overrides
  maybeVal <- getValue provider f
  case maybeVal of
    Just val -> notifySubscribers provider f val
    Nothing -> pure unit
  when provider.config.persistOverrides do
    persistOverrides provider.overrides

-- | Clear all overrides
clearAllOverrides :: FlagProvider -> Effect Unit
clearAllOverrides provider = do
  Ref.write Map.empty provider.overrides
  when provider.config.persistOverrides do
    persistOverrides provider.overrides

-- | Notify subscribers of a flag change
notifySubscribers :: FlagProvider -> Flag -> FlagValue -> Effect Unit
notifySubscribers provider f value = do
  subs <- Ref.read provider.subscribers
  for_ subs \handler -> handler f value
  where
  for_ :: forall a. Array a -> (a -> Effect Unit) -> Effect Unit
  for_ arr fn = void $ traverseImpl fn arr

foreign import traverseImpl :: forall a b. (a -> Effect b) -> Array a -> Effect (Array b)

-- ═════════════════════════════════════════════════════════════════════════════
-- Persistence
-- ═════════════════════════════════════════════════════════════════════════════

-- | Load flags from JSON string
loadFromJson :: FlagProvider -> String -> Effect Unit
loadFromJson provider json = do
  definitions <- parseJsonFlags json
  Ref.write definitions provider.definitions

foreign import parseJsonFlags :: String -> Effect (Map Flag FlagDefinition)

-- | Load flags from a URL
loadFromUrl :: FlagProvider -> String -> Aff Unit
loadFromUrl provider url = do
  json <- fetchJson url
  liftEffect $ loadFromJson provider json

foreign import fetchJson :: String -> Aff String

-- | Load persisted overrides from localStorage
foreign import loadPersistedOverrides :: Ref (Map Flag FlagValue) -> Effect Unit

-- | Persist overrides to localStorage
foreign import persistOverrides :: Ref (Map Flag FlagValue) -> Effect Unit

-- ═════════════════════════════════════════════════════════════════════════════
-- DevTools
-- ═════════════════════════════════════════════════════════════════════════════

-- | State information for a flag (for DevTools)
type FlagState =
  { flag :: Flag
  , currentValue :: Maybe FlagValue
  , defaultValue :: FlagValue
  , hasOverride :: Boolean
  , matchingRules :: Array TargetingRule
  }

-- | Get all registered flags
getAllFlags :: FlagProvider -> Effect (Array Flag)
getAllFlags provider = do
  defs <- Ref.read provider.definitions
  pure $ Map.keys defs # Array.fromFoldable

-- | Get detailed state for a flag
getFlagState :: FlagProvider -> Flag -> Effect (Maybe FlagState)
getFlagState provider f = do
  definitions <- Ref.read provider.definitions
  overrides <- Ref.read provider.overrides
  ctx <- Ref.read provider.context
  
  case Map.lookup f definitions of
    Nothing -> pure Nothing
    Just def -> do
      currentValue <- getValue provider f
      let hasOverride = Map.member f overrides
      let matchingRules = Array.filter (\r -> evaluateRule r ctx) def.rules
      pure $ Just
        { flag: f
        , currentValue
        , defaultValue: def.defaultValue
        , hasOverride
        , matchingRules
        }

-- ═════════════════════════════════════════════════════════════════════════════
-- Utilities
-- ═════════════════════════════════════════════════════════════════════════════

foreign import hashString :: String -> Int

-- | Int to Number (pure)
toNumber :: Int -> Number
toNumber = Int.toNumber

-- Note: Using Control.Monad.when

infixr 0 Tuple as /\
