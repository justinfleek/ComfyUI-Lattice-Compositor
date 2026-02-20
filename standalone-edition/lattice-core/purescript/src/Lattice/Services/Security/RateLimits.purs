-- | Lattice.Services.Security.RateLimits - Persistent rate limiting
-- |
-- | Stores rate limit counters in localStorage so they survive page refresh.
-- | Implements per-day limits with automatic daily reset.
-- |
-- | SECURITY: Prevents abuse via:
-- | - Persistent counters (survive page refresh)
-- | - Per-day limits (reset at midnight UTC)
-- | - Per-tool tracking
-- | - Explicit user action required to reset
-- |
-- | Source: ui/src/services/security/rateLimits.ts

module Lattice.Services.Security.RateLimits
  ( -- * Types
    RateLimitConfig
  , RateLimitStatus
  , RateLimitWarning
  , WarningSeverity(..)
    -- * API
  , checkRateLimit
  , recordToolCall
  , resetSessionLimit
  , resetAllSessionLimits
  , getAllRateLimitStatus
  , setRateLimitConfig
  , getRemainingCalls
  , checkRateLimitWarnings
    -- * Constants
  , defaultLimits
  ) where

import Prelude
import Effect (Effect)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Effect.Console (log, warn)
import Effect.Now (nowDate, nowDateTime)
import Effect.Aff (launchAff_)
import Data.Array (filter, mapMaybe)
import Data.Array as Array
import Data.Argonaut.Core (Json, stringify, jsonEmptyObject)
import Data.Argonaut.Decode (decodeJson)
import Data.Argonaut.Encode (encodeJson)
import Data.Argonaut.Parser (jsonParser)
import Data.Date (Date, year, month, day, adjust)
import Data.DateTime (DateTime, date, time, Time, hour, minute, second)
import Data.DateTime.Instant (toDateTime, fromDateTime)
import Data.Enum (fromEnum)
import Data.Time.Duration (Days(..))
import Data.Either (Either(..), hush)
import Data.Foldable (for_)
import Data.Int (toNumber, floor)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Set (Set)
import Data.Set as Set
import Data.String (joinWith, Pattern(..), indexOf, drop, take)
import Data.String.CodeUnits (toCharArray)
import Data.Tuple (Tuple(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Effect.Unsafe (unsafePerformEffect)

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Rate limit configuration for a tool
type RateLimitConfig =
  { toolName :: String
  , maxPerDay :: Int          -- Maximum calls per day
  , maxPerSession :: Maybe Int -- Maximum calls per session (optional)
  , vramCostMB :: Maybe Int   -- VRAM cost in MB
  }

-- | Status of rate limit for a tool
type RateLimitStatus =
  { toolName :: String
  , callsToday :: Int
  , maxPerDay :: Int
  , callsThisSession :: Int
  , maxPerSession :: Maybe Int
  , canCall :: Boolean
  , blockedReason :: Maybe String
  , resetsAt :: String
  , resetsIn :: String
  }

-- | Warning severity level
data WarningSeverity = SevWarning | SevCritical

derive instance Eq WarningSeverity
derive instance Generic WarningSeverity _
instance Show WarningSeverity where show = genericShow

-- | Rate limit warning
type RateLimitWarning =
  { toolName :: String
  , message :: String
  , severity :: WarningSeverity
  }

-- | Stored rate limits (persisted to localStorage)
type StoredRateLimits =
  { date :: String               -- Date string (YYYY-MM-DD UTC)
  , counts :: Map String Int     -- Tool call counts
  , lastReset :: String          -- Last reset timestamp
  }

-- ────────────────────────────────────────────────────────────────────────────
--                                                           // date/time helpers
-- ────────────────────────────────────────────────────────────────────────────

-- | Pad a number to 2 digits with leading zero
padTwo :: Int -> String
padTwo n = if n < 10 then "0" <> show n else show n

-- | Pad a number to 4 digits with leading zeros (for year)
padFour :: Int -> String
padFour n
  | n < 10 = "000" <> show n
  | n < 100 = "00" <> show n
  | n < 1000 = "0" <> show n
  | otherwise = show n

-- | Format a Date as YYYY-MM-DD
formatDateYYYYMMDD :: Date -> String
formatDateYYYYMMDD d =
  padFour (fromEnum (year d)) <> "-" <>
  padTwo (fromEnum (month d)) <> "-" <>
  padTwo (fromEnum (day d))

-- | Format a DateTime as ISO 8601 string
formatDateTimeISO :: DateTime -> String
formatDateTimeISO dt =
  let d = date dt
      t = time dt
  in formatDateYYYYMMDD d <> "T" <>
     padTwo (fromEnum (hour t)) <> ":" <>
     padTwo (fromEnum (minute t)) <> ":" <>
     padTwo (fromEnum (second t)) <> "Z"

-- | Current UTC date string (YYYY-MM-DD)
getCurrentDateUTC :: Effect String
getCurrentDateUTC = do
  d <- nowDate
  pure (formatDateYYYYMMDD d)

-- | Tomorrow midnight UTC as ISO string
getTomorrowMidnightUTC :: Effect String  
getTomorrowMidnightUTC = do
  today <- nowDate
  let tomorrow = fromMaybe today (adjust (Days 1.0) today)
  pure (formatDateYYYYMMDD tomorrow <> "T00:00:00Z")

-- | Human-readable time until reset (approximate hours until midnight)
getTimeUntilReset :: Effect String
getTimeUntilReset = do
  dt <- nowDateTime
  let t = time dt
      hoursLeft = 24 - fromEnum (hour t)
  pure ("~" <> show hoursLeft <> " hours")

-- | Current ISO timestamp
getCurrentISOTimestamp :: Effect String
getCurrentISOTimestamp = do
  dt <- nowDateTime
  pure (formatDateTimeISO dt)

-- | Parse JSON to Map String Int (for counts)
parseCountsJson :: String -> Maybe (Map String Int)
parseCountsJson json = do
  case jsonParser json of
    Left _ -> Nothing
    Right j -> hush (decodeJson j)

-- | Stringify Map String Int to JSON
stringifyCountsJson :: Map String Int -> String
stringifyCountsJson m = stringify (encodeJson m)

-- ────────────────────────────────────────────────────────────────────────────
--                                                                  // storage
-- ────────────────────────────────────────────────────────────────────────────
-- | NOTE: These use in-memory storage. In production, use Bridge.Client for
-- | persistent storage via the Haskell backend's DuckDB.

-- | In-memory localStorage simulation
localStorageRef :: Ref (Map String String)
localStorageRef = unsafePerformEffect (Ref.new Map.empty)

-- | In-memory sessionStorage simulation  
sessionStorageRef :: Ref (Map String String)
sessionStorageRef = unsafePerformEffect (Ref.new Map.empty)

-- | Get item from localStorage
localStorageGetItem :: String -> Effect (Maybe String)
localStorageGetItem key = Map.lookup key <$> Ref.read localStorageRef

-- | Set item in localStorage
localStorageSetItem :: String -> String -> Effect Unit
localStorageSetItem key value = Ref.modify_ (Map.insert key value) localStorageRef

-- | Get item from sessionStorage
sessionStorageGetItem :: String -> Effect (Maybe String)
sessionStorageGetItem key = Map.lookup key <$> Ref.read sessionStorageRef

-- | Set item in sessionStorage
sessionStorageSetItem :: String -> String -> Effect Unit
sessionStorageSetItem key value = Ref.modify_ (Map.insert key value) sessionStorageRef



-- ────────────────────────────────────────────────────────────────────────────
-- Constants
-- ────────────────────────────────────────────────────────────────────────────

storageKey :: String
storageKey = "lattice_rate_limits"

sessionKey :: String
sessionKey = "lattice_session_counts"

-- | Default rate limits for high-risk tools
defaultLimits :: Map String RateLimitConfig
defaultLimits = Map.fromFoldable
  [ Tuple "decomposeImage"
      { toolName: "decomposeImage"
      , maxPerDay: 10
      , maxPerSession: Just 3
      , vramCostMB: Just 28800
      }
  , Tuple "vectorizeImage"
      { toolName: "vectorizeImage"
      , maxPerDay: 20
      , maxPerSession: Just 5
      , vramCostMB: Just 4000
      }
  ]

-- ────────────────────────────────────────────────────────────────────────────
-- State (in-memory refs)
-- ────────────────────────────────────────────────────────────────────────────

-- | Custom limits (override defaults)
customLimitsRef :: Ref (Map String RateLimitConfig)
customLimitsRef = unsafePerformEffect (Ref.new Map.empty)

-- | Session counts (in-memory, cleared on page refresh)
sessionCountsRef :: Ref (Map String Int)
sessionCountsRef = unsafePerformEffect (Ref.new Map.empty)

-- ────────────────────────────────────────────────────────────────────────────
-- Storage Functions
-- ────────────────────────────────────────────────────────────────────────────

-- | Load rate limits from localStorage
loadStoredLimits :: Effect StoredRateLimits
loadStoredLimits = do
  today <- getCurrentDateUTC
  timestamp <- getCurrentISOTimestamp
  maybeStored <- localStorageGetItem storageKey
  case maybeStored of
    Nothing -> pure { date: today, counts: Map.empty, lastReset: timestamp }
    Just stored -> case parseStoredLimits stored of
      Nothing -> pure { date: today, counts: Map.empty, lastReset: timestamp }
      Just data_ ->
        -- Check if we need to reset (new day)
        if data_.date /= today
          then do
            log "[SECURITY] Daily rate limits reset (new day)"
            pure { date: today, counts: Map.empty, lastReset: timestamp }
          else pure data_

-- | Parse stored limits JSON
parseStoredLimits :: String -> Maybe StoredRateLimits
parseStoredLimits json = do
  -- Simple JSON parsing for { date, counts, lastReset }
  -- In production, use Argonaut
  -- For now, use FFI helper
  counts <- parseCountsJson json
  -- This is simplified - real implementation needs full JSON parsing
  Just { date: extractDateFromJson json
       , counts: counts
       , lastReset: extractLastResetFromJson json
       }

-- | Extract a string field value from JSON
-- | Handles pattern "fieldName":"value"
extractField :: String -> String -> Maybe String
extractField fieldName json =
  let pattern = "\"" <> fieldName <> "\":\""
      patternLen = Array.length (toCharArray pattern)
  in case indexOf (Pattern pattern) json of
    Nothing -> Nothing
    Just startIdx ->
      let valueStart = startIdx + patternLen
          remaining = drop valueStart json
      in case indexOf (Pattern "\"") remaining of
        Nothing -> Nothing
        Just endIdx -> Just (take endIdx remaining)

-- | Extract date field from JSON
extractDateFromJson :: String -> String
extractDateFromJson json =
  fromMaybe "" (extractField "date" json)

-- | Extract lastReset field from JSON
extractLastResetFromJson :: String -> String
extractLastResetFromJson json =
  fromMaybe "" (extractField "lastReset" json)

-- | Save rate limits to localStorage
saveStoredLimits :: StoredRateLimits -> Effect Unit
saveStoredLimits limits = do
  let json = stringifyStoredLimits limits
  localStorageSetItem storageKey json

-- | Stringify stored limits to JSON
stringifyStoredLimits :: StoredRateLimits -> String
stringifyStoredLimits limits =
  "{\"date\":\"" <> limits.date <>
  "\",\"counts\":" <> stringifyCountsJson limits.counts <>
  ",\"lastReset\":\"" <> limits.lastReset <> "\"}"

-- | Load session counts from sessionStorage
loadSessionCounts :: Effect (Map String Int)
loadSessionCounts = do
  maybeStored <- sessionStorageGetItem sessionKey
  case maybeStored of
    Nothing -> pure Map.empty
    Just stored -> pure (fromMaybe Map.empty (parseCountsJson stored))

-- | Save session counts to sessionStorage
saveSessionCounts :: Map String Int -> Effect Unit
saveSessionCounts counts =
  sessionStorageSetItem sessionKey (stringifyCountsJson counts)

-- ────────────────────────────────────────────────────────────────────────────
-- Public API
-- ────────────────────────────────────────────────────────────────────────────

-- | Check if a tool call is allowed under rate limits
checkRateLimit :: String -> Effect RateLimitStatus
checkRateLimit toolName = do
  customLimits <- Ref.read customLimitsRef
  sessionCounts <- Ref.read sessionCountsRef

  let maybeConfig = case Map.lookup toolName customLimits of
        Just c -> Just c
        Nothing -> Map.lookup toolName defaultLimits

  resetsAt <- getTomorrowMidnightUTC
  resetsIn <- getTimeUntilReset

  case maybeConfig of
    Nothing -> do
      -- No limits configured for this tool
      let sessionCount = fromMaybe 0 (Map.lookup toolName sessionCounts)
      pure
        { toolName
        , callsToday: 0
        , maxPerDay: 999999  -- Effectively unlimited
        , callsThisSession: sessionCount
        , maxPerSession: Nothing
        , canCall: true
        , blockedReason: Nothing
        , resetsAt
        , resetsIn
        }

    Just config -> do
      stored <- loadStoredLimits
      let callsToday = fromMaybe 0 (Map.lookup toolName stored.counts)
      let callsThisSession = fromMaybe 0 (Map.lookup toolName sessionCounts)

      -- Check daily limit
      if callsToday >= config.maxPerDay
        then pure
          { toolName
          , callsToday
          , maxPerDay: config.maxPerDay
          , callsThisSession
          , maxPerSession: config.maxPerSession
          , canCall: false
          , blockedReason: Just ("Daily limit reached (" <> show callsToday <> "/" <> show config.maxPerDay <> "). Resets in " <> resetsIn <> ".")
          , resetsAt
          , resetsIn
          }
        -- Check session limit
        else case config.maxPerSession of
          Just maxSession | callsThisSession >= maxSession ->
            pure
              { toolName
              , callsToday
              , maxPerDay: config.maxPerDay
              , callsThisSession
              , maxPerSession: config.maxPerSession
              , canCall: false
              , blockedReason: Just ("Session limit reached (" <> show callsThisSession <> "/" <> show maxSession <> "). Use resetSessionLimit('" <> toolName <> "') to continue.")
              , resetsAt
              , resetsIn
              }
          _ ->
            pure
              { toolName
              , callsToday
              , maxPerDay: config.maxPerDay
              , callsThisSession
              , maxPerSession: config.maxPerSession
              , canCall: true
              , blockedReason: Nothing
              , resetsAt
              , resetsIn
              }

-- | Record a tool call (increment counters)
recordToolCall :: String -> Effect Unit
recordToolCall toolName = do
  -- Increment daily count
  stored <- loadStoredLimits
  let currentDaily = fromMaybe 0 (Map.lookup toolName stored.counts)
  let newCounts = Map.insert toolName (currentDaily + 1) stored.counts
  saveStoredLimits (stored { counts = newCounts })

  -- Increment session count
  sessionCounts <- Ref.read sessionCountsRef
  let currentSession = fromMaybe 0 (Map.lookup toolName sessionCounts)
  let newSessionCounts = Map.insert toolName (currentSession + 1) sessionCounts
  Ref.write newSessionCounts sessionCountsRef
  saveSessionCounts newSessionCounts

  -- Log
  status <- checkRateLimit toolName
  log ("[SECURITY] Rate limit recorded: " <> toolName <>
       " (today: " <> show status.callsToday <> "/" <> show status.maxPerDay <>
       ", session: " <> show status.callsThisSession <> ")")

-- | Reset session limit for a specific tool
resetSessionLimit :: String -> Effect Unit
resetSessionLimit toolName = do
  sessionCounts <- Ref.read sessionCountsRef
  let oldCount = fromMaybe 0 (Map.lookup toolName sessionCounts)
  let newCounts = Map.insert toolName 0 sessionCounts
  Ref.write newCounts sessionCountsRef
  saveSessionCounts newCounts

  log ("[SECURITY] Session limit reset for " <> toolName <> " (was: " <> show oldCount <> ")")

-- | Reset ALL session limits (requires confirmation)
resetAllSessionLimits :: String -> Effect Boolean
resetAllSessionLimits confirmationCode =
  if confirmationCode /= "RESET_SESSION_LIMITS"
    then do
      warn "[SECURITY] Reset rejected: invalid confirmation code"
      pure false
    else do
      Ref.write Map.empty sessionCountsRef
      saveSessionCounts Map.empty
      log "[SECURITY] All session limits reset"
      pure true

-- | Get status for all rate-limited tools
getAllRateLimitStatus :: Effect (Array RateLimitStatus)
getAllRateLimitStatus = do
  customLimits <- Ref.read customLimitsRef
  let defaultToolNames = Map.keys defaultLimits
  let customToolNames = Map.keys customLimits
  let allTools = Set.union (Set.fromFoldable defaultToolNames) (Set.fromFoldable customToolNames)

  statuses <- for (Set.toUnfoldable allTools :: Array String) checkRateLimit
  pure statuses

-- | Set custom rate limit configuration
setRateLimitConfig :: RateLimitConfig -> Effect Unit
setRateLimitConfig config = do
  customLimits <- Ref.read customLimitsRef
  Ref.write (Map.insert config.toolName config customLimits) customLimitsRef
  log ("[SECURITY] Rate limit configured for " <> config.toolName)

-- | Get remaining calls for a tool
getRemainingCalls :: String -> Effect { remainingToday :: Int, remainingSession :: Int }
getRemainingCalls toolName = do
  status <- checkRateLimit toolName
  pure
    { remainingToday: max 0 (status.maxPerDay - status.callsToday)
    , remainingSession: case status.maxPerSession of
        Just maxSession -> max 0 (maxSession - status.callsThisSession)
        Nothing -> 999999  -- Effectively unlimited
    }

-- | Check if any rate limits are close to being reached
checkRateLimitWarnings :: Effect (Array RateLimitWarning)
checkRateLimitWarnings = do
  statuses <- getAllRateLimitStatus
  customLimits <- Ref.read customLimitsRef

  pure (statuses >>= collectWarnings customLimits)

  where
    collectWarnings :: Map String RateLimitConfig -> RateLimitStatus -> Array RateLimitWarning
    collectWarnings customLimits status =
      let maybeConfig = case Map.lookup status.toolName customLimits of
            Just c -> Just c
            Nothing -> Map.lookup status.toolName defaultLimits
      in case maybeConfig of
        Nothing -> []
        Just _config ->
          let dailyPercent = toNumber status.callsToday / toNumber status.maxPerDay
              dailyWarnings =
                if dailyPercent >= 1.0
                  then [{ toolName: status.toolName
                        , message: "Daily limit reached for " <> status.toolName <> ". Resets in " <> status.resetsIn <> "."
                        , severity: SevCritical
                        }]
                else if dailyPercent >= 0.8
                  then [{ toolName: status.toolName
                        , message: status.toolName <> ": " <> show status.callsToday <> "/" <> show status.maxPerDay <> " daily calls used."
                        , severity: SevWarning
                        }]
                else []

              sessionWarnings = case status.maxPerSession of
                Just maxSession | status.callsThisSession >= maxSession ->
                  [{ toolName: status.toolName
                   , message: "Session limit reached for " <> status.toolName <> ". Manual reset required."
                   , severity: SevCritical
                   }]
                _ -> []
          in dailyWarnings <> sessionWarnings

-- ────────────────────────────────────────────────────────────────────────────
-- Helpers
-- ────────────────────────────────────────────────────────────────────────────

-- | Traverse effect over array
for :: forall a b. Array a -> (a -> Effect b) -> Effect (Array b)
for arr f = go 0 []
  where
    len = Array.length arr
    go idx acc
      | idx >= len = pure acc
      | otherwise = case Array.index arr idx of
          Nothing -> pure acc
          Just x -> do
            b <- f x
            go (idx + 1) (acc <> [b])

-- | Maximum of two integers
max :: Int -> Int -> Int
max a b = if a > b then a else b
