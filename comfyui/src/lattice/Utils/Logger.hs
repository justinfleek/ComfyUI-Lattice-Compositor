-- |
-- Module      : Lattice.Utils.Logger
-- Description : Centralized logging with configurable log levels
--
-- Migrated from ui/src/utils/logger.ts
-- IO-based logger; config via MVar. No forbidden patterns.
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.Utils.Logger
  ( -- Types
    LogLevel(..)
  , LoggerConfig(..)
  , Logger(..)
  -- Config (IO)
  , newLoggerConfig
  , setLogLevel
  , setLogPrefix
  , setTimestampEnabled
  , getLogLevel
  , getLoggerConfig
  -- Logger instance
  , createLogger
  -- Pre-configured contexts
  , defaultPrefix
  ) where

import Control.Concurrent.MVar (MVar, newMVar, readMVar, modifyMVar_)
import Control.Monad (when)
import Data.Text (Text)
import qualified Data.Text as T
import Data.Time.Clock (getCurrentTime)
import Data.Time.Format (defaultTimeLocale, formatTime)

-- ============================================================================
-- TYPES
-- ============================================================================

-- | Log level ordering: debug < info < warn < error < none
data LogLevel
  = LogDebug
  | LogInfo
  | LogWarn
  | LogError
  | LogNone
  deriving (Eq, Show, Enum, Bounded)

-- | Numeric level for comparison (higher = more severe)
logLevelOrd :: LogLevel -> Int
logLevelOrd LogDebug = 0
logLevelOrd LogInfo  = 1
logLevelOrd LogWarn  = 2
logLevelOrd LogError = 3
logLevelOrd LogNone  = 4

-- | Logger configuration (mutable in IO)
data LoggerConfig = LoggerConfig
  { configLevel         :: LogLevel
  , configPrefix        :: Text
  , configEnableTimestamp :: Bool
  }
  deriving (Eq, Show)

-- | Default prefix string
defaultPrefix :: Text
defaultPrefix = "[Lattice]"

-- | Default config: warn level, no timestamp
defaultLoggerConfig :: LoggerConfig
defaultLoggerConfig = LoggerConfig
  { configLevel           = LogWarn
  , configPrefix          = defaultPrefix
  , configEnableTimestamp = False
  }

-- | Logger: context + ref to config + IO actions
data Logger = Logger
  { loggerContext   :: Text
  , loggerConfigRef :: MVar LoggerConfig
  , loggerDebug     :: Text -> IO ()
  , loggerInfo      :: Text -> IO ()
  , loggerWarn      :: Text -> IO ()
  , loggerError     :: Text -> IO ()
  , loggerLog       :: LogLevel -> Text -> IO ()
  , loggerGroup     :: Text -> IO ()
  , loggerGroupEnd  :: IO ()
  , loggerTable     :: Text -> IO ()
  , loggerTime      :: Text -> IO ()
  , loggerTimeEnd   :: Text -> IO ()
  }

-- ============================================================================
-- PURE HELPERS
-- ============================================================================

-- | Whether a message at this level should be logged given current config level
shouldLog :: LogLevel -> LogLevel -> Bool
shouldLog messageLevel configLevel =
  logLevelOrd messageLevel >= logLevelOrd configLevel

-- | Format with timestamp computed in IO (no pure timestamp to avoid error)
formatMessageIO :: LoggerConfig -> Text -> Text -> Text -> IO Text
formatMessageIO cfg level context message = do
  let prefix = if T.null (configPrefix cfg) then "" else configPrefix cfg <> " "
      ctx   = if T.null context then "" else "[" <> context <> "] "
  ts <- if configEnableTimestamp cfg
        then do
          t <- getCurrentTime
          return ("[" <> T.pack (formatTime defaultTimeLocale "%Y-%m-%dT%H:%M:%S%QZ" t) <> "] ")
        else return ""
  return (ts <> prefix <> ctx <> message)

-- ============================================================================
-- CONFIG (IO)
-- ============================================================================

-- | Create a new mutable logger config (default: warn, no timestamp)
newLoggerConfig :: IO (MVar LoggerConfig)
newLoggerConfig = newMVar defaultLoggerConfig

-- | Set the global log level
setLogLevel :: MVar LoggerConfig -> LogLevel -> IO ()
setLogLevel ref lvl = modifyMVar_ ref (\c -> return c { configLevel = lvl })

-- | Set the log prefix
setLogPrefix :: MVar LoggerConfig -> Text -> IO ()
setLogPrefix ref p = modifyMVar_ ref (\c -> return c { configPrefix = p })

-- | Enable or disable timestamps in log output
setTimestampEnabled :: MVar LoggerConfig -> Bool -> IO ()
setTimestampEnabled ref b = modifyMVar_ ref (\c -> return c { configEnableTimestamp = b })

-- | Get current log level
getLogLevel :: MVar LoggerConfig -> IO LogLevel
getLogLevel ref = configLevel <$> readMVar ref

-- | Get current config (snapshot)
getLoggerConfig :: MVar LoggerConfig -> IO LoggerConfig
getLoggerConfig = readMVar

-- ============================================================================
-- CREATE LOGGER
-- ============================================================================

-- | Create a logger instance with a specific context.
-- Pass the same MVar to all loggers that should share config.
createLogger :: MVar LoggerConfig -> Text -> Logger
createLogger ref context =
  let
    write level label msg = do
      cfg <- readMVar ref
      when (shouldLog level (configLevel cfg)) $ do
        formatted <- formatMessageIO cfg label context msg
        putStrLn (T.unpack formatted)

    debug msg = write LogDebug "DEBUG" msg
    info  msg = write LogInfo  "INFO"  msg
    warn  msg = write LogWarn  "WARN"  msg
    err   msg = write LogError "ERROR" msg

    log level msg = case level of
      LogDebug -> debug msg
      LogInfo  -> info msg
      LogWarn  -> warn msg
      LogError -> err msg
      LogNone  -> return ()

    group label = do
      cfg <- readMVar ref
      when (shouldLog LogDebug (configLevel cfg)) $
        putStrLn (T.unpack ("[GROUP] " <> context <> " " <> label))

    groupEnd = return ()  -- no-op in CLI

    table dataText = do
      cfg <- readMVar ref
      when (shouldLog LogDebug (configLevel cfg)) $ do
        putStrLn (T.unpack ("[TABLE] " <> context <> " Table:"))
        putStrLn (T.unpack dataText)

    time label = do
      cfg <- readMVar ref
      when (shouldLog LogDebug (configLevel cfg)) $
        putStrLn (T.unpack (defaultPrefix <> " [" <> context <> "] " <> label <> " (start)"))

    timeEnd _label = return ()  -- no-op without console.time

  in Logger
      { loggerContext   = context
      , loggerConfigRef = ref
      , loggerDebug     = debug
      , loggerInfo      = info
      , loggerWarn      = warn
      , loggerError     = err
      , loggerLog       = log
      , loggerGroup     = group
      , loggerGroupEnd  = groupEnd
      , loggerTable     = table
      , loggerTime      = time
      , loggerTimeEnd   = timeEnd
      }
