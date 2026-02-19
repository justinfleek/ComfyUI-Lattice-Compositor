-- | Lattice.Utils.Logger - Logging utility
-- |
-- | Centralized logging with configurable log levels.
-- | In production, only warnings and errors are shown.
-- | In development, all logs are shown.
-- |
-- | Source: lattice-core/lean/Lattice/Utils/Logger.lean

module Lattice.Utils.Logger
  ( -- Log Levels
    LogLevel(..)
  , levelPriority
  , levelToString
    -- Logger Configuration
  , LoggerConfig
  , defaultConfig
  , devConfig
    -- Log Entry
  , LogEntry
  , mkLogEntry
  , formatEntry
    -- Logger
  , Logger
  , createLogger
  , withConfig
  , setLevel
  , shouldLog
    -- Logging (Pure)
  , debugEntry
  , infoEntry
  , warnEntry
  , errorEntry
    -- Pre-configured Loggers
  , appLogger
  , storeLogger
  , engineLogger
  , layerLogger
  , renderLogger
  , audioLogger
  , exportLogger
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.String as String
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

--------------------------------------------------------------------------------
-- Log Levels
--------------------------------------------------------------------------------

-- | Log level enumeration
data LogLevel
  = LogDebug
  | LogInfo
  | LogWarn
  | LogError
  | LogNone

derive instance Eq LogLevel
derive instance Ord LogLevel
derive instance Generic LogLevel _

instance Show LogLevel where
  show = genericShow

-- | Log level priority (lower = more verbose)
levelPriority :: LogLevel -> Int
levelPriority = case _ of
  LogDebug -> 0
  LogInfo -> 1
  LogWarn -> 2
  LogError -> 3
  LogNone -> 4

-- | Convert log level to string
levelToString :: LogLevel -> String
levelToString = case _ of
  LogDebug -> "DEBUG"
  LogInfo -> "INFO"
  LogWarn -> "WARN"
  LogError -> "ERROR"
  LogNone -> "NONE"

--------------------------------------------------------------------------------
-- Logger Configuration
--------------------------------------------------------------------------------

-- | Logger configuration
type LoggerConfig =
  { level :: LogLevel
  , prefix :: String
  , enableTimestamp :: Boolean
  }

-- | Default logger configuration (production)
defaultConfig :: LoggerConfig
defaultConfig =
  { level: LogWarn
  , prefix: "[Lattice]"
  , enableTimestamp: false
  }

-- | Development configuration (all logs shown)
devConfig :: LoggerConfig
devConfig =
  { level: LogDebug
  , prefix: "[Lattice]"
  , enableTimestamp: true
  }

--------------------------------------------------------------------------------
-- Log Entry
--------------------------------------------------------------------------------

-- | A log entry ready to be outputted
type LogEntry =
  { level :: LogLevel
  , context :: String
  , message :: String
  , timestamp :: Maybe String
  , prefix :: String
  }

-- | Create a log entry
mkLogEntry :: LogLevel -> String -> String -> LoggerConfig -> Maybe String -> LogEntry
mkLogEntry level context message config timestamp =
  { level
  , context
  , message
  , timestamp: if config.enableTimestamp then timestamp else Nothing
  , prefix: config.prefix
  }

-- | Format a log entry as string
formatEntry :: LogEntry -> String
formatEntry entry =
  let parts = []
        <> (case entry.timestamp of
              Just ts -> ["[" <> ts <> "]"]
              Nothing -> [])
        <> (if String.null entry.prefix then [] else [entry.prefix])
        <> (if String.null entry.context then [] else ["[" <> entry.context <> "]"])
        <> [entry.message]
  in String.joinWith " " parts

--------------------------------------------------------------------------------
-- Logger
--------------------------------------------------------------------------------

-- | A logger instance with a specific context
type Logger =
  { context :: String
  , config :: LoggerConfig
  }

-- | Create a logger with a specific context
createLogger :: String -> Logger
createLogger context =
  { context
  , config: defaultConfig
  }

-- | Update logger config
withConfig :: Logger -> LoggerConfig -> Logger
withConfig logger config = logger { config = config }

-- | Set log level
setLevel :: Logger -> LogLevel -> Logger
setLevel logger level = logger { config = logger.config { level = level } }

-- | Should this log level be shown given the config?
shouldLog :: LogLevel -> LoggerConfig -> Boolean
shouldLog level config = levelPriority level >= levelPriority config.level

--------------------------------------------------------------------------------
-- Logging Functions (Pure)
--------------------------------------------------------------------------------

-- | Create a debug log entry (returns Nothing if level too low)
debugEntry :: Logger -> String -> Maybe LogEntry
debugEntry logger message =
  if shouldLog LogDebug logger.config
  then Just $ mkLogEntry LogDebug logger.context message logger.config Nothing
  else Nothing

-- | Create an info log entry (returns Nothing if level too low)
infoEntry :: Logger -> String -> Maybe LogEntry
infoEntry logger message =
  if shouldLog LogInfo logger.config
  then Just $ mkLogEntry LogInfo logger.context message logger.config Nothing
  else Nothing

-- | Create a warn log entry (returns Nothing if level too low)
warnEntry :: Logger -> String -> Maybe LogEntry
warnEntry logger message =
  if shouldLog LogWarn logger.config
  then Just $ mkLogEntry LogWarn logger.context message logger.config Nothing
  else Nothing

-- | Create an error log entry (returns Nothing if level too low)
errorEntry :: Logger -> String -> Maybe LogEntry
errorEntry logger message =
  if shouldLog LogError logger.config
  then Just $ mkLogEntry LogError logger.context message logger.config Nothing
  else Nothing

--------------------------------------------------------------------------------
-- Pre-configured Loggers
--------------------------------------------------------------------------------

-- | Default app logger
appLogger :: Logger
appLogger = createLogger "App"

-- | Store logger
storeLogger :: Logger
storeLogger = createLogger "Store"

-- | Engine logger
engineLogger :: Logger
engineLogger = createLogger "Engine"

-- | Layer logger
layerLogger :: Logger
layerLogger = createLogger "Layer"

-- | Render logger
renderLogger :: Logger
renderLogger = createLogger "Render"

-- | Audio logger
audioLogger :: Logger
audioLogger = createLogger "Audio"

-- | Export logger
exportLogger :: Logger
exportLogger = createLogger "Export"
