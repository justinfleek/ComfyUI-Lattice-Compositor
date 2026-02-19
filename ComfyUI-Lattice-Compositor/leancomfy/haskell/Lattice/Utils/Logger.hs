{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DeriveGeneric #-}

{-|
Module      : Lattice.Utils.Logger
Description : Logging utility
Copyright   : (c) Lattice, 2026
License     : MIT

Centralized logging with configurable log levels.
In production, only warnings and errors are shown.
In development, all logs are shown.

Source: leancomfy/lean/Lattice/Utils/Logger.lean
-}

module Lattice.Utils.Logger
  ( -- * Log Levels
    LogLevel(..)
  , levelPriority
  , levelToText
    -- * Logger Configuration
  , LoggerConfig(..)
  , defaultConfig
  , devConfig
    -- * Log Entry
  , LogEntry(..)
  , mkLogEntry
  , formatEntry
    -- * Logger
  , Logger(..)
  , createLogger
  , withConfig
  , setLevel
  , shouldLog
    -- * Logging (Pure)
  , debugEntry
  , infoEntry
  , warnEntry
  , errorEntry
    -- * Pre-configured Loggers
  , appLogger
  , storeLogger
  , engineLogger
  , layerLogger
  , renderLogger
  , audioLogger
  , exportLogger
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import GHC.Generics (Generic)

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
  deriving stock (Eq, Ord, Show, Generic)

-- | Log level priority (lower = more verbose)
levelPriority :: LogLevel -> Int
levelPriority LogDebug = 0
levelPriority LogInfo = 1
levelPriority LogWarn = 2
levelPriority LogError = 3
levelPriority LogNone = 4

-- | Convert log level to text
levelToText :: LogLevel -> Text
levelToText LogDebug = "DEBUG"
levelToText LogInfo = "INFO"
levelToText LogWarn = "WARN"
levelToText LogError = "ERROR"
levelToText LogNone = "NONE"

--------------------------------------------------------------------------------
-- Logger Configuration
--------------------------------------------------------------------------------

-- | Logger configuration
data LoggerConfig = LoggerConfig
  { configLevel :: !LogLevel
  , configPrefix :: !Text
  , configEnableTimestamp :: !Bool
  } deriving stock (Eq, Show, Generic)

-- | Default logger configuration (production)
defaultConfig :: LoggerConfig
defaultConfig = LoggerConfig
  { configLevel = LogWarn
  , configPrefix = "[Lattice]"
  , configEnableTimestamp = False
  }

-- | Development configuration (all logs shown)
devConfig :: LoggerConfig
devConfig = LoggerConfig
  { configLevel = LogDebug
  , configPrefix = "[Lattice]"
  , configEnableTimestamp = True
  }

--------------------------------------------------------------------------------
-- Log Entry
--------------------------------------------------------------------------------

-- | A log entry ready to be outputted
data LogEntry = LogEntry
  { entryLevel :: !LogLevel
  , entryContext :: !Text
  , entryMessage :: !Text
  , entryTimestamp :: !(Maybe Text)
  , entryPrefix :: !Text
  } deriving stock (Eq, Show, Generic)

-- | Create a log entry
mkLogEntry :: LogLevel -> Text -> Text -> LoggerConfig -> Maybe Text -> LogEntry
mkLogEntry level context message config timestamp = LogEntry
  { entryLevel = level
  , entryContext = context
  , entryMessage = message
  , entryTimestamp = if configEnableTimestamp config then timestamp else Nothing
  , entryPrefix = configPrefix config
  }

-- | Format a log entry as text
formatEntry :: LogEntry -> Text
formatEntry entry =
  let parts = concat
        [ case entryTimestamp entry of
            Just ts -> ["[" <> ts <> "]"]
            Nothing -> []
        , if T.null (entryPrefix entry) then [] else [entryPrefix entry]
        , if T.null (entryContext entry) then [] else ["[" <> entryContext entry <> "]"]
        , [entryMessage entry]
        ]
  in T.intercalate " " parts

--------------------------------------------------------------------------------
-- Logger
--------------------------------------------------------------------------------

-- | A logger instance with a specific context
data Logger = Logger
  { loggerContext :: !Text
  , loggerConfig :: !LoggerConfig
  } deriving stock (Eq, Show, Generic)

-- | Create a logger with a specific context
createLogger :: Text -> Logger
createLogger context = Logger
  { loggerContext = context
  , loggerConfig = defaultConfig
  }

-- | Update logger config
withConfig :: Logger -> LoggerConfig -> Logger
withConfig logger config = logger { loggerConfig = config }

-- | Set log level
setLevel :: Logger -> LogLevel -> Logger
setLevel logger level = logger
  { loggerConfig = (loggerConfig logger) { configLevel = level }
  }

-- | Should this log level be shown given the config?
shouldLog :: LogLevel -> LoggerConfig -> Bool
shouldLog level config = levelPriority level >= levelPriority (configLevel config)

--------------------------------------------------------------------------------
-- Logging Functions (Pure)
--------------------------------------------------------------------------------

-- | Create a debug log entry (returns Nothing if level too low)
debugEntry :: Logger -> Text -> Maybe LogEntry
debugEntry logger message =
  if shouldLog LogDebug (loggerConfig logger)
  then Just $ mkLogEntry LogDebug (loggerContext logger) message (loggerConfig logger) Nothing
  else Nothing

-- | Create an info log entry (returns Nothing if level too low)
infoEntry :: Logger -> Text -> Maybe LogEntry
infoEntry logger message =
  if shouldLog LogInfo (loggerConfig logger)
  then Just $ mkLogEntry LogInfo (loggerContext logger) message (loggerConfig logger) Nothing
  else Nothing

-- | Create a warn log entry (returns Nothing if level too low)
warnEntry :: Logger -> Text -> Maybe LogEntry
warnEntry logger message =
  if shouldLog LogWarn (loggerConfig logger)
  then Just $ mkLogEntry LogWarn (loggerContext logger) message (loggerConfig logger) Nothing
  else Nothing

-- | Create an error log entry (returns Nothing if level too low)
errorEntry :: Logger -> Text -> Maybe LogEntry
errorEntry logger message =
  if shouldLog LogError (loggerConfig logger)
  then Just $ mkLogEntry LogError (loggerContext logger) message (loggerConfig logger) Nothing
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
